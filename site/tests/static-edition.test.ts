import { existsSync, readFileSync, statSync } from "node:fs";
import { resolve } from "node:path";
import { describe, expect, it, vi } from "vitest";
import { search, selectionMatches, staticRequest, type SearchIndex, type StaticIndex } from "../src/api/static";

describe("static reader algorithms", () => {
  const index: SearchIndex = { rows: [{ ref: "r", table: "nodes", label: "test", papers: [],
    text: "😀 Straße Σς" }], casefold: { ...Object.fromEntries(Array.from("ABCDEFGHIJKLMNOPQRSTUVWXYZ", (c) => [c, c.toLowerCase()])),
      "ß": "ss", "Σ": "σ", "ς": "σ" }, whitespace: " \n\t" };
  it("keeps Unicode code-point highlights across casefold expansions and astral characters", () => {
    const result = search(index, new URLSearchParams({ q: "STRASSE", limit: "3" }), "m");
    expect(result.total).toBe(1);
    const actual = search(index, new URLSearchParams({ q: "strasse σ" }), "m");
    expect(actual.items[0].matches).toEqual([
      { term: "strasse", start_character: 2, end_character: 8 },
      { term: "σ", start_character: 9, end_character: 10 },
    ]);
  });
  it("filters whole passages by non-whitespace UTF-8 overlap and rejects split characters", () => {
    const bytes = new TextEncoder().encode(" é abc ");
    const data = { coverage: {}, papers: [{ stage: "short", matches: [{ anchor: "a" }] }] };
    const structure = { paper: { passages: [{ anchor: "a", content_span: { start_byte: 1, end_byte: 7 } }] } };
    expect(selectionMatches(data, structure, bytes, 0, 1).papers[0].matches).toEqual([]);
    expect(selectionMatches(data, structure, bytes, 1, 3).papers[0].matches[0].byte_overlaps[0].overlap_span)
      .toEqual({ start_byte: 1, end_byte: 3 });
    expect(() => selectionMatches(data, structure, bytes, 2, 3)).toThrow("UTF-8");
  });
});

describe("table-specific static loading", () => {
  it.each([false, true])("preserves records and pagination with per-table files=%s", async (split) => {
    vi.resetModules();
    const { staticRequest: request } = await import("../src/api/static");
    const nodes = [{ ref: "nodes:z", record: { id: "z" } }, { ref: "nodes:a", record: { id: "a" } }];
    const sources = [{ ref: "sources:s", record: { id: "s" } }];
    const summaries = nodes.map(({ ref }) => ({ ref, label: ref }));
    const index = {
      version: 1, api_version: "1.2", snapshot: { manifest_sha256: "pinned" },
      records: "records.json", summaries: "summaries.json", responses: {}, documents: {},
      ...(split ? { records_by_table: { nodes: "nodes.json", sources: "sources.json" },
        summaries_by_table: { nodes: "node-summaries.json" } } : {}),
    };
    const values: Record<string, unknown> = { "index.json": index,
      "records.json": { nodes, sources }, "summaries.json": { nodes: summaries },
      "nodes.json": nodes, "sources.json": sources, "node-summaries.json": summaries };
    const requested: string[] = [];
    vi.stubGlobal("fetch", vi.fn(async (url: string) => {
      const name = url.split("/edition/")[1];
      requested.push(name);
      if (!(name in values)) throw new Error(`Unexpected file ${name}`);
      return Response.json(values[name]);
    }));
    try {
      const first = await (await request("/api/v1/records?table=nodes&limit=1&manifest=pinned")).json();
      expect(first.data.items).toEqual([nodes[1]]);
      expect(first.data.total).toBe(2);
      expect((await (await request(first.data.next)).json()).data.items).toEqual([nodes[0]]);
      const filtered = await (await request("/api/v1/records?table=nodes&ref=nodes:z")).json();
      expect(filtered.data.items).toEqual([nodes[0]]);
      expect((await (await request("/api/v1/records?table=sources")).json()).data.items).toEqual(sources);
      expect((await (await request("/api/v1/records?table=nodes&representation=summary")).json()).data.items)
        .toEqual([summaries[1], summaries[0]]);
      if (split) {
        expect(requested).not.toContain("records.json");
        expect(requested).not.toContain("summaries.json");
        expect(requested.filter((name) => name === "nodes.json")).toHaveLength(1);
      }
      // Complete queries still include every table and pin mismatches never fetch data.
      expect((await (await request("/api/v1/records")).json()).data.items).toEqual([nodes[1], nodes[0], sources[0]]);
      const beforeMismatch = requested.length;
      expect((await request("/api/v1/records?table=nodes&manifest=wrong")).status).toBe(409);
      expect(requested).toHaveLength(beforeMismatch);
    } finally { vi.unstubAllGlobals(); }
  });
});

describe("reader structure compatibility", () => {
  it.each([false, true])("uses an optional reader projection while preserving the full route (present=%s)", async (compact) => {
    vi.resetModules();
    const { staticRequest: request } = await import("../src/api/static");
    const route = "/papers/short/structure";
    const full = { paper: { passages: [{ anchor: "passage", content_span: { start_byte: 1, end_byte: 7 } }] },
      coverage: { unresolved: ["gap"] }, correspondence_links: ["edge"] };
    const reader = { paper: full.paper, coverage: full.coverage };
    const index = { version: 1, api_version: "1.2", snapshot: { manifest_sha256: "pin" }, documents: { short: "short.md" },
      responses: { [route]: "full.json", "/papers/query?paper=short&representation=matches": "matches.json",
        ...(compact ? { [`${route}?representation=reader`]: "reader.json" } : {}) } };
    const values: Record<string, unknown> = { "index.json": index, "full.json": full, "reader.json": reader,
      "matches.json": { coverage: full.coverage, papers: [{ stage: "short", matches: [{ anchor: "passage" }] }] } };
    const requested: string[] = [];
    vi.stubGlobal("fetch", vi.fn(async (url: string) => {
      const name = url.split("/edition/")[1];
      requested.push(name);
      if (name === "short.md") return new Response(" é abc ");
      return Response.json(values[name]);
    }));
    try {
      expect((await (await request(`/api/v1${route}?representation=reader&manifest=pin`)).json()).data).toEqual(compact ? reader : full);
      const selected = await (await request("/api/v1/papers/query?paper=short&start=1&end=3&manifest=pin")).json();
      expect(selected.data.coverage).toEqual(full.coverage);
      expect(selected.data.papers[0].matches[0].byte_overlaps[0].overlap_span).toEqual({ start_byte: 1, end_byte: 3 });
      if (compact) expect(requested).not.toContain("full.json");
      expect((await (await request(`/api/v1${route}`)).json()).data).toEqual(full);
      expect((await request(`/api/v1${route}?representation=unknown`)).status).toBe(404);
      expect((await request(`/api/v1${route}?representation=reader&manifest=wrong`)).status).toBe(409);
    } finally { vi.unstubAllGlobals(); }
  });
});

describe("the tie loader", () => {
  it("asks for one paper's route and returns its data", async () => {
    vi.resetModules();
    const ties = { segments: [], ties: [], passages: [], meaning: "" };
    const get = vi.fn(async () => ({ data: ties }));
    vi.doMock("../src/api/client", () => ({ get }));
    try {
      const { loadTies } = await import("../src/api/lean");
      expect(await loadTies("short")).toBe(ties);
      expect(get).toHaveBeenCalledWith("/ties/short");
    } finally { vi.doUnmock("../src/api/client"); }
  });
});

describe("on-demand route maps", () => {
  it("finds a response through its route's map without loading other maps", async () => {
    vi.resetModules();
    const { staticRequest: request } = await import("../src/api/static");
    const index = { version: 2, api_version: "1.3", snapshot: { manifest_sha256: "pin" }, documents: {},
      responses: { "/overview": "overview.json" }, route_maps: { "/record": "records-map.json", "/papers/query": "query-map.json" } };
    const values: Record<string, unknown> = { "index.json": index, "overview.json": { a: 1 },
      "records-map.json": { "/record?ref=r": "r.json" }, "r.json": { ref: "r" } };
    const requested: string[] = [];
    vi.stubGlobal("fetch", vi.fn(async (url: string) => {
      const name = url.split("/edition/")[1];
      requested.push(name);
      return Response.json(values[name]);
    }));
    try {
      expect((await (await request("/api/v1/overview")).json()).data).toEqual({ a: 1 });
      expect(requested).not.toContain("records-map.json");
      expect((await (await request("/api/v1/record?ref=r&manifest=pin")).json()).data).toEqual({ ref: "r" });
      expect((await request("/api/v1/record?ref=missing")).status).toBe(404);
      expect(requested).not.toContain("query-map.json");
    } finally { vi.unstubAllGlobals(); }
  });
});

// The normal frontend suite stays usable without Python. The deployment job
// always exports first and sets REQUIRE_STATIC_PARITY to enforce this gate.
const out = resolve("public/edition");
const oracle = resolve("../build/edition-oracle");
const present = existsSync(resolve(out, "index.json")) && existsSync(resolve(oracle, "parity.json"));
if (process.env.REQUIRE_STATIC_PARITY && !present) throw new Error("Export the bundle before static parity tests.");
describe.skipIf(!present)("exported edition against the Python server", () => {
  const read = (name: string) => JSON.parse(readFileSync(resolve(out, name), "utf8"));
  const expected = (name: string) => JSON.parse(readFileSync(resolve(oracle, name), "utf8"));
  const index = () => read("index.json") as StaticIndex;
  const serveFiles = (requests: string[] = []) => vi.stubGlobal("fetch", vi.fn(async (url: string) => {
    requests.push(url);
    return new Response(readFileSync(resolve(out, url.split("/edition/")[1])));
  }));
  const body = async (url: string) => (await (await staticRequest(url)).json()).data;
  const allKeys = () => [...Object.keys(index().responses),
    ...Object.values(index().route_maps ?? {}).flatMap((file) => Object.keys(read(file)))];

  it("matches the server's literal search, pagination, excerpts and highlights", () => {
    const searchIndex = read(index().search) as SearchIndex;
    for (const { params, expected: result } of expected("parity.json")) {
      expect(search(searchIndex, new URLSearchParams(params), index().snapshot.manifest_sha256)).toEqual(result);
    }
  });
  it("publishes per-table files and no whole-edition copies", () => {
    const edition = index();
    expect(edition.records).toBeUndefined();
    expect(edition.summaries).toBeUndefined();
    for (const files of [edition.records_by_table, edition.summaries_by_table]) {
      expect(Object.keys(files!).sort()).toEqual(["citations", "edges", "evidence", "nodes", "sources"]);
    }
  });
  it("retains all paper content and coverage in the smaller reader structures", () => {
    for (const stage of ["long", "short", "expository"]) {
      const route = `/papers/${stage}/structure`;
      const full = expected(`structure-${stage}.json`);
      const reader = read(index().responses[`${route}?representation=reader`]);
      const { correspondence_links: _links, support_record_refs: _refs, representation: _representation,
        representation_version: _version, ...retained } = full;
      expect(reader).toEqual({ ...retained, representation: "reader_structure", representation_version: "1.0",
        omitted_fields: ["correspondence_links", "support_record_refs"] });
      expect(JSON.stringify(reader).length).toBeLessThan(JSON.stringify(full).length);
      expect(index().responses[route]).toBeUndefined();
    }
  });
  it("keeps every field the reader reads from a paper query", () => {
    const map = read(index().route_maps!["/papers/query"]);
    for (const { key, kind, full } of expected("query-samples.json")) {
      const trimmed = read(map[key]);
      expect(trimmed.papers.map((p: any) => p.stage)).toEqual(full.papers.map((p: any) => p.stage));
      if (kind === "node") {
        expect(trimmed.papers.map((p: any) => p.matches)).toEqual(full.papers.map((p: any) => p.matches.map((m: any) => ({
          anchor: m.anchor, witnesses: m.witnesses.slice(0, 1).map((w: any) => ({ root_node_id: w.root_node_id })) }))));
      } else {
        expect(trimmed.coverage).toEqual(full.coverage);
        expect(trimmed.papers.map((p: any) => p.matches)).toEqual(full.papers.map((p: any) => p.matches.map((m: any) => ({
          stage: m.stage, anchor: m.anchor, direct_claim_ids: m.direct_claim_ids, direct_assumption_ids: m.direct_assumption_ids }))));
      }
    }
  });
  it("holds the trimmed paper queries well under 15 MB", () => {
    const map = read(index().route_maps!["/papers/query"]) as Record<string, string>;
    const bytes = [...new Set(Object.values(map))].reduce((sum, file) => sum + statSync(resolve(out, file)).size, 0);
    expect(bytes).toBeLessThan(15e6);
  });
  it("restores passage text so record responses equal the server's", async () => {
    serveFiles();
    try {
      for (const { key, full } of expected("record-samples.json")) expect(await body(`/api/v1${key}`)).toEqual(full);
    } finally { vi.unstubAllGlobals(); }
  });
  it("loads only the startup files on a first visit to the map", async () => {
    const requests: string[] = [];
    serveFiles(requests);
    try {
      await body("/api/v1");
      await Promise.all(["/overview", "/graph?assumptions=true&representation=map&scope=corpus&view=arguments",
        "/records?limit=200&representation=summary&table=nodes", ...["nodes", "sources", "edges", "evidence"].map((t) => `/records?limit=200&offset=0&table=${t}`)]
        .map((path) => staticRequest(`/api/v1${path}`)));
      const names = new Set(requests.map((url) => url.split("/edition/")[1]));
      const maps = Object.values(index().route_maps!);
      expect(maps.filter((file) => names.has(file))).toEqual([]);
      expect([...names].filter((file) => file.startsWith("lean/") || file.startsWith("ties/") || file === "alignment.json")).toEqual([]);
      expect(statSync(resolve(out, "index.json")).size).toBeLessThan(10_000);
    } finally { vi.unstubAllGlobals(); }
  });
  it("serves the Lean and alignment sidecars at fixed paths", async () => {
    const edition = index();
    if (!edition.responses["/lean/modules"]) return;
    expect(edition.responses["/lean/modules"]).toBe("lean/modules.json");
    serveFiles();
    try {
      const modules = await body("/api/v1/lean/modules");
      const names = await body("/api/v1/lean/names");
      expect(names.names.length).toBe(modules.counts.declarations);
      const main = await body("/api/v1/lean/module?name=OAI.Probability.SKSupport.Main");
      expect(main.declarations.find((row: any) => row.short === "full_support").line).toBe(35);
      expect((await staticRequest("/api/v1/lean/module?name=OAI.Nothing")).status).toBe(404);
      expect((await staticRequest("/api/v1/lean/modules?manifest=wrong")).status).toBe(409);
    } finally { vi.unstubAllGlobals(); }
  });
  it("serves each paper's small tie index at a fixed path, loaded apart from the alignment", async () => {
    const edition = index();
    if (!edition.responses["/ties/short"]) return;
    const requests: string[] = [];
    serveFiles(requests);
    try {
      for (const [stage, limit] of [["short", 40_000], ["expository", 40_000], ["long", 120_000]] as const) {
        expect(edition.responses[`/ties/${stage}`]).toBe(`ties/${stage}.json`);
        expect(statSync(resolve(out, `ties/${stage}.json`)).size).toBeLessThan(limit);
        const ties = await body(`/api/v1/ties/${stage}`);
        expect(Object.keys(ties).sort()).toEqual(["meaning", "passages", "segments", "ties"]);
        let previous = 0;
        for (const [start, end, members] of ties.segments) {
          expect(start).toBeGreaterThanOrEqual(previous);
          expect(end).toBeGreaterThan(start);
          for (const member of members) expect(ties.ties[member].at).toMatch(/^b\d+-\d+$/);
          previous = end;
        }
        const tied = ties.ties.find((tie: any) => tie.lean);
        expect(tied.lines[1]).toBeGreaterThanOrEqual(tied.lines[0]);
        expect(typeof tied.name).toBe("string");
        expect(typeof tied.module).toBe("string");
      }
      expect(requests.some((url) => url.endsWith("alignment.json"))).toBe(false);
      expect((await staticRequest("/api/v1/ties/other")).status).toBe(404);
      expect((await staticRequest("/api/v1/ties/short?manifest=wrong")).status).toBe(409);
    } finally { vi.unstubAllGlobals(); }
  });
  it("carries exact Lean lines on every aligned row and statement", () => {
    if (!index().responses["/alignment"]) return;
    const { records } = read("alignment.json");
    for (const record of Object.values<any>(records)) {
      for (const row of record.lean) expect(row.lines[0]).toBeGreaterThanOrEqual(row.line);
      for (const slice of record.statements) {
        expect(slice.at).toBe(`b${slice.start_byte}-${slice.end_byte}`);
        for (const row of slice.lean) expect(row.lines[1]).toBeLessThanOrEqual(row.end_line);
      }
    }
  });
  it("serves all recorded data from static files and enforces edition pins", async () => {
    const requests: string[] = [];
    serveFiles(requests);
    try {
      const discovery = await (await staticRequest("/api/v1")).json();
      const pin = discovery.snapshot.manifest_sha256;
      const response = await staticRequest(`/api/v1/records?table=nodes&limit=3&offset=1&manifest=${pin}`);
      expect((await response.json()).data.items).toHaveLength(3);
      for (const key of allKeys()) expect((await staticRequest(`/api/v1${key}`)).status).toBe(200);
      expect((await staticRequest("/api/v1/overview?manifest=wrong")).status).toBe(409);
      expect(requests.every((url) => url.includes("/edition/"))).toBe(true);
    } finally { vi.unstubAllGlobals(); }
  });
});

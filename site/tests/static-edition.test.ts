import { existsSync, readFileSync } from "node:fs";
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

// The normal frontend suite stays usable without Python. The deployment job
// always exports first and sets REQUIRE_STATIC_PARITY to enforce this gate.
const out = resolve("public/edition");
const present = existsSync(resolve(out, "index.json"));
if (process.env.REQUIRE_STATIC_PARITY && !present) throw new Error("Export the bundle before static parity tests.");
describe.skipIf(!present)("exported edition against the Python server", () => {
  const read = (name: string) => JSON.parse(readFileSync(resolve(out, name), "utf8"));
  it("matches the server's literal search, pagination, excerpts and highlights", () => {
    const index = read("index.json") as StaticIndex;
    const searchIndex = read(index.search) as SearchIndex;
    for (const { params, expected } of read("parity.json")) {
      expect(search(searchIndex, new URLSearchParams(params), index.snapshot.manifest_sha256)).toEqual(expected);
    }
  });
  it("exports each table without changing any records or summaries", () => {
    const index = read("index.json") as StaticIndex;
    for (const [fullFile, tableFiles] of [[index.records, index.records_by_table], [index.summaries, index.summaries_by_table]] as const) {
      expect(tableFiles).toBeDefined();
      const full = read(fullFile);
      expect(Object.keys(tableFiles!).sort()).toEqual(Object.keys(full).sort());
      for (const [table, file] of Object.entries(tableFiles!)) expect(read(file)).toEqual(full[table]);
    }
  });
  it("retains all paper content and coverage in the smaller reader structures", () => {
    const index = read("index.json") as StaticIndex;
    for (const stage of ["long", "short", "expository"]) {
      const route = `/papers/${stage}/structure`;
      const full = read(index.responses[route]);
      const reader = read(index.responses[`${route}?representation=reader`]);
      const { correspondence_links: _links, support_record_refs: _refs, representation: _representation,
        representation_version: _version, ...retained } = full;
      expect(reader).toEqual({ ...retained, representation: "reader_structure", representation_version: "1.0",
        omitted_fields: ["correspondence_links", "support_record_refs"] });
      expect(JSON.stringify(reader).length).toBeLessThan(JSON.stringify(full).length);
    }
  });
  it("serves all recorded data from static files and enforces edition pins", async () => {
    const requests: string[] = [];
    vi.stubGlobal("fetch", vi.fn(async (url: string) => {
      requests.push(url);
      const name = url.split("/edition/")[1];
      return new Response(readFileSync(resolve(out, name)));
    }));
    try {
      const discovery = await (await staticRequest("/api/v1")).json();
      const pin = discovery.snapshot.manifest_sha256;
      const response = await staticRequest(`/api/v1/records?table=nodes&limit=3&offset=1&manifest=${pin}`);
      expect((await response.json()).data.items).toHaveLength(3);
      const index = read("index.json") as StaticIndex;
      for (const key of Object.keys(index.responses)) expect((await staticRequest(`/api/v1${key}`)).status).toBe(200);
      expect((await staticRequest("/api/v1/overview?manifest=wrong")).status).toBe(409);
      expect(requests.every((url) => url.includes("/edition/"))).toBe(true);
    } finally { vi.unstubAllGlobals(); }
  });
});

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

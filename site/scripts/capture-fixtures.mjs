#!/usr/bin/env node
// Capture trimmed test fixtures from a running `lean-exposition serve`.
//
//   node scripts/capture-fixtures.mjs [http://127.0.0.1:8000]
//
// The fixtures keep the fields the site reads, so layout and reader tests run
// without a server. Map links keep every semantic field the API serves
// (theorem applications, their scope, owner and source field): only the
// presentation-only parts of the response are trimmed. The full node, edge,
// evidence and source tables are captured too, so warrant and check tests run
// on real records. Recapture after reassembling the bundle.

import { mkdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";

const origin = process.argv[2] ?? "http://127.0.0.1:8000";
const out = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "tests", "fixtures");

async function get(route, params = {}) {
  const url = new URL(`/api/v1${route}`, origin);
  for (const [k, v] of Object.entries(params)) url.searchParams.set(k, String(v));
  const response = await fetch(url);
  if (!response.ok) throw new Error(`${response.status} ${url}`);
  return response;
}

const discovery = await (await get("")).json();
const manifest = discovery.snapshot.manifest_sha256;
const pinned = (params = {}) => ({ manifest, ...params });

const graph = (await (await get("/graph", pinned({ view: "arguments", representation: "map", scope: "corpus", assumptions: "true" }))).json()).data;
const summaries = (await (await get("/records", pinned({ table: "nodes", representation: "summary", limit: 200 }))).json()).data;
const overview = (await (await get("/overview", pinned())).json()).data;

await mkdir(out, { recursive: true });
const write = (name, value) => writeFile(path.join(out, name), JSON.stringify(value, null, 1) + "\n");

await write("graph-map.json", {
  manifest_sha256: manifest,
  selected_goals: graph.selected_goals,
  records: { nodes: graph.records.nodes, edges: [], citations: [], evidence: graph.records.evidence, sources: [] },
  // Links exactly as served: dropping `application` or `application_scope`
  // would put supplied premises back into the argument.
  links: graph.links,
  components: graph.components.map((c) => ({ id: c.id, cyclic: c.cyclic, members: c.members })),
  coverage: { boundaries: graph.coverage.boundaries, claim: graph.coverage.claim, empty_result_meaning: graph.coverage.empty_result_meaning, query_truncated: graph.coverage.query_truncated },
  records_href: graph.records_href,
});
await write("node-summaries.json", summaries.items);

// Full tables, following the API's pages (at most 200 records each).
async function table(name) {
  const out = [];
  for (let offset = 0; ; offset += 200) {
    const page = (await (await get("/records", pinned({ table: name, limit: 200, offset }))).json()).data;
    out.push(...page.items.map((i) => i.record));
    if (page.items.length < 200 || out.length >= page.total) return out;
  }
}
for (const name of ["nodes", "edges", "evidence", "sources"]) await write(`table-${name}.json`, await table(name));
await write("papers.json", overview.papers.map((p) => ({ stage: p.stage, paper_scope: p.paper_scope, passages: p.passages, sections: p.sections })));

for (const stage of ["long", "short", "expository"]) {
  const structure = (await (await get(`/papers/${stage}/structure`, pinned())).json()).data;
  await write(`structure-${stage}.json`, {
    stage: structure.stage,
    paper: {
      path: structure.paper.path,
      byte_length: structure.paper.byte_length,
      sections: structure.paper.sections,
      passages: structure.paper.passages,
      document_parts: structure.paper.document_parts,
    },
    reading_links: structure.reading_links,
  });
  const bytes = new Uint8Array(await (await get(`/papers/${stage}/document`, pinned())).arrayBuffer());
  await writeFile(path.join(out, `document-${stage}.md`), bytes);
}
console.log(`Captured fixtures for manifest ${manifest} into ${out}`);

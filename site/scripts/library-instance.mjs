#!/usr/bin/env node
// Select the library paper a build is for. Copies instances/<paper>/instance.json to
// src/instances/library/current.json, which the library instance reads, and writes
// public/addresses.json, the table of phrase addresses (/@<tie id>) read from the exported
// edition (public/edition/ties/<slot>.json). Run after export-static.py.
// Usage: library-instance.mjs <paper>
import { copyFileSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";

const paper = process.argv[2] ?? process.env.LX_PAPER;
if (!paper || !/^[a-z0-9-]+$/.test(paper)) throw new Error("Name the library paper: library-instance.mjs <paper>");
const from = resolve(import.meta.dirname, "../../instances", paper, "instance.json");
if (!existsSync(from)) throw new Error(`No library paper ${paper}: ${from} is missing.`);
const instance = JSON.parse(readFileSync(from, "utf8"));
// An adapted edition joins the documents only when the build staged it (LX_ADAPTED=1, set by
// scripts/build_library_paper.sh from the edition's `published` flag); otherwise the paper builds as before.
const adaptedPath = resolve(import.meta.dirname, "../../instances", paper, "adapted/edition.json");
const adapted = process.env.LX_ADAPTED === "1" && existsSync(adaptedPath) ? JSON.parse(readFileSync(adaptedPath, "utf8")).document : null;
if (adapted) instance.documents = [...instance.documents.filter((d) => d.id !== adapted.id), adapted];
// The supports links whose only evidence is the Lean's dependencies (the converter's
// "lean_dependencies" record), so the reader calls them derived from the Lean and never the
// paper's own argument. Links the paper states carry other evidence.
const graphPath = resolve(import.meta.dirname, "../../instances", paper, "evidence-graph.json");
if (existsSync(graphPath)) {
  const graph = JSON.parse(readFileSync(graphPath, "utf8"));
  instance.lean_derived_supports = (graph.edges ?? [])
    .filter((e) => e.kind === "supports" && e.evidence_ids?.length && e.evidence_ids.every((id) => id === "lean_dependencies"))
    .map((e) => `${e.from}→${e.to}`)
    .sort();
}
writeFileSync(resolve(import.meta.dirname, "../src/instances/library/current.json"), JSON.stringify(instance, null, 1) + "\n");
const phrases = {};
// Phrase addresses (/@<id>) open the main document; a companion's phrases keep the reader's own
// addresses under /read/<slot>/. Each numbered result's canonical target in the main document is the
// place of the tie at its statement block (the tie index's `canonical`), so /theorem-1.1/ lands on
// the theorem itself.
const results = {};
const main = instance.documents.find((doc) => doc.main) ?? instance.documents[0];
for (const doc of instance.documents.filter((d) => d.main)) {
  const path = resolve(import.meta.dirname, "../public/edition/ties", `${doc.slot}.json`);
  if (!existsSync(path)) continue;
  const index = JSON.parse(readFileSync(path, "utf8"));
  for (const tie of index.ties ?? []) {
    if (tie.phrase) phrases[tie.phrase] = { record: tie.record ?? null, at: tie.at };
  }
  if (doc === main) {
    for (const [record, [t, start, end]] of Object.entries(index.canonical ?? {})) {
      // With no tie at the statement block, the block's own place is the target.
      if (record.startsWith(`${paper}.`)) results[record.slice(paper.length + 1)] = [t !== null && index.ties[t] ? index.ties[t].at : `b${start}-${end}`, `b${start}-${end}`];
    }
  }
}
// Passages merged into another phrase keep their old id as an address of the phrase that holds them.
// A retired phrase link keeps its address too, but opens a notice (when it was retired, and the nearest
// current phrase to follow), never the neighbour itself.
const aliases = resolve(import.meta.dirname, "../../instances", paper, "alignment/aliases.json");
const retired = {};
if (existsSync(aliases)) {
  const table = JSON.parse(readFileSync(aliases, "utf8"));
  for (const [old, host] of Object.entries(table.passages ?? {})) {
    if (phrases[host] && !phrases[old]) phrases[old] = { ...phrases[host], host };
  }
  for (const [old, row] of Object.entries(table.retired ?? {})) {
    if (!phrases[old]) retired[old] = { retired: row.retired, nearest: row.nearest && phrases[row.nearest] ? row.nearest : null };
  }
}
// Reading notes on Lean and the supplementary checks, published beside the edition when the paper has them.
for (const [from, to] of [["generated/lean-notes.json", "lean-notes.json"], ["generated/checks.json", "checks.json"], ["generated/comparator/receipt.json", "comparator.json"]]) {
  const source = resolve(import.meta.dirname, "../../instances", paper, from);
  const target = resolve(import.meta.dirname, "../public", to);
  if (existsSync(source)) copyFileSync(source, target);
  else if (existsSync(target)) rmSync(target);
}
// The adapted edition's changes, read by the reader's changes layer.
const changesDir = resolve(import.meta.dirname, "../public/changes");
rmSync(changesDir, { recursive: true, force: true });
if (adapted) {
  mkdirSync(changesDir, { recursive: true });
  copyFileSync(resolve(import.meta.dirname, "../../instances", paper, `alignment/changes-${adapted.slot}.json`), resolve(changesDir, `${adapted.slot}.json`));
}
writeFileSync(resolve(import.meta.dirname, "../public/addresses.json"), JSON.stringify({ paper, phrases, retired, results }));
console.log(`library paper: ${paper} (${Object.keys(phrases).length} phrase addresses, ${Object.keys(retired).length} retired, ${Object.keys(results).length} result targets)`);

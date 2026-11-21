#!/usr/bin/env node
// Select the library paper a build is for. Copies instances/<paper>/instance.json to
// src/instances/library/current.json, which the library instance reads, and writes
// public/addresses.json, the table of phrase addresses (/@<tie id>) read from the exported
// edition (public/edition/ties/<slot>.json). Run after export-static.py.
// Usage: library-instance.mjs <paper>
import { copyFileSync, existsSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";

const paper = process.argv[2] ?? process.env.LX_PAPER;
if (!paper || !/^[a-z0-9-]+$/.test(paper)) throw new Error("Name the library paper: library-instance.mjs <paper>");
const from = resolve(import.meta.dirname, "../../instances", paper, "instance.json");
if (!existsSync(from)) throw new Error(`No library paper ${paper}: ${from} is missing.`);
copyFileSync(from, resolve(import.meta.dirname, "../src/instances/library/current.json"));
const instance = JSON.parse(readFileSync(from, "utf8"));
const phrases = {};
// Each numbered result's canonical target in the main document: the place of the tie at its
// statement block (the tie index's `canonical`), so /theorem-1.1/ lands on the theorem itself.
const results = {};
const main = instance.documents.find((doc) => doc.main) ?? instance.documents[0];
for (const doc of instance.documents) {
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
    if (phrases[host] && !phrases[old]) phrases[old] = phrases[host];
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
writeFileSync(resolve(import.meta.dirname, "../public/addresses.json"), JSON.stringify({ paper, phrases, retired, results }));
console.log(`library paper: ${paper} (${Object.keys(phrases).length} phrase addresses, ${Object.keys(retired).length} retired, ${Object.keys(results).length} result targets)`);

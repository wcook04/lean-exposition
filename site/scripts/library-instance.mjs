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
const instance = JSON.parse(readFileSync(from, "utf8"));
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
for (const doc of instance.documents) {
  const path = resolve(import.meta.dirname, "../public/edition/ties", `${doc.slot}.json`);
  if (!existsSync(path)) continue;
  for (const tie of JSON.parse(readFileSync(path, "utf8")).ties ?? []) {
    if (tie.phrase) phrases[tie.phrase] = { record: tie.record ?? null, at: tie.at };
  }
}
// Passages merged into another phrase keep their old id as an address of the phrase that holds them.
const aliases = resolve(import.meta.dirname, "../../instances", paper, "alignment/aliases.json");
if (existsSync(aliases)) {
  for (const [old, host] of Object.entries(JSON.parse(readFileSync(aliases, "utf8")).passages ?? {})) {
    if (phrases[host] && !phrases[old]) phrases[old] = phrases[host];
  }
}
// Reading notes on Lean and the supplementary checks, published beside the edition when the paper has them.
for (const [from, to] of [["generated/lean-notes.json", "lean-notes.json"], ["generated/checks.json", "checks.json"], ["generated/comparator/receipt.json", "comparator.json"]]) {
  const source = resolve(import.meta.dirname, "../../instances", paper, from);
  const target = resolve(import.meta.dirname, "../public", to);
  if (existsSync(source)) copyFileSync(source, target);
  else if (existsSync(target)) rmSync(target);
}
writeFileSync(resolve(import.meta.dirname, "../public/addresses.json"), JSON.stringify({ paper, phrases }));
console.log(`library paper: ${paper} (${Object.keys(phrases).length} phrase addresses)`);

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
// The paper's optional reading aids (generated/): what the formal development does in each section
// goes into the build with the instance, because the paper's text is laid out with it; the glossary
// of conventions and the showcase cards are published as one file the reader fetches when idle.
const generated = (name) => {
  const path = resolve(import.meta.dirname, "../../instances", paper, "generated", name);
  return existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : null;
};
const sectionAids = (() => {
  const raw = generated("section-aids.json") ?? generated("reading_aids.json");
  if (!raw) return null;
  // Euler's file is the table itself; Navier–Stokes's keeps the paper's sections under `paper`.
  const table = raw.paper ?? raw.sections ?? raw.aids ?? raw;
  if (Array.isArray(table)) return Object.fromEntries(table.filter((row) => row && (row.section ?? row.key) && (row.aid ?? row.text)).map((row) => [String(row.section ?? row.key), String(row.aid ?? row.text)]));
  return Object.fromEntries(Object.entries(table).filter(([, text]) => typeof text === "string"));
})();
writeFileSync(resolve(import.meta.dirname, "../src/instances/library/current.json"), JSON.stringify(sectionAids ? { ...instance, section_aids: sectionAids } : instance, null, 1));
const phrases = {};
// Phrase addresses (/@<id>) open the main document; a companion's phrases keep the reader's own
// addresses under /read/<slot>/.
for (const doc of instance.documents.filter((d) => d.main)) {
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
    if (phrases[host] && !phrases[old]) phrases[old] = { ...phrases[host], host };
  }
}
// Reading notes on Lean and the supplementary checks, published beside the edition when the paper has them.
for (const [from, to] of [["generated/lean-notes.json", "lean-notes.json"], ["generated/checks.json", "checks.json"], ["generated/comparator/receipt.json", "comparator.json"]]) {
  const source = resolve(import.meta.dirname, "../../instances", paper, from);
  const target = resolve(import.meta.dirname, "../public", to);
  if (existsSync(source)) copyFileSync(source, target);
  else if (existsSync(target)) rmSync(target);
}
const aids = { glossary: generated("glossary.json") ?? [], showcase: generated("showcase.json") ?? [] };
const aidsPath = resolve(import.meta.dirname, "../public/aids.json");
if (aids.glossary.length || aids.showcase.length) writeFileSync(aidsPath, JSON.stringify(aids));
else if (existsSync(aidsPath)) rmSync(aidsPath);
writeFileSync(resolve(import.meta.dirname, "../public/addresses.json"), JSON.stringify({ paper, phrases }));
console.log(`library paper: ${paper} (${Object.keys(phrases).length} phrase addresses)`);

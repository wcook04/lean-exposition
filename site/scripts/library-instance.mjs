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
    const place = ([t, start, end]) => [t !== null && index.ties[t] ? index.ties[t].at : `b${start}-${end}`, `b${start}-${end}`];
    for (const [record, target] of Object.entries(index.canonical ?? {})) {
      // With no tie at the statement block, the block's own place is the target.
      if (record.startsWith(`${paper}.`)) results[record.slice(paper.length + 1)] = place(target);
    }
    // A paper whose records keep other ids (a reader that moved into the library) names each
    // result's record in alignment/results.json; the address then carries the record too.
    const table = resolve(import.meta.dirname, "../../instances", paper, "alignment/results.json");
    if (existsSync(table)) {
      for (const [address, row] of Object.entries(JSON.parse(readFileSync(table, "utf8")).results ?? {})) {
        if (!row.record || row.record.startsWith(`${paper}.`)) continue;
        // A result with no statement slice in the main document opens at its record, with no place.
        results[address] = index.canonical?.[row.record] ? [...place(index.canonical[row.record]), row.record] : ["", "", row.record];
      }
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
for (const [from, to] of [["generated/lean-notes.json", "lean-notes.json"], ["generated/checks.json", "checks.json"], ["generated/comparator/receipt.json", "comparator.json"], ["generated/differences-summary.md", "differences.md"]]) {
  const source = resolve(import.meta.dirname, "../../instances", paper, from);
  const target = resolve(import.meta.dirname, "../public", to);
  if (existsSync(source)) copyFileSync(source, target);
  else if (existsSync(target)) rmSync(target);
}
const laterChecks = [];
// Our own Lean statements beside the authors' (generated/ours.json): each comparison is filed under
// the phrase that now carries its card (p::<passage>, tie::<key>, through the aliases).
{
  const source = resolve(import.meta.dirname, "../../instances", paper, "generated/ours.json");
  const target = resolve(import.meta.dirname, "../public/ours.json");
  if (existsSync(source)) {
    const ours = JSON.parse(readFileSync(source, "utf8"));
    const byPhrase = {};
    for (const row of ours.comparisons ?? []) {
      const id = row.card.replace(/^(p|tie)::/, "");
      const host = phrases[id]?.host ?? id;
      if (!phrases[host]) throw new Error(`ours.json: card ${row.card} names no phrase of the paper`);
      (byPhrase[host] ??= []).push({ lean: row.lean, fidelity: row.fidelity, note: row.note });
    }
    writeFileSync(target, JSON.stringify({ declarations: ours.declarations, byPhrase }));
    // Later checks readers may ask about (ours.checks, keyed by the Lean constant's last name): read
    // before the first render with the addresses, so a passage that mentions one shows it in place.
    for (const [constant, row] of Object.entries(ours.checks ?? {})) laterChecks.push({ constant, ...row });
  } else if (existsSync(target)) rmSync(target);
}
// Pages that moved (instance.json moved_pages): /<old>/ opens its new page, and /<old>/@<id> opens the
// phrase on whichever of the listed pages now holds it (only those off the new page are written).
const moved = {};
for (const [from, row] of Object.entries(instance.moved_pages ?? {})) {
  const slot = (slug) => instance.documents.find((d) => d.slug === slug)?.slot;
  if (!slot(row.to)) throw new Error(`moved_pages: ${from} moves to ${row.to}, which is no page of the paper`);
  if (slot(from)) throw new Error(`moved_pages: ${from} is still a page of the paper`);
  const onPage = {};
  for (const page of row.phrases_from ?? []) {
    if (!slot(page)) throw new Error(`moved_pages: ${from} lists ${page}, which is no page of the paper`);
    if (page === row.to) continue;
    const ties = JSON.parse(readFileSync(resolve(import.meta.dirname, "../../instances", paper, "alignment", `phrases-${slot(page)}.json`), "utf8")).ties ?? [];
    for (const tie of ties) onPage[tie.id] ??= page;
  }
  moved[from] = { to: row.to, phrases: onPage };
}
writeFileSync(resolve(import.meta.dirname, "../public/addresses.json"), JSON.stringify({ paper, phrases, retired, results, moved, checks: laterChecks }));
console.log(`library paper: ${paper} (${Object.keys(phrases).length} phrase addresses, ${Object.keys(retired).length} retired, ${Object.keys(results).length} result targets, ${Object.keys(moved).length} moved pages)`);

#!/usr/bin/env node
// Check reader annotations with the same KaTeX renderer the reader uses.
// Usage: node scripts/check-tex.mjs <paper>   (from site/)
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import { noteHtml } from "../src/reader/math.ts";
import { unformattedAnnotationTokens } from "./annotation-notation.ts";

const paper = process.argv[2];
const root = resolve(import.meta.dirname, "../../instances", paper ?? "");
if (!paper || !existsSync(root)) throw new Error("Name an existing reader instance");
const read = (rel) => (existsSync(resolve(root, rel)) ? JSON.parse(readFileSync(resolve(root, rel), "utf8")) : null);
const fields = [];
const notationProblems = [];

function explanation(where, note) {
  if (!note) return;
  fields.push([where, note.text], [`${where} (open question)`, note.open]);
  for (const citation of note.citations ?? []) fields.push([`${where} (citation)`, citation.supports]);
}

function phrases(file) {
  const data = read(file);
  if (!data) return;
  fields.push([`${file}: main result`, data.main_result]);
  for (const part of data.parts ?? []) {
    for (const [name, text] of Object.entries(part.titles ?? {})) fields.push([`${file}: title ${name}`, text]);
    for (const [name, text] of Object.entries(part.notes ?? {})) fields.push([`${file}: note ${name}`, text]);
  }
  for (const tie of data.ties ?? []) {
    const where = `${file}: ${tie.id}`;
    explanation(where, tie.explanation);
    for (const row of tie.lean ?? []) {
      const declaration = `${where} ${row.name}`;
      fields.push([declaration, row.fidelity_note], [declaration, row.link_note], [declaration, row.matters?.line]);
      for (const assessment of row.assessments ?? []) {
        fields.push([`${declaration} for ${assessment.phrase}`, assessment.fidelity_note]);
      }
    }
  }
}

for (const [name, title] of Object.entries(read("alignment/names.json")?.names ?? {})) {
  fields.push([`title ${name}`, title]);
}
const alignment = resolve(root, "alignment");
if (existsSync(alignment)) {
  for (const name of readdirSync(alignment)) {
    if (/^phrases-.+\.json$/.test(name)) phrases(`alignment/${name}`);
    if (/(?:^|-)results\.json$|^records\.json$/.test(name)) {
      const data = read(`alignment/${name}`);
      for (const [id, record] of Object.entries(data.records ?? data.results ?? {})) {
        for (const place of [record, ...(record.statements ?? [])]) {
          for (const row of place.lean ?? []) {
            fields.push([`${name}: ${id} ${row.name}`, row.fidelity_note], [`${name}: ${id} ${row.name}`, row.note]);
          }
        }
      }
    }
  }
}
const adapted = read("adapted/edition.json")?.document?.slot;
if (adapted && !existsSync(resolve(alignment, `phrases-${adapted}.json`))) phrases("adapted/phrases.json");

const annotations = resolve(root, "annotations");
if (existsSync(annotations)) {
  for (const name of readdirSync(annotations).sort()) {
    if (!name.endsWith(".json")) continue;
    const data = Object.entries(read(`annotations/${name}`));
    const declarations = new Set(data.flatMap(([, notes]) => Object.keys(notes).map((declaration) => declaration.split(".").at(-1))));
    for (const [phrase, notes] of data) {
      for (const [declaration, text] of Object.entries(notes)) {
        const where = `annotations/${name}: ${phrase} ${declaration}`;
        fields.push([where, text]);
        const unformatted = unformattedAnnotationTokens(text, declarations);
        if (unformatted.length) {
          notationProblems.push(`${where}: mark code with backticks and math with $…$: ${unformatted.join(", ")}`);
        }
      }
    }
  }
}

for (const [name, note] of Object.entries(read("generated/lean-notes.json")?.notes ?? {})) {
  fields.push([`Lean note ${name}`, note.text], [`Lean summary ${name}`, note.summary]);
}
for (const review of read("statement-comparisons.json")?.reviews ?? []) {
  const where = `comparison ${review.passage} ${review.name}`;
  fields.push([where, review.fidelity_note], [where, review.note]);
  explanation(where, review.explanation);
}
const readingNotes = read("lean-notes.json");
for (const [name, text] of Object.entries(readingNotes?.reader_notes ?? {})) {
  fields.push([`Lean note ${name}`, text]);
}
for (const [name, excerpts] of Object.entries(readingNotes?.excerpts ?? {})) {
  for (const excerpt of excerpts) fields.push([`Lean excerpt ${name}`, excerpt.reading_note]);
}

const localTies = read("passage-ties.json");
for (const [id, passage] of Object.entries(localTies?.passages ?? {})) {
  for (const focus of Object.values(passage.focus ?? {})) fields.push([`paper passage ${id}`, focus.note]);
}

const prose = fields.filter(([, text]) => typeof text === "string" && text.length > 0);
const problems = [...notationProblems, ...prose.flatMap(([where, text]) => noteHtml(text).errors.map((error) => `${where}: ${error}`))];
if (problems.length) {
  console.error(`${paper}: ${problems.length} annotation error(s):\n${problems.slice(0, 30).map((p) => `  - ${p}`).join("\n")}`);
  process.exit(1);
}
console.log(`${paper}: ${prose.length} annotation fields checked with the reader renderer`);

#!/usr/bin/env node
// Every formula a library paper's cards show must typeset: titles, reading notes and summaries,
// and comparison notes. Each $...$ is rendered with KaTeX; text outside formulas may hold no
// backslash command and no unmatched $. Fails naming each field that would show raw TeX.
// Usage: check-tex.mjs <paper>   (from site/)
import { existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import katex from "katex";

const paper = process.argv[2];
const root = resolve(import.meta.dirname, "../../instances", paper);
const read = (rel) => (existsSync(resolve(root, rel)) ? JSON.parse(readFileSync(resolve(root, rel), "utf8")) : null);
const fields = [];
const names = read("alignment/names.json");
for (const [name, title] of Object.entries(names?.names ?? {})) fields.push([`title ${name}`, title]);
for (const slot of ["long", "short", "expository"]) {
  const phrases = read(`alignment/phrases-${slot}.json`);
  for (const part of phrases?.parts ?? []) {
    for (const [name, t] of Object.entries(part.titles ?? {})) fields.push([`${slot} title ${name}`, t]);
    for (const [name, n] of Object.entries(part.notes ?? {})) fields.push([`${slot} note ${name}`, n]);
  }
  for (const tie of phrases?.ties ?? []) for (const row of tie.lean ?? []) if (row.fidelity_note) fields.push([`comparison ${tie.id} ${row.name}`, row.fidelity_note]);
}
for (const [name, note] of Object.entries(read("generated/lean-notes.json")?.notes ?? {})) {
  fields.push([`lean note ${name}`, note.text]);
  if (note.summary) fields.push([`lean summary ${name}`, note.summary]);
}
const problems = [];
for (const [where, text] of fields) {
  if (typeof text !== "string") continue;
  const parts = text.split(/(?<!\\)\$/);
  if (parts.length % 2 === 0) {
    problems.push(`${where}: an unmatched $`);
    continue;
  }
  parts.forEach((part, k) => {
    if (k % 2) {
      try {
        katex.renderToString(part, { throwOnError: true, output: "html", strict: "ignore" });
      } catch (error) {
        problems.push(`${where}: $${part.slice(0, 50)}$ does not typeset (${String(error.message).slice(0, 80)})`);
      }
    } else if (/\\[A-Za-z]+/.test(part.replace(/`[^`]*`/g, ""))) {
      problems.push(`${where}: a TeX command outside $...$: ${part.match(/\\[A-Za-z]+/)[0]}`);
    }
  });
}
if (problems.length) {
  console.error(`${paper}: ${problems.length} field(s) would show raw TeX:\n${problems.slice(0, 20).map((p) => `  - ${p}`).join("\n")}`);
  process.exit(1);
}
console.log(`${paper}: ${fields.length} titles, notes and comparisons typeset`);

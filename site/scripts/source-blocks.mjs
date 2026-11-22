#!/usr/bin/env node
// Print the top-level blocks of a Markdown reading copy as JSON: for each block its heading,
// its index under that heading (from 1, reset at every heading), its kind and its lines
// (1-based, end exclusive). These are the paragraph ids "<heading>#<block>" that Proof Reader's
// paragraph dispositions and an adapted edition's change map use (Proof Reader's
// web/tools/render-paper.mjs, --markdown-source): a table or list is one block, and blank lines
// inside a fence do not split it.
// Usage: source-blocks.mjs PAPER.md
import { readFileSync } from "node:fs";
import MarkdownIt from "markdown-it";

const text = readFileSync(process.argv[2], "utf8");
const tokens = new MarkdownIt({ html: true }).parse(text, {});
const blocks = [];
let heading = "";
let block = 0;
for (let i = 0; i < tokens.length; i++) {
  const token = tokens[i];
  if (token.level !== 0 || !token.map) continue;
  if (token.type === "heading_open") {
    heading = tokens[i + 1].content;
    block = 0;
    continue;
  }
  blocks.push({ heading, block: ++block, kind: token.type, line: token.map[0] + 1, end_line: token.map[1] + 1 });
}
process.stdout.write(JSON.stringify(blocks));

// What search reads besides the edition's index: the papers' exact statements from the
// alignment, and the full text of the three papers. Both are built the first time a reader
// searches, block by block, and are never touched at startup.

import type { Alignment, AlignedStatement } from "../api/lean";
import type { SearchItem, Stage } from "../api/types";
import { loadPaper } from "../app/data";
import { STAGE_ORDER } from "../app/papers";
import { routeHref } from "../app/router";
import { alignmentResource } from "../compare/useAlignment";
import { holdsWord, rankRows, type IndexRow } from "./rank";

export interface CorpusRow extends IndexRow {
  stage: Stage;
  href: string;
  section: string;
  /** A statement's kind of saying and its record's short title. */
  role?: string;
}

const STATEMENT_HREF = (statement: AlignedStatement) => routeHref({ view: "read", stage: statement.paper, anchor: statement.anchor ?? undefined, at: `b${statement.start_byte}-${statement.end_byte}` });

/** Each exact statement once, with the record that gives it. A bare mention is left to the paper's text. */
export function statementRows(alignment: Alignment): CorpusRow[] {
  const seen = new Set<string>();
  const rows: CorpusRow[] = [];
  for (const record of Object.values(alignment.records)) {
    for (const statement of record.statements) {
      const key = `${statement.paper}:${statement.start_byte}`;
      if (statement.role === "mention" || seen.has(key)) continue;
      seen.add(key);
      rows.push({ ref: `statement:${key}`, table: "statements", label: record.short, text: statement.markdown.replace(/\*\*/g, ""), stage: statement.paper, papers: [statement.paper], href: STATEMENT_HREF(statement), section: statement.section, role: statement.role });
    }
  }
  return rows;
}

const encoder = new TextEncoder();
const HEADING = /^#{1,6}\s+(.*)$/;

/** A paper cut at blank lines, keeping each block's bytes so a result can land exactly there. A display formula stays one block. */
export function paperBlocks(stage: Stage, markdown: string): CorpusRow[] {
  const rows: CorpusRow[] = [];
  let section = "";
  let byte = 0;
  let start = 0;
  let open: string[] = [];
  let inDisplay = false;
  const close = () => {
    const text = open.join("\n");
    if (text.trim() && !HEADING.test(text.trim()) && !/^references$/i.test(section)) {
      const end = start + encoder.encode(text).length;
      // An address is not the paper's words, and its hyphens would read as word breaks.
      rows.push({ ref: `paper:${stage}:${start}`, table: "paper", label: section, text: text.replace(/https?:\/\/[^\s)]+/g, "").replace(/\*\*/g, ""), stage, papers: [stage], href: routeHref({ view: "read", stage, at: `b${start}-${end}` }), section });
    }
    open = [];
  };
  for (const line of markdown.split("\n")) {
    const size = encoder.encode(line).length + 1;
    const heading = HEADING.exec(line);
    if (!inDisplay && line.trim() === "") {
      close();
      start = byte + size;
    } else {
      if (!open.length) start = byte;
      if (heading && !inDisplay) section = heading[1].trim();
      open.push(line);
      if (((line.match(/\$\$/g) ?? []).length) % 2 === 1) inDisplay = !inDisplay;
    }
    byte += size;
  }
  close();
  return rows;
}

let statements: Promise<CorpusRow[]> | null = null;
let papers: Promise<CorpusRow[]> | null = null;

function statementsResource(): Promise<CorpusRow[]> {
  statements ??= alignmentResource().then((alignment) => (alignment ? statementRows(alignment) : []));
  return statements;
}

function papersResource(): Promise<CorpusRow[]> {
  const decoder = new TextDecoder();
  papers ??= Promise.all(STAGE_ORDER.map((stage) => loadPaper(stage).then((paper) => paperBlocks(stage, decoder.decode(paper.bytes))))).then((all) => all.flat());
  papers.catch(() => {
    papers = null;
  });
  return papers;
}

const PAPERS = ["short", "long", "expository"];
const ROLES = ["statement", "definition", "derivation", "explanation", "example"];

/** A statement of what was searched for comes before a passage that only uses the words. */
export function orderStatements(items: readonly SearchItem[], q: string): SearchItem[] {
  const words = q.toLowerCase().split(/\s+/).filter(Boolean);
  const named = (item: SearchItem) => Number(words.every((word) => holdsWord(String(item.label ?? "").toLowerCase(), word)));
  const opens = (item: SearchItem) => Number((item.matches?.[0]?.start_character ?? Infinity) < 80);
  const role = (item: SearchItem) => ROLES.indexOf(String(item.role));
  const paper = (item: SearchItem) => PAPERS.indexOf(String((item.papers as string[] | undefined)?.[0]));
  return items
    .map((item, i) => ({ item, i }))
    .sort((a, b) => named(b.item) - named(a.item) || role(a.item) - role(b.item) || paper(a.item) - paper(b.item) || opens(b.item) - opens(a.item) || a.i - b.i)
    .map((row) => row.item);
}

export const searchStatements = (q: string): Promise<SearchItem[]> => statementsResource().then((rows) => orderStatements(rankRows(rows, q).get("statements") ?? [], q));
export const searchPapers = (q: string): Promise<SearchItem[]> => papersResource().then((rows) => rankRows(rows, q).get("paper") ?? []);

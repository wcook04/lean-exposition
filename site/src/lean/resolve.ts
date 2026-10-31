// Which declaration a name in the code refers to. The source index records the names
// each declaration uses, so a name is looked up there first, then along its namespace.
// A name bound in the code itself is left alone, and a name found nowhere in OpenAI's
// source is treated as Mathlib's only when it has the look of a library name.

import type { DictionaryTerm, LeanDeclaration, LeanKind, LeanNameRow, LeanNames } from "../api/lean";
import { tokenize, type LeanToken } from "./tokenize";

export interface DeclRow {
  name: string;
  short: string;
  kind: LeanKind;
  module: string;
  line: number;
  endLine: number;
}

export interface LeanIndex {
  byName: Map<string, DeclRow[]>;
  rows: DeclRow[];
  lower: string[];
}

export function buildIndex(names: LeanNames): LeanIndex {
  const byName = new Map<string, DeclRow[]>();
  const rows = names.names.map(([name, kind, module, line, endLine]: LeanNameRow) => {
    const row: DeclRow = { name, short: name.slice(name.lastIndexOf(".") + 1), kind, module: names.modules[module], line, endLine };
    const same = byName.get(name);
    if (same) same.push(row);
    else byName.set(name, [row]);
    return row;
  });
  return { byName, rows, lower: rows.map((row) => row.name.toLowerCase()) };
}

/** A name can be declared twice: once in OAI and once in the comparison challenge files. */
export function findDecl(index: LeanIndex, name: string, near?: string): DeclRow | undefined {
  const rows = index.byName.get(name);
  if (!rows) return undefined;
  if (rows.length === 1) return rows[0];
  const root = near?.split(".")[0];
  return rows.find((r) => r.module === near) ?? rows.find((r) => root && r.module.startsWith(`${root}.`)) ?? rows.find((r) => !r.module.startsWith("ComparatorChallenges")) ?? rows[0];
}

export type NameTarget =
  | { kind: "decl"; row: DeclRow; term?: DictionaryTerm }
  | { kind: "mathlib"; name: string; words?: string };

export interface Scope {
  self: string;
  namespace: string;
  module: string;
  uses: readonly string[];
  /** Names bound in the code, with the first name of their type where it was written. */
  locals: Map<string, string | undefined>;
  index: LeanIndex;
  terms: Map<string, DictionaryTerm>;
}

const NOTATION: Record<string, { name: string; words: string }> = {
  ℝ: { name: "Real", words: "The real numbers." },
  ℕ: { name: "Nat", words: "The natural numbers." },
  ℤ: { name: "Int", words: "The integers." },
  ℚ: { name: "Rat", words: "The rational numbers." },
  ℂ: { name: "Complex", words: "The complex numbers." },
};

const LOWER_LIBRARY = new Set(
  "deriv derivWithin sSup sInf iSup iInf univ volume abs exp log sqrt sin cos id max min fderiv rexp cexp nhds nhdsWithin atTop atBot".split(" "),
);

function isLibraryShaped(text: string): boolean {
  if (text.length < 2 || text.startsWith(".")) return false;
  return text.includes(".") || text.includes("_") || /^\p{Lu}/u.test(text) || LOWER_LIBRARY.has(text);
}

function namespaceChain(namespace: string): string[] {
  const parts = namespace.split(".").filter(Boolean);
  return parts.map((_, k) => parts.slice(0, parts.length - k).join("."));
}

function inUses(uses: readonly string[], name: string): string | undefined {
  const tail = `.${name}`;
  let best: string | undefined;
  for (const used of uses) {
    if (used === name) return used;
    if (used.endsWith(tail) && (!best || used.length < best.length)) best = used;
  }
  return best;
}

function lookup(name: string, scope: Scope, extra: string[] = []): DeclRow | undefined {
  const used = inUses(scope.uses, name);
  if (used) {
    const row = findDecl(scope.index, used, scope.module);
    if (row) return row;
  }
  for (const space of [...extra, ...namespaceChain(scope.namespace)]) {
    const row = findDecl(scope.index, `${space}.${name}`, scope.module);
    if (row) return row;
  }
  return findDecl(scope.index, name, scope.module);
}

function target(row: DeclRow, scope: Scope): NameTarget {
  return { kind: "decl", row, term: scope.terms.get(row.name) };
}

/** What a name in the code refers to, or null when it should stay plain text. */
export function resolveName(text: string, scope: Scope): NameTarget | null {
  if (text.startsWith(".")) return null;
  const glyph = NOTATION[text];
  if (glyph) return { kind: "mathlib", name: glyph.name, words: glyph.words };

  const parts = text.split(".");
  if (scope.locals.has(parts[0])) {
    if (parts.length === 1) return null;
    const type = scope.locals.get(parts[0]);
    if (type) {
      const owner = lookup(type, scope);
      const field = owner && findDecl(scope.index, `${owner.name}.${parts[1]}`, scope.module);
      if (field) return target(field, scope);
    }
    const used = inUses(scope.uses, parts[1]);
    const row = used ? findDecl(scope.index, used, scope.module) : undefined;
    return row ? target(row, scope) : null;
  }

  const structure = [scope.self];
  for (let k = parts.length; k > 0; k--) {
    const row = lookup(parts.slice(0, k).join("."), scope, structure);
    if (row) return target(row, scope);
  }
  return isLibraryShaped(text) ? { kind: "mathlib", name: text } : null;
}

const mathlibSearch = "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=";

export const mathlibUrl = (name: string) => `${mathlibSearch}${encodeURIComponent(name)}`;

/** Binders recorded by the tokenizer, added to `into`. */
export function collectLocals(tokens: readonly LeanToken[], into: Map<string, string | undefined>): void {
  for (const token of tokens) if (token.kind === "binder" && !(token.text in NOTATION) && !into.get(token.text)) into.set(token.text, token.of);
}

const moduleVariables = new Map<string, Map<string, string | undefined>>();

/** What the module's `variable` lines bind, for every declaration in it. */
export function variablesOf(module: string, source: string): Map<string, string | undefined> {
  let found = moduleVariables.get(module);
  if (!found) {
    found = new Map();
    for (const hit of source.matchAll(/^\s*variable\b([^\n]*(?:\n[ \t]+[^\n]*)*)/gm)) collectLocals(tokenize(`def v ${hit[1]}`), found);
    moduleVariables.set(module, found);
  }
  return found;
}

export function makeScope(decl: LeanDeclaration, module: { module: string; source: string }, index: LeanIndex, terms: Map<string, DictionaryTerm>): Scope {
  return { self: decl.name, namespace: decl.namespace, module: module.module, uses: decl.uses, locals: new Map(variablesOf(module.module, module.source)), index, terms };
}

const OPENERS = new Set(["(", "{", "[", "⦃", "⟨"]);
const CLOSERS = new Set([")", "}", "]", "⦄", "⟩"]);

export interface StatementShape {
  /** The name heading the conclusion, when the conclusion is that name applied to arguments and nothing else. */
  conclusion?: string;
  /** The name heading each `(h : P ...)` hypothesis. */
  hypotheses: string[];
}

/** Read what a statement concludes and assumes from its tokens. */
export function statementShape(tokens: readonly LeanToken[]): StatementShape {
  const real = tokens.filter((t) => t.kind !== "space" && t.kind !== "comment" && t.kind !== "doc");
  const hypotheses: string[] = [];
  const isName = (t?: LeanToken) => t !== undefined && (t.kind === "name" || t.kind === "type");
  let depth = 0;
  let colon = -1;
  let end = real.length;
  for (let i = 0; i < real.length; i++) {
    const t = real[i];
    if (t.kind === "bracket" && OPENERS.has(t.text)) {
      if (depth === 0 && colon < 0 && t.text === "(") {
        let j = i + 1;
        while (real[j]?.kind === "binder") j++;
        if (j > i + 1 && real[j]?.text === ":" && isName(real[j + 1])) hypotheses.push(real[j + 1].text);
      }
      depth++;
    } else if (t.kind === "bracket" && CLOSERS.has(t.text)) depth--;
    else if (depth === 0 && (t.text === ":=" || t.text === "where" || t.text === "by")) {
      end = i;
      break;
    } else if (depth === 0 && t.text === ":" && colon < 0) colon = i;
  }
  if (colon < 0) return { hypotheses };
  let start = colon + 1;
  depth = 0;
  let plain = true;
  for (let i = colon + 1; i < end; i++) {
    const t = real[i];
    if (t.kind === "bracket") depth += OPENERS.has(t.text) ? 1 : -1;
    else if (depth === 0 && (t.text === "→" || t.text === ",")) {
      start = i + 1;
      plain = true;
    } else if (depth === 0 && t.kind === "op") plain = false;
  }
  return { conclusion: plain && isName(real[start]) ? real[start].text : undefined, hypotheses };
}

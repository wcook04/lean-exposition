// Colouring for one recorded statement, on the map's theorem plate and in the
// record panel. The tokens come from the reading tokenizer in ../lean/tokenize;
// concatenating their texts always returns the input unchanged.

import { tokenize, type LeanTokenKind as FullKind } from "../lean/tokenize";

export type LeanTokenKind = "keyword" | "bracket" | "binder" | "arrow" | "ident" | "number" | "punct" | "space";

export interface LeanToken {
  kind: LeanTokenKind;
  text: string;
}

const ARROWS = new Set(["↔", "→", "←", "⟹", "=>", "->", "<->", "<-", "↦", "∧", "∨", "¬", ":=", "≤", "≥", "≠", "∈", "∉", "⊆", "×", "∘"]);

const KINDS: Partial<Record<FullKind, LeanTokenKind>> = {
  keyword: "keyword",
  tactic: "keyword",
  binder: "binder",
  bracket: "bracket",
  number: "number",
  space: "space",
  type: "ident",
  name: "ident",
};

/** The reading tokenizer's result in the map's smaller vocabulary. */
export function tokenizeLean(source: string): LeanToken[] {
  const tokens: LeanToken[] = [];
  for (const { kind, text } of tokenize(source)) {
    const mapped = kind === "op" ? (ARROWS.has(text) ? "arrow" : "punct") : (KINDS[kind] ?? "punct");
    const last = tokens[tokens.length - 1];
    if (last && last.kind === mapped && (mapped === "space" || mapped === "punct")) last.text += text;
    else tokens.push({ kind: mapped, text });
  }
  return tokens;
}

const SIG_OPEN = "([{⦃⟨";
const SIG_CLOSE = ")]}⦄⟩";
const DECLARATION = /^(theorem|lemma|def|abbrev|instance|example|axiom)\s/;

/**
 * Lay out a one-line declaration signature the way Lean code is usually
 * written: the head on the first line, then each top-level binder on its own
 * line and the type after the final colon, all indented by two spaces.
 * Only whitespace changes; anything that is not a single-line declaration is
 * returned unchanged.
 */
export function formatLeanSignature(source: string): string {
  const text = source.trim();
  if (!DECLARATION.test(text) || text.includes("\n")) return source;
  const lines: string[] = [];
  let current = "";
  let depth = 0;
  let seenBinder = false;
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (depth === 0 && SIG_OPEN.includes(ch)) {
      if (current.trim()) lines.push(current.trimEnd());
      current = "  ";
      seenBinder = true;
    }
    if (SIG_OPEN.includes(ch)) depth += 1;
    if (SIG_CLOSE.includes(ch)) depth = Math.max(0, depth - 1);
    // The colon that introduces the statement's type, after the binders.
    if (depth === 0 && seenBinder && ch === ":" && text[i - 1] === " " && text[i + 1] === " " && text[i + 2] !== "=") {
      lines.push(`${current.trimEnd()} :`);
      current = "  ";
      i += 1; // skip the space after the colon
      continue;
    }
    if (depth === 0 && ch === " " && current.trim() === "") continue;
    current += ch;
  }
  if (current.trim()) lines.push(current.trimEnd());
  return seenBinder ? lines.join("\n") : source;
}

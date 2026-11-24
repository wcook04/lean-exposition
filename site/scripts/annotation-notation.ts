// Code and math in consolidated notes have different reader typography. Check
// visible prose only. KaTeX and delimiter errors are reported by check-tex.mjs.
const formatted = /\\\$|`[^`]*`|\$(?:\\\$|[^$])*\$/g;
const identifiers = /[A-Za-z][A-Za-z\d_']*(?:\.[A-Za-z][A-Za-z\d_']*)*/g;
const proseTerms = new Set(["a.e", "e.g", "i.e", "KaTeX", "LaTeX"]);
const symbols = /[\p{Script=Greek}⁰¹²³⁴⁵⁶⁷⁸⁹\u207a-\u209cℓℕℤℚℝℂ∀∃∈∉∋⊂⊆⊇≤≥≠↔→⇒≃⟨⟩⊕⊗∑∏√∞∂∅∘∧∨¬±−×·′=+^<>`]/gu;
const expressions = /\b(?:\d+\s*\/\s*\d+|\d+[a-z]\b|[A-Za-z]\([\w, ]+\)|[A-Za-z]'(?=[\s.,?!]|$))/g;

/** Unstyled tokens with a clear code or math reading. Ordinary prose can overlap
 * with unqualified Lean names, so only flag those when named explicitly. */
export function unformattedAnnotationTokens(text: string, declarations: ReadonlySet<string>): string[] {
  const plain = text.replace(formatted, " ");
  const tokens = new Set<string>();
  for (const name of plain.match(identifiers) ?? []) {
    if (proseTerms.has(name)) continue;
    if (/[_.]|[a-z\d][A-Z]/.test(name)) tokens.add(name);
  }
  for (const match of plain.matchAll(/\bLean (?:theorem|lemma|definition|declaration|identifier)\s+([A-Za-z][A-Za-z\d']*)/g)) {
    if (declarations.has(match[1])) tokens.add(match[1]);
  }
  for (const token of plain.match(symbols) ?? []) tokens.add(token);
  for (const token of plain.match(expressions) ?? []) tokens.add(token);
  for (const match of plain.matchAll(/\b(?:divided by|multiplied by|variable|parameter)\s+([A-Za-z])(?=[.,;:!?)]|$)/g)) {
    tokens.add(match[1]);
  }
  return [...tokens];
}

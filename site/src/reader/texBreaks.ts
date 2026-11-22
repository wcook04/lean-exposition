// Where a display formula may break, read from its TeX.
//
// A display too wide for its column breaks at its top level only: never inside braces,
// brackets, \left…\right or an environment. In order of preference it breaks
//   1. between independent formulas: at a comma (or semicolon) followed by \quad or \qquad,
//      "A = B, \qquad C = D." becomes two stacked lines;
//   2. before each relation sign after the first (=, ≤, <, …), as aligned continuation lines;
//   3. before a plus or minus, with a hanging indent.
// breakForms returns these as complete TeX for KaTeX, coarsest first; the reader shows the first
// that fits (PaperBody.tsx, fitDisplay). The equation number stays on the last line.

interface Token {
  /** The token's text: a command with its name ("\\qquad"), a one-character symbol, or a space run. */
  text: string;
  /** Nesting depth before the token: braces, brackets, \left…\right and environments together. */
  depth: number;
}

const OPEN = new Set(["{", "(", "[", "\\{", "\\lbrace", "\\langle", "\\lvert", "\\lVert", "\\lfloor", "\\lceil", "\\left", "\\begin"]);
const CLOSE = new Set(["}", ")", "]", "\\}", "\\rbrace", "\\rangle", "\\rvert", "\\rVert", "\\rfloor", "\\rceil", "\\right", "\\end"]);

/** Relation signs a display may break before. */
const RELATIONS = new Set([
  "=", "<", ">", "\\le", "\\leq", "\\ge", "\\geq", "\\leqslant", "\\geqslant", "\\lesssim", "\\gtrsim",
  "\\ll", "\\gg", "\\ne", "\\neq", "\\equiv", "\\approx", "\\sim", "\\simeq", "\\coloneqq",
]);
const SUMS = new Set(["+", "-", "\\pm", "\\mp"]);
const QUADS = new Set(["\\quad", "\\qquad"]);

export function tokenize(tex: string): Token[] {
  const out: Token[] = [];
  let depth = 0;
  let i = 0;
  while (i < tex.length) {
    const c = tex[i];
    let text: string;
    if (c === "\\") {
      const m = /^\\([A-Za-z]+|.)/s.exec(tex.slice(i));
      text = m ? m[0] : "\\";
    } else if (/\s/.test(c)) {
      text = /^\s+/.exec(tex.slice(i))![0];
    } else text = c;
    out.push({ text, depth });
    i += text.length;
    // \left( and \right) carry their delimiter: the pair counts once, not the delimiter too.
    if (text === "\\left" || text === "\\right") {
      const d = /^\s*(\\[A-Za-z]+|\\.|.)/s.exec(tex.slice(i));
      if (d) {
        out.push({ text: d[0], depth: text === "\\left" ? depth + 1 : Math.max(0, depth - 1) });
        i += d[0].length;
      }
    }
    if (OPEN.has(text)) depth++;
    else if (CLOSE.has(text)) depth = Math.max(0, depth - 1);
  }
  return out;
}

export interface DisplayParts {
  /** The formula, without an outer equation environment, its number, label or \nonumber. */
  body: string;
  /** The number's command as written ("\\tag{1.2}"), or null. */
  tag: string | null;
}

/** Take the number and any outer equation environment off a display's TeX. */
export function splitDisplay(tex: string): DisplayParts {
  let body = tex.trim();
  const env = /^\\begin\{(equation\*?)\}([\s\S]*)\\end\{\1\}$/.exec(body);
  if (env) body = env[2];
  let tag: string | null = null;
  const tokens = tokenize(body);
  let kept = "";
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.depth === 0 && (t.text === "\\tag" || t.text === "\\label")) {
      let j = i + 1;
      if (tokens[j]?.text === "*") j++;
      while (tokens[j] && /^\s+$/.test(tokens[j].text)) j++;
      if (tokens[j]?.text !== "{") {
        kept += t.text;
        continue;
      }
      let k = j + 1;
      while (k < tokens.length && !(tokens[k].text === "}" && tokens[k].depth === 1)) k++;
      const text = tokens.slice(i, k + 1).map((x) => x.text).join("");
      if (t.text === "\\tag") tag = text;
      i = k;
      continue;
    }
    if (t.depth === 0 && (t.text === "\\nonumber" || t.text === "\\notag")) continue;
    kept += t.text;
  }
  return { body: kept.trim(), tag };
}

const significant = (t: Token | undefined) => !!t && !/^\s+$/.test(t.text);

/** Split at top-level commas (or semicolons) followed by \quad or \qquad. The comma stays on the left. */
export function independentFormulas(body: string): string[] {
  const tokens = tokenize(body);
  const parts: string[] = [];
  let current = "";
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    current += t.text;
    if (t.depth !== 0 || (t.text !== "," && t.text !== ";")) continue;
    let j = i + 1;
    let quads = 0;
    while (j < tokens.length && tokens[j].depth === 0 && (QUADS.has(tokens[j].text) || !significant(tokens[j]))) {
      if (QUADS.has(tokens[j].text)) quads++;
      j++;
    }
    if (!quads || j >= tokens.length) continue;
    parts.push(current.trim());
    current = "";
    i = j - 1;
  }
  if (current.trim()) parts.push(current.trim());
  return parts.length > 1 ? parts : [body.trim()];
}

/** Top-level positions (token indices) of relation signs; ":" before "=" belongs to the "=". */
function relationAt(tokens: Token[]): number[] {
  const at: number[] = [];
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.depth !== 0 || !RELATIONS.has(t.text)) continue;
    // A relation right after "_" or "^" is a script; the second of two relations ("<=") is not a new line.
    const prev = previous(tokens, i);
    if (prev && (prev.text === "_" || prev.text === "^")) continue;
    if (prev && RELATIONS.has(prev.text)) continue;
    at.push(prev?.text === ":" ? tokens.indexOf(prev) : i);
  }
  return at;
}

function previous(tokens: Token[], i: number): Token | undefined {
  for (let j = i - 1; j >= 0; j--) if (significant(tokens[j])) return tokens[j];
  return undefined;
}

/** Top-level positions of binary plus and minus signs (not a leading sign, nor one after a relation or another operator). */
function sumAt(tokens: Token[], from = 0): number[] {
  const at: number[] = [];
  for (let i = from; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.depth !== 0 || !SUMS.has(t.text)) continue;
    const prev = previous(tokens, i);
    if (!prev || RELATIONS.has(prev.text) || SUMS.has(prev.text) || prev.text === "," || prev.text === "_" || prev.text === "^" || prev.text === ":") continue;
    if (prev.depth === 0 && OPEN.has(prev.text)) continue;
    at.push(i);
  }
  return at;
}

const join = (tokens: Token[], from: number, to: number) => tokens.slice(from, to).map((t) => t.text).join("").trim();

/** The relation lines of one formula: its left side, then one line per relation sign. */
export function relationLines(formula: string): { left: string; rights: string[] } {
  const tokens = tokenize(formula);
  const at = relationAt(tokens);
  if (!at.length) return { left: "", rights: [formula.trim()] };
  const rights: string[] = [];
  for (let k = 0; k < at.length; k++) rights.push(join(tokens, at[k], at[k + 1] ?? tokens.length));
  return { left: join(tokens, 0, at[0]), rights };
}

/**
 * Split a line at top-level plus and minus signs into `pieces` runs of about equal length. A
 * line that starts with its relation sign keeps the sign on its first run.
 */
export function sumRuns(line: string, pieces: number): string[] {
  const tokens = tokenize(line);
  const first = tokens.findIndex(significant);
  const start = first >= 0 && RELATIONS.has(tokens[first].text) ? first + 1 : 0;
  const at = sumAt(tokens, start);
  if (!at.length || pieces < 2) return [line.trim()];
  const total = line.length;
  const cuts: number[] = [];
  let offset = 0;
  const offsets = tokens.map((t) => {
    const o = offset;
    offset += t.text.length;
    return o;
  });
  for (let k = 1; k < pieces; k++) {
    const goal = (total * k) / pieces;
    let best = -1;
    for (const i of at) if (!cuts.includes(i) && (best < 0 || Math.abs(offsets[i] - goal) < Math.abs(offsets[best] - goal))) best = i;
    if (best >= 0 && !cuts.includes(best)) cuts.push(best);
  }
  cuts.sort((a, b) => a - b);
  const runs: string[] = [];
  let from = 0;
  for (const c of cuts) {
    const run = join(tokens, from, c);
    if (run) runs.push(run);
    from = c;
  }
  runs.push(join(tokens, from, tokens.length));
  return runs.filter(Boolean);
}

/** A new line. The empty group keeps a following "[" from reading as the line break's spacing argument. */
const ROW = "\\\\{}";

/** A display that already has its own lines or columns is not broken again. */
function alreadyLaidOut(body: string): boolean {
  return tokenize(body).some((t) => t.depth === 0 && (t.text === "\\\\" || t.text === "&"));
}

/** One formula's rows: [left of the alignment point, right of it]. */
type Rows = [string, string][];

function formulaRows(formula: string, relations: boolean, pieces: number): Rows {
  const { left, rights } = relations ? relationLines(formula) : { left: "", rights: [formula] };
  const rows: Rows = [];
  rights.forEach((right, k) => {
    const runs = sumRuns(right, pieces);
    runs.forEach((run, r) => rows.push([k === 0 && r === 0 ? left : "", r === 0 ? run : `\\qquad{}${run}`]));
  });
  return rows;
}

function blockTex(rows: Rows): string {
  if (rows.length === 1 && !rows[0][0]) return rows[0][1];
  return `\\begin{aligned}${rows.map(([l, r]) => `${l}&${r}`).join(ROW)}\\end{aligned}`;
}

function formTex(blocks: Rows[], tag: string | null): string {
  const number = tag ?? "";
  if (blocks.length === 1) {
    const rows = blocks[0];
    if (rows.length === 1) return `${rows[0][0]}${rows[0][1]}${number}`;
    return `\\begin{align*}${rows.map(([l, r]) => `${l}&${r}`).join(ROW)}${number}\\end{align*}`;
  }
  return `\\begin{gather*}${blocks.map(blockTex).join(ROW)}${number}\\end{gather*}`;
}

/**
 * The broken forms of a display's TeX, coarsest first: stacked independent formulas, then
 * also a line per relation sign, then also runs split at plus and minus (in two, then three).
 * Empty when the formula has no top-level break or already has its own lines. With
 * `number: false` the forms leave the equation number out.
 */
export function breakForms(tex: string, { number = true }: { number?: boolean } = {}): string[] {
  const split = splitDisplay(tex);
  const body = split.body;
  // Without its number when the reader sets the number beside the formula itself.
  const tag = number ? split.tag : null;
  if (!body || alreadyLaidOut(body)) return [];
  const formulas = independentFormulas(body);
  const forms: string[] = [];
  const add = (blocks: Rows[]) => {
    const rows = blocks.reduce((n, b) => n + b.length, 0);
    if (rows < 2) return;
    const form = formTex(blocks, tag);
    if (!forms.includes(form)) forms.push(form);
  };
  if (formulas.length > 1) add(formulas.map((f) => [["", f]] as Rows));
  add(formulas.map((f) => formulaRows(f, true, 1)));
  add(formulas.map((f) => formulaRows(f, true, 2)));
  add(formulas.map((f) => formulaRows(f, true, 3)));
  return forms;
}

/**
 * A display's single equation number as it is printed ("(1.2)"; a starred \tag* as written),
 * when the TeX has exactly one plain \tag. Null otherwise: no number, several, or one with markup.
 */
export function plainNumber(tex: string): string | null {
  if ((tex.match(/\\tag\b/g) ?? []).length !== 1) return null;
  const { tag } = splitDisplay(tex);
  const m = tag ? /^\\tag(\*?)\s*\{([^{}\\$]*)\}$/.exec(tag) : null;
  if (!m || !m[2].trim()) return null;
  return m[1] ? m[2].trim() : `(${m[2].trim()})`;
}

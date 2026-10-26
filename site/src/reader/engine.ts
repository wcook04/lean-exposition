// Manuscript rendering engine.
//
// prepareDocument() slices the exact Markdown bytes into the API's document
// parts, then (cheaply, without KaTeX) strips front matter, comments and
// passage markers, extracts LaTeX figures, protects math, collects every
// reference definition of the whole document, parses each part with
// markdown-it and assigns document-unique fragment ids. render(i) turns one
// part's tokens into sanitised HTML and substitutes KaTeX output last.

import MarkdownIt from "markdown-it";
import type { Env, Token } from "markdown-it";
import { AnchorRegistry, byteOffsetOf, githubSlug, pandocIdentifier } from "./anchors";
import { classifyHref } from "./links";
import {
  DISPLAY_CLOSE,
  DISPLAY_OPEN,
  INLINE_CLOSE,
  INLINE_OPEN,
  protectMath,
  renderTex,
  type MathSpan,
} from "./math";
import { sanitizeHtml } from "./sanitize";

export { byteOffsetOf };

export interface PreparedPart {
  index: number;
  kind: "passage" | "text";
  anchor?: string;
  span: { start: number; end: number };
  headings: { id: string; level: number; title: string; aliases: string[] }[];
  anchors: string[];
  figures: { key: string; caption: string; source: string }[];
  blank: boolean;
}

export interface PreparedDocument {
  stage: string;
  frontMatter: Record<string, unknown> | null;
  parts: PreparedPart[];
  anchorIndex: Map<string, number>;
  /** Number of math spans (including figure captions) across all parts. */
  mathCount: number;
  /** Non-fatal problems found while preparing (duplicate explicit ids). */
  issues: string[];
  render(index: number): RenderedPart;
  renderAll(): RenderedPart[];
}

export interface RenderedPart {
  index: number;
  html: string;
  mathErrors: { tex: string; message: string }[];
}

export interface PrepareInput {
  stage: string;
  bytes: Uint8Array;
  parts?: { kind: string; span: { start_byte: number; end_byte: number }; passageAnchor?: string }[];
  documentPath: string;
  documentPaths: Record<string, string>;
}

// ---------------------------------------------------------------- markdown-it

interface RenderEnv extends Env {
  /** The account a fragment link belongs to, so a copy shown elsewhere can resolve it. */
  stage: string;
  documentPath: string;
  documentPaths: Record<string, string>;
  linkClose: string[];
}

const md = new MarkdownIt({ html: true, linkify: false, typographer: true });
// A print-only space request has no web content. Match only a whole line;
// Markdown's code rules run first, so literal examples remain untouched.
md.block.ruler.before("paragraph", "print_spacing", (state, startLine, _endLine, silent) => {
  if (state.sCount[startLine] - state.blkIndent >= 4) return false;
  const line = state.src.slice(state.bMarks[startLine] + state.tShift[startLine], state.eMarks[startLine]);
  const command = /^\\Needspace[ \t]*(?=\{)/.exec(line);
  if (!command) return false;
  const argument = braceGroup(line, command[0].length);
  if (!argument || line.slice(argument.end).trim()) return false;
  if (!silent) state.line = startLine + 1;
  return true;
}, { alt: ["paragraph"] });
// Pandoc's `smart` extension converts quotes, dashes and ellipses but not
// (c), (r), (tm) or +-. Keep markdown-it's smartquotes, replace the rest.
md.disable("replacements");
md.core.ruler.after("inline", "pandoc_dashes", (state) => {
  for (const block of state.tokens) {
    if (block.type !== "inline" || !block.children) continue;
    for (const t of block.children) {
      if (t.type === "text") {
        t.content = t.content.replace(/---/g, "—").replace(/--/g, "–").replace(/\.\.\./g, "…");
      }
    }
  }
});

// Bold run-in paragraphs ("**Theorem 1 (…).**", "**Proof.**", "**Strict curvature.**").
const RUN_IN = /^(\p{Lu}[\p{L}\p{N}-]*)[^]*[.:?]$/u;
md.core.ruler.push("run_in", (state) => {
  const tokens = state.tokens;
  for (let i = 0; i + 1 < tokens.length; i++) {
    if (tokens[i].type !== "paragraph_open" || tokens[i + 1].type !== "inline") continue;
    const kids = tokens[i + 1].children ?? [];
    let k = 0;
    while (k < kids.length && kids[k].type === "text" && kids[k].content.trim() === "") k++;
    if (kids[k]?.type !== "strong_open") continue;
    let text = "";
    let j = k + 1;
    for (; j < kids.length && kids[j].type !== "strong_close"; j++) text += kids[j].content;
    if (j >= kids.length) continue;
    const m = RUN_IN.exec(text.trim());
    if (!m) continue;
    tokens[i].attrJoin("class", "run-in");
    tokens[i].attrSet("data-run-in", m[1].toLowerCase());
    kids[k].attrJoin("class", "run-in__lead");
  }
});

const esc = md.utils.escapeHtml;
const PAPER_STAGES = new Set(["long", "short", "expository"]);

md.renderer.rules.link_open = (tokens, idx, _opts, envAny) => {
  const env = envAny as unknown as RenderEnv;
  const t = tokens[idx];
  const href = String(t.attrGet("href") ?? "");
  const title = t.attrGet("title");
  const titleAttr = title ? ` title="${esc(String(title))}"` : "";
  const target = classifyHref(href, env.documentPath, env.documentPaths);
  switch (target.kind) {
    case "fragment": {
      env.linkClose.push("</a>");
      const own = PAPER_STAGES.has(env.stage) ? ` data-in="${esc(env.stage)}"` : "";
      return `<a href="${esc(target.href)}"${own}${titleAttr}>`;
    }
    case "external":
      env.linkClose.push("</a>");
      return `<a href="${esc(target.href)}" class="ext" data-external="" target="_blank" rel="noopener noreferrer"${titleAttr}>`;
    case "mailto":
      env.linkClose.push("</a>");
      return `<a href="${esc(target.href)}"${titleAttr}>`;
    case "companion":
      env.linkClose.push("</a>");
      return `<a href="${esc(target.href)}" class="companion" data-companion="${esc(target.stage)}" data-fragment="${esc(target.fragment)}"${titleAttr}>`;
    case "unresolved":
      env.linkClose.push("</span>");
      return `<span class="link-unresolved" data-unresolved-href="${esc(target.original)}">`;
    default:
      env.linkClose.push("</span>");
      return `<span class="link-blocked">`;
  }
};
md.renderer.rules.link_close = (_t, _i, _o, envAny) => (envAny as unknown as RenderEnv).linkClose.pop() ?? "</a>";

const defaultHeadingOpen = md.renderer.rules.heading_open;
md.renderer.rules.heading_open = (tokens, idx, opts, env, self) => {
  const aliases = (tokens[idx].meta?.aliases as string[] | undefined) ?? [];
  const pre = aliases.map((a) => `<a id="${esc(a)}" class="anchor" aria-hidden="true"></a>`).join("");
  const open = defaultHeadingOpen ? defaultHeadingOpen(tokens, idx, opts, env, self) : self.renderToken(tokens, idx, opts);
  return pre + open;
};

// ----------------------------------------------------------------- utilities

const decoder = () => new TextDecoder("utf-8", { ignoreBOM: true });

/** Minimal YAML for manuscript front matter: scalars, lists, `|` blocks. */
export function parseFrontMatter(src: string): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  const lines = src.split(/\r?\n/);
  const scalar = (v: string): unknown => {
    const s = v.trim();
    if (/^".*"$/.test(s)) {
      try {
        return JSON.parse(s);
      } catch {
        return s.slice(1, -1);
      }
    }
    if (/^'.*'$/.test(s)) return s.slice(1, -1).replace(/''/g, "'");
    if (s === "true") return true;
    if (s === "false") return false;
    if (/^-?\d+(\.\d+)?$/.test(s)) return Number(s);
    return s;
  };
  const indentOf = (l: string) => l.length - l.trimStart().length;
  for (let i = 0; i < lines.length; i++) {
    const m = /^([A-Za-z0-9_-]+):\s*(.*)$/.exec(lines[i]);
    if (!m) continue;
    const [, key, rest] = m;
    if (rest !== "" && rest !== "|" && rest !== ">") {
      out[key] = scalar(rest);
      continue;
    }
    const block: string[] = [];
    while (i + 1 < lines.length && (lines[i + 1].trim() === "" || indentOf(lines[i + 1]) > 0)) block.push(lines[++i]);
    if (rest === "|" || rest === ">") {
      out[key] = dedent(block).join(rest === "|" ? "\n" : " ");
      continue;
    }
    const items: unknown[] = [];
    for (let b = 0; b < block.length; b++) {
      const im = /^(\s*)-\s*(.*)$/.exec(block[b]);
      if (!im) continue;
      const ind = im[1].length;
      if (im[2] === "|" || im[2] === ">") {
        const body: string[] = [];
        while (b + 1 < block.length && (block[b + 1].trim() === "" || indentOf(block[b + 1]) > ind)) body.push(block[++b]);
        items.push(dedent(body).join("\n").replace(/\n+$/, ""));
      } else items.push(scalar(im[2]));
    }
    out[key] = items;
  }
  return out;
}

function dedent(lines: string[]): string[] {
  const ind = Math.min(...lines.filter((l) => l.trim()).map((l) => l.length - l.trimStart().length));
  return lines.map((l) => l.slice(Number.isFinite(ind) ? ind : 0));
}

/** Synchronous SHA-256 (hex) of a string's UTF-8 bytes. */
export function sha256Hex(text: string): string {
  const K = new Uint32Array([
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
  ]);
  const data = new TextEncoder().encode(text);
  const bitLen = data.length * 8;
  const padded = new Uint8Array(((data.length + 9 + 63) >> 6) << 6);
  padded.set(data);
  padded[data.length] = 0x80;
  const view = new DataView(padded.buffer);
  view.setUint32(padded.length - 8, Math.floor(bitLen / 0x100000000));
  view.setUint32(padded.length - 4, bitLen >>> 0);
  const H = new Uint32Array([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]);
  const W = new Uint32Array(64);
  const rotr = (x: number, n: number) => (x >>> n) | (x << (32 - n));
  for (let off = 0; off < padded.length; off += 64) {
    for (let t = 0; t < 16; t++) W[t] = view.getUint32(off + t * 4);
    for (let t = 16; t < 64; t++) {
      const s0 = rotr(W[t - 15], 7) ^ rotr(W[t - 15], 18) ^ (W[t - 15] >>> 3);
      const s1 = rotr(W[t - 2], 17) ^ rotr(W[t - 2], 19) ^ (W[t - 2] >>> 10);
      W[t] = (W[t - 16] + s0 + W[t - 7] + s1) >>> 0;
    }
    let [a, b, c, d, e, f, g, h] = H;
    for (let t = 0; t < 64; t++) {
      const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
      const ch = (e & f) ^ (~e & g);
      const t1 = (h + S1 + ch + K[t] + W[t]) >>> 0;
      const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + maj) >>> 0;
      h = g;
      g = f;
      f = e;
      e = (d + t1) >>> 0;
      d = c;
      c = b;
      b = a;
      a = (t1 + t2) >>> 0;
    }
    H[0] += a; H[1] += b; H[2] += c; H[3] += d; H[4] += e; H[5] += f; H[6] += g; H[7] += h;
  }
  return Array.from(H, (x) => x.toString(16).padStart(8, "0")).join("");
}

// ------------------------------------------------------------------- figures

/** Read a balanced `{…}` group starting at `open` (index of `{`). */
function braceGroup(s: string, open: number): { body: string; end: number } | null {
  if (s[open] !== "{") return null;
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    const c = s[i];
    if (c === "\\") {
      i++;
      continue;
    }
    if (c === "{") depth++;
    else if (c === "}" && --depth === 0) return { body: s.slice(open + 1, i), end: i + 1 };
  }
  return null;
}

function commandArg(s: string, name: string): { body: string; start: number; end: number } | null {
  const at = s.indexOf(`\\${name}{`);
  if (at < 0) return null;
  const g = braceGroup(s, at + name.length + 1);
  return g ? { body: g.body, start: at, end: g.end } : null;
}

function stripTexComments(s: string): string {
  return s
    .split("\n")
    .map((l) => l.replace(/(^|[^\\])%.*$/, "$1"))
    .join("\n");
}

/** Caption TeX to HTML (math left as placeholders) and to plain text. */
function convertCaption(tex: string, spans: MathSpan[]): { html: string; plain: string } {
  const { text } = protectMath(tex.replace(/\s+/g, " ").trim(), spans);
  const walk = (s: string, asHtml: boolean): string => {
    let out = "";
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (c === "\\") {
        const m = /^\\([A-Za-z]+|.)/.exec(s.slice(i));
        const name = m ? m[1] : "";
        if (name === "href") {
          const u = braceGroup(s, i + 5);
          const t = u ? braceGroup(s, u.end) : null;
          if (u && t) {
            const inner = walk(t.body, asHtml);
            if (asHtml && /^https?:\/\//i.test(u.body.trim())) {
              out += `<a href="${esc(u.body.trim())}" class="ext" data-external="" target="_blank" rel="noopener noreferrer">${inner}</a>`;
            } else out += inner;
            i = t.end - 1;
            continue;
          }
        }
        if (name === "emph" || name === "textit" || name === "textbf" || name === "text") {
          const g = braceGroup(s, i + 1 + name.length);
          if (g) {
            const inner = walk(g.body, asHtml);
            const tag = name === "textbf" ? "strong" : name === "text" ? "" : "em";
            out += asHtml && tag ? `<${tag}>${inner}</${tag}>` : inner;
            i = g.end - 1;
            continue;
          }
        }
        if (name.length === 1 && "%&#_$ {}".includes(name)) {
          out += asHtml ? esc(name) : name;
          i += 1;
          continue;
        }
        if (name === "\\") {
          out += asHtml ? "<br>" : " ";
          i += 1;
          continue;
        }
        // Unknown command: keep it visible rather than dropping text.
        out += asHtml ? esc(`\\${name}`) : `\\${name}`;
        i += name.length;
        continue;
      }
      if (c === "{" || c === "}") continue;
      if (c === "~") {
        out += " ";
        continue;
      }
      if (s.startsWith("---", i)) {
        out += "—";
        i += 2;
        continue;
      }
      if (s.startsWith("--", i)) {
        out += "–";
        i += 1;
        continue;
      }
      if (s.startsWith("``", i)) {
        out += "“";
        i += 1;
        continue;
      }
      if (s.startsWith("''", i)) {
        out += "”";
        i += 1;
        continue;
      }
      out += asHtml ? esc(c) : c;
    }
    return out;
  };
  const html = walk(text, true);
  const plain = walk(text, false).replace(
    new RegExp(`[${INLINE_OPEN}${DISPLAY_OPEN}](\\d+)[${INLINE_CLOSE}${DISPLAY_CLOSE}]`, "g"),
    (_m, n: string) => spans[Number(n)]?.tex ?? "",
  );
  return { html, plain };
}

interface FigureInfo {
  key: string;
  caption: string;
  source: string;
  captionHtml: string;
}

const FIG_OPEN = "";
const FIG_CLOSE = "";

/**
 * Figure KEY rule (stable; React figure components are keyed by it):
 *   the `\label{…}` value inside the figure when present, otherwise
 *   `fig-` + the first 10 hex characters of SHA-256 over the figure source
 *   from `\begin{figure}` to `\end{figure}` inclusive, with every run of
 *   whitespace collapsed to one space and the ends trimmed.
 */
export function figureKey(figureEnv: string): string {
  const label = commandArg(stripTexComments(figureEnv), "label");
  if (label && label.body.trim()) return label.body.trim();
  return "fig-" + sha256Hex(figureEnv.replace(/\s+/g, " ").trim()).slice(0, 10);
}

function parseFigure(env: string, spans: MathSpan[]): FigureInfo {
  const clean = stripTexComments(env);
  const tikz = /\\begin\{tikzpicture\}[\s\S]*?\\end\{tikzpicture\}/.exec(env);
  let captionTex = commandArg(clean, "caption")?.body ?? "";
  captionTex = captionTex.replace(/\\label\{[^}]*\}/g, "");
  const { html, plain } = convertCaption(captionTex, spans);
  return { key: figureKey(env), caption: plain, source: tikz ? tikz[0] : env, captionHtml: html };
}

const FIGURE_ENV = /\\begin\{figure\*?\}(?:\[[^\]]*\])?[\s\S]*?\\end\{figure\*?\}/g;

function extractFigures(src: string, figures: FigureInfo[], spans: MathSpan[]): string {
  const mark = (env: string) => {
    figures.push(parseFigure(env, spans));
    return `\n\n${FIG_OPEN}${figures.length - 1}${FIG_CLOSE}\n\n`;
  };
  // Fenced raw LaTeX (```{=latex}): figures become slots, anything else is
  // dropped, as Pandoc drops raw LaTeX when writing HTML.
  let out = src.replace(/^(`{3,}|~{3,})[ \t]*\{=latex\}[^\n]*\n([\s\S]*?)^\1[ \t]*$/gm, (_m, _f, body: string) => {
    const envs = body.match(FIGURE_ENV) ?? [];
    return envs.map(mark).join("");
  });
  // Unfenced figure environments (Pandoc raw_tex blocks).
  out = out.replace(new RegExp(`^[ \\t]*${FIGURE_ENV.source}[ \\t]*$`, "gm"), (env) => mark(env.trim()));
  return out;
}

// ---------------------------------------------------------------- preparation

interface PartState {
  tokens: Token[];
  spans: MathSpan[];
  figures: FigureInfo[];
  rendered?: RenderedPart;
}

function preprocess(text: string, atStart: boolean, frontMatter: { value: Record<string, unknown> | null }): string {
  let src = text;
  if (atStart) {
    const fm = /^---[ \t]*\r?\n([\s\S]*?)\r?\n(?:---|\.\.\.)[ \t]*(?:\r?\n|$)/.exec(src);
    if (fm) {
      frontMatter.value = parseFrontMatter(fm[1]);
      src = src.slice(fm[0].length);
    }
  }
  // Whole-line comments (passage markers, editorial notes) vanish with their line.
  src = src.replace(/^[ \t]*<!--[\s\S]*?-->[ \t]*(?:\r?\n|$)/gm, "");
  src = src.replace(/<!--[\s\S]*?-->/g, "");
  // PDF-only wrappers around companion links: keep the inner Markdown link.
  src = src.replace(/<span\s+class="pdf-companion"[^>]*>([\s\S]*?)<\/span>/g, "$1");
  // Explicit bookmarks.
  src = src.replace(/<a\s+id="([^"]+)"\s*>\s*<\/a>/g, '<a id="$1" class="anchor" aria-hidden="true"></a>');
  return src;
}

const REF_DEF = /^ {0,3}\[(?:[^\]\\\n]|\\.)+\]:[ \t]*\S.*$/gm;

function inlineText(children: Token[], spans: MathSpan[]): string {
  let s = "";
  for (const c of children) {
    if (c.type === "text" || c.type === "code_inline") s += c.content;
    else if (c.type === "softbreak" || c.type === "hardbreak") s += " ";
  }
  return s.replace(new RegExp(`[${INLINE_OPEN}${DISPLAY_OPEN}](\\d+)[${INLINE_CLOSE}${DISPLAY_CLOSE}]`, "g"), (_m, n: string) => spans[Number(n)]?.tex ?? "");
}

export function prepareDocument(input: PrepareInput): PreparedDocument {
  const { bytes } = input;
  const dec = decoder();
  const partSpecs = input.parts?.length
    ? input.parts
    : [{ kind: "unmapped_text", span: { start_byte: 0, end_byte: bytes.length } }];

  const frontMatter = { value: null as Record<string, unknown> | null };
  const sources: string[] = [];
  const raw: string[] = [];
  for (const p of partSpecs) {
    const text = dec.decode(bytes.subarray(p.span.start_byte, p.span.end_byte));
    raw.push(text);
    sources.push(preprocess(text, p.span.start_byte === 0, frontMatter));
  }

  // Reference definitions from the whole document, available to every part.
  const references: NonNullable<Env["references"]> = {};
  const defs = sources.flatMap((s) => s.match(REF_DEF) ?? []);
  if (defs.length) md.parse(defs.join("\n\n"), { references });

  const registry = new AnchorRegistry();
  const states: PartState[] = [];
  const parts: PreparedPart[] = [];
  let mathCount = 0;

  // Pass 1: figures, math, parse, explicit anchors.
  sources.forEach((src0, index) => {
    const spans: MathSpan[] = [];
    const figures: FigureInfo[] = [];
    const withFigures = extractFigures(src0, figures, spans);
    const { text } = protectMath(withFigures, spans);
    const tokens = md.parse(text, { references });
    states.push({ tokens, spans, figures });
    mathCount += spans.length;
    const spec = partSpecs[index];
    const kind = spec.kind === "mapped_passage" ? "passage" : "text";
    const anchor = spec.passageAnchor ?? (kind === "passage" ? /<!--\s*passage:([^\s>]+)\s*-->/.exec(raw[index])?.[1] : undefined);
    const anchors: string[] = [];
    for (const m of text.matchAll(/<a id="([^"]+)" class="anchor"/g)) {
      if (registry.claimExplicit(m[1], index)) anchors.push(m[1]);
    }
    parts.push({
      index,
      kind,
      ...(anchor ? { anchor } : {}),
      span: { start: spec.span.start_byte, end: spec.span.end_byte },
      headings: [],
      anchors,
      figures: figures.map(({ key, caption, source }) => ({ key, caption, source })),
      blank: raw[index].trim() === "",
    });
  });

  // Pass 2: heading ids in document order.
  states.forEach((st, index) => {
    const part = parts[index];
    for (let i = 0; i < st.tokens.length; i++) {
      const t = st.tokens[i];
      if (t.type !== "heading_open") continue;
      const inline = st.tokens[i + 1];
      const title = inlineText(inline?.children ?? [], st.spans).trim();
      const id = registry.claimHeading(pandocIdentifier(title), index);
      t.attrSet("id", id);
      const aliases: string[] = [];
      const gh = githubSlug(title);
      if (gh !== id && registry.claimAlias(gh, index)) aliases.push(gh);
      t.meta = { ...(t.meta ?? {}), aliases };
      // A bookmark-only paragraph immediately before a heading names that
      // section too. Keep the existing bookmark in place; only its association
      // is added here, so comparison panes can find the section's passage.
      const before = st.tokens[i - 1]?.type === "paragraph_close"
        && st.tokens[i - 2]?.type === "inline" && st.tokens[i - 3]?.type === "paragraph_open"
        ? st.tokens[i - 2].content : "";
      const bookmark = /<a id="([^"]+)" class="anchor" aria-hidden="true"><\/a>/g;
      const explicit = before.replace(bookmark, "").trim() === ""
        ? [...before.matchAll(bookmark)].map((match) => match[1]).filter((anchor) => registry.partOf(anchor) === index)
        : [];
      part.headings.push({ id, level: Number(t.tag.slice(1)), title, aliases: [...aliases, ...explicit] });
      part.anchors.push(id, ...aliases);
    }
  });

  const anchorIndex = registry.entries();
  const issues = registry.duplicates.map((d) => `duplicate explicit id "${d.id}" in parts ${d.parts[0]} and ${d.parts[1]}`);

  const render = (index: number): RenderedPart => {
    const st = states[index];
    if (!st) throw new RangeError(`no part ${index}`);
    if (st.rendered) return st.rendered;
    const env: RenderEnv = {
      references,
      stage: input.stage,
      documentPath: input.documentPath,
      documentPaths: input.documentPaths,
      linkClose: [],
    };
    let html = md.renderer.render(st.tokens, md.options, env);
    html = html.replace(new RegExp(`<p>${FIG_OPEN}(\\d+)${FIG_CLOSE}</p>`, "g"), (_m, n: string) => {
      const f = st.figures[Number(n)];
      const key = esc(f.key);
      return `<figure class="paper-figure" data-figure="${key}"><div class="paper-figure__art" data-figure-slot="${key}"></div><figcaption>${f.captionHtml}</figcaption></figure>`;
    });
    html = sanitizeHtml(html);
    html = html.replace(/<p>((?:\s*<a [^>]*class="anchor"[^>]*><\/a>)+)\s*<\/p>/g, "$1");
    const mathErrors: { tex: string; message: string }[] = [];
    const typeset = (n: string) => {
      const span = st.spans[Number(n)];
      if (!span) return "";
      const r = renderTex(span.tex, span.display);
      if (r.error) mathErrors.push({ tex: span.tex, message: r.error });
      return r.html;
    };
    html = html.replace(new RegExp(`<p>${DISPLAY_OPEN}(\\d+)${DISPLAY_CLOSE}</p>`, "g"), (_m, n: string) => `<div class="math-display">${typeset(n)}</div>`);
    html = html.replace(new RegExp(`${DISPLAY_OPEN}(\\d+)${DISPLAY_CLOSE}`, "g"), (_m, n: string) => `<span class="math-display">${typeset(n)}</span>`);
    // Punctuation directly after inline math stays on the formula's line.
    html = html.replace(
      new RegExp(`${INLINE_OPEN}(\\d+)${INLINE_CLOSE}([.,;:!?)\\]\u2019\u201d]+)?`, "g"),
      // Chrome breaks after KaTeX's last box despite the wrapper, so a short
      // formula is kept whole; a long one may still break between relations.
      (_m, n: string, punct?: string) => {
        if (!punct) return typeset(n);
        const whole = (st.spans[Number(n)]?.tex.length ?? 0) <= 48 ? " math-nobreak--whole" : "";
        return `<span class="math-nobreak${whole}">${typeset(n)}${punct}</span>`;
      },
    );
    st.rendered = { index, html, mathErrors };
    return st.rendered;
  };

  return {
    stage: input.stage,
    frontMatter: frontMatter.value,
    parts,
    anchorIndex,
    mathCount,
    issues,
    render,
    renderAll: () => parts.map((p) => render(p.index)),
  };
}

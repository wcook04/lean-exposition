// TeX math: protection before Markdown parsing and KaTeX rendering after.
//
// Math is located with Pandoc's `tex_math_dollars` rules and replaced by
// private-use placeholders, so the Markdown parser never sees TeX (a `|` in
// `$\nu=\mu|_K$` must not split a table cell, `_` and `*` must not become
// emphasis). After Markdown rendering and sanitisation the placeholders are
// replaced by KaTeX output, which our own code generates with `trust: false`.

import katex from "katex";

export interface MathSpan {
  tex: string;
  display: boolean;
}

// Inline: U+E000 n U+E001; display: U+E002 n U+E003.
export const INLINE_OPEN = "";
export const INLINE_CLOSE = "";
export const DISPLAY_OPEN = "";
export const DISPLAY_CLOSE = "";

export function placeholder(index: number, display: boolean): string {
  return display ? `${DISPLAY_OPEN}${index}${DISPLAY_CLOSE}` : `${INLINE_OPEN}${index}${INLINE_CLOSE}`;
}

const isSpace = (c: string | undefined) => c === undefined || /\s/.test(c);
const isDigit = (c: string | undefined) => c !== undefined && c >= "0" && c <= "9";

/**
 * Replace each `$…$` / `$$…$$` span with a placeholder. Fenced code blocks and
 * backtick code spans are left alone; `\$` stays a literal dollar.
 * `spans` is appended to, so several texts can share one numbering.
 */
export function protectMath(src: string, spans: MathSpan[] = []): { text: string; spans: MathSpan[] } {
  let out = "";
  let i = 0;
  const n = src.length;
  let lineStart = true;
  let fence: string | null = null;

  while (i < n) {
    if (lineStart) {
      const lineEnd = src.indexOf("\n", i);
      const line = src.slice(i, lineEnd < 0 ? n : lineEnd);
      const m = /^ {0,3}(`{3,}|~{3,})/.exec(line);
      if (fence !== null || m) {
        if (fence === null && m) fence = m[1];
        else if (fence !== null && m && m[1][0] === fence[0] && m[1].length >= fence.length && line.trim() === m[1]) fence = null;
        const stop = lineEnd < 0 ? n : lineEnd + 1;
        out += src.slice(i, stop);
        i = stop;
        continue;
      }
    }
    const c = src[i];
    lineStart = false;
    if (c === "\n") {
      out += c;
      i++;
      lineStart = true;
      continue;
    }
    if (c === "\\" && i + 1 < n) {
      out += src.slice(i, i + 2);
      i += 2;
      continue;
    }
    if (c === "`") {
      let run = 1;
      while (src[i + run] === "`") run++;
      const ticks = "`".repeat(run);
      let j = src.indexOf(ticks, i + run);
      while (j >= 0 && src[j + run] === "`") j = src.indexOf(ticks, j + run + 1);
      if (j < 0) {
        out += ticks;
        i += run;
        continue;
      }
      out += src.slice(i, j + run);
      i = j + run;
      continue;
    }
    if (c === "$") {
      if (src[i + 1] === "$") {
        const close = findClose(src, i + 2, true);
        if (close > i + 2) {
          spans.push({ tex: src.slice(i + 2, close).trim(), display: true });
          out += placeholder(spans.length - 1, true);
          i = close + 2;
          continue;
        }
      } else if (!isSpace(src[i + 1])) {
        const close = findClose(src, i + 1, false);
        if (close > i + 1) {
          spans.push({ tex: src.slice(i + 1, close), display: false });
          out += placeholder(spans.length - 1, false);
          i = close + 1;
          continue;
        }
      }
    }
    out += c;
    i++;
  }
  return { text: out, spans };
}

function findClose(src: string, from: number, display: boolean): number {
  for (let j = from; j < src.length; j++) {
    const c = src[j];
    if (c === "\\") {
      j++;
      continue;
    }
    if (!display && c === "\n" && /^[ \t]*\n/.test(src.slice(j + 1, j + 80))) return -1;
    if (c !== "$") continue;
    if (display) {
      if (src[j + 1] === "$") return j;
      continue;
    }
    if (!isSpace(src[j - 1]) && !isDigit(src[j + 1])) return j;
    return -1;
  }
  return -1;
}

export interface MathResult {
  html: string;
  error?: string;
}

const escapeHtml = (s: string) =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

export function renderTex(tex: string, display: boolean): MathResult {
  try {
    const html = katex.renderToString(tex, {
      displayMode: display,
      throwOnError: true,
      trust: false,
      strict: "ignore",
      output: "htmlAndMathml",
    });
    return { html };
  } catch (e) {
    const message = e instanceof Error ? e.message : String(e);
    return {
      html: `<code class="tex-fallback" data-display="${display}" title="${escapeHtml(message)}">${escapeHtml(tex)}</code>`,
      error: message,
    };
  }
}

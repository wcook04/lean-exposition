// Shared pieces for the redrawn paper figures: KaTeX-typeset labels placed
// over an SVG plot by percentages of its viewBox, so mathematics stays crisp,
// selectable and themed while the geometry scales with the reading column.
import katex from "katex";
import type { CSSProperties, ReactNode } from "react";

const cache = new Map<string, string>();

/** Typeset one TeX expression; throws on any KaTeX error. */
export function texHtml(source: string): string {
  let html = cache.get(source);
  if (html === undefined) {
    html = katex.renderToString(source, { throwOnError: true, output: "html", strict: "error" });
    cache.set(source, html);
  }
  return html;
}

function escapeHtml(text: string): string {
  return text.replace(/[&<>"']/g, (c) => `&#${c.charCodeAt(0)};`);
}

/**
 * Text with inline `$...$` mathematics, as in the TikZ node source. Punctuation
 * right after a formula stays on the formula's line, as in the papers' prose.
 */
export function richHtml(source: string): string {
  const parts = source.split("$");
  if (parts.length % 2 === 0) throw new Error(`Unbalanced $ in figure label: ${source}`);
  let out = "";
  for (let i = 0; i < parts.length; i++) {
    if (i % 2 === 0) {
      out += escapeHtml(parts[i]);
      continue;
    }
    const glued = /^[.,;:!?)\]’”]+/.exec(parts[i + 1] ?? "");
    if (!glued) {
      out += texHtml(parts[i]);
      continue;
    }
    out += `<span style="white-space:nowrap">${texHtml(parts[i])}${escapeHtml(glued[0])}</span>`;
    parts[i + 1] = parts[i + 1].slice(glued[0].length);
  }
  return out;
}

export function Rich({ src, className }: { src: string; className?: string }) {
  return <span className={className} dangerouslySetInnerHTML={{ __html: richHtml(src) }} />;
}

/** Maps TikZ centimetre coordinates onto an SVG viewBox (y upwards in TikZ). */
export interface Frame {
  W: number;
  H: number;
  X: (x: number) => number;
  Y: (y: number) => number;
  at: (x: number, y: number) => [number, number];
}

export function frame(xMin: number, xMax: number, yMin: number, yMax: number, scale = 100): Frame {
  const W = (xMax - xMin) * scale;
  const H = (yMax - yMin) * scale;
  const X = (x: number) => (x - xMin) * scale;
  const Y = (y: number) => (yMax - y) * scale;
  return { W, H, X, Y, at: (x, y) => [(X(x) / W) * 100, (Y(y) / H) * 100] };
}

/** TikZ anchors: `above` places the label above the point, and so on. */
export type Anchor = "center" | "above" | "below" | "left" | "right" | "above-left" | "above-right" | "below-left";

export function Label({
  at,
  anchor = "center",
  src,
  className,
  children,
}: {
  at: [number, number];
  anchor?: Anchor;
  src?: string;
  className?: string;
  children?: ReactNode;
}) {
  const style: CSSProperties = { left: `${at[0]}%`, top: `${at[1]}%` };
  const cls = `fig-label fig-label--${anchor}${className ? ` ${className}` : ""}`;
  if (src !== undefined) {
    return <span className={cls} style={style} dangerouslySetInnerHTML={{ __html: richHtml(src) }} />;
  }
  return (
    <span className={cls} style={style}>
      {children}
    </span>
  );
}

/** An open axis tip in the manner of TikZ's default `->`. */
export function AxisTip({ x, y, dir, size = 13 }: { x: number; y: number; dir: "right" | "up"; size?: number }) {
  const w = size * 0.45;
  const d =
    dir === "right"
      ? `M${x - size} ${y - w} Q${x - size * 0.35} ${y - w * 0.3} ${x} ${y} Q${x - size * 0.35} ${y + w * 0.3} ${x - size} ${y + w}`
      : `M${x - w} ${y + size} Q${x - w * 0.3} ${y + size * 0.35} ${x} ${y} Q${x + w * 0.3} ${y + size * 0.35} ${x + w} ${y + size}`;
  return <path className="fig-axis-tip" d={d} />;
}

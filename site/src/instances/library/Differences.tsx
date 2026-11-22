// About's "Differences between the paper and the Lean": the paper's own summary of where the formal
// statements and the paper's words part ways (differences.md, from the instance's
// generated/differences-summary.md), set as Markdown with its formulas typeset.
import { useEffect, useState } from "react";
import MarkdownIt from "markdown-it";
import DOMPurify from "dompurify";
import { texHtml } from "../../figures/tex";

const md = new MarkdownIt({ html: false, linkify: true });

/** Formulas first (display $$...$$, then inline $...$), so Markdown never sees their underscores. */
function render(source: string): string {
  const held: string[] = [];
  const hold = (html: string) => `\u0000${held.push(html) - 1}\u0000`;
  const text = source
    .replace(/^#[^\n]*\n+/, "")
    .replace(/\$\$([\s\S]+?)\$\$/g, (whole, tex) => {
      try {
        return hold(`<span class="tex tex--display">${texHtml(`\\displaystyle ${tex}`)}</span>`);
      } catch {
        return whole;
      }
    })
    .replace(/(?<!\\)\$([^$\n]+?)\$/g, (whole, tex) => {
      try {
        return hold(`<span class="tex">${texHtml(tex)}</span>`);
      } catch {
        return whole;
      }
    });
  const html = md.render(text).replace(/\u0000(\d+)\u0000/g, (_, k) => held[Number(k)]);
  return DOMPurify.sanitize(html);
}

export const DIFFERENCES_ANCHOR = "differences";

export function DifferencesSection() {
  const [html, setHtml] = useState<string | null>(null);
  useEffect(() => {
    let live = true;
    fetch(`${import.meta.env.BASE_URL}differences.md`)
      .then((r) => (r.ok ? r.text() : ""))
      .then((text) => live && text.trim() && setHtml(render(text)))
      .catch(() => {});
    return () => {
      live = false;
    };
  }, []);
  if (!html) return null;
  return (
    <section aria-labelledby="about-differences" id={DIFFERENCES_ANCHOR}>
      <h2 id="about-differences">Differences between the paper and the Lean</h2>
      <div className="about__differences" dangerouslySetInnerHTML={{ __html: html }} />
    </section>
  );
}

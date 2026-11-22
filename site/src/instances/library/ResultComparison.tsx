// About's adapted-edition comparison: the edition's result-by-result comparison (its edition.json
// `result_comparison.reading`, published at <slug>/<name>), set as Markdown with its formulas typeset
// and its relative links resolved against the address it is published at.
import { useEffect, useState } from "react";
import type { LibraryDocument } from "./data";
import { renderMarkdown } from "./Differences";

export const COMPARISON_ANCHOR = "result-comparison";

/** Where a supplement of the edition is served: the PDFs under pdf/, the rest in the edition's folder. */
export function supplementHref(doc: LibraryDocument, name: string, pdf: boolean): string {
  return `${import.meta.env.BASE_URL}${pdf ? "pdf" : doc.slug}/${name}`;
}

export function ResultComparison({ doc }: { doc: LibraryDocument }) {
  const reading = doc.result_comparison?.reading;
  const [html, setHtml] = useState<string | null>(null);
  useEffect(() => {
    if (!reading) return;
    let live = true;
    const at = supplementHref(doc, reading.name ?? reading.file, false);
    fetch(at)
      .then((r) => (r.ok ? r.text() : ""))
      .then((text) => live && text.trim() && setHtml(renderMarkdown(text, at)))
      .catch(() => {});
    return () => {
      live = false;
    };
  }, [doc, reading]);
  if (!reading) return null;
  return (
    <section aria-labelledby="about-result-comparison" aria-busy={!html ? "true" : undefined} id={COMPARISON_ANCHOR}>
      <h2 id="about-result-comparison">{reading.label ?? "Result-by-result comparison"}</h2>
      {html && <div className="about__differences" dangerouslySetInnerHTML={{ __html: html }} />}
    </section>
  );
}

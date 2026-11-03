// One exact slice of a paper, typeset by the reader's own pipeline, so a statement
// here looks as it does on its page. Reference links resolve from the paper once it
// is loaded; until then they show their words. Lives behind lazy.tsx: KaTeX and
// markdown-it stay out of the main bundle.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { AlignedStatement } from "../api/lean";
import type { Stage } from "../api/types";
import { documentPaths, loadDocument } from "../reader/documents";
import { hasReferenceLink, renderSlice, type PreparedDocument } from "../reader/engine";
import { mountFigures } from "../reader/mount";
import { freshSlots, markWideMaths } from "../reader/page/PaperBody";
import { withoutIds } from "../reader/page/model";
import { onIdle } from "./idle";
import "../reader/reader-content.css";
import "../reader/reader-page.css";
import "./slice.css";

export interface StatementSliceProps {
  statement: AlignedStatement;
  /** Narrower type for side panels and the map pane. */
  compact?: boolean;
}

const references = new Map<Stage, PreparedDocument["references"]>();
const typeset = new Map<string, string>();

function sliceHtml(statement: AlignedStatement): string {
  const refs = references.get(statement.paper);
  const linked = !!refs && hasReferenceLink(statement.markdown);
  const key = `${statement.paper}:${statement.start_byte}:${statement.end_byte}:${linked}`;
  let html = typeset.get(key);
  if (html === undefined) {
    const paths = documentPaths();
    const { html: body } = renderSlice(statement.markdown, { stage: statement.paper, documentPath: paths[statement.paper], documentPaths: paths, references: refs });
    html = withoutIds(body);
    typeset.set(key, html);
  }
  return html;
}

/** Typeset a slice before it is shown, so walking to it costs no formula. */
export function primeSlice(statement: AlignedStatement): void {
  sliceHtml(statement);
}

/** One exact slice of a paper, typeset as the reader typesets it. */
export function StatementSlice({ statement, compact }: StatementSliceProps) {
  const needsPaper = hasReferenceLink(statement.markdown) && !references.has(statement.paper);
  const [, setLoaded] = useState(0);
  useEffect(() => {
    if (!needsPaper) return;
    let alive = true;
    // Parsing a whole paper is the one slow step here, so it waits for a quiet moment.
    const load = () =>
      loadDocument(statement.paper).then(
        ({ doc }) => {
          references.set(statement.paper, doc.references);
          if (alive) setLoaded((n) => n + 1);
        },
        () => undefined,
      );
    const cancel = onIdle(load, 1500);
    return () => {
      alive = false;
      cancel();
    };
  }, [needsPaper, statement.paper]);

  const html = useMemo(() => sliceHtml(statement), [statement, needsPaper]);
  const ref = useRef<HTMLDivElement>(null);
  useLayoutEffect(() => {
    const body = ref.current;
    if (!body) return;
    const unmount = mountFigures(freshSlots(body));
    const unmark = markWideMaths(body);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);

  return <div ref={ref} className={`slice prose${compact ? " slice--compact" : ""}`} dangerouslySetInnerHTML={{ __html: html }} />;
}

// The pane's view of an adapted edition's change: one Selected change (the authors' text, the
// edition's, the kind, the note and the sources).

import { useMemo } from "react";
import { documentPaths } from "../documents";
import { renderSlice } from "../engine";
import { kindWords, type Change, type ChangeMap } from "./changes";
import "./adapted.css";

/** A change's note, with its formulas typeset. */
function Note({ text, stage }: { text: string; stage: string }) {
  const html = useMemo(() => {
    const paths = documentPaths();
    return renderSlice(text, { stage, documentPath: paths[stage as keyof typeof paths], documentPaths: paths }).html;
  }, [text, stage]);
  return <div className="change-card__note" dangerouslySetInnerHTML={{ __html: html }} />;
}

function Slice({ markdown, stage }: { markdown: string; stage: string }) {
  const html = useMemo(() => {
    const paths = documentPaths();
    return renderSlice(markdown, { stage, documentPath: paths[stage as keyof typeof paths], documentPaths: paths }).html;
  }, [markdown, stage]);
  return <div className="change-card__text prose" dangerouslySetInnerHTML={{ __html: html }} />;
}

interface CardProps {
  change: Change;
  map: ChangeMap;
  onClose(): void;
  onGo(change: Change): void;
  onAuthors(change: Change): void;
}

export function ChangeCard({ change, map, onClose, onGo, onAuthors }: CardProps) {
  const k = map.changes.findIndex((c) => c.id === change.id);
  const prev = map.changes[k - 1];
  const next = map.changes[k + 1];
  const added = !change.replaced.length && !change.text_unchanged;
  return (
    <section className="change-card" aria-labelledby="change-title">
      <header className="change-card__head">
        <p className="change-card__state">Selected change, adapted edition</p>
        <h3 id="change-title" tabIndex={-1}>
          {kindWords(change.kind)} <span className="change-card__id">{change.id}</span>
        </h3>
        <div className="change-card__controls">
          <button type="button" className="lean-page__action" onClick={onClose}>Close</button>
        </div>
      </header>
      <Note text={change.note} stage={map.adapted} />
      <h4>In the authors’ paper</h4>
      {change.text_unchanged ? (
        <p className="change-card__none">The words of this paragraph are the authors’ in both texts; the change is to the edition’s TeX source only.</p>
      ) : added ? (
        <p className="change-card__none">Nothing: the edition adds this text. The authors’ paper has no paragraph here.</p>
      ) : (
        <Slice markdown={change.authors_text} stage={map.authors} />
      )}
      <h4>In the adapted edition</h4>
      <Slice markdown={change.adapted_text} stage={map.adapted} />
      <dl className="change-card__facts">
        <dt>Kind</dt>
        <dd>{kindWords(change.kind)}</dd>
        <dt>{change.sources.length === 1 ? "Source" : "Sources"}</dt>
        <dd>
          {change.sources.map((s, i) => (
            <span key={i} className="change-card__source">
              {s.url ? <a href={s.url} target="_blank" rel="noopener">{s.title ?? s.ref}</a> : s.ref}
              {s.where ? `, ${s.where}` : ""}
            </span>
          ))}
        </dd>
      </dl>
      <p className="change-card__review">Prepared with AI assistance; no change has been reviewed by the authors.</p>
      <nav className="change-card__walk" aria-label="Other changes">
        <button type="button" className="lean-page__action" disabled={!prev} onClick={() => prev && onGo(prev)}>Previous change</button>
        <span className="change-card__count">{k + 1} of {map.changes.length}</span>
        <button type="button" className="lean-page__action" disabled={!next} onClick={() => next && onGo(next)}>Next change</button>
      </nav>
      {!added && (
        <p>
          <button type="button" className="lean-page__action" onClick={() => onAuthors(change)}>See this paragraph in the authors’ paper</button>
        </p>
      )}
    </section>
  );
}

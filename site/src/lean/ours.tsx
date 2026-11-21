// Our own Lean statements, shown beside the authors' declaration on a phrase's card. They were
// written and proved by this reader's maintainer from the authors' Lean library; they are not the
// authors' Lean, and every block says so in words and in its own style (lean/ours.css).
// Data: a library paper's ours.json (site/scripts/library-instance.mjs), loaded once, on demand.

import { useEffect, useState } from "react";
import site from "@instance/site";
import { noteHtml } from "../reader/page/PhraseCard";
import { isFidelity, phraseVerdict } from "../compare/fidelityWords";
import "./ours.css";

interface OurDeclaration {
  title: string;
  summary?: string;
  note?: string;
  source: string;
  file: string;
  status?: { compiled?: string; axioms?: string[]; comparator?: string };
}
interface Ours {
  declarations: Record<string, OurDeclaration>;
  byPhrase: Record<string, { lean: string; fidelity: string; note: string }[]>;
}

let loading: Promise<Ours | null> | null = null;
function loadOurs(): Promise<Ours | null> {
  if (!site.library) return Promise.resolve(null);
  loading ??= fetch(`${import.meta.env.BASE_URL}ours.json`)
    .then((r) => (r.ok ? (r.json() as Promise<Ours>) : null))
    .catch(() => null);
  return loading;
}

const REPOSITORY = "https://github.com/wcook04/proof-reader/blob/main/";

/** Our statements compared with this phrase, each as a block of its own, under the authors' card. */
export function OurStatements({ phrase }: { phrase: string | undefined }) {
  const [ours, setOurs] = useState<Ours | null>(null);
  useEffect(() => {
    let live = true;
    if (phrase) void loadOurs().then((data) => live && setOurs(data));
    return () => {
      live = false;
    };
  }, [phrase]);
  const rows = phrase ? (ours?.byPhrase[phrase] ?? []) : [];
  if (!rows.length) return null;
  return (
    <>
      {rows.map((row) => {
        const decl = ours!.declarations[row.lean];
        const verdict = isFidelity(row.fidelity) ? phraseVerdict(row.fidelity) : null;
        return (
          <section key={row.lean} className="ours" aria-label="Our statement, proved from the authors' Lean library">
            <p className="ours__badge">Our statement, proved from the authors' Lean library. Not the authors' Lean.</p>
            <h4 className="ours__title">
              {decl?.title ?? row.lean} <code className="ours__name">{row.lean}</code>
            </h4>
            {verdict && (
              <p className="ours__fidelity">
                <strong>{verdict}</strong>: <span dangerouslySetInnerHTML={{ __html: noteHtml(row.note).html }} /> <span className="ours__who">AI-assessed</span>
              </p>
            )}
            {decl?.summary && <p className="ours__summary" dangerouslySetInnerHTML={{ __html: noteHtml(decl.summary).html }} />}
            {decl && (
              <details className="ours__more">
                <summary>Its Lean, and how it was checked</summary>
                {decl.note && <p dangerouslySetInnerHTML={{ __html: noteHtml(decl.note).html }} />}
                <pre className="ours__source"><code>{decl.source}</code></pre>
                <p className="ours__status">
                  In <a href={`${REPOSITORY}${decl.file}`} target="_blank" rel="noopener">wcook04/proof-reader, {decl.file}</a>.
                  {decl.status?.compiled && <> Compiled on {decl.status.compiled}.</>}
                  {decl.status?.axioms?.length ? <> Axioms: {decl.status.axioms.join(", ")}.</> : null}
                  {decl.status?.comparator && <> Comparator: {decl.status.comparator}.</>}
                </p>
              </details>
            )}
          </section>
        );
      })}
    </>
  );
}

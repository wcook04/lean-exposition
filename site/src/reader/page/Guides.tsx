// Read the paper's own guide to its formal conventions beside the paper.

import { useMemo } from "react";
import type { Stage } from "../../api/types";
import { PAPER_NAMES } from "../../app/papers";
import { routeHref } from "../../app/router";
import { useDocument } from "../documents";
import { TonesSwitch } from "./Outline";
import { ComparisonLegend } from "./PhraseCard";

function Head({ title, onClose }: { title: string; onClose(): void }) {
  return (
    <header className="guide-panel__head">
      <h3 tabIndex={-1}>{title}</h3>
      <button type="button" className="lean-page__action" onClick={onClose}>
        Close
      </button>
    </header>
  );
}

export function GuidePanel({ stage, onClose }: { stage: Stage; onClose(): void }) {
  const state = useDocument(stage);
  const html = useMemo(() => (state.status === "ready" ? state.value.doc.renderAll().map((part) => part.html).join("") : ""), [state]);
  return (
    <section className="guide-panel" aria-label="How to read the Lean">
      <Head title="How to read the Lean" onClose={onClose} />
      {state.status === "loading" && <p className="guide-panel__lead">Loading the guide…</p>}
      {state.status === "error" && <p className="guide-panel__lead">The guide could not be loaded. The paper and its links are unaffected.</p>}
      {state.status === "ready" && (
        <>
          <div className="guide-panel__text prose" dangerouslySetInnerHTML={{ __html: html }} />
          <ComparisonLegend />
          <TonesSwitch />
          <p className="guide-panel__who">
            <a href={routeHref({ view: "read", stage })}>Open “{PAPER_NAMES[stage].short}” as a page</a>
          </p>
        </>
      )}
    </section>
  );
}

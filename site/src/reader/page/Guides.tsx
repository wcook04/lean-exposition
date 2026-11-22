// Two guides that can stand in the right pane, where a paper supplies them. "Start here" is the
// paper's showcase: a short list of worked examples chosen to show how the formalisation matches
// the paper, each with one line on why it is worth reading. "How to read the Lean" is the paper's
// own guide to its formal conventions, shown in the pane so the paper keeps its place.

import { useMemo } from "react";
import type { Stage } from "../../api/types";
import { PAPER_NAMES } from "../../app/papers";
import { routeHref } from "../../app/router";
import type { RouteStep, ShowcaseCard } from "../aids";
import { useDocument } from "../documents";
import { TonesSwitch } from "./Outline";
import { ComparisonLegend, noteHtml } from "./PhraseCard";

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

/** `about`: what the paper's main formal statement asserts, where the paper gives that (the aid for its title). */
export function StartHere({ cards, about, more, titleOf, onOpen, onClose }: { cards: readonly ShowcaseCard[]; about?: string; /** The paper's longer start-here page, where it has one. */ more?: string; titleOf(card: string): string; onOpen(card: string): void; onClose?(): void }) {
  return (
    <section className="guide-panel" aria-label="Start here">
      {onClose ? (
        <Head title="Start here" onClose={onClose} />
      ) : (
        <header className="guide-panel__head">
          <h3>Start here</h3>
        </header>
      )}
      {about && <p className="guide-panel__about" dangerouslySetInnerHTML={{ __html: noteHtml(about).html }} />}
      {more && (
        <p className="guide-panel__who">
          <a href={more}>Read the whole of “Start here”</a>
        </p>
      )}
      <p className="guide-panel__lead">
        {cards.length === 1 ? "One place" : `${cards.length} places`} to start from. Each opens its words in the paper, with the comparison and the Lean beside them.
      </p>
      <p className="guide-panel__who">Chosen and described with AI. No mathematician has reviewed the choice or the descriptions.</p>
      <ol className="guide-panel__cards">
        {cards.map((item, i) => (
          <li key={item.card}>
            <button type="button" onClick={() => onOpen(item.card)}>
              <span className="guide-panel__n" aria-hidden="true">
                {i + 1}
              </span>
              <span className="guide-panel__title">{titleOf(item.card)}</span>
              <span className="guide-panel__why">{item.why}</span>
            </button>
          </li>
        ))}
      </ol>
    </section>
  );
}

/** "Follow the proof": the paper's proof as ordered steps, each opening its result with the Lean beside it. */
export function ProofRoute({ steps, onOpen, onClose }: { steps: readonly RouteStep[]; onOpen(card: string): void; onClose(): void }) {
  return (
    <section className="guide-panel" aria-label="Follow the proof">
      <Head title="Follow the proof" onClose={onClose} />
      <p className="guide-panel__lead">The proof in {steps.length} steps, in the order the argument uses them. Each opens its result in the paper with the comparison and the Lean beside it.</p>
      <p className="guide-panel__who">Drafted with AI; no mathematician has reviewed it.</p>
      <ol className="guide-panel__cards">
        {steps.map((item, i) => {
          const body = (
            <>
              <span className="guide-panel__n" aria-hidden="true">
                {i + 1}
              </span>
              <span className="guide-panel__title" dangerouslySetInnerHTML={{ __html: noteHtml(item.result).html }} />
              {item.statement && <span className="guide-panel__why guide-panel__statement" dangerouslySetInnerHTML={{ __html: noteHtml(item.statement).html }} />}
              {item.why_needed && (
                <span className="guide-panel__why">
                  <strong>Why the proof needs it:</strong> <span dangerouslySetInnerHTML={{ __html: noteHtml(item.why_needed).html }} />
                </span>
              )}
            </>
          );
          const lean = item.lean?.[0];
          return (
            <li key={`${item.step}:${item.result}`}>
              {lean ? (
                <button type="button" onClick={() => onOpen(`result:${lean}`)}>
                  {body}
                </button>
              ) : (
                <div className="guide-panel__plain">{body}</div>
              )}
            </li>
          );
        })}
      </ol>
    </section>
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

// A visit to another treatment. From 1280px it is a comparison: the passage
// the reader came from and the destination side by side, each with its own
// account, heading and scroller, the relation between them stated above both.
// Narrower, the destination opens alone at full width. Either way the paper
// underneath stays where it was; "Return to …" restores the saved origin,
// Close keeps the paper as it is, and the destination can become the paper
// ("Read the long record from here").

import { useLayoutEffect, useMemo, useRef } from "react";
import type { Stage } from "../../api/types";
import { describeError, useEdition } from "../../app/data";
import { PAPER_NAMES } from "../../app/papers";
import { routeHref } from "../../app/router";
import { sectionLabel } from "../../map/TheoremPlate";
import { useDocument } from "../documents";
import { mountFigures } from "../mount";
import { freshSlots, markWideMaths, type Links } from "./PaperBody";
import { authoredRoutes, companionAnchor, passageOf, relationWord, resolveBeside, sectionTitleIn, statusWords, withoutIds, type Structures } from "./model";

interface Props {
  target: { stage: Stage; anchor: string };
  /** The passage the visit started from, when it is known. */
  origin: { stage: Stage; anchor: string } | null;
  /** "Short paper §4", the place Return restores. */
  originLabel: string;
  compare: boolean;
  structures: Structures;
  links: Links;
  onReturn(): void;
  onClose(): void;
  onPromote(stage: Stage, anchor: string): void;
  /** A link inside a column: the next visit, keeping the same origin. */
  onFollow(stage: Stage, anchor: string): void;
}

export function Visit({ target, origin, originLabel, compare, structures, onReturn, onClose, onPromote, onFollow }: Props) {
  const { graph } = useEdition();
  // How the destination stands to the origin: an authored link first, then a shared claim.
  const relation = useMemo(() => {
    if (!origin) return null;
    const route = authoredRoutes(structures, origin.stage, origin.anchor).find((r) => r.stage === target.stage && r.anchor === target.anchor);
    if (route) return { word: relationWord(route), rationale: route.rationale };
    const mine = passageOf(structures[origin.stage], origin.anchor)?.claim_ids ?? [];
    const theirs = passageOf(structures[target.stage], target.anchor)?.claim_ids ?? [];
    const shared = mine.find((id) => theirs.includes(id));
    if (shared)
      return {
        word: "Linked to the same step",
        rationale: `Both passages are linked to “${graph.nodes.get(shared)?.label ?? shared}”. Being linked to the same step does not mean that the two passages make the same argument.`,
      };
    return null;
  }, [origin, target, structures, graph]);

  const targetTitle = sectionTitleIn(structures[target.stage], target.anchor);
  const targetName = `${PAPER_NAMES[target.stage].short}${targetTitle ? ` ${sectionLabel(targetTitle).split(" ")[0]}` : ""}`;
  const sideBySide = compare && !!origin;

  return (
    <div className={`visit${sideBySide ? " visit--compare" : ""}`} role="region" aria-label={sideBySide ? "Two passages side by side" : `${targetName}, opened over your place in the paper`}>
      <header className="visit__head">
        <div className="visit__relation">
          <p className="visit__route">
            <span className="visit__from">From {originLabel}</span> → {targetName}
            {relation && <span className="caps visit__word">{relation.word}</span>}
          </p>
          {relation?.rationale && <p className="visit__why">{relation.rationale}</p>}
        </div>
        <div className="visit__actions">
          <button type="button" className="control visit__return" onClick={onReturn}>
            Return to {originLabel}
          </button>
          <button type="button" className="control control--plain" onClick={() => onPromote(target.stage, target.anchor)}>
            Continue reading the {PAPER_NAMES[target.stage].short.toLowerCase()} from here
          </button>
          {origin && origin.stage !== target.stage && (
            <a className="visit__comparepapers" href={routeHref({ view: "compare", levels: [origin.stage, target.stage] })}>
              Compare these two papers
            </a>
          )}
          <button type="button" className="visit__close" aria-label="Close this passage and stay at your place in the paper" onClick={onClose}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
          </button>
        </div>
      </header>
      <div className="visit__columns">
        {sideBySide && origin && <PassageColumn label="Where you were reading" place={origin} structures={structures} onFollow={onFollow} source />}
        <PassageColumn label={relation?.word ?? "Opened passage"} place={target} structures={structures} onFollow={onFollow} />
      </div>
    </div>
  );
}

function PassageColumn({
  label,
  place,
  structures,
  onFollow,
  source,
}: {
  label: string;
  place: { stage: Stage; anchor: string };
  structures: Structures;
  onFollow(stage: Stage, anchor: string): void;
  source?: boolean;
}) {
  const loaded = useDocument(place.stage);
  const bodyRef = useRef<HTMLDivElement>(null);
  const scrollRef = useRef<HTMLDivElement>(null);
  const account = PAPER_NAMES[place.stage].short;

  const view = useMemo(() => {
    if (loaded.status !== "ready") return null;
    const { doc, paper } = loaded.value;
    const hit = resolveBeside(doc, paper.structure, place.anchor);
    if (!hit) return { missing: true as const };
    const html = withoutIds(doc.render(hit.part).html);
    const title = hit.passage ? sectionTitleIn(paper.structure, hit.passage) : (doc.parts[hit.part].headings[0]?.title ?? null);
    return { missing: false as const, html, title, fragment: hit.fragment, status: statusWords(paper.structure.state, paper.structure.review_state) };
  }, [loaded, place.anchor]);

  useLayoutEffect(() => {
    const body = bodyRef.current;
    if (!body || !view || view.missing) return;
    // The column's own title already names the opening heading.
    const first = body.querySelector(":scope > :is(h1,h2,h3,h4,h5,h6)");
    if (first && view.title && first.textContent?.trim() === view.title.trim()) first.classList.add("visually-hidden");
    const unmount = mountFigures(freshSlots(body));
    const unmark = markWideMaths(body);
    const scroller = scrollRef.current;
    if (scroller) {
      const mark = view.fragment ? body.querySelector<HTMLElement>(`[data-id="${CSS.escape(view.fragment)}"]`) : null;
      scroller.scrollTop = mark ? Math.max(0, mark.getBoundingClientRect().top - scroller.getBoundingClientRect().top + scroller.scrollTop - 16) : 0;
    }
    return () => {
      unmount();
      unmark();
    };
  }, [view]);

  // Links inside the copy: its own fragments and the other accounts open as the next visit.
  const onClick = (event: React.MouseEvent) => {
    const a = (event.target as Element).closest?.("a");
    if (!a || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    if (a.dataset.companion) {
      event.preventDefault();
      const stage = a.dataset.companion as Stage;
      onFollow(stage, companionAnchor(structures[stage], a.dataset.fragment));
    } else if (a.dataset.in && a.dataset.fragment) {
      event.preventDefault();
      onFollow(a.dataset.in as Stage, a.dataset.fragment);
    }
  };

  return (
    <article className={`visit__column${source ? " visit__column--source" : ""}`} aria-label={`${account}${view && !view.missing && view.title ? `, ${sectionLabel(view.title)}` : ""}`}>
      <header className="visit__columnhead">
        <p className="caps">{label}</p>
        <h2 className="visit__title">{view && !view.missing && view.title ? sectionLabel(view.title) : account}</h2>
        <p className="visit__meta">
          {account}
          {view && !view.missing && view.status ? `. ${view.status}` : ""}
        </p>
      </header>
      <div className="visit__scroll" ref={scrollRef} tabIndex={-1} onClick={onClick}>
        {loaded.status === "error" && <p className="visit__message">{describeError(loaded.error).title}</p>}
        {loaded.status === "loading" && <p className="visit__message faint">Loading the {account.toLowerCase()}…</p>}
        {view?.missing && (
          <p className="visit__message">
            The {account.toLowerCase()} has no passage or section called “{place.anchor}”.
          </p>
        )}
        {view && !view.missing && <div ref={bodyRef} className="visit__text prose" dangerouslySetInnerHTML={{ __html: view.html }} />}
      </div>
    </article>
  );
}

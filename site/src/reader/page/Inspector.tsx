// "Steps linked to this passage": the inspector a reader opens beside the paper. It lists
// every record mapped to the whole passage (claims first, then assumptions),
// independently of any goal; choosing one shows its recorded relations as a
// short list, with the full record and the argument map one step further.
// For a text selection it lists the passages the selection touches.

import { useMemo, useState } from "react";
import type { Stage } from "../../api/types";
import { get } from "../../api/client";
import { describeError, useEdition, useResource } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { PAPER_NAMES } from "../../app/papers";
import { kindName } from "../../map/labels";
import { sectionLabel } from "../../map/TheoremPlate";
import { RecordPanel } from "../../panels/RecordPanel";
import type { ArgEdge, ArgGraph, LinkKind } from "../../model/graph";
import type { Links } from "./PaperBody";
import { passageOf, passageRecords, placeName, sectionTitleIn, type Structures } from "./model";

export type InspectorTarget =
  | { kind: "passage"; anchor: string | null }
  | { kind: "selection"; start: number; end: number; passages: number };

interface Props {
  stage: Stage;
  target: InspectorTarget;
  structures: Structures;
  node: string | null;
  links: Links;
  /** Shown inside a modal that has its own title bar. */
  inModal?: boolean;
  onSelect(id: string | null): void;
  onClose(): void;
  onSameTopic(anchor: string, opener: HTMLElement): void;
  onVisit(stage: Stage, anchor: string): void;
}

const RELATION_NAME: Record<LinkKind, string> = {
  supports: "Recorded support",
  assumes: "Explicit assumption",
  formalizes: "Recorded Lean correspondence",
  lean_type_dependency: "Lean type dependency",
  lean_value_dependency: "Lean proof or value dependency",
  lean_via: "Lean use through helpers",
  lean_structural_dependency: "Lean structural dependency",
};

export function Inspector(props: Props) {
  const { stage, target, structures, node, inModal, onClose } = props;
  const { graph } = useEdition();
  const [full, setFull] = useState(false);
  const account = PAPER_NAMES[stage].short;

  if (full && node && graph.nodes.has(node)) {
    return (
      <section className="inspector inspector--record" aria-label="The whole step">
        <div className="inspector__bar">
          <button type="button" className="control control--plain inspector__back" onClick={() => setFull(false)}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M7.5 2.5L4 6l3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
            </svg>
            Back to the passage
          </button>
        </div>
        <div className="inspector__scroll">
          <RecordPanel
            nodeId={node}
            compact
            onClose={() => setFull(false)}
            onSelect={(id) => props.onSelect(id)}
            onTrace={(trace) => navigate({ view: "map", node, trace })}
            passageHref={(s, anchor) => props.links.beside(s, anchor)}
          />
        </div>
      </section>
    );
  }

  const anchor = target.kind === "passage" ? target.anchor : null;
  const title = anchor ? sectionTitleIn(structures[stage], anchor) : null;
  const heading = target.kind === "selection" ? (target.passages === 1 ? "Steps linked to this passage" : `Steps linked to these ${target.passages} passages`) : "Steps linked to this passage";

  return (
    <section className="inspector" aria-labelledby={inModal ? undefined : "inspector-title"} aria-label={inModal ? heading : undefined}>
      {!inModal && (
        <header className="inspector__head">
          <h2 id="inspector-title" className="inspector__title" tabIndex={-1}>
            {heading}
          </h2>
          <button type="button" className="inspector__close" aria-label={`Close ${heading.toLowerCase()}`} onClick={onClose}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
          </button>
        </header>
      )}
      <div className="inspector__scroll">
        {target.kind === "passage" ? (
          <PassageView {...props} anchor={anchor} title={title} account={account} graph={graph} onFull={() => setFull(true)} />
        ) : (
          <SelectionView {...props} selection={target} graph={graph} onFull={() => setFull(true)} />
        )}
      </div>
    </section>
  );
}

function PassageView({
  stage,
  anchor,
  title,
  account,
  structures,
  node,
  graph,
  onSelect,
  onSameTopic,
  onFull,
}: Props & { anchor: string | null; title: string | null; account: string; graph: ArgGraph; onFull(): void }) {
  const ids = useMemo(() => passageRecords(anchor ? passageOf(structures[stage], anchor) : undefined), [anchor, structures, stage]);
  const outside = node && !ids.includes(node) && graph.nodes.has(node) ? node : null;
  return (
    <>
      <div className="inspector__where">
        <p className="inspector__place">
          {account}
          {title ? `, ${sectionLabel(title)}` : ""}
        </p>
        {anchor && (
          <button type="button" className="inspector__topic" aria-haspopup="dialog" onClick={(event) => onSameTopic(anchor, event.currentTarget)}>
            Linked passages
          </button>
        )}
      </div>
      {anchor && ids.length > 0 && (
        <>
          <h3 className="inspector__label">Steps linked to this whole passage</h3>
          <p className="inspector__note">A step is one claim, assumption, main result or Lean declaration in the argument that the argument map draws.</p>
          <ul className="records">
            {ids.map((id) => (
              <li key={id}>
                <RecordRow id={id} graph={graph} selected={id === node} onSelect={onSelect} />
                {id === node && <Relations id={id} graph={graph} onSelect={onSelect} onFull={onFull} />}
              </li>
            ))}
          </ul>
        </>
      )}
      {anchor && ids.length === 0 && <p className="inspector__message">No step is linked to this passage.</p>}
      {!anchor && !outside && <p className="inspector__message">This part of the paper is not inside a passage that is linked to records.</p>}
      {outside && (
        <>
          <h3 className="inspector__label">{anchor ? "The step you opened from this passage" : "The step you opened"}</h3>
          <ul className="records">
            <li>
              <RecordRow id={outside} graph={graph} selected onSelect={onSelect} />
              <Relations id={outside} graph={graph} onSelect={onSelect} onFull={onFull} />
            </li>
          </ul>
        </>
      )}
    </>
  );
}

function RecordRow({ id, graph, selected, onSelect }: { id: string; graph: ArgGraph; selected: boolean; onSelect(id: string | null): void }) {
  const n = graph.nodes.get(id);
  if (!n) {
    return (
      <div className="record-row record-row--missing">
        <span className="record-row__title">{id}</span>
        <span className="record-row__note">No step on this site has this identifier.</span>
      </div>
    );
  }
  return (
    <button
      type="button"
      className={`record-row${n.kind === "assumption" ? " record-row--assumption" : ""}`}
      aria-expanded={selected}
      onClick={() => onSelect(selected ? null : id)}
    >
      <span className="record-row__meta">
        <span className="caps">{kindName(n.kind)}</span>
        <span className="record-row__source" data-slot={n.origin.slot}>
          <span className="src-sq" aria-hidden="true" />
          {n.origin.label}
        </span>
      </span>
      <span className={`record-row__title${n.kind === "declaration" ? " lean" : ""}`}>{n.label}</span>
    </button>
  );
}

function Relations({ id, graph, onSelect, onFull }: { id: string; graph: ArgGraph; onSelect(id: string | null): void; onFull(): void }) {
  const uses = (graph.out.get(id) ?? []).filter((e) => graph.nodes.has(e.to));
  const usedBy = (graph.in.get(id) ?? []).filter((e) => graph.nodes.has(e.from));
  const line = (edge: ArgEdge, other: string) => {
    const n = graph.nodes.get(other)!;
    return (
      <li key={edge.key}>
        <span className="relation__kind">
          <span className={`rel-sample rel-sample--${edge.kind}`} aria-hidden="true" />
          {RELATION_NAME[edge.kind]}
        </span>
        <button type="button" className={`relation__target${n.kind === "declaration" ? " lean" : ""}`} onClick={() => onSelect(other)}>
          {n.label}
        </button>
      </li>
    );
  };
  return (
    <div className="relations">
      <h4 className="relations__label">
        Uses <span className="num">{uses.length}</span>
      </h4>
      {uses.length ? <ul>{uses.map((e) => line(e, e.to))}</ul> : <p className="relations__none">The argument as written stops here.</p>}
      <h4 className="relations__label">
        Used by <span className="num">{usedBy.length}</span>
      </h4>
      {usedBy.length ? <ul>{usedBy.map((e) => line(e, e.from))}</ul> : <p className="relations__none">Nothing is recorded as using it.</p>}
      <div className="relations__actions">
        <button type="button" className="control" onClick={onFull}>
          Show the full record
        </button>
        <a className="relations__map" href={routeHref({ view: "map", node: id })}>
          Open in the argument map →
        </a>
      </div>
    </div>
  );
}

// ---------------------------------------------------------- selection

interface QueryMatch {
  anchor: string;
  stage: Stage;
  direct_claim_ids: string[];
  direct_assumption_ids: string[];
}

interface QueryResult {
  match_count: number;
  papers: { stage: Stage; matches: QueryMatch[] }[];
  coverage: { empty_result_meaning?: string };
}

function SelectionView({
  stage,
  selection,
  structures,
  node,
  graph,
  onSelect,
  onVisit,
  onFull,
}: Props & { selection: { start: number; end: number; passages: number }; graph: ArgGraph; onFull(): void }) {
  const result = useResource<QueryResult>(`query:${stage}:${selection.start}:${selection.end}`, () =>
    get<QueryResult>("/papers/query", { paper: stage, start: selection.start, end: selection.end, representation: "matches" }).then((r) => r.data),
  );
  const matches = result.status === "ready" ? result.value.papers.flatMap((p) => p.matches) : [];
  return (
    <>
      <p className="inspector__note">Steps are linked to whole passages, not to single words. Every passage that your selection touches is listed, with the records linked to it.</p>
      {result.status === "loading" && <p className="inspector__message faint">Loading the passages…</p>}
      {result.status === "error" && (
        <p className="inspector__message" role="alert">
          {describeError(result.error).title}. {describeError(result.error).detail}
        </p>
      )}
      {result.status === "ready" && matches.length === 0 && (
        <p className="inspector__message">Your selection does not touch any passage that is linked to records. {result.value.coverage.empty_result_meaning ?? ""}</p>
      )}
      {matches.map((m) => {
        const ids = [...new Set([...m.direct_claim_ids, ...m.direct_assumption_ids])];
        return (
          <div key={`${m.stage}:${m.anchor}`} className="selection-match">
            <h3 className="inspector__label">
              {m.stage === stage ? (
                placeName(structures, stage, m.stage, m.anchor)
              ) : (
                <button type="button" className="linklike" onClick={() => onVisit(m.stage, m.anchor)}>
                  {placeName(structures, stage, m.stage, m.anchor)}
                </button>
              )}
            </h3>
            <ul className="records">
              {ids.map((id) => (
                <li key={id}>
                  <RecordRow id={id} graph={graph} selected={id === node} onSelect={onSelect} />
                  {id === node && <Relations id={id} graph={graph} onSelect={onSelect} onFull={onFull} />}
                </li>
              ))}
            </ul>
          </div>
        );
      })}
    </>
  );
}

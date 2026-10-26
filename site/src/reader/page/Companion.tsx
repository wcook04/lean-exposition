// The companion pane beside the paper. By default it is the whole argument
// with the claims of the passage in view lit; it becomes a record when a
// claim is chosen, another passage when a route is opened beside, or the
// matches for a selection. Closing any of them returns to the map.

import { forwardRef, useEffect, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../../api/types";
import { get } from "../../api/client";
import { describeError, useEdition, useResource } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { PAPER_NAMES } from "../../app/papers";
import { MapView, type Insets, type MapViewHandle } from "../../map/MapView";
import { goalFor } from "../../map/treeModel";
import { RecordPanel } from "../../panels/RecordPanel";
import { sectionLabel } from "../../map/TheoremPlate";
import { useDocument } from "../documents";
import { mountFigures } from "../mount";
import { freshSlots, markWideMaths, type Links } from "./PaperBody";
import { describeRecords, passageOf, passageRecords, placeName, resolveBeside, sectionTitleIn, withoutIds, type Structures } from "./model";

export type PaneMode =
  | { kind: "map" }
  | { kind: "record"; node: string }
  | { kind: "beside"; stage: Stage; anchor: string }
  | { kind: "selection"; start: number; end: number; parts: number };

export interface CompanionHandle {
  fitEcho(ids: string[]): void;
}

interface Props {
  stage: Stage;
  mode: PaneMode;
  echo: string[];
  echoMapped: boolean;
  structures: Structures;
  links: Links;
  node?: string;
  onClose(): void;
  onSelect(id: string): void;
  /** Rendered above the pane's content (the section menu at narrower widths). */
  header?: React.ReactNode;
}

export const Companion = forwardRef<CompanionHandle, Props>(function Companion(props, ref) {
  const { mode, header } = props;
  const mapRef = useRef<MapViewHandle>(null);
  useImperativeHandle(ref, () => ({
    fitEcho: (ids) => {
      if (ids.length) mapRef.current?.fitNodes(ids, true);
    },
  }));
  return (
    <div className="companion-pane" data-mode={mode.kind}>
      {header}
      {mode.kind === "map" && <MapPane {...props} mapRef={mapRef} />}
      {mode.kind === "record" && <RecordPane {...props} node={mode.node} />}
      {mode.kind === "beside" && <BesidePane {...props} target={mode} />}
      {mode.kind === "selection" && <SelectionPane {...props} selection={mode} />}
    </div>
  );
});

// ---------------------------------------------------------------- map

const CHIPS_MAX = 4;

function MapPane({ echo, echoMapped, links, onSelect, mapRef }: Props & { mapRef: React.RefObject<MapViewHandle | null> }) {
  const { graph } = useEdition();
  const set = useMemo(() => (echo.length ? new Set(echo) : null), [echo]);
  // The tree starts from the goal the passage's claims serve (the main theorem by default).
  const goal = useMemo(() => {
    const counts = new Map<string, number>();
    for (const id of echo) {
      const g = goalFor(graph, id, graph.goals);
      if (g) counts.set(g, (counts.get(g) ?? 0) + 1);
    }
    let best: string | undefined;
    let n = 0;
    for (const [g, c] of counts) if (c > n) [best, n] = [g, c];
    return best;
  }, [echo, graph]);
  // Only the route from the goal down to the passage's lit records (every chain of
  // uses between them), plus each lit record's own direct uses, folded behind its foot.
  const within = useMemo(() => {
    if (!goal || !echo.length) return undefined;
    const kinds = new Set(["supports", "formalizes", "assumes"]);
    const below = new Set([goal]);
    const queue = [goal];
    while (queue.length) {
      for (const e of graph.out.get(queue.shift()!) ?? []) {
        if (kinds.has(e.kind) && !below.has(e.to)) {
          below.add(e.to);
          queue.push(e.to);
        }
      }
    }
    const route = new Set(echo.filter((id) => below.has(id)));
    const up = [...route];
    while (up.length) {
      for (const e of graph.in.get(up.shift()!) ?? []) {
        if (kinds.has(e.kind) && below.has(e.from) && !route.has(e.from)) {
          route.add(e.from);
          up.push(e.from);
        }
      }
    }
    const out = new Set(route);
    for (const id of echo) for (const e of graph.out.get(id) ?? []) if (kinds.has(e.kind)) out.add(e.to);
    return out;
  }, [goal, echo, graph]);
  const [all, setAll] = useState(false);
  useEffect(() => setAll(false), [echo]);
  const insets: Insets = useMemo(() => ({ top: 16, right: 16, bottom: 16, left: 16 }), []);
  const shown = all ? echo : echo.slice(0, CHIPS_MAX);
  return (
    <section className="pane pane--map" aria-labelledby="pane-map-title">
      <header className="pane__head">
        <h2 id="pane-map-title" className="pane__title">
          The passage in the argument
        </h2>
        {echo.length > 0 ? (
          <>
            <p className="pane__note">
              Lit on the map: the {describeRecords(echo, graph)} the passage you are reading discusses.
            </p>
            <ul className="pane__chips">
              {shown.map((id) => {
                const node = graph.nodes.get(id)!;
                return (
                  <li key={id}>
                    <a className="claim-chip" href={links.node(id)} data-region={node.region}>
                      <span className="region-dot" aria-hidden="true" />
                      <span className={node.kind === "declaration" ? "lean" : undefined}>{node.label}</span>
                    </a>
                  </li>
                );
              })}
              {echo.length > CHIPS_MAX && (
                <li>
                  <button type="button" className="pane__more" aria-expanded={all} onClick={() => setAll((v) => !v)}>
                    {all ? "Fewer" : `and ${echo.length - CHIPS_MAX} more`}
                  </button>
                </li>
              )}
            </ul>
          </>
        ) : (
          <p className="pane__note">
            {echoMapped
              ? "The passage you are reading is mapped, but none of its records is drawn on this map."
              : "The text you are reading is not mapped to a recorded claim. The map shows the whole argument."}
          </p>
        )}
      </header>
      <div className="pane__map">
        <MapView
          ref={mapRef}
          graph={graph}
          goal={goal}
          compact
          echo={set}
          within={within}
          insets={insets}
          onSelect={(id) => id && onSelect(id)}
          onTrace={(id) => navigate({ view: "map", node: id, trace: "rests" })}
          onRegion={() => undefined}
        />
      </div>
    </section>
  );
}

// ------------------------------------------------------------- record

function RecordPane({ node, links, onClose, onSelect }: Props & { node: string }) {
  const { graph } = useEdition();
  if (!graph.nodes.has(node)) {
    return (
      <section className="pane">
        <PaneBar onClose={onClose} />
        <p className="pane__message">“{node}” is not a record in this edition.</p>
      </section>
    );
  }
  return (
    <section className="pane pane--record">
      <PaneBar onClose={onClose} />
      <div className="pane__scroll">
        <RecordPanel
          nodeId={node}
          compact
          onClose={onClose}
          onSelect={onSelect}
          onTrace={(trace) => navigate({ view: "map", node, trace })}
          passageHref={(stage, anchor) => links.beside(stage, anchor)}
        />
      </div>
    </section>
  );
}

function PaneBar({ onClose, children }: { onClose(): void; children?: React.ReactNode }) {
  return (
    <div className="pane__bar">
      <button type="button" className="control control--plain pane__back" onClick={onClose}>
        <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
          <path d="M7.5 2.5L4 6l3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
        Back to the map
      </button>
      {children}
    </div>
  );
}

// ------------------------------------------------------------- beside

function BesidePane({ stage: here, target, structures, links, node, onClose }: Props & { target: { stage: Stage; anchor: string } }) {
  const loaded = useDocument(target.stage);
  const { graph } = useEdition();
  const bodyRef = useRef<HTMLDivElement>(null);
  const scrollRef = useRef<HTMLDivElement>(null);

  const view = useMemo(() => {
    if (loaded.status !== "ready") return null;
    const { doc, paper } = loaded.value;
    const hit = resolveBeside(doc, paper.structure, target.anchor);
    if (!hit) return { missing: true as const };
    const html = withoutIds(doc.render(hit.part).html);
    const title =
      (hit.fragment ? headingAt(html, hit.fragment) : null) ??
      (hit.passage ? sectionTitleIn(paper.structure, hit.passage) : (doc.parts[hit.part].headings[0]?.title ?? null));
    const records = passageRecords(hit.passage ? passageOf(paper.structure, hit.passage) : undefined).filter((id) => graph.nodes.has(id));
    return { missing: false as const, html, title, records, passage: hit.passage, fragment: hit.fragment };
  }, [loaded, target.anchor, graph]);

  useLayoutEffect(() => {
    const body = bodyRef.current;
    if (!body || !view || view.missing) return;
    const unmount = mountFigures(freshSlots(body));
    const unmark = markWideMaths(body);
    const cleanup = () => {
      unmount();
      unmark();
    };
    const scroller = scrollRef.current;
    if (scroller) {
      const mark = view.fragment ? body.querySelector<HTMLElement>(`[data-id="${CSS.escape(view.fragment)}"]`) : null;
      scroller.scrollTop = mark ? Math.max(0, mark.getBoundingClientRect().top - scroller.getBoundingClientRect().top + scroller.scrollTop - 16) : 0;
    }
    return cleanup;
  }, [view]);

  const account = PAPER_NAMES[target.stage].short;
  const openHref = routeHref({ view: "read", stage: target.stage, anchor: view && !view.missing ? (view.fragment ?? view.passage ?? target.anchor) : target.anchor, node });

  const onClick = (event: React.MouseEvent) => {
    const a = (event.target as Element).closest?.("a");
    if (!a || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const href = a.getAttribute("href") ?? "";
    if (a.closest(".beside__text")) {
      if (href.startsWith("#")) {
        event.preventDefault();
        navigate(links.beside(target.stage, decodeURIComponent(href.slice(1))));
      } else if (a.dataset.companion) {
        event.preventDefault();
        navigate(links.beside(a.dataset.companion as Stage, a.dataset.fragment ?? ""));
      }
    }
  };

  return (
    <section className="pane pane--beside" aria-labelledby="beside-title" onClick={onClick}>
      <div className="pane__bar">
        <button type="button" className="control control--plain pane__back" onClick={onClose}>
          <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
            <path d="M7.5 2.5L4 6l3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
          </svg>
          Close
        </button>
        <a className="control pane__open" href={openHref}>
          {target.stage === here ? "Go to it in this account" : `Open it in the ${account.toLowerCase()}`}
        </a>
      </div>
      <header className="pane__head pane__head--beside">
        <h2 id="beside-title" className="pane__context">
          {target.stage === here ? `Elsewhere in the ${account.toLowerCase()}` : account}
          {view && !view.missing && view.title ? `, ${sectionLabel(view.title)}` : ""}
        </h2>
      </header>
      <div className="pane__scroll" ref={scrollRef}>
        {loaded.status === "error" && <p className="pane__message">{describeError(loaded.error).title}</p>}
        {loaded.status === "loading" && <p className="pane__message faint">Opening the {account.toLowerCase()}…</p>}
        {view?.missing && (
          <p className="pane__message">
            The {account.toLowerCase()} has no passage or section called “{target.anchor}” in this edition.
          </p>
        )}
        {view && !view.missing && (
          <>
            <div ref={bodyRef} className="beside__text prose prose--compact" dangerouslySetInnerHTML={{ __html: view.html }} />
            {view.records.length > 0 && (
              <div className="beside__claims">
                <h3 className="pane__label">Claims this passage discusses</h3>
                <ul className="pane__chips">
                  {view.records.map((id) => {
                    const n = graph.nodes.get(id)!;
                    return (
                      <li key={id}>
                        <a className="claim-chip" href={links.node(id)} data-region={n.region}>
                          <span className="region-dot" aria-hidden="true" />
                          <span className={n.kind === "declaration" ? "lean" : undefined}>{n.label}</span>
                        </a>
                      </li>
                    );
                  })}
                </ul>
              </div>
            )}
            {view.passage && structures[target.stage] && (
              <p className="beside__where faint">From {placeName(structures, here, target.stage, view.passage)}.</p>
            )}
          </>
        )}
      </div>
    </section>
  );
}

// ---------------------------------------------------------- selection

interface QueryMatch {
  anchor: string;
  stage: Stage;
  direct_claim_ids: string[];
  direct_assumption_ids: string[];
  evidence_class: string;
  whole_passage_extends_beyond_selected_ranges: boolean;
}

interface QueryResult {
  match_count: number;
  papers: { stage: Stage; matches: QueryMatch[] }[];
  coverage: { empty_result_meaning?: string };
}

function SelectionPane({ stage, selection, structures, links, onClose }: Props & { selection: { start: number; end: number; parts: number } }) {
  const { graph } = useEdition();
  const result = useResource<QueryResult>(`query:${stage}:${selection.start}:${selection.end}`, () =>
    get<QueryResult>("/papers/query", { paper: stage, start: selection.start, end: selection.end, representation: "matches" }).then((r) => r.data),
  );
  const matches = result.status === "ready" ? result.value.papers.flatMap((p) => p.matches) : [];
  return (
    <section className="pane pane--selection" aria-labelledby="selection-title">
      <PaneBar onClose={onClose} />
      <header className="pane__head">
        <h2 id="selection-title" className="pane__title">
          What your selection maps to
        </h2>
        <p className="pane__note">
          The match is made by whole passages: a mapped passage counts when any of it lies in the{" "}
          {selection.parts === 1 ? "part of the text" : `${selection.parts} parts of the text`} your selection touches, not by the selected words alone.
        </p>
      </header>
      <div className="pane__scroll">
        {result.status === "loading" && <p className="pane__message faint">Asking the record…</p>}
        {result.status === "error" && (
          <p className="pane__message" role="alert">
            {describeError(result.error).title}. {describeError(result.error).detail}
          </p>
        )}
        {result.status === "ready" && matches.length === 0 && (
          <p className="pane__message">
            No mapped passage overlaps this text. {result.value.coverage.empty_result_meaning ?? ""}
          </p>
        )}
        {matches.length > 0 && (
          <ol className="matches">
            {matches.map((m) => {
              const ids = [...new Set([...m.direct_claim_ids, ...m.direct_assumption_ids])].filter((id) => graph.nodes.has(id));
              return (
                <li key={`${m.stage}:${m.anchor}`} className="match">
                  <a className="match__place" href={links.beside(m.stage, m.anchor)}>
                    {placeName(structures, stage, m.stage, m.anchor)}
                  </a>
                  {ids.length > 0 ? (
                    <ul className="pane__chips">
                      {ids.map((id) => {
                        const n = graph.nodes.get(id)!;
                        return (
                          <li key={id}>
                            <a className="claim-chip" href={links.node(id)} data-region={n.region}>
                              <span className="region-dot" aria-hidden="true" />
                              <span className={n.kind === "declaration" ? "lean" : undefined}>{n.label}</span>
                            </a>
                          </li>
                        );
                      })}
                    </ul>
                  ) : (
                    <p className="faint">Mapped without a claim drawn on the map.</p>
                  )}
                </li>
              );
            })}
          </ol>
        )}
      </div>
    </section>
  );
}

/** The heading a fragment names: the heading it is, or the first one after its bookmark. */
function headingAt(html: string, fragment: string): string | null {
  const at = html.indexOf(`data-id="${fragment.replace(/"/g, "&quot;")}"`);
  if (at < 0) return null;
  const open = html.lastIndexOf("<", at);
  const match = /<h([1-6])\b[^>]*>([\s\S]*?)<\/h\1>/.exec(html.slice(open));
  if (!match || match.index > 400) return null;
  const text = new DOMParser().parseFromString(match[2], "text/html").body.textContent ?? "";
  return text.trim() || null;
}

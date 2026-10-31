// The argument map beside the paper, from 1280px, and as a sheet on narrower
// screens. It opens with every branch drawn: records this paper discusses at full
// strength, the rest quieter. It follows what the reader is reading: as a passage
// settles under the reading line, the map frames that passage's records and
// outlines them in amber, and records already passed stay tinted, so the map shows
// the paper's path and how far along it the reader is. The reader stays in charge:
// panning, zooming or unfolding pauses following. Choosing a card scrolls the text
// to its best passage and opens the record in a sheet docked under the map; for a
// record this paper does not discuss, it also says which paper does.

import { memo, useCallback, useEffect, useMemo, useRef, useState, type MutableRefObject, type ReactNode } from "react";
import type { AlignedStatement, Alignment } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "../../map/ArgumentTree";
import { mainGoal, startingGoals } from "../../map/TheoremPlate";
import { useKeptCamera } from "../../map/scene";
import { chooseGoal, reach, scopedGraph } from "../../map/treeModel";
import { useReducedMotion } from "../../map/canvas/useReducedMotion";
import { bestSlice, firstPassageFor, type Structures } from "./model";
import { RecordDock, readDockShare, type OpenRecord } from "./RecordDock";
import "./map-pane.css";

/** The inspector's width when it slides in over the pane (--reader-inspector). */
const INSPECTOR_W = 336;
/** --t-state: the canvas crossfades when the main result changes. */
const CROSSFADE_MS = 160;

/** Narrow tiles, so that at the 11px floor the whole argument fits a 1440px window's half. */
const PANE_TILE_W = 140;

/** Lights these records on the map from outside it, without moving anything. */
export type PaneHover = (ids: ReadonlySet<string> | null) => void;

interface Props {
  stage: Stage;
  structures: Structures;
  /** The passage being followed (already settled under the reading line), or null before any. */
  anchor: string | null;
  /** The records to light: those of the statement under the reading line, or else of the passage. */
  records: readonly string[];
  /** All the records of the passage, which decide the main result. Defaults to `records`. */
  passage?: readonly string[];
  /** Records reached earlier in the paper, tinted on the map. */
  passed?: ReadonlySet<string>;
  /** "§3 of 8, 14 of 37 records so far". */
  progress?: string;
  alignment?: Alignment | null;
  /** The record open in the docked sheet. */
  record?: OpenRecord | null;
  /** Filled by the pane: the paper's record chips light cards through it. */
  hoverRef?: MutableRefObject<PaneHover | null>;
  /** The passage inspector, drawn over the right of the pane. */
  overlay?: ReactNode;
  inert?: boolean;
  /** The pane fills a modal, which has its own title and close control. */
  inModal?: boolean;
  onHide(): void;
  /** A card was chosen: open the record and take the text to its best slice, else this passage, if it has one. */
  onRecord?(id: string, anchor: string | null, slice: AlignedStatement | null): void;
  onCloseRecord?(): void;
  passageHref?(stage: Stage, anchor: string): string;
}

export const MapPane = memo(function MapPane({
  stage,
  structures,
  anchor,
  records,
  passage = records,
  passed,
  progress,
  alignment = null,
  record = null,
  hoverRef,
  overlay,
  inert,
  inModal,
  onHide,
  onRecord,
  onCloseRecord,
  passageHref,
}: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const reduced = useReducedMotion();
  const treeRef = useRef<MapViewHandle>(null);
  useKeptCamera(treeRef, useCallback((id: string) => graph.nodes.has(id), [graph]));
  const bodyRef = useRef<HTMLDivElement>(null);

  // ---- Which main result -------------------------------------------------------------

  const candidates = useMemo(
    () => startingGoals(edition).map((g) => ({ id: g.id, title: g.title, own: g.stages.includes(stage) })),
    [edition, stage],
  );
  const reaches = useMemo(() => new Map<string, Set<string>>(), [graph]);
  // As the map draws it: the goal's scoped argument.
  const reachOf = useCallback(
    (goal: string) => {
      let r = reaches.get(goal);
      if (!r) {
        r = reach(scopedGraph(graph, goal), goal);
        reaches.set(goal, r);
      }
      return r;
    },
    [graph, reaches],
  );
  // The paper's main result stays on the pane. Only a passage with nothing to draw
  // there borrows another result, and the next passage that has returns to it.
  const home = useMemo(() => mainGoal(edition), [edition]);
  const goalFor = useCallback(
    (ids: readonly string[]) => (!ids.length || ids.some((id) => reachOf(home).has(id)) ? home : (chooseGoal(ids, candidates, reachOf, home) ?? home)),
    [home, candidates, reachOf],
  );
  const [goal, setGoal] = useState(() => goalFor(passage));
  const [fadeTo, setFadeTo] = useState<string | null>(null);
  const title = candidates.find((c) => c.id === goal)?.title ?? graph.nodes.get(goal)?.label ?? goal;

  // ---- Following ---------------------------------------------------------------------

  // Every newly opened pane follows; a pause lasts for this open pane only.
  const [following, setFollowing] = useState(true);
  const [paused, setPaused] = useState(false);
  const [notice, setNotice] = useState<string | null>(null);
  const followingRef = useRef(following);
  followingRef.current = following;
  // The statement's records where the map draws them, else the rest of its passage.
  const drawable = useMemo(() => {
    const exact = records.filter((id) => reachOf(goal).has(id));
    return exact.length ? exact : passage.filter((id) => reachOf(goal).has(id));
  }, [records, passage, reachOf, goal]);
  // A chip in the paper, or a list in the sheet, lights its cards while pointed at.
  const [hovered, setHovered] = useState<ReadonlySet<string> | null>(null);
  useEffect(() => {
    if (!hoverRef) return;
    hoverRef.current = setHovered;
    return () => {
      hoverRef.current = null;
    };
  }, [hoverRef]);
  const litIds = useMemo(() => (drawable.length ? new Set(drawable) : null), [drawable]);
  // Scrolling must stay smooth, so while it runs the trail is written straight onto the
  // tiles (one attribute each, no render), and the map draws the lit lines when it stops.
  const [settledLit, setSettledLit] = useState(litIds);
  useEffect(() => {
    let timer = 0;
    const settle = () => setSettledLit(litIds);
    const onScroll = () => {
      window.clearTimeout(timer);
      timer = window.setTimeout(settle, 140);
    };
    timer = window.setTimeout(settle, 140);
    window.addEventListener("scroll", onScroll, { passive: true });
    return () => {
      window.clearTimeout(timer);
      window.removeEventListener("scroll", onScroll);
    };
  }, [litIds]);
  const writeTrail = useCallback(() => {
    bodyRef.current?.querySelectorAll<HTMLElement>(".card[data-record]").forEach((card) => {
      const id = card.dataset.record!;
      const state = litIds?.has(id) ? "here" : passed?.has(id) ? "passed" : "";
      if ((card.dataset.trail ?? "") !== state) card.dataset.trail = state;
    });
  }, [litIds, passed]);
  // The records this paper links a passage to: everything else on the map is drawn faded.
  const coverage = useMemo(() => {
    const ids = new Set<string>();
    for (const p of structures[stage]?.paper.passages ?? []) for (const id of [...p.claim_ids, ...p.assumption_ids]) ids.add(id);
    return ids;
  }, [structures, stage]);
  const overlayOpen = !!overlay;
  // The docked sheet lies over the lower part of the canvas; the map frames what it leaves.
  const [bodyH, setBodyH] = useState(0);
  const [share, setShare] = useState(readDockShare);
  useEffect(() => {
    const body = bodyRef.current;
    if (!body) return;
    const observer = new ResizeObserver(() => setBodyH(body.clientHeight));
    observer.observe(body);
    setBodyH(body.clientHeight);
    return () => observer.disconnect();
  }, []);
  const dockH = record ? Math.round(bodyH * share) : 0;
  const insets: Insets = useMemo(
    () => ({ top: 12, left: 16, bottom: 12 + dockH, right: overlayOpen ? INSPECTOR_W + 16 : 16 }),
    [overlayOpen, dockH],
  );

  useEffect(() => setNotice(null), [anchor]);
  // After every commit: the tree may have drawn new tiles.
  useEffect(writeTrail);

  // The camera holds still while what is lit stands in the canvas the sheet leaves.
  const inViewRef = useRef<(ids: readonly string[]) => boolean>(() => false);
  inViewRef.current = (ids) => {
    const canvas = bodyRef.current?.getBoundingClientRect();
    if (!canvas?.width) return false;
    const bottom = canvas.bottom - dockH;
    return ids.every((id) => {
      const cards = bodyRef.current!.querySelectorAll<HTMLElement>(`.card[data-record="${CSS.escape(id)}"]`);
      if (!cards.length) return true; // an assumption, drawn on the records that assume it
      return [...cards].some((card) => {
        const r = card.getBoundingClientRect();
        return r.top >= canvas.top && r.bottom <= bottom && r.left >= canvas.left && r.right <= canvas.right;
      });
    });
  };
  const inView = (ids: readonly string[]) => inViewRef.current(ids);

  useEffect(() => {
    if (!following || fadeTo) return;
    const want = goalFor(passage);
    if (want !== goal) {
      // Another main result: a deliberate crossfade, never a jump mid-motion.
      setFadeTo(want);
      return;
    }
    if (drawable.length && !inView(drawable)) treeRef.current?.focusIds(drawable);
    // Refocus when the passage, the main result or following changes (the map re-centres itself when its room changes).
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [drawable.join("|"), goal, following, fadeTo]);

  useEffect(() => {
    if (!fadeTo) return;
    const t = window.setTimeout(
      () => {
        setGoal(fadeTo);
        setFadeTo(null);
      },
      reduced ? 0 : CROSSFADE_MS,
    );
    return () => window.clearTimeout(t);
  }, [fadeTo, reduced]);

  // Every branch is drawn from the start, so following only frames; it never folds.
  const recordsRef = useRef(records);
  recordsRef.current = records;
  useEffect(() => {
    const open = window.setTimeout(() => treeRef.current?.expandAll(), 0);
    // Then the whole argument; the passage being read moves it only if it lies outside.
    const frame = window.setTimeout(() => {
      treeRef.current?.fitAll(false);
      if (followingRef.current && recordsRef.current.length && !inView(recordsRef.current)) treeRef.current?.focusIds(recordsRef.current);
    }, 80);
    return () => {
      window.clearTimeout(open);
      window.clearTimeout(frame);
    };
  }, [goal]);

  const onUserMove = useCallback(() => {
    if (!followingRef.current) return;
    followingRef.current = false;
    setFollowing(false);
    setPaused(true);
  }, []);

  const toggleFollowing = () => {
    // The pending initial frame reads this ref, so a click takes effect at once.
    followingRef.current = !followingRef.current;
    setPaused(false);
    setFollowing(followingRef.current);
  };

  // ---- Back into the text ------------------------------------------------------------

  const onSelect = useCallback(
    (id: string | null) => {
      if (!id) return;
      const slice = bestSlice(alignment, stage, id);
      const passage = slice?.anchor ?? firstPassageFor(structures[stage], [id]);
      setNotice(slice || passage ? null : id);
      onRecord?.(id, passage, slice);
    },
    [alignment, structures, stage, onRecord],
  );

  const onTrace = useCallback((id: string) => navigate({ view: "map", goal, node: id, trace: "rests" }), [goal]);
  const tree = useMemo(
    () => (
      <ArgumentTree
        key={goal}
        ref={treeRef}
        graph={graph}
        goal={goal}
        insets={insets}
        persist={false}
        mode="overview"
        tileWidth={PANE_TILE_W}
        selected={record?.id}
        litIds={settledLit}
        previewIds={hovered}
        coverage={coverage}
        onSelect={onSelect}
        onTrace={onTrace}
        onUserMove={onUserMove}
      />
    ),
    [goal, graph, insets, record?.id, settledLit, hovered, coverage, onSelect, onTrace, onUserMove],
  );

  const mapHref = routeHref({ view: "map", goal, node: drawable[0] });
  const noticeLabel = notice ? (graph.nodes.get(notice)?.label ?? notice) : "";
  // Where a record this paper does not discuss is read instead.
  const elsewhere = notice
    ? STAGE_ORDER.filter((s) => s !== stage)
        .map((s) => ({ stage: s, anchor: firstPassageFor(structures[s], [notice]) }))
        .filter((r): r is { stage: Stage; anchor: string } => !!r.anchor)
    : [];

  const state = paused && !following ? "Paused while you move the map" : anchor && !records.length ? "No record is linked to this passage." : "";

  return (
    <section className="map-pane" aria-label="Argument map beside the text" inert={inert ? true : undefined}>
      <header className="map-pane__head">
        <div className="map-pane__row">
          <span className="map-pane__goal" title={title}>
            {title}
          </span>
          <button
            type="button"
            className={`map-pane__follow${paused && !following ? " map-pane__follow--resume" : ""}`}
            aria-pressed={following}
            title={following ? "Turn off following the text" : "Follow the passage you are reading"}
            onClick={toggleFollowing}
          >
            <span className="map-pane__dot" aria-hidden="true" />
            {following ? "Following the text" : "Follow the text"}
          </button>
          <a
            className="map-pane__open"
            href={mapHref}
            onClick={(event) => {
              if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
              event.preventDefault();
              navigate({ view: "map", goal, node: drawable[0] });
            }}
          >
            Open the full map
          </a>
          {!inModal && (
            <button type="button" className="map-pane__hide" aria-label="Hide the map beside the text" onClick={onHide}>
              <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
                <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
              </svg>
            </button>
          )}
        </div>
        <div className="map-pane__row map-pane__row--trail">
          {progress && <span className="map-pane__progress">{progress}</span>}
          <span className="map-pane__state" role="status">
            {state}
          </span>
          <span className="map-pane__legend">
            <span className="map-pane__swatch map-pane__swatch--passed" aria-hidden="true" />
            Passed
            <span className="map-pane__swatch map-pane__swatch--lit" aria-hidden="true" />
            This passage
            <span className="map-pane__swatch" aria-hidden="true" />
            Ahead
            <span className="map-pane__swatch map-pane__swatch--faded" aria-hidden="true" />
            Not in the {PAPER_NAMES[stage].short.toLowerCase()}
          </span>
        </div>
      </header>
      <div className="map-pane__body" ref={bodyRef}>
        {notice && (
          <p className="map-pane__notice" role="status">
            <span>
              <strong>{noticeLabel}</strong>: this paper does not discuss it.
            </span>
            {elsewhere.map((r) => (
              <a key={r.stage} href={routeHref({ view: "read", stage: r.stage, anchor: r.anchor })}>
                Read it in the {PAPER_NAMES[r.stage].short.toLowerCase()}
              </a>
            ))}
            <button type="button" className="map-pane__dismiss" aria-label="Dismiss" onClick={() => setNotice(null)}>
              ×
            </button>
          </p>
        )}
        <div className={`map-pane__canvas${fadeTo ? " is-fading" : ""}`}>
          {tree}
        </div>
        {record && (
          <RecordDock
            record={record}
            share={share}
            onShare={setShare}
            onClose={() => onCloseRecord?.()}
            onSelect={onSelect}
            onEcho={setHovered}
            passageHref={passageHref ?? ((s, a) => routeHref({ view: "read", stage: s, anchor: a }))}
          />
        )}
        {overlay}
      </div>
    </section>
  );
});

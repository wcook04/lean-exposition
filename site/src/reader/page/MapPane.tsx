// The right page: the graph above the Lean, or beside it where the page is at least 860px
// wide, with a drag handle between them. Either can be closed and the choice is remembered.
// It opens with every branch drawn, records this paper discusses at full strength and the
// rest quieter, and it follows the reader: as a statement settles under the reading line its
// card lights, the camera moves only if the card has left the view, and its Lean fills the
// Lean page. Records already passed stay tinted. Panning or zooming pauses the camera. Under
// 1280px the same page opens as a sheet.

import { memo, useCallback, useEffect, useMemo, useRef, useState, type MutableRefObject, type ReactNode } from "react";
import type { Alignment } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { PAPER_NAMES } from "../../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "../../map/ArgumentTree";
import { mainGoal, startingGoals } from "../../map/TheoremPlate";
import { chooseGoal, reach, scopedGraph } from "../../map/treeModel";
import { useReducedMotion } from "../../map/canvas/useReducedMotion";
import { passageTopics, statementFor, type TieModel } from "../ties";
import { passageOf, passageRecords, trailAt, trailWords, type OutlineEntry, type PaperTrail, type Structures } from "./model";
import { clampDock, DOCK_MAX, DOCK_MIN, LeanDock, readDockShare, readPanes, saveDockShare, savePanes, type LeanView, type Panes } from "./RecordDock";
import { rightPreview, type Pin, type ReaderSignals } from "./rightPage";
import { useSignal, useSlowSignal } from "./signal";
import "./map-pane.css";

/** From this page width the Lean stands beside the graph, next to the paper. */
const SIDE_BY_SIDE = 860;
/** --t-state: the canvas crossfades when the main result changes. */
const CROSSFADE_MS = 160;

/** Narrow tiles, so that at the 11px floor the whole argument fits a 1440px window's half. */
const PANE_TILE_W = 140;

/** Lights these records on the map from outside it, without moving anything. */
export type PaneHover = (ids: ReadonlySet<string> | null) => void;

interface Props {
  stage: Stage;
  structures: Structures;
  outline: OutlineEntry[];
  trail: PaperTrail;
  /** What changes as the reader reads; the page re-renders here, never above. */
  signals: ReaderSignals;
  ties: TieModel;
  /** What the address has pinned. */
  pin: Pin | null;
  alignment?: Alignment | null;
  /** Filled by the pane: the paper's statements light cards through it. */
  hoverRef?: MutableRefObject<PaneHover | null>;
  /** Stands in on the Lean page: the passage inspector. */
  leanSlot?: ReactNode;
  inert?: boolean;
  /** The page fills a sheet, which has its own close control. */
  inModal?: boolean;
  onHide(): void;
  /** A card or list item was chosen. */
  onRecord?(id: string): void;
  onRelease(): void;
  onPoint(tie: number | null, record?: string): void;
  passageHref?(stage: Stage, anchor: string): string;
}

export const MapPane = memo(function MapPane({ stage, structures, outline, trail, signals, ties, pin, alignment = null, hoverRef, leanSlot, inert, inModal, onHide, onRecord, onRelease, onPoint, passageHref }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const reduced = useReducedMotion();
  const treeRef = useRef<MapViewHandle>(null);
  const bodyRef = useRef<HTMLDivElement>(null);
  const rootRef = useRef<HTMLElement>(null);

  // ---- What the reader is on ---------------------------------------------------------

  const follow = useSlowSignal(signals.follow);
  const pointed = useSignal(signals.point);
  const caption = useSignal(signals.caption);
  const preview = useSignal(rightPreview);
  const anchor = follow.anchor;
  const passage = useMemo(() => passageRecords(anchor ? passageOf(structures[stage], anchor) : undefined), [anchor, structures, stage]);
  const followRecord = follow.tie !== null ? ties.index.ties[follow.tie].record : null;
  const records = useMemo(() => (pin ? [pin.record] : followRecord ? [followRecord] : passage), [pin, followRecord, passage]);
  const passed = useMemo(() => trailAt(trail, anchor, passage), [trail, anchor, passage]);
  const progress = useMemo(() => trailWords(outline, follow.part, passed), [outline, follow.part, passed]);
  const view = useMemo<LeanView>(() => {
    // The pinned statement itself under the pointer is just the pin.
    if (pointed && !(pin && pointed.record === pin.record && pointed.tie === pin.tie)) return pointed.tie !== null ? { via: "point", kind: "statement", tie: pointed.tie, record: pointed.record } : { via: "point", kind: "record", record: pointed.record };
    if (pin) return pin.tie !== null ? { via: "pin", kind: "statement", tie: pin.tie, record: pin.record } : { via: "pin", kind: "record", record: pin.record };
    if (follow.tie !== null) return { via: "follow", kind: "statement", tie: follow.tie, record: ties.index.ties[follow.tie].record };
    const topics = passageTopics(ties, anchor);
    const ids = topics.length ? topics : passage;
    return anchor && ids.length ? { via: "follow", kind: "passage", anchor, records: ids } : { via: "follow", kind: "nothing" };
  }, [pointed, pin, follow.tie, ties, anchor, passage]);

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
  const followingRef = useRef(following);
  followingRef.current = following;
  // The statement's records where the map draws them, else the rest of its passage.
  const drawable = useMemo(() => {
    const exact = records.filter((id) => reachOf(goal).has(id));
    return exact.length ? exact : passage.filter((id) => reachOf(goal).has(id));
  }, [records, passage, reachOf, goal]);
  // A chip in the paper, or a list in the sheet, lights its cards while pointed at.
  const [hovered, setHovered] = useState<ReadonlySet<string> | null>(null);
  const litIds = useMemo(() => (drawable.length ? new Set(drawable) : null), [drawable]);
  const passedIds = passed.passed;
  // The tree's own selection moves its camera. A pin must not, so it is only ever lit here.
  const pinned = pin?.record ?? null;
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
      const state = pinned === id ? "pinned" : litIds?.has(id) ? "here" : passedIds.has(id) ? "passed" : "";
      if ((card.dataset.trail ?? "") !== state) card.dataset.trail = state;
    });
  }, [litIds, passedIds, pinned]);
  // The records this paper links a passage to: everything else on the map is drawn faded.
  const coverage = useMemo(() => {
    const ids = new Set<string>();
    for (const p of structures[stage]?.paper.passages ?? []) for (const id of [...p.claim_ids, ...p.assumption_ids]) ids.add(id);
    return ids;
  }, [structures, stage]);
  // The split between the graph and the Lean, remembered, with more for the Lean on a short page.
  const [share, setShare] = useState<number | null>(null);
  const [panes, setPanes] = useState<Panes>(() => (inModal ? { graph: !window.matchMedia("(max-width: 700px)").matches, lean: true } : readPanes({ graph: true, lean: true })));
  const setPane = useCallback(
    (name: keyof Panes, shown: boolean) => {
      setPanes((was) => {
        const next = { ...was, [name]: shown };
        if (!inModal) savePanes(next);
        return next;
      });
    },
    [inModal],
  );
  const insets: Insets = useMemo(() => ({ top: 12, left: 16, bottom: 12, right: 16 }), []);
  useEffect(() => {
    const root = rootRef.current;
    if (!root) return;
    const value = share ?? readDockShare(root.clientHeight);
    root.style.setProperty("--lean-share", String(value));
  }, [share]);

  // The drag writes one custom property; the map hears the new room when it ends.
  const onHandleDown = (event: React.PointerEvent<HTMLDivElement>) => {
    const root = rootRef.current;
    if (event.button !== 0 || !root) return;
    event.preventDefault();
    const handle = event.currentTarget;
    handle.setPointerCapture(event.pointerId);
    const box = root.getBoundingClientRect();
    const side = box.width >= SIDE_BY_SIDE;
    let value = share ?? readDockShare(box.height);
    root.classList.add("is-dragging");
    const move = (e: PointerEvent) => {
      // Stacked, the Lean is below the handle; side by side, it is to the left of it.
      value = clampDock(side ? (e.clientX - box.left) / box.width : (box.bottom - e.clientY) / box.height);
      root.style.setProperty("--lean-share", String(value));
    };
    const end = () => {
      handle.removeEventListener("pointermove", move);
      handle.removeEventListener("pointerup", end);
      handle.removeEventListener("pointercancel", end);
      root.classList.remove("is-dragging");
      saveDockShare(value);
      setShare(value);
    };
    handle.addEventListener("pointermove", move);
    handle.addEventListener("pointerup", end);
    handle.addEventListener("pointercancel", end);
  };

  const onHandleKey = (event: React.KeyboardEvent) => {
    const root = rootRef.current;
    if (!root) return;
    const side = root.clientWidth >= SIDE_BY_SIDE;
    const step = event.key === (side ? "ArrowRight" : "ArrowUp") ? 0.05 : event.key === (side ? "ArrowLeft" : "ArrowDown") ? -0.05 : 0;
    if (!step) return;
    event.preventDefault();
    const next = clampDock((share ?? readDockShare(root.clientHeight)) + step);
    saveDockShare(next);
    setShare(next);
  };

  useEffect(() => {
    if (!hoverRef) return;
    hoverRef.current = setHovered;
    return () => {
      hoverRef.current = null;
    };
  }, [hoverRef]);

  // After every commit: the tree may have drawn new tiles.
  useEffect(writeTrail);

  // The camera holds still while what is lit stands in the canvas the sheet leaves.
  const inViewRef = useRef<(ids: readonly string[]) => boolean>(() => false);
  inViewRef.current = (ids) => {
    const canvas = bodyRef.current?.getBoundingClientRect();
    if (!canvas?.width) return false;
    const bottom = canvas.bottom;
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
    const want = goalFor(pin ? [pin.record] : passage);
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

  const onSelect = useCallback((id: string | null) => id && onRecord?.(id), [onRecord]);
  const onCard = useCallback((id: string | null) => onPoint(id ? statementFor(ties, id) : null, id ?? undefined), [onPoint, ties]);

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
        litIds={settledLit}
        previewIds={hovered}
        coverage={coverage}
        onSelect={onSelect}
        onHover={onCard}
        onTrace={onTrace}
        onUserMove={onUserMove}
      />
    ),
    [goal, graph, insets, settledLit, hovered, coverage, onSelect, onCard, onTrace, onUserMove],
  );

  const mapHref = routeHref({ view: "map", goal, node: drawable[0] });
  const closeGraph = () => (panes.lean ? setPane("graph", false) : onHide());
  const closeLean = () => (panes.graph ? setPane("lean", false) : onHide());

  return (
    <section ref={rootRef} className={`map-pane${panes.graph && panes.lean ? " map-pane--both" : ""}`} aria-label="The proof beside the text" inert={inert ? true : undefined}>
      <div className="map-pane__pages">
      {panes.graph && (
        <div className="map-pane__graph">
          <header className="map-pane__head">
            <div className="map-pane__row">
              <span className="map-pane__goal" title={title}>
                {title}
              </span>
              {paused && !following && (
                <button type="button" className="map-pane__follow map-pane__follow--resume" onClick={toggleFollowing}>
                  Follow the text again
                </button>
              )}
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
              <button type="button" className="map-pane__hide" aria-label="Close the graph" onClick={closeGraph}>
                <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
                  <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
                </svg>
              </button>
            </div>
            <div className="map-pane__row map-pane__row--trail">
              {progress && <span className="map-pane__progress">{progress}</span>}
              <span className="map-pane__legend">
                <span className="map-pane__swatch map-pane__swatch--passed" aria-hidden="true" />
                Passed
                <span className="map-pane__swatch map-pane__swatch--lit" aria-hidden="true" />
                Here
                <span className="map-pane__swatch" aria-hidden="true" />
                Ahead
                <span className="map-pane__swatch map-pane__swatch--faded" aria-hidden="true" />
                Not in the {PAPER_NAMES[stage].short.toLowerCase()}
              </span>
            </div>
          </header>
          <div className="map-pane__body" ref={bodyRef}>
            <div className={`map-pane__canvas${fadeTo ? " is-fading" : ""}`}>{tree}</div>
          </div>
        </div>
      )}
      {panes.graph && panes.lean && (
        <div
          className="map-pane__handle"
          role="separator"
          aria-orientation="horizontal"
          aria-label="Resize the graph and the Lean"
          aria-valuemin={Math.round(DOCK_MIN * 100)}
          aria-valuemax={Math.round(DOCK_MAX * 100)}
          aria-valuenow={Math.round((share ?? 0.5) * 100)}
          tabIndex={0}
          onPointerDown={onHandleDown}
          onKeyDown={onHandleKey}
        >
          <span aria-hidden="true" />
        </div>
      )}
      {panes.lean && (
        <LeanDock
          view={view}
          ties={ties}
          stage={stage}
          alignment={alignment}
          caption={pointed ? null : caption}
          captionRecords={caption ? passageTopics(ties, caption) : undefined}
          slot={preview ?? leanSlot}
          onRelease={onRelease}
          onPick={(id) => onRecord?.(id)}
          onPoint={onPoint}
          onClose={closeLean}
          passageHref={passageHref ?? ((s, a) => routeHref({ view: "read", stage: s, anchor: a }))}
        />
      )}
      </div>
      {!(panes.graph && panes.lean) && (
        <button type="button" className="map-pane__reopen" onClick={() => setPane(panes.graph ? "lean" : "graph", true)}>
          {panes.graph ? "Show the Lean" : "Show the graph"}
        </button>
      )}
    </section>
  );
});

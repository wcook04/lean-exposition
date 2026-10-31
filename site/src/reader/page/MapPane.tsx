// The right page: the graph, full height, a sidecar to the paper. It comes along as the reader
// scrolls. It opens with every branch drawn, records this paper discusses at full strength
// and the rest quieter: as a statement settles under the reading line its card lights, the
// camera moves only if the card has left the view, and one line under the graph names it in
// plain words. Cards ahead are in lighter ink and cards passed at full strength. Panning or
// zooming pauses the camera. That is Graph mode. Lean mode gives the pane to the Lean, in one of
// two ways: clicking a card or a statement opens that step, which rises from its card and stays
// put, and the toggle's Lean with nothing opened follows the text. The graph underneath is not
// touched, so coming back leaves it as it was. The handle draws the graph back above the Lean
// for those who want both. Under 1280px the same page opens as a sheet.

import { memo, useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type MutableRefObject, type ReactNode } from "react";
import type { Alignment } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { recordLine, shortTitle } from "../../compare/useAlignment";
import type { LeanWalk } from "../../lean/walk";
import { PAPER_NAMES } from "../../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "../../map/ArgumentTree";
import { mainGoal, startingGoals } from "../../map/TheoremPlate";
import { useKeptCamera } from "../../map/scene";
import { chooseGoal, reach, scopedGraph } from "../../map/treeModel";
import { recordMark } from "../../map/leanMarks";
import { useReducedMotion } from "../../map/canvas/useReducedMotion";
import { leanTruth, passageTopics, statementFor, type TieModel } from "../ties";
import { passageOf, passageRecords, trailAt, trailWords, type OutlineEntry, type PaperTrail, type Structures } from "./model";
import { clampDock, DOCK_MAX, DOCK_MIN, LeanDock, readDockShare, recordOfDecl, saveDockShare, type LeanOpen } from "./RecordDock";
import { ModeToggle, type PaneMode } from "./ModeToggle";
import { rightPreview, type Pin, type ReaderSignals } from "./rightPage";
import { useSignal, useSlowSignal } from "./signal";
import "./map-pane.css";

/** From this page width the Lean stands beside the graph, next to the paper. */
const SIDE_BY_SIDE = 860;
/** From this share up the Lean has the pane, and no graph shows. */
const WHOLE_PANE = 0.97;
/** How much of the page a preview under the pointer takes. */
const PREVIEW_SHARE = 0.42;
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
  /** A declaration the address names, reached by walking the Lean. */
  decl?: string | null;
  declModule?: string;
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
  /** From an opened statement to the Lean following the text. */
  onFollowText?(): void;
  mode: PaneMode;
  onMode(mode: PaneMode): void;
  onPoint(tie: number | null, record?: string): void;
  onName?(walk: LeanWalk): void;
  /** Open the steps and links of the passage being read. */
  onPassage?(anchor: string | null, opener: HTMLElement): void;
  /** The passage a part of the paper belongs to, if it belongs to one. */
  passagePart?(part: number): string | undefined;
  passageHref?(stage: Stage, anchor: string): string;
}

export const MapPane = memo(function MapPane({ stage, structures, outline, trail, signals, ties, pin, decl = null, declModule, alignment = null, hoverRef, leanSlot, inert, inModal, onHide, onRecord, onRelease, onFollowText, mode, onMode, onPoint, onName, onPassage, passagePart, passageHref }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const reduced = useReducedMotion();
  const treeRef = useRef<MapViewHandle>(null);
  useKeptCamera(treeRef, useCallback((id: string) => graph.nodes.has(id), [graph]));
  const bodyRef = useRef<HTMLDivElement>(null);
  const rootRef = useRef<HTMLElement>(null);

  // ---- What the reader is on ---------------------------------------------------------

  const follow = useSlowSignal(signals.follow);
  const pointed = useSignal(signals.point);
  const caption = useSignal(signals.caption);
  const partAt = useSlowSignal(signals.part);
  const preview = useSignal(rightPreview);
  const anchor = follow.anchor;
  const passage = useMemo(() => passageRecords(anchor ? passageOf(structures[stage], anchor) : undefined), [anchor, structures, stage]);
  const followRecord = follow.tie !== null ? ties.index.ties[follow.tie].record : null;
  const records = useMemo(() => (pin ? [pin.record] : followRecord ? [followRecord] : passage), [pin, followRecord, passage]);
  const passed = useMemo(() => trailAt(trail, anchor, passage), [trail, anchor, passage]);
  const progress = useMemo(() => trailWords(outline, follow.part, passed), [outline, follow.part, passed]);
  const slot = preview ?? leanSlot;
  const openRecord = pin?.record ?? (decl ? recordOfDecl(alignment, decl) : null);
  // A step with no Lean does not open: the line under the graph says so.
  const pinLean = !!pin && (pin.tie !== null ? ties.index.ties[pin.tie].lean : !!recordLine(pin.record)?.lean);
  // The Lean closed, what is said under the graph lasts as long as the pin does.
  const expanded = pinLean || !!decl || !!slot;
  /** A reference under the pointer: it comes and goes, so it takes a modest part of the page. */
  const previewOnly = !!preview && !pinLean && !decl && !leanSlot;
  /** Lean mode with nothing opened: the Lean follows the text. */
  const keep = mode === "lean" && !expanded;
  const leanShown = mode === "lean" || expanded;
  const leanOpen = useMemo<LeanOpen>(() => {
    if (expanded || pin) return { via: "pin", record: openRecord, tie: decl ? null : (pin?.tie ?? null), decl, declModule };
    if (pointed) return { via: "point", record: pointed.record, tie: pointed.tie, decl: null };
    if (followRecord) return { via: "follow", record: followRecord, tie: follow.tie, decl: null };
    const topics = passageTopics(ties, anchor);
    return { via: "follow", record: null, tie: null, decl: null, topics: topics.length ? topics : passage };
  }, [expanded, openRecord, decl, declModule, pin, pointed, followRecord, follow.tie, ties, anchor, passage]);
  /** The card the Lean rises from, found as it opens. */
  const [from, setFrom] = useState<HTMLElement | null>(null);

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
  const pinned = openRecord;
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
      const state = pinned === id ? "pinned" : litIds?.has(id) ? "here" : passedIds.has(id) ? "passed" : "ahead";
      if ((card.dataset.trail ?? "") !== state) card.dataset.trail = state;
    });
  }, [litIds, passedIds, pinned]);
  // The records this paper links a passage to: everything else on the map is drawn faded.
  const coverage = useMemo(() => {
    const ids = new Set<string>();
    for (const p of structures[stage]?.paper.passages ?? []) for (const id of [...p.claim_ids, ...p.assumption_ids]) ids.add(id);
    return ids;
  }, [structures, stage]);
  // Kept open, the Lean holds part of the page for good, so the map frames what is left.
  const [kept, setKept] = useState({ bottom: 0, left: 0 });
  const insets: Insets = useMemo(() => ({ top: 12, left: 16 + kept.left, bottom: 12 + kept.bottom, right: 16 }), [kept]);
  const canvasRef = useRef<HTMLDivElement>(null);
  const wasOpen = useRef(false);
  const framedFrom = useRef<ReturnType<MapViewHandle["getScene"]> | null>(null);

  // How far the Lean rises, remembered. It is a layer over the graph: the canvas beneath keeps
  // its size and its camera. Only a transform carries the card into the part left showing, and
  // that goes when the Lean closes, so the graph is exactly as it was.
  const isSide = () => (rootRef.current?.clientWidth ?? 0) >= SIDE_BY_SIDE;
  const keptOnly = keep;
  const applyShare = useCallback(
    (value?: number) => {
      const root = rootRef.current;
      if (!root) return;
      const side = root.clientWidth >= SIDE_BY_SIDE;
      root.style.setProperty("--lean-share", String(value ?? (previewOnly && !keep ? PREVIEW_SHARE : leanShown ? readDockShare(side) : 0)));
    },
    [keep, leanShown, previewOnly],
  );
  const measureKept = useCallback(() => {
    const pages = rootRef.current?.querySelector<HTMLElement>(".map-pane__pages");
    const side = !!pages && pages.clientWidth >= SIDE_BY_SIDE;
    const share = readDockShare(side);
    // Only a Lean drawn down beside the graph leaves a graph to frame.
    if (!keep || !pages || share >= WHOLE_PANE) return setKept({ bottom: 0, left: 0 });
    // The graph's line and head are not part of the canvas: only what lies over the canvas counts.
    const body = bodyRef.current?.getBoundingClientRect();
    const box = pages.getBoundingClientRect();
    const cover = side ? box.width * share : Math.max(0, (body?.bottom ?? box.bottom) - (box.bottom - box.height * share));
    setKept(side ? { bottom: 0, left: Math.round(cover) } : { bottom: Math.round(cover), left: 0 });
  }, [keep]);
  useLayoutEffect(measureKept, [measureKept]);
  const place = useCallback(() => {
    const canvas = canvasRef.current;
    const body = bodyRef.current;
    const lean = rootRef.current?.querySelector(".lean-page");
    if (!canvas || !body) return;
    const card = openRecord ? body.querySelector<HTMLElement>(`.card[data-record="${CSS.escape(openRecord)}"]`) : null;
    // No card to show (a declaration of no step, a step not drawn here): no band of blank graph.
    rootRef.current?.classList.toggle("map-pane--fold", expanded && !card && !slot);
    // Under the whole pane there is no band to lift it into.
    if (!card || !lean || !expanded || readDockShare(isSide()) >= WHOLE_PANE) {
      canvas.style.transform = "";
      return;
    }
    const b = body.getBoundingClientRect();
    const l = lean.getBoundingClientRect();
    // Measured where it stands now, which may be part way through gliding to the last place.
    const now = new DOMMatrixReadOnly(getComputedStyle(canvas).transform);
    const seen = card.getBoundingClientRect();
    const c = { left: seen.left - now.e, right: seen.right - now.e, top: seen.top - now.f, bottom: seen.bottom - now.f };
    // Centred in what is left of the graph, so the place is plain at a glance.
    if (isSide()) {
      const left = l.right + 8;
      canvas.style.transform = `translateX(${Math.round((left + b.right) / 2 - (c.left + c.right) / 2)}px)`;
    } else {
      // The head gives way while the Lean is open, so the band is all graph.
      const top = body.closest(".map-pane__pages")!.getBoundingClientRect().top;
      const bottom = l.top - 11;
      canvas.style.transform = `translate(${Math.round((b.left + b.right) / 2 - (c.left + c.right) / 2)}px, ${Math.round((top + bottom) / 2 - (c.top + c.bottom) / 2)}px)`;
    }
  }, [openRecord, expanded, slot]);

  useLayoutEffect(() => {
    applyShare();
    if (!expanded) {
      if (canvasRef.current) canvasRef.current.style.transform = "";
      setFrom(null);
      // A card that had to be framed to open: the camera goes back to where the reader left it.
      if (framedFrom.current) treeRef.current?.restoreScene(framedFrom.current);
      framedFrom.current = null;
      return;
    }
    const card = openRecord ? (bodyRef.current?.querySelector<HTMLElement>(`.card[data-record="${CSS.escape(openRecord)}"]`) ?? null) : null;
    setFrom(card);
    if (card && !inViewRef.current([openRecord!])) {
      // Off the view: frame it first, and only then lift it clear of the Lean.
      framedFrom.current ??= treeRef.current?.getScene() ?? null;
      treeRef.current?.focusIds([openRecord!]);
      const t = window.setTimeout(place, 380);
      return () => window.clearTimeout(t);
    }
    // On a deep link the tree and the camera are still arriving: place it as each lands.
    const frame = requestAnimationFrame(place);
    const later = [160, 420, 900, 1600].map((ms) => window.setTimeout(place, ms));
    return () => {
      cancelAnimationFrame(frame);
      later.forEach((t) => window.clearTimeout(t));
    };
  }, [expanded, openRecord, applyShare, place]);

  // The drag writes one custom property; the card moves back into view when it ends.
  const onHandleDown = (event: React.PointerEvent<HTMLDivElement>) => {
    const root = rootRef.current;
    if (event.button !== 0 || !root) return;
    event.preventDefault();
    const handle = event.currentTarget;
    handle.setPointerCapture(event.pointerId);
    const box = root.querySelector<HTMLElement>(".map-pane__pages")!.getBoundingClientRect();
    const side = isSide();
    // At rest the handle lies at the foot of the graph: drawing it up keeps the Lean open.
    const rest = !keep && !expanded;
    let value = rest ? 0 : readDockShare(side);
    let raised = false;
    const startY = event.clientY;
    const startX = event.clientX;
    root.classList.add("is-dragging");
    const move = (e: PointerEvent) => {
      // Stacked, the Lean is below the handle; side by side, it is to the left of it.
      const raw = side ? (e.clientX - box.left) / box.width : (box.bottom - e.clientY) / box.height;
      if (rest && !raised) {
        if (Math.abs(side ? e.clientX - startX : e.clientY - startY) < 24) return;
        raised = true;
      }
      value = rest ? clampDock(raw) : raw;
      applyShare(value);
    };
    const end = () => {
      handle.removeEventListener("pointermove", move);
      handle.removeEventListener("pointerup", end);
      handle.removeEventListener("pointercancel", end);
      root.classList.remove("is-dragging");
      if (rest && !raised) return;
      // Dragged nearly shut, the kept page closes.
      if (keptOnly && value < DOCK_MIN * 0.8) {
        setKept({ bottom: 0, left: 0 });
        onMode("graph");
        return;
      }
      value = clampDock(value);
      saveDockShare(value, side);
      if (rest) onMode("lean");
      else {
        applyShare(value);
        measureKept();
        place();
      }
    };
    handle.addEventListener("pointermove", move);
    handle.addEventListener("pointerup", end);
    handle.addEventListener("pointercancel", end);
  };

  const onHandleKey = (event: React.KeyboardEvent) => {
    const side = isSide();
    const step = event.key === (side ? "ArrowRight" : "ArrowUp") ? 0.05 : event.key === (side ? "ArrowLeft" : "ArrowDown") ? -0.05 : 0;
    if (!step) return;
    event.preventDefault();
    if (!leanShown) {
      if (step > 0) onMode("lean");
      return;
    }
    const next = clampDock(readDockShare(side) + step);
    saveDockShare(next, side);
    applyShare(next);
    measureKept();
    place();
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
    const bottom = canvas.bottom - kept.bottom;
    const left = canvas.left + kept.left;
    return ids.every((id) => {
      const cards = bodyRef.current!.querySelectorAll<HTMLElement>(`.card[data-record="${CSS.escape(id)}"]`);
      if (!cards.length) return true; // an assumption, drawn on the records that assume it
      return [...cards].some((card) => {
        const r = card.getBoundingClientRect();
        return r.top >= canvas.top && r.bottom <= bottom && r.left >= left && r.right <= canvas.right;
      });
    });
  };
  const inView = (ids: readonly string[]) => inViewRef.current(ids);

  useEffect(() => {
    if (!following || fadeTo) return;
    // A pin never changes the main result: closing it must leave the graph as it was.
    const want = goalFor(passage);
    if (want !== goal) {
      // Another main result: a deliberate crossfade, never a jump mid-motion.
      setFadeTo(want);
      return;
    }
    // With the Lean open the graph is left alone, so it is as it was when the Lean closes. The
    // run that closes it is left out too: the canvas is still gliding back, and every card reads off.
    const away = expanded || (keep && readDockShare(isSide()) >= WHOLE_PANE);
    const closing = wasOpen.current && !away;
    wasOpen.current = away;
    if (!away && !closing && drawable.length && !inView(drawable)) treeRef.current?.focusIds(drawable);
    // Refocus when the passage, the main result or following changes (the map re-centres itself when its room changes).
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [drawable.join("|"), goal, following, fadeTo, expanded, keep]);

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
        statusOf={recordMark}
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
  const line = lineFor();

  return (
    <section ref={rootRef} className={`map-pane${leanShown ? " map-pane--open" : ""}`} aria-label="The proof beside the text" inert={inert ? true : undefined}>
      <div className="map-pane__bar">
        <ModeToggle mode={mode} onMode={onMode} />
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
        {!inModal && (
          <button type="button" className="map-pane__hide" aria-label="Hide the pane" onClick={onHide}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
          </button>
        )}
      </div>
      <div className="map-pane__pages">
        <div className="map-pane__graph">
          <header className="map-pane__head">
            <div className="map-pane__row map-pane__row--trail">
              {progress && <span className="map-pane__progress">{progress}</span>}
              <span className="map-pane__legend">The graph fills in as you read. Faintest: not in the {PAPER_NAMES[stage].short.toLowerCase()}.</span>
            </div>
          </header>
          <div className="map-pane__body" ref={bodyRef}>
            <div ref={canvasRef} className={`map-pane__canvas${fadeTo ? " is-fading" : ""}`}>
              {tree}
            </div>
          </div>
          <div className="map-pane__foot">
            <p className="map-pane__line" data-via={line.via} role="status">
              {line.words}
            </p>
            {pin && !expanded ? (
              <button type="button" className="map-pane__keep" onClick={onRelease}>
                Follow the text
              </button>
            ) : (
              <>
                {anchor && onPassage && (
                  <button type="button" className="map-pane__keep" onClick={(event) => onPassage(anchor, event.currentTarget)}>
                    This passage
                  </button>
                )}
              </>
            )}
          </div>
        </div>
        {!previewOnly && (!inModal || leanShown) && (
          <div
            className="map-pane__handle"
            role="separator"
            aria-orientation="horizontal"
            aria-label="Draw the Lean up over the graph, or size it"
            aria-valuemin={0}
            aria-valuemax={Math.round(DOCK_MAX * 100)}
            aria-valuenow={leanShown ? Math.round(readDockShare() * 100) : 0}
            tabIndex={0}
            onPointerDown={onHandleDown}
            onKeyDown={onHandleKey}
          >
            <span aria-hidden="true" />
          </div>
        )}
        {(leanShown || previewOnly) && (
          <>
            <LeanDock
              open={leanOpen}
              ties={ties}
              stage={stage}
              alignment={alignment}
              slot={slot}
              from={from}
              onRelease={onRelease}
              onFollowText={onFollowText}
              onPick={(id) => onRecord?.(id)}
              onPoint={onPoint}
              onName={onName}
              passageHref={passageHref ?? ((s, a) => routeHref({ view: "read", stage: s, anchor: a }))}
            />
          </>
        )}
      </div>
    </section>
  );

  /** One line under the graph, in plain words: what the reader is on or pointing at. */
  function lineFor(): { via: string; words: string } {
    const named = (id: string) => shortTitle(id, graph.nodes.get(id)?.label ?? id);
    /** "Has Lean: click to open it.", or the note or the plain fact where there is none to open. */
    const says = (id: string, t: number | null, invite: string) => {
      if (t === null) return recordLine(id)?.lean ? `${named(id)}. Has Lean: ${invite}.` : `${named(id)}. No Lean linked.`;
      const truth = leanTruth(ties, t, alignment);
      if (truth.lean) return `${named(id)}. ${truth.words}: ${invite}.`;
      return truth.note ?? `${named(id)}. No Lean linked.`;
    };
    // What is not drawn is said here, so that no note ever covers a card.
    const drawn = (id: string) => (reachOf(goal).has(id) ? "" : " Not in the argument drawn here.");
    if (pin && !expanded) return { via: "pin", words: `${says(pin.record, pin.tie, "")}${drawn(pin.record)}` };
    if (pointed) return { via: "point", words: `${says(pointed.record, pointed.tie, "click to open it")}${drawn(pointed.record)}` };
    if (caption) {
      const topics = passageTopics(ties, caption).filter((id) => graph.nodes.has(id));
      if (topics.length) return { via: "point", words: `No exact tie in this paragraph. Its passage discusses ${topics.slice(0, 3).map(named).join(", ")}${topics.length > 3 ? ", and more" : ""}.` };
    }
    if (followRecord) return { via: "follow", words: `Reading: ${says(followRecord, follow.tie, "click the statement or its card")}${drawn(followRecord)}` };
    // Past the last passage (the references, say) the nearest passage is not what is on the page.
    const inPassage = !!anchor && passagePart?.(partAt) === anchor;
    const topics = inPassage ? passageTopics(ties, anchor).filter((id) => graph.nodes.has(id)) : [];
    if (topics.length) return { via: "follow", words: `No exact statement here. This passage discusses ${topics.slice(0, 3).map(named).join(", ")}${topics.length > 3 ? ", and more" : ""}.` };
    return { via: "follow", words: "Nothing in this stretch of the paper is tied to the Lean." };
  }
});

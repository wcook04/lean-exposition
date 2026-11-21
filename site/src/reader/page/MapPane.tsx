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
import { isPhraseLayer, leanTruth, passageTopics, phraseTitle, statementFor, topicOf, type TieModel } from "../ties";
import { passageOf, passageRecords, trailAt, trailWords, type OutlineEntry, type PaperTrail, type Structures } from "./model";
import { clampDock, DOCK_MAX, DOCK_MIN, LeanDock, readDockShare, recordOfDecl, saveDockShare, type LeanOpen } from "./RecordDock";
import { readSplitShare, saveSplitShare } from "./panePrefs";
import { ModeToggle, type PaneMode } from "./ModeToggle";
import { rightPreview, type Pin, type ReaderSignals } from "./rightPage";
import { useSignal, useSlowSignal } from "./signal";
import { dockDecl } from "./PhraseCard";
import { declarationNeighbourhood } from "./leanNeighbours";
import { LeanNeighbourView } from "./LeanNeighbourView";
import { useLeanModule, useLeanShell } from "../../lean/data";
import "./map-pane.css";

/** From this page width the Lean stands beside the graph, next to the paper. */
const SIDE_BY_SIDE = 860;
/** The phrase split, until a reader draws its handle: the graph above, the card below. */
const splitShare = { current: readSplitShare() };
/** From this share up the Lean has the pane, and no graph shows. */
const WHOLE_PANE = 0.97;
/** How much of the page a preview under the pointer takes. */
const PREVIEW_SHARE = 0.42;
/** --t-state: the canvas crossfades when the main result changes. */
const CROSSFADE_MS = 160;

/** Narrow tiles, so that at the 11px floor the whole argument fits a 1440px window's half. */
const PANE_TILE_W = 140;
/** Tall enough for three lines, so that every title is shown whole. */
const PANE_TILE_H = 62;

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
  // A statement pinned while the graph was chosen stays on the graph, with its card lit.
  // A phrase opened on the Graph tab splits the pane: the graph above, its card and Lean below.
  // The Graph tab always splits the pane: the graph above, and below it the Lean of what is open,
  // or of what is being read. A phrase opened there is a `phrasePin`.
  const split = mode === "graph" && !decl && !slot;
  const phrasePin = split && !!pin && pin.tie !== null && isPhraseLayer(ties) && ties.index.ties[pin.tie].lean;
  const expanded = (pinLean && mode === "lean") || !!decl || !!slot || split;
  /** A reference under the pointer: it comes and goes, so it takes a modest part of the page. */
  const previewOnly = !!preview && !pinLean && !decl && !leanSlot;
  /** Lean mode with nothing opened: the Lean follows the text. */
  const keep = mode === "lean" && !expanded;
  const leanShown = mode === "lean" || expanded;
  const leanOpen = useMemo<LeanOpen>(() => {
    if ((expanded && !split) || pin) return { via: "pin", record: openRecord, tie: decl ? null : (pin?.tie ?? null), decl, declModule };
    if (pointed) return { via: "point", record: pointed.record, tie: pointed.tie, decl: null };
    if (followRecord) return { via: "follow", record: followRecord, tie: follow.tie, decl: null };
    const topics = passageTopics(ties, anchor);
    return { via: "follow", record: null, tie: null, decl: null, topics: topics.length ? topics : passage };
  }, [expanded, split, openRecord, decl, declModule, pin, pointed, followRecord, follow.tie, ties, anchor, passage]);
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
  // In the split, the graph centres the phrase's own step, or, where the map does not draw
  // it, the nearest phrase's step in reading order.
  const ownDrawn = !!pin && split && reachOf(goal).has(pin.record);
  const splitStep = useMemo(() => {
    if (!split || !pin) return null;
    if (ownDrawn) return pin.record;
    if (!phrasePin || pin.tie === null) return null;
    const at = ties.order.indexOf(pin.tie);
    for (let d = 1; d < ties.order.length; d++) {
      for (const k of [at - d, at + d]) {
        const id = ties.index.ties[ties.order[k]]?.record;
        if (id && reachOf(goal).has(id)) return id;
      }
    }
    return null;
  }, [split, phrasePin, pin, ownDrawn, ties, reachOf, goal]);
  /** The card the open Lean rises from, and that the graph keeps in view beside it. */
  const cardRecord = split ? splitStep : openRecord;

  // A phrase whose declaration is no step drawn here: the top half draws that declaration with
  // its Lean neighbours instead, following the card's selected tab, until the reader asks for
  // the argument map back.
  const [showArgument, setShowArgument] = useState(false);
  useEffect(() => setShowArgument(false), [pin?.record, pin?.tie]);
  const shown = useSignal(dockDecl);
  const firstRow = phrasePin && pin && pin.tie !== null ? ties.index.ties[pin.tie].rows?.[0] : undefined;
  const target = phrasePin && !ownDrawn && !showArgument ? (shown ?? (firstRow ? { name: firstRow.name, module: firstRow.module } : null)) : null;
  const shellState = useLeanShell();
  const moduleState = useLeanModule(target?.module);
  const neighbours = useMemo(() => {
    if (!target || shellState.status !== "ready" || moduleState.status !== "ready") return null;
    const decl = moduleState.module.declarations.find((d) => d.name === target.name);
    if (!decl) return null;
    const { shell } = shellState;
    const lines = moduleState.module.source.split("\n");
    const titleOf = (name: string) => shell.plain.get(name) ?? alignment?.names?.[name] ?? name.slice(name.lastIndexOf(".") + 1).replace(/_/g, " ");
    return declarationNeighbourhood({
      name: decl.name,
      title: (pin && pin.tie !== null && ties.index.ties[pin.tie].rows?.find((row) => row.name === decl.name)?.plain) || titleOf(decl.name),
      kind: decl.kind,
      statement: lines.slice(decl.line - 1, decl.signature_end_line).join("\n"),
      uses: decl.uses,
      usedBy: decl.used_by,
      rowOf: (name) => {
        const row = shell.index.byName.get(name)?.[0];
        return row ? { kind: row.kind, module: row.module, line: row.line } : undefined;
      },
      titleOf,
      origin: graph.nodes.get(home)!.origin,
    });
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [target?.name, target?.module, shellState, moduleState, alignment, graph, pin, ties]);

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
  const pinned = split ? (ownDrawn ? openRecord : null) : openRecord;
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
  const insets: Insets = useMemo(() => ({ top: 12, left: 16 + kept.left, bottom: 24 + kept.bottom, right: 16 }), [kept]);
  const canvasRef = useRef<HTMLDivElement>(null);
  const wasOpen = useRef(false);
  const framedFrom = useRef<ReturnType<MapViewHandle["getScene"]> | null>(null);

  // How far the Lean rises, remembered. It is a layer over the graph: the canvas beneath keeps
  // its size and its camera. Only a transform carries the card into the part left showing, and
  // that goes when the Lean closes, so the graph is exactly as it was.
  // The split stands one above the other at every width, at its own share of the pane.
  const isSide = () => !split && (rootRef.current?.clientWidth ?? 0) >= SIDE_BY_SIDE;
  const shareOf = (side: boolean) => (split ? splitShare.current : readDockShare(side));
  const keptOnly = keep;
  const applyShare = useCallback(
    (value?: number) => {
      const root = rootRef.current;
      if (!root) return;
      const side = isSide();
      root.style.setProperty("--lean-share", String(value ?? (previewOnly && !keep ? PREVIEW_SHARE : leanShown ? shareOf(side) : 0)));
    },
    [keep, leanShown, previewOnly],
  );
  const measureKept = useCallback(() => {
    const pages = rootRef.current?.querySelector<HTMLElement>(".map-pane__pages");
    const side = !split && !!pages && pages.clientWidth >= SIDE_BY_SIDE;
    const share = shareOf(side);
    // Only a Lean drawn down beside the graph leaves a graph to frame; so does the split.
    if ((!keep && !split) || !pages || share >= WHOLE_PANE) return setKept({ bottom: 0, left: 0 });
    // The graph's line and head are not part of the canvas: only what lies over the canvas counts.
    const body = bodyRef.current?.getBoundingClientRect();
    const box = pages.getBoundingClientRect();
    // Stacked, the handle (11px) lies over the canvas too.
    const cover = side ? box.width * share : Math.max(0, (body?.bottom ?? box.bottom) - (box.bottom - box.height * share)) + (split ? 11 : 0);
    setKept(side ? { bottom: 0, left: Math.round(cover) } : { bottom: Math.round(cover), left: 0 });
  }, [keep, split]);
  useLayoutEffect(measureKept, [measureKept]);
  const place = useCallback(() => {
    const canvas = canvasRef.current;
    const body = bodyRef.current;
    const lean = rootRef.current?.querySelector(".lean-page");
    if (!canvas || !body) return;
    const card = cardRecord ? body.querySelector<HTMLElement>(`.card[data-record="${CSS.escape(cardRecord)}"]`) : null;
    // No card to show (a declaration of no step, a step not drawn here): no band of blank graph.
    // The split keeps its graph: the line above it says what is not drawn.
    rootRef.current?.classList.toggle("map-pane--fold", expanded && !card && !slot && !split);
    // Under the whole pane there is no band to lift it into; the split frames with its camera instead.
    if (split || !card || !lean || !expanded || shareOf(isSide()) >= WHOLE_PANE) {
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
      // The head gives way while the Lean is open, so the band is all graph; the split keeps its head.
      const top = split ? b.top : body.closest(".map-pane__pages")!.getBoundingClientRect().top;
      const bottom = l.top - 11;
      canvas.style.transform = `translate(${Math.round((b.left + b.right) / 2 - (c.left + c.right) / 2)}px, ${Math.round((top + bottom) / 2 - (c.top + c.bottom) / 2)}px)`;
    }
  }, [cardRecord, expanded, slot, split]);

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
    if (split) {
      // The split frames with its camera (the subject fit below), never by moving the canvas.
      setFrom(null);
      if (canvasRef.current) canvasRef.current.style.transform = "";
      return;
    }
    const card = cardRecord ? (bodyRef.current?.querySelector<HTMLElement>(`.card[data-record="${CSS.escape(cardRecord)}"]`) ?? null) : null;
    setFrom(card);
    if (card && (split || !inViewRef.current([cardRecord!]))) {
      // Off the view: frame it first, and only then lift it clear of the Lean.
      framedFrom.current ??= treeRef.current?.getScene() ?? null;
      treeRef.current?.focusIds([cardRecord!]);
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
  }, [expanded, cardRecord, applyShare, place, split]);

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
    let value = rest ? 0 : shareOf(side);
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
      if (split) saveSplitShare((splitShare.current = value));
      else saveDockShare(value, side);
      if (rest) onMode("lean");
      else {
        applyShare(value);
        measureKept();
        place();
        window.setTimeout(fitSubject, 60);
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
    const next = clampDock(shareOf(side) + step);
    if (split) saveSplitShare((splitShare.current = next));
    else saveDockShare(next, side);
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
    // The handle lies over the canvas's last rows: a card under it is not in view.
    const bottom = canvas.bottom - kept.bottom - 14;
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
    wasOpen.current = expanded || (keep && shareOf(isSide()) >= WHOLE_PANE);
    // The frame itself is the subject fit's (below), on each change of subject.
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

  // ---- Fitting the subject ------------------------------------------------------------
  //
  // Whenever what the graph is about changes (a phrase or card opened, a statement pointed
  // at, the passage being read), the graph frames it whole in what is visible of it: the
  // selected card with what it uses and what uses it, or the passage's cards. It zooms out as
  // far as the cards stay readable; where even that cannot hold it all, it frames the selected
  // card with its nearest neighbours. A pan or zoom by hand holds until the subject changes,
  // and the divider or a new window size frames the subject again.
  const around = useCallback(
    (id: string, limit = Infinity) => {
      const drawn = reachOf(goal);
      const ids = [id];
      for (const e of graph.out.get(id) ?? []) if (drawn.has(e.to) && ids.length <= limit) ids.push(e.to);
      for (const e of graph.in.get(id) ?? []) if (drawn.has(e.from) && ids.length <= limit) ids.push(e.from);
      return [...new Set(ids)];
    },
    [graph, reachOf, goal],
  );
  const subject = useMemo((): { key: string; ids: string[]; core: string; nearest: string[] } | null => {
    if (neighbours && target) {
      const ids = [...neighbours.graph.nodes.keys()];
      return { key: `lean:${target.name}`, ids, core: target.name, nearest: [target.name, ...(neighbours.graph.out.get(target.name) ?? []).slice(0, 2).map((e) => e.to)] };
    }
    if (split && pin) return cardRecord ? { key: `split:${cardRecord}`, ids: around(cardRecord), core: cardRecord, nearest: around(cardRecord, 2) } : null;
    if (pin && !expanded && reachOf(goal).has(pin.record)) return { key: `pin:${pin.record}`, ids: around(pin.record), core: pin.record, nearest: around(pin.record, 2) };
    if (expanded && !split) return null;
    return drawable.length ? { key: `read:${drawable.join("|")}`, ids: drawable, core: drawable[0], nearest: [drawable[0]] } : null;
  }, [neighbours, target, split, cardRecord, around, pin, expanded, reachOf, goal, drawable]);
  const subjectRef = useRef(subject);
  subjectRef.current = subject;
  const reducedRef = useRef(reduced);
  reducedRef.current = reduced;
  /** The selected card and the two cards drawn nearest it among its neighbours, else the given ones. */
  const nearestDrawn = (core: string, given: readonly string[]): readonly string[] => {
    const body = bodyRef.current;
    const centre = (id: string) => {
      const card = body?.querySelector<HTMLElement>(`.card[data-record="${CSS.escape(id)}"]`);
      const r = card?.getBoundingClientRect();
      return r ? { x: (r.left + r.right) / 2, y: (r.top + r.bottom) / 2 } : null;
    };
    const at = centre(core);
    const all = subjectRef.current?.ids ?? given;
    if (!at) return given;
    const near = all
      .filter((id) => id !== core)
      .map((id) => ({ id, c: centre(id) }))
      .filter((row): row is { id: string; c: { x: number; y: number } } => !!row.c)
      .sort((a, b) => Math.hypot(a.c.x - at.x, a.c.y - at.y) - Math.hypot(b.c.x - at.x, b.c.y - at.y))
      .slice(0, 2)
      .map((row) => row.id);
    return [core, ...near];
  };
  const fitSubject = useCallback(() => {
    const now = subjectRef.current;
    const tree = treeRef.current;
    // What is framed, for checks: the cards that must stand inside the visible graph.
    const mark = (ids: readonly string[]) => rootRef.current?.setAttribute("data-framed", ids.join(" "));
    if (!now) return mark([]);
    const ids = now.ids;
    mark(ids);
    // A declaration's Lean neighbours lay themselves out to fit; only the map has a camera.
    if (!tree || now.key.startsWith("lean:")) return;
    const animate = !reducedRef.current;
    tree.focusIds(ids);
    window.setTimeout(() => {
      if (subjectRef.current?.key !== now.key) return;
      treeRef.current?.fitNodes(ids, animate, 250);
      // At the readable floor the whole set may still not fit: then the selected card and its nearest.
      // Checked once the glide has ended, and again once a tree that was still drawing has drawn.
      // Then, if those still cannot fit at a readable size, the selected card alone, centred.
      let framed: readonly string[] = ids;
      const fallBack = () => {
        if (subjectRef.current?.key !== now.key || inViewRef.current(framed)) return;
        framed = framed === ids ? nearestDrawn(now.core, now.nearest) : [now.core];
        mark(framed);
        treeRef.current?.fitNodes(framed, animate, 250);
      };
      [320, 700, 1100, 1500].forEach((ms) => window.setTimeout(fallBack, ms));
    }, 60);
  }, []);
  useEffect(() => {
    if (!subject) return void fitSubject();
    if (fadeTo) return;
    // A new subject ends a pause made by hand.
    followingRef.current = true;
    setFollowing(true);
    setPaused(false);
    fitSubject();
    // Only a new subject, a new main result, or a new room for the graph frames again.
  }, [subject?.key, goal, fadeTo, kept.bottom, kept.left, fitSubject]);
  useEffect(() => {
    let timer = 0;
    const onResize = () => {
      window.clearTimeout(timer);
      timer = window.setTimeout(fitSubject, 150);
    };
    window.addEventListener("resize", onResize);
    return () => {
      window.clearTimeout(timer);
      window.removeEventListener("resize", onResize);
    };
  }, [fitSubject]);

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
        tileHeight={PANE_TILE_H}
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
    <section ref={rootRef} className={`map-pane${leanShown ? " map-pane--open" : ""}${split ? " map-pane--split" : ""}`} aria-label="The proof beside the text" inert={inert ? true : undefined}>
      <div className="map-pane__bar">
        <ModeToggle mode={mode} onMode={onMode} />
        <span className="map-pane__goal" title={title}>
          {title}
        </span>
        {paused && !following && (
          <button type="button" className="map-pane__follow map-pane__follow--resume" onClick={toggleFollowing}>
            Move the graph with the text again
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
            {/* What the reader is on, named at the head of the graph and changing as the paper scrolls. */}
            <div className="map-pane__now" data-via={line.via} data-named={line.name ? "" : undefined}>
              <div className="map-pane__top">
                <span className="map-pane__via">{line.lead}</span>
                {progress && <span className="map-pane__progress">{progress}</span>}
                {passed.total > 0 && (
                  <span className="map-pane__meter" aria-hidden="true">
                    <i style={{ inlineSize: `${(100 * passed.seen) / passed.total}%` }} />
                  </span>
                )}
              </div>
              <p className="map-pane__line" data-via={line.via} role="status">
                {line.name && (
                  <>
                    <strong className="map-pane__name">{line.name}</strong>
                    <span className="visually-hidden">. </span>
                  </>
                )}
                <span className="map-pane__rest">{line.rest}</span>
              </p>
              {split && !ownDrawn && (neighbours || showArgument) ? (
                <button type="button" className="map-pane__keep" onClick={() => setShowArgument(!showArgument)}>
                  {showArgument ? "Show its Lean neighbours" : "Show the argument map"}
                </button>
              ) : pin && (!expanded || split) ? (
                <button type="button" className="map-pane__keep" onClick={onRelease}>
                  Close this statement
                </button>
              ) : (
                anchor &&
                onPassage && (
                  <button type="button" className="map-pane__keep" onClick={(event) => onPassage(anchor, event.currentTarget)}>
                    This passage
                  </button>
                )
              )}
            </div>
          </header>
          <div className="map-pane__body" ref={bodyRef}>
            {neighbours && target ? (
              <LeanNeighbourView hood={neighbours} name={target.name} />
            ) : (
              <div ref={canvasRef} className={`map-pane__canvas${fadeTo ? " is-fading" : ""}`}>
                {tree}
              </div>
            )}
          </div>
          <div className="map-pane__foot">
            <span className="map-pane__legend">
              <i className="map-pane__key" aria-hidden="true" />
              Amber: the passage on screen. Darker: already read. Faintest: not in the {PAPER_NAMES[stage].short.toLowerCase()}.
            </span>
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
            aria-valuenow={leanShown ? Math.round((split ? splitShare.current : readDockShare()) * 100) : 0}
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
              onFollowText={split ? undefined : onFollowText}
              noClose={split}
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

  /** What the reader is on or pointing at, in plain words: a label, the step's name and one line about it. */
  function lineFor(): { via: string; lead?: string; name?: string; rest: string } {
    const named = (id: string) => shortTitle(id, graph.nodes.get(id)?.label ?? id);
    /** The step's name and "Has Lean: click to open it.", or the note or the plain fact where there is none to open. */
    const says = (id: string, t: number | null, invite: string): { name?: string; rest: string } => {
      const has = (words: string) => (invite ? `${words}: ${invite}.` : `${words}.`);
      if (t === null) return { name: named(id), rest: recordLine(id)?.lean ? has("Has Lean") : "No Lean linked." };
      const truth = leanTruth(ties, t, alignment);
      // A phrase is named by its declaration, and says its topic.
      if (isPhraseLayer(ties)) {
        const topic = topicOf(ties, t);
        return { name: phraseTitle(ties, t), rest: `${topic ? `Topic: ${topic.name}. ` : ""}${truth.lean ? has("Has Lean") : "No Lean linked."}` };
      }
      if (truth.lean) return { name: named(id), rest: has(truth.words) };
      return truth.note ? { rest: truth.note } : { name: named(id), rest: "No Lean linked." };
    };
    // What is not drawn is said here, so that no note ever covers a card.
    const drawn = (id: string) => (reachOf(goal).has(id) ? "" : " Not in the argument drawn here.");
    const about = (via: string, lead: string, id: string, t: number | null, invite: string) => {
      const said = says(id, t, invite);
      return { via, lead, name: said.name, rest: `${said.rest}${drawn(id)}` };
    };
    // The split's head names the phrase's step on the map; the card below names its Lean.
    if (pin && split && neighbours) {
      return { via: "pin", lead: "Lean neighbours", name: neighbours.graph.nodes.get(target!.name)?.label, rest: "This declaration and its Lean neighbours; it is not a step in the argument drawn here." };
    }
    if (pin && split) {
      const topic = pin.tie !== null ? topicOf(ties, pin.tie) : null;
      if (ownDrawn) return { via: "pin", lead: "Step on the map", name: named(pin.record), rest: topic ? `Topic: ${topic.name}.` : "" };
      return { via: "pin", lead: "Step on the map", rest: `Its Lean is not in the argument drawn here.${splitStep ? ` Nearest step: ${named(splitStep)}.` : ""}` };
    }
    if (pin && !expanded) return about("pin", "Open", pin.record, pin.tie, "");
    if (pointed) return about("point", "Pointing at", pointed.record, pointed.tie, "click to open it");
    if (caption) {
      const topics = passageTopics(ties, caption).filter((id) => graph.nodes.has(id));
      if (topics.length) return { via: "point", rest: `No exact tie in this paragraph. Steps in its passage: ${topics.slice(0, 3).map(named).join(", ")}${topics.length > 3 ? ", and more" : ""}.` };
    }
    if (followRecord) return about("follow", "Reading", followRecord, follow.tie, "click the statement or its card");
    // Past the last passage (the references, say) the nearest passage is not what is on the page.
    const inPassage = !!anchor && passagePart?.(partAt) === anchor;
    const topics = inPassage ? passageTopics(ties, anchor).filter((id) => graph.nodes.has(id)) : [];
    if (topics.length) return { via: "follow", rest: `No exact statement here. Steps in this passage: ${topics.slice(0, 3).map(named).join(", ")}${topics.length > 3 ? ", and more" : ""}.` };
    return { via: "follow", rest: "Nothing in this stretch of the paper is tied to the Lean." };
  }
});

// The right page. It has two views, Graph and Lean, each filling the pane, and they share one
// subject: the declaration of a clicked phrase, a clicked card, a clicked paragraph, or else
// the paragraph under the reading line. A click changes the subject and never the view; only
// the view buttons, and a control that names the other view ("Open its Lean"), change it.
//
// Graph is the focus graph (FocusGraph, specified in docs/graph-pane.md): the subject in the
// middle, everything that uses it on the left and everything it uses on the right, grouped by topic, with
// the dock under it showing one card in detail. The whole proof map stays one button away,
// in the same place. Lean is the Lean of the subject, the whole height of the pane. Under
// 1280px the same page opens as a sheet; under 600px of width the graph folds to one line.

import { memo, useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type MutableRefObject, type ReactNode } from "react";
import type { Alignment } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { PAPER_NAMES } from "../../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "../../map/ArgumentTree";
import { FocusGraph, type FGCard } from "../../map/FocusGraph";
import { mainGoal, startingGoals } from "../../map/TheoremPlate";
import { useKeptCamera } from "../../map/scene";
import { chooseGoal, reach, scopedGraph } from "../../map/treeModel";
import { recordMark } from "../../map/leanMarks";
import { fetchModule, moduleIfLoaded, useLeanShell } from "../../lean/data";
import type { LeanWalk } from "../../lean/walk";
import { passageTopics, phraseTitle, statementFor, type TieModel } from "../ties";
import { focusOn, makeFocus, modulesFor, paperPlaces, passageStart, startOf, type Subject } from "./focusModel";
import { passageOf, passageRecords, type Structures } from "./model";
import { LeanDock, ParagraphLinks, plainName, recordOfDecl, type LeanOpen } from "./RecordDock";
import { SubjectBand, type SubjectState } from "./SubjectBand";
import { GuidePanel, StartHere } from "./Guides";
import { useAids } from "../aids";
import site from "@instance/site";
import { clampDock, DOCK_MAX, DOCK_MIN, readDockShare, saveDockShare } from "./panePrefs";
import { ModeToggle, type PaneMode } from "./ModeToggle";
import { POINT_DWELL, rightPreview, type Pin, type ReaderSignals } from "./rightPage";
import { useSignal, useSlowSignal } from "./signal";
import { dockDecl, noteHtml } from "./PhraseCard";
import "../../map/focus-graph.css";
import "./map-pane.css";

/** Under this width the graph folds to one line, and the dock keeps the rest. */
const FOLD_WIDTH = 600;
/** Narrow tiles, so that the whole argument fits the pane when it is opened there. */
const PANE_TILE_W = 140;
const PANE_TILE_H = 62;

/** Lights these records on the graph from outside it, without moving anything. */
export type PaneHover = (ids: ReadonlySet<string> | null) => void;

/** A paragraph the reader clicked: the records tied to it, or its passage's. */
export interface HeldParagraph {
  anchor: string | null;
  records: string[];
  /** Where no step is tied to it: the first declaration its phrases are tied to. */
  decl?: string;
  /** Every link in the paragraph, in the order of the text. */
  ties?: number[];
  /** The paragraph on the page. */
  block?: HTMLElement;
}

interface Props {
  stage: Stage;
  structures: Structures;
  /** What changes as the reader reads; the page re-renders here, never above. */
  signals: ReaderSignals;
  ties: TieModel;
  /** What the address has pinned: a clicked phrase or card. */
  pin: Pin | null;
  /** A declaration the address names: a card clicked, or a name walked to in the Lean. */
  decl?: string | null;
  declModule?: string;
  /** A paragraph the reader clicked. */
  held?: HeldParagraph | null;
  alignment?: Alignment | null;
  /** Filled by the pane: the paper's statements light cards through it. */
  hoverRef?: MutableRefObject<PaneHover | null>;
  /** Fills the pane while it is open: the passage inspector, or the sections. */
  leanSlot?: ReactNode;
  inert?: boolean;
  /** The page fills a sheet, which has its own close control. */
  inModal?: boolean;
  onHide(): void;
  /** A record was chosen (a card, a link in the route): it becomes the subject. */
  onRecord?(id: string): void;
  /** A declaration was chosen: it becomes the subject. */
  onDecl?(name: string, module?: string): void;
  /** "Resume here": let go of what was selected and follow the paper from where the reader is. The paper does not move. */
  onRelease(): void;
  /** "Return to selected words": the paper goes back to the selection, which stays. */
  onReturn?(): void;
  /** Where a passage is in the paper, in words: "§5.6", a heading. */
  placeOf?(anchor: string | undefined): string;
  /** Linked words were chosen in the pane (a paragraph's list, a showcase card): select them; `land` also brings the paper to them. */
  onOpenTie?(tie: number, land?: boolean): void;
  /** From an opened statement to the Lean following the text. */
  onFollowText?(): void;
  mode: PaneMode;
  onMode(mode: PaneMode): void;
  onPoint(tie: number | null, record?: string): void;
  onName?(walk: LeanWalk): void;
  /** Open the steps and links of the passage being read. */
  onPassage?(anchor: string | null, opener: HTMLElement): void;
  passageHref?(stage: Stage, anchor: string): string;
}

type Why = "decl" | "pin" | "phrase" | "steps" | "paragraph" | "follow";

/** A title as the paper sets it: inline TeX typeset, the rest as text. */
function TitleText({ card }: { card: FGCard }) {
  if (!card.title.includes("$")) return <>{card.title}</>;
  const html = noteHtml(card.title.replace(/\$`([^`]*)`\$/g, (_, tex: string) => `$${tex}$`)).html;
  return <span dangerouslySetInnerHTML={{ __html: html }} />;
}
const renderTitle = (card: FGCard) => <TitleText card={card} />;

export const MapPane = memo(function MapPane({ stage, structures, signals, ties, pin, decl = null, declModule, held = null, alignment = null, hoverRef, leanSlot, inert, inModal, onHide, onRecord, onDecl, onRelease, onReturn, placeOf, onOpenTie, mode, onMode, onPoint, onName, onPassage, passageHref }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const rootRef = useRef<HTMLElement>(null);
  const viewRef = useRef<HTMLDivElement>(null);

  // ---- What the reader is on ---------------------------------------------------------

  const follow = useSlowSignal(signals.follow);
  const pointed = useSignal(signals.point);
  const preview = useSignal(rightPreview);
  const anchor = follow.anchor;
  const passage = useMemo(() => passageRecords(anchor ? passageOf(structures[stage], anchor) : undefined), [anchor, structures, stage]);
  const followRecord = follow.tie !== null ? ties.index.ties[follow.tie].record : null;
  const pinTie = pin && pin.tie !== null ? ties.index.ties[pin.tie] : null;

  // ---- The paper's argument and its main result ----------------------------------------

  const home = useMemo(() => mainGoal(edition), [edition]);
  const selected = useMemo(() => edition.overview?.papers.find((p) => p.stage === stage)?.paper_scope.selected_goal_ids ?? [], [edition, stage]);
  const reaches = useMemo(() => new Map<string, Set<string>>(), [graph]);
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
  const candidates = useMemo(() => startingGoals(edition).map((g) => ({ id: g.id, title: g.title, own: g.stages.includes(stage) })), [edition, stage]);

  // ---- The data the drawing reads ------------------------------------------------------

  const shellState = useLeanShell();
  const shell = shellState.status === "ready" ? shellState.shell : null;
  const places = useMemo(
    () => paperPlaces(ties, (structures[stage]?.paper.sections ?? []).map((s) => ({ start: s.heading_span.start_byte, title: s.title }))),
    [ties, structures, stage],
  );
  const readAt = follow.tie !== null ? startOf(ties.index.ties[follow.tie].at) : passageStart(ties, anchor);
  const [loaded, setLoaded] = useState(0);
  const input = useMemo(
    () => ({ graph, stage, home, selected, onMap: (id: string) => reachOf(home).has(id), alignment, shell, module: (name: string) => moduleIfLoaded(name), places, readAt }),
    // `loaded` changes when a module arrives: moduleIfLoaded then answers.
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [graph, stage, home, selected, reachOf, alignment, shell, places, readAt, loaded],
  );
  const tools = useMemo(() => makeFocus(input), [input]);

  // ---- The subject -----------------------------------------------------------------------

  // The declaration a phrase's card shows (its selected tab): the graph follows it.
  const shown = useSignal(dockDecl);
  const [showSteps, setShowSteps] = useState(false);
  useEffect(() => setShowSteps(false), [pin?.record, pin?.tie]);
  /** The steps around a phrase that no step holds: its passage's, else the nearest phrase's that has one. */
  const stepsNear = useCallback(
    (t: number): string[] => {
      const tie = ties.index.ties[t];
      const own = passageTopics(ties, tie.anchor).filter((id) => graph.nodes.get(id)?.kind !== "declaration" && graph.nodes.has(id));
      if (own.length) return own;
      const at = ties.order.indexOf(t);
      for (let d = 1; d < ties.order.length; d++) {
        for (const k of [at - d, at + d]) {
          const id = ties.index.ties[ties.order[k]]?.record;
          if (id && graph.nodes.has(id) && graph.nodes.get(id)!.kind !== "declaration") return [id];
        }
      }
      return [];
    },
    [ties, graph],
  );
  const onGraph = useCallback((id: string) => graph.nodes.has(id), [graph]);
  const asSubject = useCallback((id: string): Subject => (graph.nodes.get(id)?.kind === "declaration" ? { kind: "decl", name: tools.declOf(id)! } : { kind: "records", ids: [id] }), [graph, tools]);

  const fresh = useMemo((): { subject: Subject; why: Why } | null => {
    if (decl) return { subject: { kind: "decl", name: decl }, why: "decl" };
    if (pin) {
      if (onGraph(pin.record)) return { subject: asSubject(pin.record), why: "pin" };
      if (pin.tie !== null && pinTie?.rows?.length) {
        const steps = showSteps ? stepsNear(pin.tie) : [];
        if (steps.length) return { subject: { kind: "records", ids: steps }, why: "steps" };
        return { subject: { kind: "decl", name: shown?.name ?? pinTie.rows[0].name }, why: "phrase" };
      }
    }
    if (held) {
      const ids = held.records.filter(onGraph);
      if (ids.length) return { subject: { kind: "records", ids }, why: "paragraph" };
      return held.decl ? { subject: { kind: "decl", name: held.decl }, why: "paragraph" } : null;
    }
    // Following: the statement under the reading line, its step or else its declaration.
    if (followRecord && onGraph(followRecord)) return { subject: asSubject(followRecord), why: "follow" };
    const first = follow.tie !== null ? ties.index.ties[follow.tie].rows?.[0]?.name : undefined;
    if (first) return { subject: { kind: "decl", name: first }, why: "follow" };
    return null;
  }, [decl, pin, pinTie, onGraph, asSubject, showSteps, stepsNear, shown, held, followRecord, follow.tie, ties]);
  // A paragraph with nothing tied to it keeps the last subject, and the line over the drawing says whose it is.
  // Before anything has been tied, the statement nearest the reading position, or else the main result,
  // so the graph is never blank and never draws a whole passage at once.
  const kept = useRef<{ subject: Subject; why: Why; anchor: string | null } | null>(null);
  if (fresh) kept.current = { ...fresh, anchor: held?.anchor ?? anchor };
  const opening = useMemo((): { subject: Subject; why: Why } => {
    let best: string | null = null;
    let gap = Infinity;
    for (const t of ties.order) {
      const tie = ties.index.ties[t];
      if (!tie.record || !onGraph(tie.record)) continue;
      const d = Math.abs((startOf(tie.at) ?? 0) - (readAt ?? 0));
      if (d < gap) [best, gap] = [tie.record, d];
    }
    return { subject: best ? asSubject(best) : { kind: "records", ids: [home] }, why: "follow" };
  }, [ties, onGraph, asSubject, readAt, home]);
  const current = fresh ?? kept.current ?? opening;
  const stale = !fresh && !!kept.current;
  const subjectKey = current ? (current.subject.kind === "decl" ? `d:${current.subject.name}` : `r:${current.subject.ids.join("|")}`) : "";

  // The Lean modules the drawing reads, fetched once each.
  const needed = useMemo(() => (current ? modulesFor(current.subject, tools) : []), [current, tools]);
  useEffect(() => {
    let live = true;
    for (const name of needed) {
      if (moduleIfLoaded(name)) continue;
      fetchModule(name).then(
        () => live && setLoaded((n) => n + 1),
        () => undefined,
      );
    }
    return () => {
      live = false;
    };
  }, [needed]);

  const focus = useMemo(() => (current ? focusOn(current.subject, input, tools) : null), [current, input, tools]);
  const cardOf = useCallback((id: string) => focus?.cards.get(id), [focus]);

  // ---- Pointing: the paper lights cards, cards preview in the dock ----------------------

  const [hovered, setHovered] = useState<ReadonlySet<string> | null>(null);
  useEffect(() => {
    if (!hoverRef) return;
    hoverRef.current = setHovered;
    return () => {
      hoverRef.current = null;
    };
  }, [hoverRef]);
  const lit = useMemo(() => {
    const ids = new Set<string>();
    if (pointed) {
      if (onGraph(pointed.record)) ids.add(pointed.record);
      else if (pointed.tie !== null) for (const row of ties.index.ties[pointed.tie].rows ?? []) ids.add(tools.declCard(row.name));
    }
    for (const id of hovered ?? []) if (onGraph(id)) ids.add(id);
    return [...ids];
  }, [pointed, hovered, onGraph, ties, tools]);

  const [previewCard, setPreviewCard] = useState<string | null>(null);
  const previewTimer = useRef(0);
  const onCardHover = useCallback((id: string | null) => {
    window.clearTimeout(previewTimer.current);
    if (!id) return setPreviewCard(null);
    previewTimer.current = window.setTimeout(() => setPreviewCard(id), POINT_DWELL);
  }, []);
  useEffect(() => () => window.clearTimeout(previewTimer.current), []);
  useEffect(() => setPreviewCard(null), [subjectKey, mode]);

  /** A card or a link in the route was chosen: it becomes the subject. */
  const onSubject = useCallback(
    (id: string) => {
      setPreviewCard(null);
      const name = tools.declOf(id);
      if (name) onDecl?.(name, tools.rowOf(name)?.module);
      else onRecord?.(id);
    },
    [tools, onDecl, onRecord],
  );

  // ---- What the dock and the Lean view show ----------------------------------------------

  const openRecord = pin?.record ?? (decl ? recordOfDecl(alignment, decl) : null);
  const heldFirst = held?.records.find(onGraph) ?? null;
  const following = (): LeanOpen => {
    if (followRecord) return { via: "follow", record: followRecord, tie: follow.tie, decl: null };
    const topics = passageTopics(ties, anchor);
    return { via: "follow", record: null, tie: null, decl: null, topics: topics.length ? topics : passage };
  };
  const dockOpen = useMemo<LeanOpen>(() => {
    if (previewCard) {
      const name = tools.declOf(previewCard);
      return name ? { via: "point", record: null, tie: null, decl: name, declModule: tools.rowOf(name)?.module } : { via: "point", record: previewCard, tie: null, decl: null };
    }
    if (decl) return { via: "pin", record: null, tie: null, decl, declModule };
    if (pin) return { via: "pin", record: pin.record, tie: pin.tie, decl: null };
    if (held) {
      if (heldFirst) return { via: "pin", record: heldFirst, tie: statementFor(ties, heldFirst), decl: null };
      if (held.decl) return { via: "pin", record: null, tie: null, decl: held.decl, declModule: tools.rowOf(held.decl)?.module };
      return { via: "pin", record: null, tie: null, decl: null, topics: passageTopics(ties, held.anchor) };
    }
    return following();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [previewCard, tools, decl, declModule, pin, held, heldFirst, ties, followRecord, follow.tie, anchor, passage]);
  const leanOpen = useMemo<LeanOpen>(() => {
    if (pin || decl) return { via: "pin", record: openRecord, tie: decl ? null : (pin?.tie ?? null), decl, declModule };
    if (heldFirst) return { via: "pin", record: heldFirst, tie: statementFor(ties, heldFirst), decl: null };
    if (held?.decl) return { via: "pin", record: null, tie: null, decl: held.decl, declModule: tools.rowOf(held.decl)?.module };
    if (held) return { via: "pin", record: null, tie: null, decl: null, topics: passageTopics(ties, held.anchor) };
    if (pointed) return { via: "point", record: pointed.record, tie: pointed.tie, decl: null };
    return following();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [pin, decl, openRecord, declModule, held, heldFirst, tools, ties, pointed, followRecord, follow.tie, anchor, passage]);

  // ---- The whole proof map, one button away ------------------------------------------------

  const [whole, setWhole] = useState(false);
  const treeRef = useRef<MapViewHandle>(null);
  useKeptCamera(treeRef, useCallback((id: string) => graph.nodes.has(id), [graph]));
  const subjectRecords = useMemo(() => (current?.subject.kind === "records" ? [...current.subject.ids] : []), [current]);
  const goal = useMemo(
    () => (!subjectRecords.length || subjectRecords.some((id) => reachOf(home).has(id)) ? home : (chooseGoal(subjectRecords, candidates, reachOf, home) ?? home)),
    [subjectRecords, reachOf, home, candidates],
  );
  const coverage = useMemo(() => {
    const ids = new Set<string>();
    for (const p of structures[stage]?.paper.passages ?? []) for (const id of [...p.claim_ids, ...p.assumption_ids]) ids.add(id);
    return ids;
  }, [structures, stage]);
  const litIds = useMemo(() => (subjectRecords.length ? new Set(subjectRecords) : null), [subjectRecords]);
  const previewIds = useMemo(() => (lit.length ? new Set(lit) : null), [lit]);
  const insets: Insets = useMemo(() => ({ top: 12, left: 16, bottom: 24, right: 16 }), []);
  useEffect(() => {
    if (!whole) return;
    const open = window.setTimeout(() => treeRef.current?.expandAll(), 0);
    const frame = window.setTimeout(() => {
      const ids = subjectRecords.filter((id) => reachOf(goal).has(id));
      if (ids.length) treeRef.current?.focusIds(ids);
      else treeRef.current?.fitAll(false);
    }, 80);
    return () => {
      window.clearTimeout(open);
      window.clearTimeout(frame);
    };
    // Framed when it opens; afterwards the reader moves it.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [whole, goal]);
  const onTreeHover = useCallback((id: string | null) => onPoint(id ? statementFor(ties, id) : null, id ?? undefined), [onPoint, ties]);
  const onTrace = useCallback((id: string) => navigate({ view: "map", goal, node: id, trace: "rests" }), [goal]);
  const onTreeSelect = useCallback((id: string | null) => id && onSubject(id), [onSubject]);

  // ---- The dock's height, and the fold on a narrow pane ---------------------------------

  const [narrow, setNarrow] = useState(false);
  const [unfolded, setUnfolded] = useState(false);
  useLayoutEffect(() => {
    const el = rootRef.current;
    if (!el) return;
    const read = () => setNarrow(el.clientWidth > 0 && el.clientWidth < FOLD_WIDTH);
    read();
    const ro = new ResizeObserver(read);
    ro.observe(el);
    return () => ro.disconnect();
  }, []);
  const [share, setShare] = useState(readDockShare);
  const onHandleDown = (event: React.PointerEvent<HTMLDivElement>) => {
    const view = viewRef.current;
    if (event.button !== 0 || !view) return;
    event.preventDefault();
    const handle = event.currentTarget;
    handle.setPointerCapture(event.pointerId);
    const box = view.getBoundingClientRect();
    let value = share;
    view.classList.add("is-dragging");
    const move = (e: PointerEvent) => {
      value = clampDock((box.bottom - e.clientY) / box.height);
      view.style.setProperty("--dock-share", String(value));
    };
    const end = () => {
      handle.removeEventListener("pointermove", move);
      handle.removeEventListener("pointerup", end);
      handle.removeEventListener("pointercancel", end);
      view.classList.remove("is-dragging");
      saveDockShare(value);
      setShare(value);
    };
    handle.addEventListener("pointermove", move);
    handle.addEventListener("pointerup", end);
    handle.addEventListener("pointercancel", end);
  };
  const onHandleKey = (event: React.KeyboardEvent) => {
    const step = event.key === "ArrowUp" ? 0.05 : event.key === "ArrowDown" ? -0.05 : 0;
    if (!step) return;
    event.preventDefault();
    const next = clampDock(share + step);
    saveDockShare(next);
    setShare(next);
  };
  useLayoutEffect(() => {
    viewRef.current?.style.setProperty("--dock-share", String(share));
  });

  // ---- The line over the drawing ----------------------------------------------------------

  const subjectTitle = focus?.subjects.length === 1 ? (focus.cards.get(focus.subjects[0])?.title ?? "") : "";
  // Letting go is in the subject band ("Resume here"); the line over the drawing only says what is drawn.
  const again = null;
  const label = ((): ReactNode => {
    if (!current) return null;
    const why = current.why;
    if (stale) {
      const shown = subjectTitle ? <>“{subjectTitle}”</> : "the steps";
      return <>No Lean is linked to this paragraph. The graph keeps {shown} from the last paragraph that had any.</>;
    }
    const offMap = current.subject.kind === "decl" && !reachOf(home).has(focus?.subjects[0] ?? "");
    if (why === "phrase")
      return (
        <>
          The Lean around the declaration this phrase is tied to.
          <button type="button" onClick={() => setShowSteps(true)}>
            Show the paragraph’s steps
          </button>
          {again}
        </>
      );
    if (why === "steps")
      return (
        <>
          The steps of the paragraph around this phrase.
          <button type="button" onClick={() => setShowSteps(false)}>
            Show the Lean around its declaration
          </button>
          {again}
        </>
      );
    if (why === "decl") return <>{offMap ? "The Lean around the declaration you chose." : "The declaration you chose."}{again}</>;
    if (why === "pin") return <>The step you chose.{again}</>;
    if (why === "paragraph")
      return (
        <>
          The steps of the paragraph you chose.
          {again}
        </>
      );
    if (current.subject.kind === "decl") return <>The Lean around the declaration this paragraph is tied to.</>;
    return null;
  })();

  // ---- Layout ----------------------------------------------------------------------------

  const counts = useMemo(() => {
    if (!focus) return { uses: 0, usedBy: 0 };
    const here = new Set(focus.subjects);
    const uses = new Set(focus.edges.filter((e) => here.has(e.from) && !here.has(e.to)).map((e) => e.to));
    const usedBy = new Set(focus.edges.filter((e) => here.has(e.to) && !here.has(e.from)).map((e) => e.from));
    return { uses: uses.size, usedBy: usedBy.size };
  }, [focus]);
  const folded = narrow && !unfolded && !whole;

  // ---- The subject band, and the two guides that can stand in the pane ----------------------

  const aids = useAids();
  const guideStage = site.library && stage === site.library.main ? Object.values(site.library.pages ?? {})[0] : undefined;
  const [aside, setAside] = useState<"start" | "guide" | null>(null);
  // A guide is read with nothing else in mind: a new selection takes its place.
  useEffect(() => setAside(null), [pin?.record, pin?.tie, decl, held]);
  const holding = !!pin || !!decl || !!held;
  const bandState: SubjectState = decl
    ? "declaration"
    : pin
      ? pin.tie !== null
        ? "words"
        : "step"
      : held
        ? "paragraph"
        : preview || (mode === "lean" && pointed)
          ? "preview"
          : "following";
  const bandPlace = pinTie ? (placeOf?.(pinTie.anchor ?? undefined) ?? "") : held ? (placeOf?.(held.anchor ?? undefined) ?? "") : "";
  const bandTitle = pin?.tie != null ? phraseTitle(ties, pin.tie) : decl ? plainName(alignment, decl) : subjectTitle;
  const heldList = held?.ties?.length && !pin && !decl && onOpenTie ? <ParagraphLinks ties={ties} list={held.ties} onOpen={(t) => onOpenTie(t)} onPoint={onPoint} /> : null;
  /** A showcase card names linked words, a numbered result or a declaration: open whichever it is. */
  const openCard = useCallback(
    (card: string) => {
      const at = card.indexOf(":");
      const [kind, id] = [card.slice(0, at), card.slice(at + 1)];
      setAside(null);
      if (kind === "tie") {
        const t = ties.order.find((n) => ties.index.ties[n].phrase === id);
        if (t !== undefined) onOpenTie?.(t, true);
        return;
      }
      // A result opens at the words that state it, where the paper has them; else as a declaration.
      const stated = kind === "result" ? ties.order.find((n) => ties.index.ties[n].role === "statement" && ties.index.ties[n].rows?.some((row) => row.name === id)) : undefined;
      if (stated !== undefined) onOpenTie?.(stated, true);
      else onDecl?.(id, tools.rowOf(id)?.module);
    },
    [ties, onOpenTie, onDecl, tools],
  );
  const cardTitle = useCallback(
    (card: string) => {
      const at = card.indexOf(":");
      const [kind, id] = [card.slice(0, at), card.slice(at + 1)];
      if (kind === "tie") {
        const t = ties.order.find((n) => ties.index.ties[n].phrase === id);
        return t !== undefined ? phraseTitle(ties, t) : id;
      }
      return plainName(alignment, id);
    },
    [ties, alignment],
  );
  const about = site.sectionAids?.[stage]?.[PAPER_NAMES[stage].short];
  // Before the paper's first link (its title and authors) there is nothing to follow: the pane offers where to start.
  const firstLink = ties.order.length ? startOf(ties.index.ties[ties.order[0]].at) : null;
  const atFront = !holding && follow.tie === null && (readAt === null || readAt === undefined || firstLink === null || readAt < firstLink);
  const frontSlot = atFront && aids.showcase.length > 0 ? <StartHere cards={aids.showcase} about={about} titleOf={cardTitle} onOpen={openCard} /> : undefined;
  const asideSlot =
    aside === "start" ? (
      <StartHere cards={aids.showcase} about={about} titleOf={cardTitle} onOpen={openCard} onClose={() => setAside(null)} />
    ) : aside === "guide" && guideStage ? (
      <GuidePanel stage={guideStage} onClose={() => setAside(null)} />
    ) : null;
  const fill = !!leanSlot || !!asideSlot;
  const mapHref = routeHref({ view: "map", goal, node: subjectRecords[0] });

  const drawing = whole ? (
    <div className="map-pane__canvas">
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
        litIds={litIds}
        previewIds={previewIds}
        coverage={coverage}
        onSelect={onTreeSelect}
        onHover={onTreeHover}
        onTrace={onTrace}
      />
    </div>
  ) : folded ? (
    <div className="map-pane__strip" role="group" aria-label="The graph, folded">
      <span className="map-pane__strip-title">{subjectTitle || (focus?.subjects.length ? `${focus.subjects.length} steps` : "Nothing drawn here")}</span>
      <span className="map-pane__strip-counts">
        uses {counts.uses}, used by {counts.usedBy}
      </span>
      <button type="button" onClick={() => setUnfolded(true)}>
        Show the graph
      </button>
    </div>
  ) : focus ? (
    <FocusGraph
      subjects={focus.subjects}
      card={cardOf}
      edges={focus.edges}
      route={focus.route}
      routeNote={focus.routeNote}
      label={label}
      lit={lit}
      held={previewCard}
      onSubject={onSubject}
      onHover={onCardHover}
      renderTitle={renderTitle}
      roles={focus.roles}
      manyLabel={current?.why === "paragraph" ? "Tied to this paragraph" : "In this passage"}
    />
  ) : (
    <p className="map-pane__none">Nothing in this stretch of the paper is tied to a step or to the Lean.</p>
  );

  return (
    <section ref={rootRef} className="map-pane" data-view={fill ? "panel" : mode} aria-label="The proof beside the text" inert={inert ? true : undefined}>
      <div className="map-pane__bar">
        <ModeToggle mode={mode} onMode={onMode} />
        {aids.showcase.length > 0 && (
          <button type="button" className="map-pane__whole map-pane__guide" aria-pressed={aside === "start"} onClick={() => setAside(aside === "start" ? null : "start")}>
            Start here
          </button>
        )}
        {guideStage && (
          <button type="button" className="map-pane__whole map-pane__guide" aria-pressed={aside === "guide"} onClick={() => setAside(aside === "guide" ? null : "guide")}>
            How to read the Lean
          </button>
        )}
        {mode === "graph" && !fill && (
          <button type="button" className="map-pane__whole" aria-pressed={whole} onClick={() => setWhole(!whole)}>
            {whole ? "Around this step" : "Whole proof map"}
          </button>
        )}
        {narrow && unfolded && !whole && mode === "graph" && !fill && (
          <button type="button" className="map-pane__whole" onClick={() => setUnfolded(false)}>
            Fold the graph
          </button>
        )}
        {anchor && onPassage && !fill && (
          <button type="button" className="map-pane__whole" onClick={(event) => onPassage(anchor, event.currentTarget)}>
            This passage
          </button>
        )}
        {mode === "graph" && !fill && <a
          className="map-pane__open"
          href={mapHref}
          onClick={(event) => {
            if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
            event.preventDefault();
            navigate({ view: "map", goal, node: subjectRecords[0] });
          }}
        >
          Open the full map
        </a>}
        {!inModal && (
          <button type="button" className="map-pane__hide" aria-label="Hide the pane" onClick={onHide}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
          </button>
        )}
      </div>
      {!fill && <SubjectBand state={bandState} place={bandPlace} title={bandTitle} onResume={holding ? onRelease : undefined} onReturn={(pin?.tie != null || held?.block) && onReturn ? onReturn : undefined} />}
      {fill ? (
        <div className="map-pane__fill">
          <LeanDock open={leanOpen} ties={ties} stage={stage} alignment={alignment} slot={leanSlot ?? asideSlot} onRelease={onRelease} onPick={(id) => onRecord?.(id)} onPoint={onPoint} onName={onName} passageHref={passageHref ?? ((s, a) => routeHref({ view: "read", stage: s, anchor: a }))} />
        </div>
      ) : mode === "lean" ? (
        <div className="map-pane__lean">
          <LeanDock
            open={leanOpen}
            ties={ties}
            stage={stage}
            alignment={alignment}
            slot={preview ?? heldList}
            emptySlot={frontSlot}
            onOpenGraph={() => onMode("graph")}
            onPick={(id) => onRecord?.(id)}
            onPoint={onPoint}
            onName={onName}
            passageHref={passageHref ?? ((s, a) => routeHref({ view: "read", stage: s, anchor: a }))}
          />
        </div>
      ) : (
        <div ref={viewRef} className={`map-pane__graphview${folded ? " is-folded" : ""}`}>
          <div className="map-pane__drawing">{drawing}</div>
          {!folded && (
            <div
              className="map-pane__handle"
              role="separator"
              aria-orientation="horizontal"
              aria-label="Size the part under the graph"
              aria-valuemin={Math.round(DOCK_MIN * 100)}
              aria-valuemax={Math.round(DOCK_MAX * 100)}
              aria-valuenow={Math.round(share * 100)}
              tabIndex={0}
              onPointerDown={onHandleDown}
              onKeyDown={onHandleKey}
            >
              <span aria-hidden="true" />
            </div>
          )}
          <div className="map-pane__dock">
            <LeanDock
              open={dockOpen}
              ties={ties}
              stage={stage}
              alignment={alignment}
              slot={preview ?? (previewCard ? null : heldList)}
              onOpenLean={() => onMode("lean")}
              onPick={(id) => onRecord?.(id)}
              onPoint={onPoint}
              onName={onName}
              passageHref={passageHref ?? ((s, a) => routeHref({ view: "read", stage: s, anchor: a }))}
            />
          </div>
        </div>
      )}
    </section>
  );
});

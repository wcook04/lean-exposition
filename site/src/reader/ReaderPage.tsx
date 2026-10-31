// The paper reader: one account at its reading measure, with the proof on the page facing
// it. Four verbs run the page (reading-model.md). Follow: the reading line picks the
// statement under it, which takes the highlighter at once, and once it has held the line
// for a moment the right page shows its card and its Lean. Point: a tied statement reacts
// to the pointer or to focus, and after a short dwell the right page previews it. Open: a
// click pins it, as one history entry whose address names the record and the statement.
// Back: the browser's own, to the same pixel.
//
// Scrolling never sets state on this component. It writes attributes (statements.ts) and
// signals (page/signal.ts) that the few small things showing them read. A chosen treatment
// elsewhere still opens as a visit over the paper, which stays where it was.

import { startTransition, Suspense, useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Alignment } from "../api/lean";
import type { PaperStructure, Stage } from "../api/types";
import { describeError, loadPaperStructure, useEdition, useResource } from "../app/data";
import { BackControl } from "../app/BackControl";
import { navigate, routeHref, type Route } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { prefersReducedMotion } from "../app/theme";
import { restoreScroll } from "../app/restore";
import { namePlace, onLeave } from "../app/trail";
import { sectionLabel } from "../map/TheoremPlate";
import type { ArgGraph } from "../model/graph";
import type { PreparedDocument } from "./engine";
import { alignmentResource } from "../compare/useAlignment";
import { code, lazyCode } from "../app/code";
import { loadDocument, useDocument, type LoadedDocument } from "./documents";
import { PaperBody, type BodyHandle, type Links } from "./page/PaperBody";
import { Inspector, type InspectorTarget } from "./page/Inspector";
import { Chooser } from "./page/Chooser";
import { Visit } from "./page/Visit";
import { Modal } from "./page/Modal";
import { OutlineColumn, PdfLink, Sections, SectionsPopover } from "./page/Outline";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import type { PaneHover } from "./page/MapPane";
import { RightSheet } from "./page/RightSheet";
import { FOLLOW_HOLD, POINT_DWELL, type Followed, type Pin, type Pointed, type ReaderSignals } from "./page/rightPage";
import { Signal, useSignal } from "./page/signal";
import { Statements } from "./page/statements";
import { statementFor, statementOf, stepFrom, type TieModel } from "./ties";
import {
  chainOf,
  companionAnchor,
  firstPassageFor,
  outlineOf,
  outlineTieCounts,
  paperTrail,
  passageOf,
  passageRecords,
  partsOfLines,
  passagesBetween,
  recordTally,
  resolveAnchor,
  resolveAt,
  resolveBeside,
  sectionNumber,
  sectionTitleIn,
  selectionSpan,
  statusWords,
  type Destination,
  type OutlineEntry,
  type Structures,
} from "./page/model";
import {
  blockAtLine,
  existingHistoryKey,
  historyKey,
  loadPosition,
  partIdOf,
  partOfPosition,
  patchHistoryState,
  restoreKey,
  savePosition,
  scrollForPosition,
  visitOrigin,
  type ReadingPosition,
  type VisitOrigin,
} from "./page/position";
import "./reader-content.css";
import "./reader-page.css";

// The pane and the map engine arrive after the paper has painted.
const mapPane = code(() => import("./page/MapPane"));
const MapPane = lazyCode(mapPane, (m) => m.MapPane);
// Beside the paper the pane is part of the page, so its code starts with the page's.
if (window.matchMedia?.("(min-width: 1280px)").matches) mapPane.start();

type ReadRoute = Extract<Route, { view: "read" }>;

export function ReaderPage({ route }: { route: ReadRoute }) {
  const loaded = useDocument(route.stage);
  // The other accounts' structures name destinations; the paper never waits for them.
  const others = useResource<Structures>("reader:structures", () =>
    Promise.all(STAGE_ORDER.map((s) => loadPaperStructure(s).then((structure) => [s, structure] as const))).then(
      (pairs) => Object.fromEntries(pairs) as Structures,
    ),
  );
  const own = loaded.status === "ready" && loaded.value.paper.stage === route.stage ? loaded.value.paper.structure : null;
  const othersValue = others.status === "ready" ? others.value : null;
  const structures = useMemo<Structures>(() => ({ ...(othersValue ?? {}), ...(own ? { [route.stage]: own } : {}) }), [othersValue, own, route.stage]);
  const account = PAPER_NAMES[route.stage].short;

  if (loaded.status === "error") {
    const { title, detail } = describeError(loaded.error);
    return (
      <div className="page-message" role="alert">
        <h1>{title}</h1>
        <p>{detail}</p>
      </div>
    );
  }
  if (loaded.status !== "ready" || !own) {
    return (
      <p className="reader-loading" aria-live="polite">
        Loading the {account.toLowerCase()}…
      </p>
    );
  }
  return <Reader key={route.stage} route={route} loaded={loaded.value} structures={structures} />;
}

function useMedia(query: string): boolean {
  const [matches, setMatches] = useState(() => window.matchMedia(query).matches);
  useEffect(() => {
    const media = window.matchMedia(query);
    const update = () => setMatches(media.matches);
    update();
    media.addEventListener("change", update);
    return () => media.removeEventListener("change", update);
  }, [query]);
  return matches;
}

const MAP_PANE_KEY = "lx-reader-map";

function readMapShown(): boolean {
  try {
    return localStorage.getItem(MAP_PANE_KEY) !== "hidden";
  } catch {
    return true;
  }
}

const whenIdle = (run: () => void, timeout: number): (() => void) => {
  if (typeof window.requestIdleCallback === "function") {
    const id = window.requestIdleCallback(run, { timeout });
    return () => window.cancelIdleCallback(id);
  }
  const id = setTimeout(run, 120);
  return () => clearTimeout(id);
};

function linesOf(blocks: Element[]): { el: Element; line: number }[] {
  return blocks.flatMap((el) => {
    const line = Number((el as HTMLElement).dataset.line);
    return line ? [{ el, line }] : [];
  });
}

/** The top-level blocks of a part with their first lines; a list counts item by item. */
function partBlocks(part: HTMLElement | null | undefined): { el: Element; line: number }[] {
  const text = part?.querySelector(":scope > .part__text");
  if (!text) return [];
  const blocks = Array.from(text.children).flatMap((el) => (el.matches("ul, ol") ? Array.from(el.children) : [el]));
  return linesOf(blocks);
}

/** The blocks of a part that a slice's lines touch. `last` is the part's last line. */
function blocksOf(part: HTMLElement | null | undefined, last: number, lines: { start: number; end: number }): Element[] {
  const blocks = partBlocks(part);
  return blocks.filter((b, i) => b.line <= lines.end && (blocks[i + 1]?.line ?? last + 1) > lines.start).map((b) => b.el);
}

/** The reading line, as a share of the height below the strip. */
const READING_LINE = 0.3;
/** How far from the reading line a statement still counts as what is being read. */
const LINE_REACH = 0.32;
/** Further than this share of the window in one hold is flying, not reading. */
const FLYING = 0.5;
/** What the thread reaches on the Lean page: the lit lines where they are drawn, else the step's title. */
const LEAN_TARGET = "[data-lit], .lean-clause, .lean-page__title";
const SCROLL_KEYS = new Set(["ArrowDown", "ArrowUp", "PageDown", "PageUp", " ", "Home", "End"]);

function cssPx(name: string, fallback: number): number {
  const value = parseFloat(getComputedStyle(document.documentElement).getPropertyValue(name));
  return Number.isFinite(value) ? value : fallback;
}

/** The part at a viewport line, by binary search over the parts in order. */
function partAt(body: BodyHandle | null, count: number, line: number): number {
  if (!body) return 0;
  let lo = 0;
  let hi = count - 1;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    const el = body.partElement(mid);
    const bottom = el ? el.getBoundingClientRect().bottom : line + 1;
    if (bottom <= line) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

interface SelectionAction {
  x: number;
  y: number;
  below: boolean;
  start: number;
  end: number;
  passages: number;
}

interface GoOptions {
  replace?: boolean;
  /** The visit origin the new entry carries; undefined carries the current one, null drops it. */
  visit?: VisitOrigin | null;
  /** A history key whose saved position the new entry opens at. */
  restore?: string;
}

function Reader({ route, loaded, structures }: { route: ReadRoute; loaded: LoadedDocument; structures: Structures }) {
  const { graph, snapshot } = useEdition();
  const edition = snapshot.cache_key;
  const { doc, paper, ties } = loaded;
  const stage = route.stage;
  const structure = paper.structure;
  const wide = useMedia("(min-width: 1360px)");
  const mid = useMedia("(min-width: 1120px)");
  // From 1280px the paper moves left and the argument map stands beside it, the
  // reader's remembered choice. Up to 1500px the outline folds to give them the room.
  const paneRoom = useMedia("(min-width: 1280px)");
  const outlineRoom = useMedia("(min-width: 1501px)");
  const phone = useMedia("(max-width: 700px)");
  const [mapShown, setMapShown] = useState(readMapShown);
  const paneOn = paneRoom && mapShown;
  const showMap = useCallback((shown: boolean) => {
    setMapShown(shown);
    try {
      localStorage.setItem(MAP_PANE_KEY, shown ? "shown" : "hidden");
    } catch {
      /* storage unavailable */
    }
  }, []);
  /** Below 1280px, or with the page turned off: the right page as a sheet, opened on demand. */
  const [sheetOpen, setSheetOpen] = useState(false);
  // The first screen is the paper: the map and the alignment arrive in idle time.
  const [paneReady, setPaneReady] = useState(false);
  const [alignment, setAlignment] = useState<Alignment | null>(null);
  useEffect(
    () =>
      whenIdle(() => {
        startTransition(() => setPaneReady(true));
        void alignmentResource().then(setAlignment);
      }, 500),
    [],
  );
  const paneHover = useRef<PaneHover | null>(null);

  // Written by the scroll path and pointer; read by small leaves and by the right page.
  const signals = useRef<ReaderSignals>({
    heading: new Signal<string | null>(null),
    part: new Signal(0),
    follow: new Signal<Followed>({ tie: null, anchor: null, part: 0 }, sameFollow),
    point: new Signal<Pointed | null>(null),
    caption: new Signal<string | null>(null),
  }).current;
  const statements = useMemo(() => new Statements(ties, doc.parts), [ties, doc]);
  useEffect(() => () => statements.dispose(), [statements]);

  const bodyRef = useRef<BodyHandle>(null);
  const paperRef = useRef<HTMLDivElement>(null);
  const stripRef = useRef<HTMLDivElement>(null);
  const keyRef = useRef<string>("");
  const selfAnchor = useRef<string | undefined>(route.anchor);
  /** The `l` this page wrote itself, so the route effect does not land on it. */
  const selfAt = useRef<string | undefined | null>(null);
  const lastAnchor = useRef<string | undefined>(route.anchor);
  const lastAt = useRef<string | undefined>(route.at);
  const lastHref = useRef<string>("");
  const inspectOpener = useRef<HTMLElement | null>(null);

  const outline = useMemo(() => outlineOf(doc), [doc]);
  const countsRef = useMemo(() => outlineTieCounts(outline, structure, doc, ties), [outline, structure, doc, ties]);
  const inspectFollowing = useRef(false);
  const [notice, setNotice] = useState<string | null>(null);
  const [action, setAction] = useState<SelectionAction | null>(null);
  const [inspect, setInspect] = useState<InspectorTarget | null>(null);
  const [chooser, setChooser] = useState<string | null>(null);
  const [sectionsOpen, setSectionsOpen] = useState(false);
  const [visit, setVisit] = useState<VisitOrigin | null>(() => visitOrigin());
  const visitRef = useRef(visit);
  visitRef.current = visit;

  /** The reading line: below the top bar and the location strip. */
  const readingTop = useCallback(() => cssPx("--topbar-h", 56) + (stripRef.current?.offsetHeight ?? 0), []);

  // ---- Where the page opens ----------------------------------------------------------

  /** The statement an address names: this record's slice, or whichever statement has that slice. */
  const statementAt = useCallback(
    (node: string | undefined, at: string | undefined): number | null => {
      const exact = statementFor(ties, node, at);
      if (exact !== null || !at) return exact;
      const found = ties.index.ties.findIndex((tie) => tie.at === at);
      return found >= 0 ? found : null;
    },
    [ties],
  );

  const initial = useMemo(() => {
    keyRef.current = historyKey();
    const from = restoreKey();
    const saved = loadPosition(keyRef.current) ?? (from ? loadPosition(from) : null);
    const savedPart = saved ? partOfPosition(saved, { stage, edition, parts: doc.parts }) : null;
    const hit = route.anchor ? resolveAnchor(doc, route.anchor) : null;
    const lines = route.at ? resolveAt(doc, route.at) : null;
    const named = statementAt(route.node, route.at);
    const start = savedPart ?? (named !== null ? statements.partOf(named) : undefined) ?? (lines ? partsOfLines(doc.parts, lines)[0] : undefined) ?? hit?.part ?? 0;
    const parts = new Set<number>();
    for (let i = start - 2; i <= start + 3; i++) if (i >= 0 && i < doc.parts.length) parts.add(i);
    if (start < 4) [0, 1, 2].forEach((i) => i < doc.parts.length && parts.add(i));
    return { parts: [...parts], saved: savedPart !== null ? saved : null };
    // Computed once per mounted paper.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const measurePosition = useCallback((): ReadingPosition | null => {
    const body = bodyRef.current;
    if (!body) return null;
    const top = readingTop();
    const part = partAt(body, doc.parts.length, top + 1);
    const el = body.partElement(part);
    if (!el) return null;
    return { edition, stage, part, partId: partIdOf(doc.parts[part]), offset: top - el.getBoundingClientRect().top, top, block: blockAtLine(el, top) };
  }, [doc, stage, edition, readingTop]);

  const saveNow = useCallback(() => {
    const position = measurePosition();
    if (position) savePosition(position);
  }, [measurePosition]);

  // Whatever the way of leaving: a link, Back, a reload.
  useEffect(() => onLeave(saveNow), [saveNow]);

  const restoring = useRef<(() => void) | null>(null);
  useEffect(() => () => restoring.current?.(), []);

  const restorePosition = useCallback(
    async (position: ReadingPosition) => {
      const body = bodyRef.current;
      const part = partOfPosition(position, { stage, edition, parts: doc.parts });
      if (!body || part === null) return false;
      await body.ensure([part - 1, part, part + 1]);
      const el = body.partElement(part);
      if (!el) return false;
      const line = position.top ?? readingTop();
      const y = () => scrollForPosition(el, position, line);
      window.scrollTo({ top: Math.max(0, y()), behavior: "instant" as ScrollBehavior });
      body.hold(el);
      // Parts around it and their mathematics are still settling: stay on the line
      // until they have, and go back to it once when late fonts reflow the text.
      restoring.current?.();
      const settled = () => body.reanchor(true);
      const fonts = document.fonts;
      const refit = () => (restoring.current = restoreScroll({ window: y }, { onDone: settled }));
      const stop = restoreScroll(
        { window: y },
        {
          onDone: () => {
            settled();
            fonts?.addEventListener("loadingdone", refit, { once: true });
            window.setTimeout(() => fonts?.removeEventListener("loadingdone", refit), 3000);
          },
        },
      );
      restoring.current = () => {
        stop();
        fonts?.removeEventListener("loadingdone", refit);
      };
      return true;
    },
    [doc, stage, edition, readingTop],
  );

  const jumpTo = useCallback(
    async (anchor: string, options: { smooth?: boolean; focus?: boolean } = {}) => {
      const body = bodyRef.current;
      if (!body) return false;
      const hit = resolveAnchor(doc, anchor);
      if (!hit) {
        setNotice(`The ${PAPER_NAMES[stage].short.toLowerCase()} has no passage “${anchor}”, so the page opens at the start of the paper.`);
        return false;
      }
      setNotice(null);
      await body.ensure([hit.part - 1, hit.part, hit.part + 1]);
      const root = paperRef.current;
      let target = hit.id ? root?.querySelector<HTMLElement>(`#${CSS.escape(hit.id)}`) : body.partElement(hit.part);
      // A passage whose section heading closes the part before it lands with that heading in view.
      if (!hit.id && target) {
        const before = body.partElement(hit.part - 1)?.querySelector(":scope > .part__text")?.lastElementChild;
        if (before?.matches("h1,h2,h3,h4,h5,h6")) target = before as HTMLElement;
      }
      if (!target) return false;
      const distance = Math.abs(target.getBoundingClientRect().top);
      const smooth = !!options.smooth && !prefersReducedMotion() && distance < window.innerHeight * 1.5;
      target.scrollIntoView({ block: "start", behavior: smooth ? "smooth" : ("instant" as ScrollBehavior) });
      if (!smooth) body.hold(target);
      if (options.focus) {
        const isHeading = (el: Element | null) => !!el?.matches("h1,h2,h3,h4,h5,h6");
        const heading = isHeading(target) ? target : isHeading(target.nextElementSibling) ? (target.nextElementSibling as HTMLElement) : null;
        if (heading) {
          heading.setAttribute("tabindex", "-1");
          heading.focus({ preventScroll: true });
        }
      }
      // A smooth scroll can be cut short by parts rendering on the way; land exactly.
      const settle = () => {
        const off = target.getBoundingClientRect().top;
        const expected = parseFloat(getComputedStyle(document.documentElement).scrollPaddingTop) + parseFloat(getComputedStyle(target).scrollMarginTop || "0");
        if (Math.abs(off - expected) > 6) target.scrollIntoView({ block: "start", behavior: "instant" as ScrollBehavior });
        body.hold(target);
      };
      if (smooth) {
        let done = false;
        const finish = () => {
          if (done) return;
          done = true;
          window.removeEventListener("scrollend", finish);
          settle();
        };
        window.addEventListener("scrollend", finish, { once: true });
        window.setTimeout(finish, 900);
      } else requestAnimationFrame(settle);
      return true;
    },
    [doc, stage],
  );

  /** The reading line, in pixels from the top of the window. */
  const readingLine = useCallback(() => {
    const top = readingTop();
    return top + (window.innerHeight - top) * READING_LINE;
  }, [readingTop]);

  /**
   * The exact landing of an address. A statement comes to the reading line and is lit there.
   * Lines with no statement mark their blocks, amber at first and quietly while they stay
   * the target, under the strip.
   */
  const landSlice = useCallback(
    async (at: string | undefined, options: { scroll?: boolean; smooth?: boolean; node?: string } = {}) => {
      const body = bodyRef.current;
      const root = paperRef.current;
      if (!body || !root) return false;
      root.querySelectorAll("[data-slice]").forEach((el) => el.removeAttribute("data-slice"));
      const statement = statementAt(options.node, at);
      let target: Element | undefined;
      let landing: () => number;
      if (statement !== null) {
        const part = statements.partOf(statement);
        await body.ensure([part - 1, part, part + 1]);
        target = statements.first(statement) ?? undefined;
        if (!target) return false;
        if (options.scroll === false) return true;
        const line = readingLine();
        landing = () => target!.getBoundingClientRect().top + window.scrollY - line;
      } else {
        const lines = at ? resolveAt(doc, at) : null;
        const parts = lines ? partsOfLines(doc.parts, lines) : [];
        if (!lines || !parts.length) return false;
        await body.ensure([parts[0] - 1, ...parts, parts[parts.length - 1] + 1]);
        const blocks = parts.flatMap((part) => blocksOf(body.partElement(part), part === parts[parts.length - 1] ? doc.parts[part].lines.end : doc.parts[part + 1]?.lines.start - 1, lines));
        if (!blocks.length) return false;
        blocks.forEach((el) => el.setAttribute("data-slice", ""));
        if (options.scroll === false) return true;
        target = blocks[0];
        landing = () => target!.getBoundingClientRect().top + window.scrollY - readingTop() - 16;
      }
      setNotice(null);
      const smooth = !!options.smooth && !prefersReducedMotion() && Math.abs(landing() - window.scrollY) < window.innerHeight * 1.5;
      window.scrollTo({ top: Math.max(0, landing()), behavior: smooth ? "smooth" : ("instant" as ScrollBehavior) });
      const settle = () => {
        if (Math.abs(landing() - window.scrollY) > 6) window.scrollTo({ top: Math.max(0, landing()), behavior: "instant" as ScrollBehavior });
        body.hold(target!);
      };
      if (smooth) {
        let done = false;
        const finish = () => {
          if (done) return;
          done = true;
          window.removeEventListener("scrollend", finish);
          settle();
        };
        window.addEventListener("scrollend", finish, { once: true });
        window.setTimeout(finish, 900);
      } else requestAnimationFrame(settle);
      return true;
    },
    [doc, readingTop, readingLine, statements, statementAt, ties],
  );

  /**
   * A deliberate navigation: save the outgoing line now (not on the scroll
   * debounce), push a history entry, and carry the visit origin with it.
   */
  const go = useCallback(
    (to: Route, options: GoOptions = {}) => {
      saveNow();
      const carry = options.visit === undefined ? visitRef.current : options.visit;
      navigate(to, { replace: options.replace });
      patchHistoryState({ lxVisit: carry ?? undefined, lxRestore: options.restore });
    },
    [saveNow],
  );

  // Open at the saved line, the anchor, or the top.
  useLayoutEffect(() => {
    // The page holds the reading position itself (PaperBody); the browser's
    // own scroll anchoring would pick nodes in the sticky columns and add to it.
    const root = document.documentElement;
    const previousAnchor = root.style.overflowAnchor;
    root.style.overflowAnchor = "none";
    // A record's address opened cold lands on its statement, with or without `l`.
    const named = statementAt(route.node, route.at);
    const at = named !== null ? ties.index.ties[named].at : route.at;
    if (initial.saved) {
      void restorePosition(initial.saved);
      if (at) void landSlice(at, { scroll: false, node: route.node });
    } else if (at) {
      void landSlice(at, { node: route.node }).then((ok) => {
        if (!ok && route.anchor) void jumpTo(route.anchor);
      });
    } else if (route.anchor) void jumpTo(route.anchor);
    else {
      // A record this paper discusses without an exact slice opens at its passage.
      const passage = route.node ? firstPassageFor(structure, [route.node]) : null;
      if (passage) void jumpTo(passage);
      else window.scrollTo({ top: 0, behavior: "instant" as ScrollBehavior });
    }
    if (restoreKey()) patchHistoryState({ lxRestore: undefined });
    lastHref.current = window.location.href;
    return () => {
      root.style.overflowAnchor = previousAnchor;
    };
    // Once per mounted paper.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // Every history entry gets a key and the position the reader is at. An entry
  // returned to by Back or Forward already has a key: its saved line is
  // restored, even when its #anchor is the same as the one being left.
  useEffect(() => {
    const href = window.location.href;
    if (href === lastHref.current) return;
    lastHref.current = href;
    const previousKey = keyRef.current;
    const existing = existingHistoryKey();
    const fromPop = !!existing && existing !== previousKey;
    keyRef.current = historyKey();
    setVisit(visitOrigin());
    const anchorChanged = route.anchor !== lastAnchor.current;
    lastAnchor.current = route.anchor;
    const atChanged = route.at !== lastAt.current;
    lastAt.current = route.at;
    const from = restoreKey();
    const saved = fromPop ? loadPosition(keyRef.current) : from ? loadPosition(from) : null;
    if (from) patchHistoryState({ lxRestore: undefined });
    // A pin from a sentence, or the address keeping up with the reader: the paper stays.
    const own = selfAt.current === route.at;
    selfAt.current = null;
    const paperMoves = !own && !saved && (atChanged ? !!route.at : false);
    if (atChanged || own) void landSlice(route.at, { scroll: paperMoves, smooth: !fromPop, node: route.node });
    if (saved) {
      void restorePosition(saved).then((ok) => {
        if (!ok && anchorChanged && route.anchor) void jumpTo(route.anchor);
      });
    } else if (paperMoves) {
      // landSlice has the page.
    } else if (anchorChanged && route.anchor && route.anchor !== selfAnchor.current) {
      void jumpTo(route.anchor, { smooth: !fromPop });
    } else {
      saveNow();
    }
    selfAnchor.current = undefined;
  }, [route, jumpTo, landSlice, restorePosition, saveNow]);

  // ---- What is on the right page ------------------------------------------------------

  /** The address names a pin: the record, and its statement when this paper has one. */
  const pin = useMemo<Pin | null>(() => {
    if (!route.node) return null;
    const statement = statementAt(route.node, route.at);
    return { record: route.node, tie: statement !== null && ties.index.ties[statement].record === route.node ? statement : null };
  }, [route.node, route.at, statementAt, ties]);
  const pinRef = useRef(pin);
  pinRef.current = pin;
  /** A pin is released by scrolling away: the reader's own hand, after it has been on screen. */
  const pinSeen = useRef(false);
  const handMoved = useRef(false);
  /** The statement under the reading line, on the page at once. */
  const current = useRef<number | null>(null);
  const currentSegment = useRef<number | null>(null);
  /** Stepped to by keys: the line leaves it alone until the reader scrolls by hand. */
  const stepped = useRef(false);
  const pointed = useRef<number | null>(null);
  const pointAtRef = useRef<(t: number | null, record?: string) => void>(() => undefined);
  const movedAt = useRef(0);
  const update = useRef<() => void>(() => undefined);
  const thread = useRef<SVGPathElement>(null);

  /**
   * The thread: a short line across the gutter from the statement to the Lean beside it. It
   * only ever crosses the empty gutter, so it can touch no card and no text, and it goes
   * whenever either end is off the screen. Drawn from what is on screen, with no state.
   */
  const drawThread = useCallback(() => {
    const path = thread.current;
    if (!path) return;
    const t = pinRef.current?.tie ?? current.current;
    const first = t !== null ? statements.first(t) : null;
    const paper = paperRef.current?.querySelector(".paper")?.getBoundingClientRect();
    const page = document.querySelector(".lean-page");
    const pane = page?.getBoundingClientRect();
    const target = (page?.querySelector(LEAN_TARGET) ?? null)?.getBoundingClientRect();
    const box = first?.getClientRects()[0];
    const top = readingTop();
    if (!box || !paper || !pane || !target || pane.left - paper.right < 16 || page?.closest(".map-pane__pages")?.querySelector(".lean-page") !== page || box.top < top || box.bottom > window.innerHeight || target.top < pane.top || target.bottom > pane.bottom) {
      if (path.getAttribute("d")) path.setAttribute("d", "");
      return;
    }
    const y0 = box.top + box.height / 2;
    const y1 = target.top + Math.min(target.height, 22) / 2;
    const x0 = paper.right + 4;
    const x1 = pane.left - 1;
    const mid = (x0 + x1) / 2;
    path.setAttribute("d", `M${x0.toFixed(1)} ${y0.toFixed(1)}C${mid.toFixed(1)} ${y0.toFixed(1)} ${mid.toFixed(1)} ${y1.toFixed(1)} ${x1.toFixed(1)} ${y1.toFixed(1)}`);
  }, [statements, readingTop]);

  useEffect(() => {
    pinSeen.current = false;
    handMoved.current = false;
    statements.light("pin", pin?.tie ?? null);
    statements.light("on", pin ? null : current.current);
    update.current();
  }, [pin, statements]);

  const release = useCallback(() => {
    const here = hereRef.current;
    if (here.node || here.at) navigate({ ...here, node: undefined, at: undefined }, { replace: true });
  }, []);

  useEffect(() => {
    let frame = 0;
    let saveTimer = 0;
    let holdTimer = 0;
    let addressTimer = 0;
    let settled = "";
    /** The passage that holds the reading line, or the nearest; every statement belongs to one. */
    const passageAt = (body: BodyHandle, line: number) => {
      const at = partAt(body, doc.parts.length, line);
      let follow = at;
      while (follow >= 0 && doc.parts[follow]?.kind !== "passage") follow--;
      if (follow < 0) {
        follow = at;
        while (follow < doc.parts.length && doc.parts[follow]?.kind !== "passage") follow++;
      }
      return follow < doc.parts.length ? follow : -1;
    };
    const settle = (tie: number | null, part: number) => {
      const anchor = doc.parts[part]?.anchor ?? null;
      signals.follow.set({ tie, anchor, part });
      // The address keeps up with the reader once they have stopped, never as a history entry.
      window.clearTimeout(addressTimer);
      if (tie === null || pinRef.current) return;
      addressTimer = window.setTimeout(() => {
        const here = hereRef.current;
        const at = ties.index.ties[tie].at;
        if (here.at === at || here.node || here.beside) return;
        selfAt.current = at;
        navigate({ ...here, at }, { replace: true });
      }, 1400);
    };
    const run = () => {
      frame = 0;
      const body = bodyRef.current;
      if (!body) return;
      const top = readingTop();
      const line = top + (window.innerHeight - top) * READING_LINE;
      let part = partAt(body, doc.parts.length, line);
      const atLine = part;
      // Unmapped text at the reading line (a title block, a bridge paragraph):
      // follow the first mapped passage on screen instead, if there is one.
      if (doc.parts[part]?.kind !== "passage") {
        for (let i = Math.max(0, part - 1); i < doc.parts.length; i++) {
          const r = body.partElement(i)?.getBoundingClientRect();
          if (!r || r.top > window.innerHeight * 0.8) break;
          if (doc.parts[i].kind === "passage" && r.bottom > top + 40) {
            part = i;
            break;
          }
        }
      }
      signals.part.set(part);
      if (!stepped.current) {
        const segment = statements.atLine(line, (window.innerHeight - top) * LINE_REACH, atLine);
        currentSegment.current = segment;
        current.current = segment === null ? null : statementOf(ties, segment);
        if (!pinRef.current) statements.light("on", current.current);
      }
      const passage = passageAt(body, line);
      const key = `${current.current}|${passage}`;
      if (key !== settled) {
        settled = key;
        window.clearTimeout(holdTimer);
        const held = current.current;
        // A long statement can hold the line while the page flies past: wait for the page too.
        let from = window.scrollY;
        const hold = () => {
          const moved = Math.abs(window.scrollY - from);
          from = window.scrollY;
          if (moved > window.innerHeight * FLYING) holdTimer = window.setTimeout(hold, FOLLOW_HOLD);
          else settle(held, passage);
        };
        holdTimer = window.setTimeout(hold, FOLLOW_HOLD);
      }
      const held = pinRef.current?.tie ?? null;
      if (held !== null) {
        const box = statements.extent(held);
        if (box) {
          const visible = box.bottom > top && box.top < window.innerHeight;
          if (visible) pinSeen.current = true;
          else if (pinSeen.current && handMoved.current) release();
        }
      }
      let heading: string | null = null;
      for (const entry of outline) {
        if (entry.part < part) heading = entry.id;
        else if (entry.part === part) {
          const el = paperRef.current?.querySelector<HTMLElement>(`#${CSS.escape(entry.id)}`);
          if (el && el.getBoundingClientRect().top <= line + 4) heading = entry.id;
        } else break;
      }
      if (window.scrollY < 8) heading = null;
      signals.heading.set(heading);
      drawThread();
    };
    update.current = () => {
      if (!frame) frame = requestAnimationFrame(run);
    };
    const onScroll = () => {
      movedAt.current = performance.now();
      // The words under the pointer have moved on.
      if (signals.caption.get()) signals.caption.set(null);
      if (pointed.current !== null) pointAtRef.current(null);
      update.current();
      window.clearTimeout(saveTimer);
      saveTimer = window.setTimeout(() => saveNow(), 200);
    };
    /** The reader's own hand on the page gives the line back to the reader. */
    const onHand = () => {
      stepped.current = false;
      handMoved.current = true;
    };
    const onKeyScroll = (event: KeyboardEvent) => {
      if (SCROLL_KEYS.has(event.key)) onHand();
    };
    const onBar = (event: PointerEvent) => {
      if (event.target === document.documentElement) onHand();
    };
    window.addEventListener("scroll", onScroll, { passive: true });
    window.addEventListener("resize", onScroll, { passive: true });
    window.addEventListener("wheel", onHand, { passive: true });
    window.addEventListener("touchmove", onHand, { passive: true });
    window.addEventListener("keydown", onKeyScroll);
    window.addEventListener("pointerdown", onBar);
    const first = window.setTimeout(run, 60);
    return () => {
      window.removeEventListener("scroll", onScroll);
      window.removeEventListener("resize", onScroll);
      window.removeEventListener("wheel", onHand);
      window.removeEventListener("touchmove", onHand);
      window.removeEventListener("keydown", onKeyScroll);
      window.removeEventListener("pointerdown", onBar);
      cancelAnimationFrame(frame);
      window.clearTimeout(saveTimer);
      window.clearTimeout(holdTimer);
      window.clearTimeout(addressTimer);
      window.clearTimeout(first);
    };
  }, [doc, outline, ties, statements, signals, saveNow, readingTop, release, drawThread]);

  // The Lean page changes and scrolls on its own; the thread keeps up.
  useEffect(() => {
    const redraw = () => requestAnimationFrame(drawThread);
    const off = signals.follow.subscribe(() => window.setTimeout(redraw, 120));
    const onInner = (event: Event) => (event.target as Element).closest?.(".lean-page") && redraw();
    window.addEventListener("scroll", onInner, { capture: true, passive: true });
    return () => {
      off();
      window.removeEventListener("scroll", onInner, { capture: true });
    };
  }, [signals, drawThread]);

  const trail = useMemo(() => paperTrail(structure), [structure]);

  // The place being left, named once for every way of leaving it.
  useEffect(
    () =>
      namePlace(() => {
        const chain = chainOf(outline, signals.heading.get());
        const last = chain[chain.length - 1];
        return `${PAPER_NAMES[stage].short}${last ? ` ${sectionNumber(last.title)}` : ""}`;
      }),
    [outline, signals, stage],
  );

  // ---- Links -------------------------------------------------------------------------

  const here: ReadRoute = useMemo(
    () => ({ view: "read", stage, anchor: route.anchor, at: route.at, node: route.node, beside: route.beside }),
    [stage, route.anchor, route.at, route.node, route.beside],
  );
  const hereRef = useRef(here);
  hereRef.current = here;
  const links: Links = useMemo(
    () => ({
      node: (id) => routeHref({ ...here, node: id, beside: undefined }),
      beside: (s, anchor) => routeHref({ ...here, beside: { stage: s, anchor } }),
    }),
    [here],
  );

  /** "Short paper §4" for a passage of this account. */
  const placeLabel = useCallback(
    (anchor: string | undefined) => {
      const title = anchor ? sectionTitleIn(structure, anchor) : null;
      return `${PAPER_NAMES[stage].short}${title ? ` ${sectionNumber(title)}` : ""}`;
    },
    [structure, stage],
  );

  const originHere = useCallback(
    (anchor: string | undefined): VisitOrigin => ({ key: keyRef.current, stage, anchor, label: placeLabel(anchor) }),
    [stage, placeLabel],
  );

  // ---- Inspector -----------------------------------------------------------------------

  // An open passage list keeps up with the reader: once its passage has left the
  // window it moves to the passage being read, instead of standing stale beside it.
  useEffect(() => {
    if (inspect?.kind !== "passage") return;
    return signals.follow.subscribe(() => {
      const { anchor: followAnchor } = signals.follow.get();
      if (!followAnchor || inspect.anchor === followAnchor) return;
      const part = inspect.anchor ? doc.parts.findIndex((p) => p.kind === "passage" && p.anchor === inspect.anchor) : -1;
      const box = part >= 0 ? bodyRef.current?.partElement(part)?.getBoundingClientRect() : null;
      if (box && box.bottom > readingTop() && box.top < window.innerHeight) return;
      inspectFollowing.current = true;
      setInspect({ kind: "passage", anchor: followAnchor });
    });
  }, [inspect, signals, doc, readingTop]);

  const openInspector = useCallback((anchor: string | null, opener: HTMLElement | null) => {
    inspectOpener.current = opener;
    setInspect((prev) => (prev?.kind === "passage" && prev.anchor === anchor ? null : { kind: "passage", anchor }));
  }, []);

  const closeInspector = useCallback(() => {
    setInspect(null);
    if (route.node) navigate({ ...here, node: undefined }, { replace: true });
    const opener = inspectOpener.current;
    if (opener?.isConnected) opener.focus({ preventScroll: true });
  }, [route.node, here]);

  /** A record chosen in a list: opened like a card. */
  const selectRecord = useCallback(
    (id: string | null) => {
      if (!id) return release();
      const statement = statementFor(ties, id);
      selfAt.current = statement !== null ? ties.index.ties[statement].at : undefined;
      navigate({ ...hereRef.current, node: id, at: statement !== null ? ties.index.ties[statement].at : undefined, beside: undefined });
    },
    [ties, release],
  );

  // ---- Pinning -------------------------------------------------------------------------

  /** A statement in the paper: one history entry, and the paper does not move. */
  const openStatement = useCallback(
    (t: number) => {
      const tie = ties.index.ties[t];
      selfAt.current = tie.at;
      go({ ...hereRef.current, node: tie.record, at: tie.at, beside: undefined });
    },
    [ties, go],
  );

  // On desktop the inspector is a column, not a modal: take focus to its title once, explicitly.
  const inspectKey = inspect ? (inspect.kind === "passage" ? `p:${inspect.anchor}` : `s:${inspect.start}`) : "";
  useEffect(() => {
    if (inspectFollowing.current) {
      inspectFollowing.current = false;
      return;
    }
    if (!inspect || !mid || !inspectOpener.current) return;
    document.getElementById("inspector-title")?.focus({ preventScroll: true });
    // Only when another passage is opened.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [inspectKey]);

  // ---- Visits --------------------------------------------------------------------------

  const openVisit = useCallback(
    (from: string | undefined, to: { stage: Stage; anchor: string }) => {
      void loadDocument(to.stage).catch(() => undefined);
      setChooser(null);
      go({ ...here, beside: to }, { visit: originHere(from) });
    },
    [go, here, originHere],
  );

  const closeVisit = useCallback(() => go({ ...here, beside: undefined }, { visit: null }), [go, here]);

  const returnToOrigin = useCallback(() => {
    const v = visitRef.current;
    if (!v) {
      // Entered from an address: the origin is the place the address names.
      closeVisit();
      if (route.anchor && route.beside) void jumpTo(route.anchor);
      return;
    }
    if (v.stage === stage) go({ ...here, beside: undefined }, { visit: null, restore: v.key });
    else go({ view: "read", stage: v.stage, anchor: v.anchor }, { visit: null, restore: v.key });
  }, [closeVisit, go, here, jumpTo, route.anchor, route.beside, stage]);

  const promote = useCallback(
    (s: Stage, anchor: string) => {
      const v = visitRef.current ?? originHere(route.anchor);
      if (s === stage) go({ ...here, beside: undefined, anchor }, { visit: null });
      else go({ view: "read", stage: s, anchor }, { visit: v });
    },
    [go, here, originHere, route.anchor, stage],
  );

  const toggleMap = useCallback(() => showMap(!mapShown), [showMap, mapShown]);
  const closeSheet = useCallback(() => {
    setSheetOpen(false);
    if (hereRef.current.node) release();
  }, [release]);
  const hideMap = useCallback(() => {
    showMap(false);
    closeSheet();
  }, [showMap, closeSheet]);

  const dismissVisit = useCallback(() => {
    patchHistoryState({ lxVisit: undefined });
    setVisit(null);
  }, []);

  // While a visit is open the paper underneath keeps its place and leaves the tab order.
  useEffect(() => {
    if (!route.beside) return;
    const root = document.documentElement;
    const previous = root.style.overflow;
    root.style.overflow = "hidden";
    return () => {
      root.style.overflow = previous;
    };
  }, [route.beside]);

  // ---- Pointing ------------------------------------------------------------------------

  const pointTimer = useRef(0);
  const leaveTimer = useRef(0);

  /** Light a statement now, and after a dwell let the right page preview it. Moving off restores. */
  const pointAt = useCallback(
    (t: number | null, record?: string) => {
      window.clearTimeout(leaveTimer.current);
      if (t === pointed.current && t !== null) return;
      window.clearTimeout(pointTimer.current);
      pointed.current = t;
      statements.light("point", t);
      if (t === null && !record) {
        leaveTimer.current = window.setTimeout(() => {
          paneHover.current?.(null);
          signals.point.set(null);
        }, 60);
        return;
      }
      const id = record ?? ties.index.ties[t!].record;
      paneHover.current?.(new Set([id]));
      pointTimer.current = window.setTimeout(() => signals.point.set({ tie: t, record: id }), POINT_DWELL);
    },
    [statements, signals, ties],
  );
  pointAtRef.current = pointAt;
  useEffect(
    () => () => {
      window.clearTimeout(pointTimer.current);
      window.clearTimeout(leaveTimer.current);
    },
    [],
  );

  const onPaperPointer = (event: React.PointerEvent) => {
    if (event.pointerType === "touch") return;
    // Words sliding under a still pointer are not the reader pointing at them.
    if (performance.now() - movedAt.current < 120) return;
    const target = event.target as Element;
    const mark = target.closest?.<HTMLElement>("[data-t]");
    if (mark) {
      signals.caption.set(null);
      pointAt(statementOf(ties, Number(mark.dataset.t)));
      return;
    }
    pointAt(null);
    const anchor = target.closest?.<HTMLElement>("[data-passage]")?.dataset.passage;
    signals.caption.set(anchor && target.closest(".part__text") ? anchor : null);
  };

  const onPaperLeave = () => {
    pointAt(null);
    signals.caption.set(null);
  };

  const onPaperFocus = (event: React.FocusEvent) => {
    const mark = (event.target as Element).closest?.<HTMLElement>("[data-t]");
    if (mark) pointAt(statementOf(ties, Number(mark.dataset.t)));
  };

  // ---- Keys ----------------------------------------------------------------------------

  /** Move to the next tied statement: to the reading line, as though the reader had scrolled there. */
  const step = useCallback(
    (by: 1 | -1) => {
      // Between statements the step starts from where the reader is, not from the paper's start.
      const at = signals.part.get();
      const from = currentSegment.current;
      const next = from !== null ? stepFrom(ties, from, by) : by > 0 ? (ties.stops.find((t) => statements.partOf(t) >= at) ?? null) : ([...ties.stops].reverse().find((t) => statements.partOf(t) < at) ?? null);
      if (next === null) return;
      if (pinRef.current) release();
      stepped.current = true;
      current.current = next;
      currentSegment.current = ties.segmentsOf[next][0];
      statements.light("on", next);
      update.current();
      void landSlice(ties.index.ties[next].at, { node: ties.index.ties[next].record, smooth: true }).then(() => {
        const first = statements.first(next);
        if (first) {
          first.setAttribute("tabindex", "0");
          first.focus({ preventScroll: true });
        }
      });
    },
    [ties, statements, signals, landSlice, release],
  );

  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.defaultPrevented || document.querySelector("[data-modal-open]")) return;
      const target = event.target as HTMLElement | null;
      const typing = !!target?.closest?.("input, textarea, select, [contenteditable]");
      if (event.key === "Escape") {
        if (action) setAction(null);
        else if (route.beside) {
          event.preventDefault();
          closeVisit();
        } else if (inspect && (mid || paneOn)) {
          event.preventDefault();
          closeInspector();
        } else if (!paneOn && sheetOpen) {
          event.preventDefault();
          closeSheet();
        } else if (pinRef.current) {
          event.preventDefault();
          release();
        }
        return;
      }
      if (typing || event.metaKey || event.ctrlKey || event.altKey || route.beside) return;
      if (event.key === "j" || event.key === "k") {
        event.preventDefault();
        step(event.key === "j" ? 1 : -1);
      } else if (event.key === "Enter" && current.current !== null) {
        // Enter on a control belongs to that control.
        if (target && target !== document.body && !target.closest("[data-t]")) return;
        event.preventDefault();
        openStatement(current.current);
      }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [route.beside, inspect, mid, action, closeVisit, closeInspector, sheetOpen, paneOn, closeSheet, release, step, openStatement]);

  // ---- Clicks inside the paper ---------------------------------------------------------

  const downAt = useRef<{ x: number; y: number } | null>(null);
  const pinTimer = useRef(0);

  const onPaperClick = (event: React.MouseEvent) => {
    const target = event.target as Element;
    const a = target.closest?.("a");
    if (event.button !== 0) return;
    if (!a) {
      if (target.closest?.("button")) return;
      const mark = target.closest?.<HTMLElement>("[data-t]");
      window.clearTimeout(pinTimer.current);
      if (!mark || event.detail > 1) return;
      // A drag or a selection is reading, not asking.
      const down = downAt.current;
      const moved = !!down && Math.hypot(event.clientX - down.x, event.clientY - down.y) > 5;
      const selection = window.getSelection();
      if (moved || (selection && !selection.isCollapsed && selection.toString().trim())) return;
      const t = statementOf(ties, Number(mark.dataset.t));
      if (t === null) return;
      // The second click of a double click selects a word; wait to see that it does not come.
      if ((event.nativeEvent as PointerEvent).pointerType === "touch") openStatement(t);
      else pinTimer.current = window.setTimeout(() => openStatement(t), 210);
      return;
    }
    const href = a.getAttribute("href") ?? "";
    const from = a.closest<HTMLElement>("[data-passage]")?.dataset.passage ?? doc.parts[signals.part.get()]?.anchor;
    if (a.dataset.companion !== undefined && a.closest(".part__text")) {
      if (event.metaKey || event.ctrlKey || event.shiftKey) return; // the browser opens it in a new tab or window
      event.preventDefault();
      const target = a.dataset.companion as Stage;
      const fragment = companionAnchor(structures[target], a.dataset.fragment);
      if (event.altKey) go({ view: "read", stage: target, anchor: fragment || undefined }, { visit: originHere(from) });
      else openVisit(from, { stage: target, anchor: fragment });
      return;
    }
    if (href.startsWith("#") && href.length > 1 && !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey) {
      event.preventDefault();
      jumpWithHistory(decodeURIComponent(href.slice(1)), false);
    }
  };

  /** An explicit jump (outline, breadcrumb, in-text reference): a history stop of its own. */
  const jumpWithHistory = (id: string, focus: boolean) => {
    selfAnchor.current = id;
    go({ ...here, anchor: id, at: undefined, node: undefined, beside: undefined });
    void jumpTo(id, { smooth: true, focus });
  };

  /** A line of the paper found by search: a history stop, marked where it lands. */
  const jumpToLine = (line: number) => {
    go({ ...here, at: String(line), node: undefined, beside: undefined });
  };

  /** From the map: the paper goes to the statement, and the graph stays where it is. */
  const openFromMap = useCallback(
    (id: string) => {
      const statement = statementFor(ties, id);
      const tie = statement !== null ? ties.index.ties[statement] : null;
      const to = { ...hereRef.current, node: id, at: tie?.at, beside: undefined };
      if (tie && hereRef.current.at === tie.at) void landSlice(tie.at, { smooth: true, node: id });
      go(to);
    },
    [go, ties, landSlice],
  );

  const toTop = () => {
    go({ ...here, anchor: undefined, at: undefined, node: undefined, beside: undefined });
    window.scrollTo({ top: 0, behavior: prefersReducedMotion() ? ("instant" as ScrollBehavior) : "smooth" });
  };

  // ---- Selections ----------------------------------------------------------------------

  useEffect(() => {
    let pointerDown = false;
    let timer = 0;
    const evaluate = () => {
      const sel = window.getSelection();
      const root = paperRef.current;
      if (!sel || sel.isCollapsed || !sel.rangeCount || !root || !sel.toString().trim()) {
        setAction(null);
        return;
      }
      const range = sel.getRangeAt(0);
      const partOf = (node: Node) => (node instanceof Element ? node : node.parentElement)?.closest<HTMLElement>("[data-part]");
      const a = partOf(range.startContainer);
      const b = partOf(range.endContainer);
      if (!a || !b || !root.contains(a) || !root.contains(b) || (!a.querySelector(".part__text") && !a.closest(".part__text"))) {
        setAction(null);
        return;
      }
      const i = Number(a.dataset.part);
      const j = Number(b.dataset.part);
      const passages = passagesBetween(doc.parts, i, j);
      if (!passages) {
        setAction(null);
        return;
      }
      const rects = Array.from(range.getClientRects()).filter((r) => r.width > 0 && r.height > 0);
      const first = rects[0] ?? range.getBoundingClientRect();
      const below = first.top < readingTop() + 52;
      const anchorRect = below ? (rects[rects.length - 1] ?? first) : first;
      const rootRect = root.getBoundingClientRect();
      const x = Math.min(Math.max(anchorRect.left + anchorRect.width / 2 - rootRect.left, 110), rootRect.width - 110);
      const y = (below ? anchorRect.bottom + 10 : anchorRect.top - 10) - rootRect.top;
      const span = selectionSpan(doc.parts, i, j);
      setAction({ start: span.start, end: span.end, passages, x, y, below });
    };
    const onChange = () => {
      window.clearTimeout(timer);
      if (pointerDown) return;
      timer = window.setTimeout(evaluate, 160);
    };
    const onDown = (event: PointerEvent) => {
      if ((event.target as Element).closest?.(".select-action")) return;
      pointerDown = true;
    };
    const onUp = () => {
      if (!pointerDown) return;
      pointerDown = false;
      window.clearTimeout(timer);
      timer = window.setTimeout(evaluate, 60);
    };
    document.addEventListener("selectionchange", onChange);
    document.addEventListener("pointerdown", onDown);
    document.addEventListener("pointerup", onUp);
    return () => {
      document.removeEventListener("selectionchange", onChange);
      document.removeEventListener("pointerdown", onDown);
      document.removeEventListener("pointerup", onUp);
      window.clearTimeout(timer);
    };
  }, [doc, readingTop]);

  const askSelection = (event: React.MouseEvent<HTMLButtonElement>) => {
    if (!action) return;
    inspectOpener.current = event.currentTarget.closest(".reader")?.querySelector<HTMLElement>(".reader__paper") ?? null;
    setInspect({ kind: "selection", start: action.start, end: action.end, passages: action.passages });
    setAction(null);
  };

  // ---- Layout --------------------------------------------------------------------------

  const names = PAPER_NAMES[stage];
  const status = statusWords(structure.state, structure.review_state);
  const pdf = { href: `${import.meta.env.BASE_URL}${PAPER_PDFS[stage].path}`, pages: PAPER_PDFS[stage].pages };
  const head = { name: names.short, job: names.job, reader: names.reader, status, pdf };
  const inspecting = !!inspect;
  // Beside the right page the inspector takes the Lean page's place instead of a column.
  const columnInspector = inspecting && mid && !paneOn;
  const outlineColumn = mid && !(columnInspector && !wide) && !(paneOn && !outlineRoom);
  const sectionsProps = { entries: outline, counts: countsRef, doc, onJump: (id: string) => jumpWithHistory(id, true), onLine: jumpToLine };
  const visitOriginPassage = route.beside
    ? visit && visit.stage === stage
      ? (visit.anchor ?? null)
      : route.anchor
        ? (resolveBeside(doc, structure, route.anchor)?.passage ?? null)
        : null
    : null;

  const sameTopicOf = useCallback((anchor: string) => setChooser(anchor), []);
  const paneProps = {
    stage,
    structures,
    outline,
    trail,
    signals,
    ties,
    pin,
    alignment,
    hoverRef: paneHover,
    onRecord: openFromMap,
    onRelease: release,
    passageHref: links.beside,
    onPoint: pointAt,
  };

  const inspector = inspect && (
    <Inspector
      stage={stage}
      target={inspect}
      structures={structures}
      node={route.node ?? null}
      links={links}
      inModal={!mid}
      onSelect={selectRecord}
      onClose={closeInspector}
      onSameTopic={(anchor) => setChooser(anchor)}
      onVisit={(s, anchor) => openVisit(inspect.kind === "passage" ? (inspect.anchor ?? undefined) : doc.parts[signals.part.get()]?.anchor, { stage: s, anchor })}
    />
  );

  return (
    <div
      className={`reader reader--${wide ? "wide" : mid ? "mid" : "narrow"}${columnInspector ? " reader--inspecting" : ""}${outlineColumn ? " reader--outlined" : ""}${paneOn ? " reader--follow" : ""}`}
    >
      {outlineColumn && (
        <aside className="reader__outline" inert={route.beside ? true : undefined}>
          <Heading signals={signals}>{(current) => <OutlineColumn {...sectionsProps} current={current} head={head} />}</Heading>
        </aside>
      )}

      <div
        className="reader__paper"
        ref={paperRef}
        onClick={onPaperClick}
        onPointerDown={(event) => (downAt.current = { x: event.clientX, y: event.clientY })}
        onPointerOver={onPaperPointer}
        onPointerLeave={onPaperLeave}
        onFocus={onPaperFocus}
        onBlur={() => pointAt(null)}
        inert={route.beside ? true : undefined}
      >
        <div className="reader-strip" ref={stripRef}>
          <BackControl className="reader-strip__back" />
          {mid && !outlineColumn && <Heading signals={signals}>{(current) => <SectionsPopover {...sectionsProps} current={current} />}</Heading>}
          <Crumbs signals={signals} outline={outline} name={names.short} stage={stage} phone={phone} onTop={toTop} onJump={(id) => jumpWithHistory(id, true)} />
          {ties.stops.length > 0 && <StepControls signals={signals} ties={ties} onStep={step} />}
          {mid && (
            <button
              type="button"
              className="control reader-strip__map"
              aria-pressed={paneRoom ? paneOn : undefined}
              onClick={paneRoom ? toggleMap : () => setSheetOpen(true)}
            >
              <svg viewBox="0 0 14 14" width="13" height="13" aria-hidden="true">
                <rect x="1.5" y="1.5" width="11" height="11" rx="1.5" fill="none" stroke="currentColor" strokeWidth="1.3" />
                <path d="M7 1.5v11" stroke="currentColor" strokeWidth="1.3" />
              </svg>
              {paneRoom ? "Proof beside the paper" : "Open the proof"}
            </button>
          )}
          {visit && !route.beside && (
            <div className="reader-strip__visit">
              <button type="button" className="control reader-strip__return" onClick={returnToOrigin}>
                <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
                  <path d="M7.5 2.5L4 6l3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
                </svg>
                Return to {visit.label}
              </button>
              <button type="button" className="reader-strip__dismiss" aria-label={`Stay here and remove the button that returns to ${visit.label}`} onClick={dismissVisit}>
                <svg viewBox="0 0 12 12" width="10" height="10" aria-hidden="true">
                  <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
                </svg>
              </button>
            </div>
          )}
        </div>

        {!outlineColumn && (
          <p className="account-line">
            {!phone && <>{names.job} </>}
            {names.reader}
            {status && <> {status}</>} <PdfLink pdf={pdf} />
          </p>
        )}
        {notice && (
          <p className="reader-notice" role="status">
            {notice}
          </p>
        )}
        {ties.stops.length > 0 && (
          <p className="paper-hint">
            {phone ? "Tap" : "Click"} any marked statement to see its Lean. <span className="paper-hint__more">A tick in the margin marks a statement tied to a step of the proof, darker where the step has Lean.{!phone && " Press j and k to step through them."}</span>
          </p>
        )}
        <PaperBody
          ref={bodyRef}
          stage={stage}
          doc={doc}
          structures={structures}
          graph={graph}
          initial={initial.parts}
          topInset={readingTop()}
          inspected={inspect?.kind === "passage" ? inspect.anchor : null}
          statements={statements}
          onInspect={openInspector}
          onSameTopic={sameTopicOf}
        />
        {action && (
          <button
            type="button"
            className={`select-action${action.below ? " select-action--below" : ""}`}
            style={{ left: action.x, top: action.y }}
            onMouseDown={(event) => event.preventDefault()}
            onClick={askSelection}
          >
            {action.passages === 1 ? "Records linked to this passage" : `Records linked to these ${action.passages} passages`}
          </button>
        )}
      </div>

      {columnInspector && (
        <aside className="reader__inspector" aria-label="Records linked to this passage" inert={route.beside ? true : undefined}>
          {inspector}
        </aside>
      )}

      {paneOn && (
        <svg className="reader-thread" aria-hidden="true">
          <path ref={thread} />
        </svg>
      )}

      {paneOn && (
        <div className="reader__map">
          {paneReady && (
            <Suspense fallback={null}>
              <MapPane {...paneProps} inert={!!route.beside} onHide={hideMap} leanSlot={inspecting ? inspector : undefined} />
            </Suspense>
          )}
        </div>
      )}

      {!paneOn && !route.beside && (sheetOpen || !!pin) && (
        <RightSheet phone={phone} onClose={closeSheet}>
          <Suspense fallback={<p className="right-sheet__wait">Loading the proof</p>}>
            <MapPane {...paneProps} inModal onHide={closeSheet} />
          </Suspense>
        </RightSheet>
      )}

      {!mid && !route.beside && (
        <div className="reader-bar">
          <button type="button" className="reader-bar__button" aria-haspopup="dialog" onClick={() => setSectionsOpen(true)}>
            <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true">
              <path d="M2.5 4h11M2.5 8h11M2.5 12h7" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
            </svg>
            Sections
          </button>
          <button type="button" className="reader-bar__button" onClick={() => setSheetOpen(true)}>
            <svg viewBox="0 0 14 14" width="14" height="14" aria-hidden="true">
              <rect x="1.5" y="1.5" width="11" height="11" rx="1.5" fill="none" stroke="currentColor" strokeWidth="1.3" />
              <path d="M7 1.5v11" stroke="currentColor" strokeWidth="1.3" />
            </svg>
            Proof
          </button>
          <PassageDetails signals={signals} doc={doc} structure={structure} graph={graph} onOpen={openInspector} />
        </div>
      )}

      {!mid && inspect && (
        <Modal
          title={inspect.kind === "selection" ? (inspect.passages === 1 ? "Records linked to this passage" : `Records linked to these ${inspect.passages} passages`) : "Records linked to this passage"}
          placement={phone ? "sheet" : "side-end"}
          className="modal--inspector"
          onClose={closeInspector}
        >
          {inspector}
        </Modal>
      )}

      {!mid && sectionsOpen && (
        <Modal title="Sections" placement={phone ? "sheet" : "side-start"} className="modal--sections" onClose={() => setSectionsOpen(false)}>
          <p className="modal__account">
            {names.short}
            {status && <span className="faint">. {status}</span>}
          </p>
          <Heading signals={signals}>
            {(current) => (
              <Sections
                {...sectionsProps}
                current={current}
                onJump={(id) => {
                  setSectionsOpen(false);
                  jumpWithHistory(id, true);
                }}
                onLine={(line) => {
                  setSectionsOpen(false);
                  jumpToLine(line);
                }}
              />
            )}
          </Heading>
        </Modal>
      )}

      {chooser && (
        <Chooser
          here={{ stage, anchor: chooser }}
          structures={structures}
          graph={graph}
          placement={phone ? "sheet" : "centre"}
          beside={links.beside}
          onChoose={(d: Destination) => openVisit(chooser, { stage: d.stage, anchor: d.anchor })}
          onBegin={(s) => {
            const from = chooser;
            setChooser(null);
            go({ view: "read", stage: s }, { visit: originHere(from) });
          }}
          onClose={() => setChooser(null)}
        />
      )}

      {route.beside && (
        <Visit
          key={`${route.beside.stage}:${route.beside.anchor}`}
          target={route.beside}
          origin={visitOriginPassage ? { stage, anchor: visitOriginPassage } : null}
          originLabel={visit?.label ?? placeLabel(visitOriginPassage ?? undefined)}
          compare={paneRoom}
          structures={structures}
          links={links}
          onReturn={returnToOrigin}
          onClose={closeVisit}
          onPromote={promote}
          onFollow={(s, anchor) => go({ ...here, beside: { stage: s, anchor } })}
        />
      )}
    </div>
  );
}

function sameFollow(a: Followed, b: Followed): boolean {
  return a.tie === b.tie && a.anchor === b.anchor && a.part === b.part;
}

/** Renders with the section being read: the one thing here that changes while scrolling. */
function Heading({ signals, children }: { signals: ReaderSignals; children(current: string | null): React.ReactNode }) {
  return <>{children(useSignal(signals.heading))}</>;
}

function Crumbs({ signals, outline, name, stage, phone, onTop, onJump }: { signals: ReaderSignals; outline: OutlineEntry[]; name: string; stage: Stage; phone: boolean; onTop(): void; onJump(id: string): void }) {
  const chain = chainOf(outline, useSignal(signals.heading));
  return (
    <nav className="crumbs" aria-label="Where you are in this paper">
      <ol>
        <li>
          <a
            href={routeHref({ view: "read", stage })}
            aria-current={chain.length ? undefined : "location"}
            onClick={(event) => {
              if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
              event.preventDefault();
              onTop();
            }}
          >
            {name}
          </a>
        </li>
        {chain.map((entry, i) => {
          const last = i === chain.length - 1;
          return (
            <li key={entry.id} className={last ? "crumbs__here" : undefined}>
              <a
                href={`#${encodeURIComponent(entry.id)}`}
                title={sectionLabel(entry.title)}
                aria-current={last ? "location" : undefined}
                onClick={(event) => {
                  if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
                  event.preventDefault();
                  onJump(entry.id);
                }}
              >
                {last && !phone ? sectionLabel(entry.title) : sectionNumber(entry.title)}
              </a>
            </li>
          );
        })}
      </ol>
    </nav>
  );
}

/** "12 of 86" between two arrows: the tied statements, one at a time. j and k do the same. */
function StepControls({ signals, ties, onStep }: { signals: ReaderSignals; ties: TieModel; onStep(by: 1 | -1): void }) {
  const { tie } = useSignal(signals.follow);
  const place = tie === null ? -1 : ties.place[tie];
  const arrow = (d: string) => (
    <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
      <path d={d} fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  );
  return (
    <div className="reader-strip__steps" role="group" aria-label="Tied statements">
      <button type="button" aria-label="Previous tied statement" title="Previous tied statement (k)" onClick={() => onStep(-1)}>
        {arrow("M7.5 2.5L4 6l3.5 3.5")}
      </button>
      <span className="num" aria-live="polite">
        {place >= 0 ? `${place + 1} of ${ties.stops.length}` : `${ties.stops.length} statements`}
      </span>
      <button type="button" aria-label="Next tied statement" title="Next tied statement (j)" onClick={() => onStep(1)}>
        {arrow("M4.5 2.5L8 6l-3.5 3.5")}
      </button>
    </div>
  );
}

function PassageDetails({ signals, doc, structure, graph, onOpen }: { signals: ReaderSignals; doc: PreparedDocument; structure: PaperStructure; graph: ArgGraph; onOpen(anchor: string | null, opener: HTMLElement | null): void }) {
  const part = useSignal(signals.part);
  const anchor = doc.parts[part]?.kind === "passage" ? doc.parts[part].anchor : undefined;
  const records = anchor ? passageRecords(passageOf(structure, anchor)) : [];
  return (
    <button
      type="button"
      className="reader-bar__button"
      aria-haspopup="dialog"
      aria-label={records.length ? `Passage details: ${recordTally(records, graph)}` : "Passage details"}
      onClick={(event) => onOpen(anchor ?? null, event.currentTarget)}
    >
      Passage details
      {records.length > 0 && <span className="reader-bar__count num">{records.length}</span>}
    </button>
  );
}

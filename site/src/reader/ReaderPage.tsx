// The paper reader: one account at a protected measure, its sections beside
// it, and context only when the reader asks for it. Each mapped passage has a
// slim margin mark and two quiet controls: its records, which open the "In
// this passage" inspector, and "Same topic in…", which offers the authored
// treatments elsewhere. A chosen treatment opens as a visit (side by side from
// 1280px) over the paper, which stays where it was. Deliberate jumps make
// history entries, passive scrolling never does, and every entry keeps its
// reading position, so Back and "Return to …" land on the line the reader left.

import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { PaperStructure, Stage } from "../api/types";
import { get } from "../api/client";
import { describeError, useEdition, useResource } from "../app/data";
import { navigate, routeHref, type Route } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { prefersReducedMotion } from "../app/theme";
import { sectionLabel } from "../map/TheoremPlate";
import { loadDocument, useDocument, type LoadedDocument } from "./documents";
import { PaperBody, type BodyHandle, type Links } from "./page/PaperBody";
import { Inspector, type InspectorTarget } from "./page/Inspector";
import { Chooser } from "./page/Chooser";
import { Visit } from "./page/Visit";
import { Modal } from "./page/Modal";
import { OutlineColumn, Sections, SectionsPopover } from "./page/Outline";
import { MapPane } from "./page/MapPane";
import {
  chainOf,
  companionAnchor,
  outlineOf,
  passageOf,
  passageRecords,
  passagesBetween,
  recordTally,
  resolveAnchor,
  resolveBeside,
  sectionNumber,
  sectionTitleIn,
  selectionSpan,
  statusWords,
  type Destination,
  type Structures,
} from "./page/model";
import {
  existingHistoryKey,
  historyKey,
  loadPosition,
  partIdOf,
  partOfPosition,
  patchHistoryState,
  restoreKey,
  savePosition,
  visitOrigin,
  type ReadingPosition,
  type VisitOrigin,
} from "./page/position";
import "./reader-content.css";
import "./reader-page.css";

type ReadRoute = Extract<Route, { view: "read" }>;

export function ReaderPage({ route }: { route: ReadRoute }) {
  const loaded = useDocument(route.stage);
  // The other accounts' structures name destinations; the paper never waits for them.
  const others = useResource<Structures>("reader:structures", () =>
    Promise.all(STAGE_ORDER.map((s) => get<PaperStructure>(`/papers/${s}/structure`).then((r) => [s, r.data] as const))).then(
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
    return sessionStorage.getItem(MAP_PANE_KEY) !== "hidden";
  } catch {
    return true;
  }
}

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
  const { doc, paper } = loaded;
  const stage = route.stage;
  const structure = paper.structure;
  const wide = useMedia("(min-width: 1360px)");
  const mid = useMedia("(min-width: 1120px)");
  const compareRoom = useMedia("(min-width: 1280px)");
  const phone = useMedia("(max-width: 700px)");
  // From 1480px the paper moves left and the argument map follows it on the right.
  const followRoom = useMedia("(min-width: 1480px)");
  const [mapShown, setMapShown] = useState(readMapShown);
  const paneOn = followRoom && mapShown;
  const showMap = useCallback((shown: boolean) => {
    setMapShown(shown);
    try {
      sessionStorage.setItem(MAP_PANE_KEY, shown ? "shown" : "hidden");
    } catch {
      /* storage unavailable */
    }
  }, []);

  const bodyRef = useRef<BodyHandle>(null);
  const paperRef = useRef<HTMLDivElement>(null);
  const stripRef = useRef<HTMLDivElement>(null);
  const keyRef = useRef<string>("");
  const selfAnchor = useRef<string | undefined>(route.anchor);
  const lastAnchor = useRef<string | undefined>(route.anchor);
  const lastHref = useRef<string>("");
  const inspectOpener = useRef<HTMLElement | null>(null);

  const outline = useMemo(() => outlineOf(doc), [doc]);
  const [currentPart, setCurrentPart] = useState(0);
  const [currentHeading, setCurrentHeading] = useState<string | null>(null);
  /** The passage under the map's reading line (38% down the text area), and that passage once it has stayed there. */
  const [followPart, setFollowPart] = useState(-1);
  const [followAnchor, setFollowAnchor] = useState<string | null>(null);
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

  const initial = useMemo(() => {
    keyRef.current = historyKey();
    const from = restoreKey();
    const saved = loadPosition(keyRef.current) ?? (from ? loadPosition(from) : null);
    const savedPart = saved ? partOfPosition(saved, { stage, edition, parts: doc.parts }) : null;
    const hit = route.anchor ? resolveAnchor(doc, route.anchor) : null;
    const start = savedPart ?? hit?.part ?? 0;
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
    return { edition, stage, part, partId: partIdOf(doc.parts[part]), offset: Math.round(top - el.getBoundingClientRect().top) };
  }, [doc, stage, edition, readingTop]);

  const saveNow = useCallback((key = keyRef.current) => {
    const position = measurePosition();
    if (position && key) savePosition(key, position);
  }, [measurePosition]);

  const restorePosition = useCallback(
    async (position: ReadingPosition) => {
      const body = bodyRef.current;
      const part = partOfPosition(position, { stage, edition, parts: doc.parts });
      if (!body || part === null) return false;
      await body.ensure([part - 1, part, part + 1]);
      const el = body.partElement(part);
      if (!el) return false;
      const y = el.getBoundingClientRect().top + window.scrollY - readingTop() + position.offset;
      window.scrollTo({ top: Math.max(0, y), behavior: "instant" as ScrollBehavior });
      body.reanchor(true);
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
        setNotice(`The ${PAPER_NAMES[stage].short.toLowerCase()} in this edition has no passage “${anchor}”, so the page opens at the start of the paper.`);
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
    const previous = window.history.scrollRestoration;
    window.history.scrollRestoration = "manual";
    // The page holds the reading position itself (PaperBody); the browser's
    // own scroll anchoring would pick nodes in the sticky columns and add to it.
    const root = document.documentElement;
    const previousAnchor = root.style.overflowAnchor;
    root.style.overflowAnchor = "none";
    if (initial.saved) void restorePosition(initial.saved);
    else if (route.anchor) void jumpTo(route.anchor);
    else window.scrollTo({ top: 0, behavior: "instant" as ScrollBehavior });
    if (restoreKey()) patchHistoryState({ lxRestore: undefined });
    lastHref.current = window.location.href;
    return () => {
      saveNow();
      window.history.scrollRestoration = previous;
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
    if (fromPop && previousKey) saveNow(previousKey);
    keyRef.current = historyKey();
    setVisit(visitOrigin());
    const anchorChanged = route.anchor !== lastAnchor.current;
    lastAnchor.current = route.anchor;
    const from = restoreKey();
    const saved = fromPop ? loadPosition(keyRef.current) : from ? loadPosition(from) : null;
    if (from) patchHistoryState({ lxRestore: undefined });
    if (saved) {
      void restorePosition(saved).then((ok) => {
        if (!ok && anchorChanged && route.anchor) void jumpTo(route.anchor);
      });
    } else if (anchorChanged && route.anchor && route.anchor !== selfAnchor.current) {
      void jumpTo(route.anchor, { smooth: !fromPop });
    } else {
      saveNow();
    }
    selfAnchor.current = undefined;
  }, [route, jumpTo, restorePosition, saveNow]);

  // ---- Following the reader ------------------------------------------------------------

  useEffect(() => {
    let frame = 0;
    let saveTimer = 0;
    const update = () => {
      frame = 0;
      const body = bodyRef.current;
      if (!body) return;
      const top = readingTop();
      const line = top + (window.innerHeight - top) * 0.3;
      let part = partAt(body, doc.parts.length, line);
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
      setCurrentPart(part);
      // The map follows the passage under a lower reading line, or the nearest one above it
      // (before the first passage, the first one below).
      const followLine = top + (window.innerHeight - top) * 0.38;
      const at = partAt(body, doc.parts.length, followLine);
      let follow = at;
      while (follow >= 0 && doc.parts[follow]?.kind !== "passage") follow--;
      if (follow < 0) {
        follow = at;
        while (follow < doc.parts.length && doc.parts[follow]?.kind !== "passage") follow++;
      }
      setFollowPart(follow < doc.parts.length ? follow : -1);
      let heading: string | null = null;
      for (const entry of outline) {
        if (entry.part < part) heading = entry.id;
        else if (entry.part === part) {
          const el = paperRef.current?.querySelector<HTMLElement>(`#${CSS.escape(entry.id)}`);
          if (el && el.getBoundingClientRect().top <= line + 4) heading = entry.id;
        } else break;
      }
      if (window.scrollY < 8) heading = null;
      setCurrentHeading(heading);
    };
    const onScroll = () => {
      if (!frame) frame = requestAnimationFrame(update);
      window.clearTimeout(saveTimer);
      saveTimer = window.setTimeout(() => saveNow(), 200);
    };
    window.addEventListener("scroll", onScroll, { passive: true });
    window.addEventListener("resize", onScroll, { passive: true });
    const first = window.setTimeout(update, 60);
    return () => {
      window.removeEventListener("scroll", onScroll);
      window.removeEventListener("resize", onScroll);
      cancelAnimationFrame(frame);
      window.clearTimeout(saveTimer);
      window.clearTimeout(first);
    };
  }, [doc, outline, saveNow, readingTop]);

  const currentAnchor = doc.parts[currentPart]?.kind === "passage" ? doc.parts[currentPart].anchor : undefined;

  // Fast scrolling passes passages by: the map acts once one has been current for 180ms.
  useEffect(() => {
    const part = doc.parts[followPart];
    const anchor = part?.kind === "passage" ? (part.anchor ?? null) : null;
    const t = window.setTimeout(() => setFollowAnchor(anchor), 180);
    return () => window.clearTimeout(t);
  }, [followPart, doc]);
  const followRecords = useMemo(() => (followAnchor ? passageRecords(passageOf(structure, followAnchor)) : []), [followAnchor, structure]);

  // ---- Links -------------------------------------------------------------------------

  const here: ReadRoute = useMemo(() => ({ view: "read", stage, anchor: route.anchor, node: route.node, beside: route.beside }), [stage, route.anchor, route.node, route.beside]);
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

  // A record named in the address (from the map or search) opens the inspector beside the paper.
  useEffect(() => {
    if (!route.node || inspect || !mid) return;
    const hit = route.anchor ? resolveBeside(doc, structure, route.anchor) : null;
    const anchor = hit?.passage && passageRecords(passageOf(structure, hit.passage)).includes(route.node) ? hit.passage : null;
    setInspect({ kind: "passage", anchor });
    // Only when the record changes.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [route.node]);

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

  const selectRecord = useCallback(
    (id: string | null) => navigate({ ...here, node: id ?? undefined, beside: undefined }, { replace: true }),
    [here],
  );

  // On desktop the inspector is a column, not a modal: take focus to its title once, explicitly.
  const inspectKey = inspect ? (inspect.kind === "passage" ? `p:${inspect.anchor}` : `s:${inspect.start}`) : "";
  useEffect(() => {
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

  // ---- Keys ----------------------------------------------------------------------------

  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      if (document.querySelector("[data-modal-open]")) return;
      if (action) {
        setAction(null);
        return;
      }
      if (route.beside) {
        event.preventDefault();
        closeVisit();
      } else if (inspect && mid) {
        event.preventDefault();
        closeInspector();
      }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [route.beside, inspect, mid, action, closeVisit, closeInspector]);

  // ---- Clicks inside the paper ---------------------------------------------------------

  const onPaperClick = (event: React.MouseEvent) => {
    const a = (event.target as Element).closest?.("a");
    if (!a || event.button !== 0) return;
    const href = a.getAttribute("href") ?? "";
    const from = a.closest<HTMLElement>("[data-passage]")?.dataset.passage ?? currentAnchor;
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
    go({ ...here, anchor: id, beside: undefined });
    void jumpTo(id, { smooth: true, focus });
  };

  /** From the map beside the text: scroll to the passage, then its margin mark flashes amber once. */
  const jumpFromMap = useCallback(
    (anchor: string) => {
      selfAnchor.current = anchor;
      go({ ...here, anchor, beside: undefined });
      void jumpTo(anchor, { smooth: true }).then((ok) => {
        if (!ok) return;
        let done = false;
        const flash = () => {
          if (done) return;
          done = true;
          window.removeEventListener("scrollend", flash);
          const el = paperRef.current?.querySelector<HTMLElement>(`[data-passage="${CSS.escape(anchor)}"]`);
          if (!el) return;
          el.classList.remove("part--flash");
          void el.offsetWidth;
          el.classList.add("part--flash");
          window.setTimeout(() => el.classList.remove("part--flash"), 1200);
        };
        // After the smooth scroll ends; at once when the page did not move (or had already landed).
        const y0 = window.scrollY;
        window.addEventListener("scrollend", flash, { once: true });
        window.setTimeout(() => Math.abs(window.scrollY - y0) < 1 && flash(), 120);
        window.setTimeout(flash, 950);
      });
    },
    [go, here, jumpTo],
  );

  const toTop = () => {
    go({ ...here, anchor: undefined, beside: undefined });
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
  const head = { name: names.short, job: names.job, reader: names.reader, status };
  const chain = chainOf(outline, currentHeading);
  const inspecting = !!inspect;
  // Beside the map the inspector slides in over the right of the pane instead of taking a column.
  const columnInspector = inspecting && mid && !paneOn;
  const outlineColumn = mid && !(columnInspector && !wide);
  const sectionsProps = { entries: outline, current: currentHeading, onJump: (id: string) => jumpWithHistory(id, true) };
  const currentRecords = currentAnchor ? passageRecords(passageOf(structure, currentAnchor)) : [];
  const visitOriginPassage = route.beside
    ? visit && visit.stage === stage
      ? (visit.anchor ?? null)
      : route.anchor
        ? (resolveBeside(doc, structure, route.anchor)?.passage ?? null)
        : null
    : null;

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
      onVisit={(s, anchor) => openVisit(inspect.kind === "passage" ? (inspect.anchor ?? undefined) : currentAnchor, { stage: s, anchor })}
    />
  );

  return (
    <div
      className={`reader reader--${wide ? "wide" : mid ? "mid" : "narrow"}${columnInspector ? " reader--inspecting" : ""}${outlineColumn ? " reader--outlined" : ""}${paneOn ? " reader--follow" : ""}`}
    >
      {outlineColumn && (
        <aside className="reader__outline" inert={route.beside ? true : undefined}>
          <OutlineColumn {...sectionsProps} head={head} />
        </aside>
      )}

      <div className="reader__paper" ref={paperRef} onClick={onPaperClick} inert={route.beside ? true : undefined}>
        <div className="reader-strip" ref={stripRef}>
          {mid && !outlineColumn && <SectionsPopover {...sectionsProps} />}
          <nav className="crumbs" aria-label="Where you are in this paper">
            <ol>
              <li>
                <a
                  href={routeHref({ view: "read", stage })}
                  aria-current={chain.length ? undefined : "location"}
                  onClick={(event) => {
                    if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
                    event.preventDefault();
                    toTop();
                  }}
                >
                  {names.short}
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
                        jumpWithHistory(entry.id, true);
                      }}
                    >
                      {last && !phone ? sectionLabel(entry.title) : sectionNumber(entry.title)}
                    </a>
                  </li>
                );
              })}
            </ol>
          </nav>
          {followRoom && !mapShown && (
            <button type="button" className="control reader-strip__map" onClick={() => showMap(true)}>
              <svg viewBox="0 0 14 14" width="13" height="13" aria-hidden="true">
                <rect x="1.5" y="1.5" width="11" height="11" rx="1.5" fill="none" stroke="currentColor" strokeWidth="1.3" />
                <path d="M7 1.5v11" stroke="currentColor" strokeWidth="1.3" />
              </svg>
              Show the map beside the text
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
            {status && <> {status}</>}
          </p>
        )}
        {notice && (
          <p className="reader-notice" role="status">
            {notice}
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
          onInspect={openInspector}
          onSameTopic={(anchor) => setChooser(anchor)}
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
        <div className="reader__map">
          <MapPane
            stage={stage}
            structures={structures}
            anchor={followAnchor}
            records={followRecords}
            inert={!!route.beside}
            onHide={() => showMap(false)}
            onJump={jumpFromMap}
            overlay={
              inspecting ? (
                <aside className="reader__inspector reader__inspector--over" aria-label="Records linked to this passage">
                  {inspector}
                </aside>
              ) : undefined
            }
          />
        </div>
      )}

      {!mid && !route.beside && (
        <div className="reader-bar">
          <button type="button" className="reader-bar__button" aria-haspopup="dialog" onClick={() => setSectionsOpen(true)}>
            <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true">
              <path d="M2.5 4h11M2.5 8h11M2.5 12h7" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
            </svg>
            Sections
          </button>
          <button
            type="button"
            className="reader-bar__button"
            aria-haspopup="dialog"
            aria-label={currentRecords.length ? `Passage details: ${recordTally(currentRecords, graph)}` : "Passage details"}
            onClick={(event) => openInspector(currentAnchor ?? null, event.currentTarget)}
          >
            Passage details
            {currentRecords.length > 0 && <span className="reader-bar__count num">{currentRecords.length}</span>}
          </button>
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
            {status && <span className="faint"> · {status}</span>}
          </p>
          <Sections
            {...sectionsProps}
            onJump={(id) => {
              setSectionsOpen(false);
              jumpWithHistory(id, true);
            }}
          />
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
          compare={compareRoom}
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

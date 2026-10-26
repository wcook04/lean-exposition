// The paper reader: one account in a reading column, its sections beside it,
// and a companion pane that follows the passage in view. Routes to the other
// accounts open beside the text, so the reader never loses their place; Back
// returns to the line they left.

import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { PaperStructure, Stage } from "../api/types";
import { get } from "../api/client";
import { describeError, useEdition, useResource } from "../app/data";
import { navigate, routeHref, type Route } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { prefersReducedMotion } from "../app/theme";
import { loadDocument, useDocument, type LoadedDocument } from "./documents";
import { PaperBody, type BodyHandle, type Links } from "./page/PaperBody";
import { Companion, type CompanionHandle, type PaneMode } from "./page/Companion";
import { OutlineColumn, OutlineMenu } from "./page/Outline";
import {
  firstPassageFor,
  outlineOf,
  passageOf,
  passageRecords,
  recordCount,
  resolveAnchor,
  selectionSpan,
  statusWords,
  type Structures,
} from "./page/model";
import { historyKey, loadPosition, savePosition, type ReadingPosition } from "./page/position";
import "./reader-content.css";
import "./reader-page.css";

type ReadRoute = Extract<Route, { view: "read" }>;

export function ReaderPage({ route }: { route: ReadRoute }) {
  const loaded = useDocument(route.stage);
  const structures = useResource<Structures>("reader:structures", () =>
    Promise.all(STAGE_ORDER.map((s) => get<PaperStructure>(`/papers/${s}/structure`).then((r) => [s, r.data] as const))).then(
      (pairs) => Object.fromEntries(pairs) as Structures,
    ),
  );
  const account = PAPER_NAMES[route.stage].short;

  if (loaded.status === "error" || structures.status === "error") {
    const { title, detail } = describeError(loaded.status === "error" ? loaded.error : (structures as { error: unknown }).error);
    return (
      <div className="page-message" role="alert">
        <h1>{title}</h1>
        <p>{detail}</p>
      </div>
    );
  }
  if (loaded.status !== "ready" || structures.status !== "ready" || loaded.value.paper.stage !== route.stage) {
    return (
      <p className="reader-loading" aria-live="polite">
        Opening the {account.toLowerCase()}…
      </p>
    );
  }
  return <Reader key={route.stage} route={route} loaded={loaded.value} structures={structures.value} />;
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

function topbarHeight(): number {
  const value = parseFloat(getComputedStyle(document.documentElement).getPropertyValue("--topbar-h"));
  return Number.isFinite(value) ? value : 56;
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
  /** Set in the margin beside the selection's first line (wide screens), off the text. */
  margin?: { width: number };
  start: number;
  end: number;
  parts: number;
}

function Reader({ route, loaded, structures }: { route: ReadRoute; loaded: LoadedDocument; structures: Structures }) {
  const { graph } = useEdition();
  const { doc, paper } = loaded;
  const stage = route.stage;
  const structure = paper.structure;
  const wide = useMedia("(min-width: 1280px)");
  const mid = useMedia("(min-width: 900px)");

  const bodyRef = useRef<BodyHandle>(null);
  const paperRef = useRef<HTMLDivElement>(null);
  const companionRef = useRef<CompanionHandle>(null);
  const keyRef = useRef<string>("");
  const popRef = useRef(false);
  const selfAnchor = useRef<string | undefined>(route.anchor);
  const lastAnchor = useRef<string | undefined>(route.anchor);
  const lastHref = useRef<string>("");

  const outline = useMemo(() => outlineOf(doc), [doc]);
  const [currentPart, setCurrentPart] = useState(0);
  const [currentHeading, setCurrentHeading] = useState<string | null>(null);
  const [echo, setEcho] = useState<string[]>([]);
  const [notice, setNotice] = useState<string | null>(null);
  const [selection, setSelection] = useState<{ start: number; end: number; parts: number } | null>(null);
  const [action, setAction] = useState<SelectionAction | null>(null);
  const [sheet, setSheet] = useState(false);

  // ---- Where the page opens ----------------------------------------------------------

  const initial = useMemo(() => {
    keyRef.current = historyKey();
    const saved = loadPosition(keyRef.current);
    const hit = route.anchor ? resolveAnchor(doc, route.anchor) : null;
    const start = saved && saved.stage === stage && saved.part < doc.parts.length ? saved.part : (hit?.part ?? 0);
    const parts = new Set<number>();
    for (let i = start - 2; i <= start + 3; i++) if (i >= 0 && i < doc.parts.length) parts.add(i);
    if (start < 4) [0, 1, 2].forEach((i) => i < doc.parts.length && parts.add(i));
    return { parts: [...parts], saved: saved && saved.stage === stage ? saved : null, hit };
    // Computed once per mounted paper.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const measurePosition = useCallback((): ReadingPosition | null => {
    const body = bodyRef.current;
    if (!body) return null;
    const top = topbarHeight();
    const part = partAt(body, doc.parts.length, top + 1);
    const el = body.partElement(part);
    if (!el) return null;
    return { stage, part, offset: Math.round(top - el.getBoundingClientRect().top) };
  }, [doc, stage]);

  const restorePosition = useCallback(
    async (position: ReadingPosition) => {
      const body = bodyRef.current;
      if (!body) return;
      await body.ensure([position.part - 1, position.part, position.part + 1]);
      const el = body.partElement(position.part);
      if (!el) return;
      const y = el.getBoundingClientRect().top + window.scrollY - topbarHeight() + position.offset;
      window.scrollTo({ top: Math.max(0, y), behavior: "instant" as ScrollBehavior });
      body.reanchor(true);
    },
    [],
  );

  const jumpTo = useCallback(
    async (anchor: string, options: { smooth?: boolean; focus?: boolean } = {}) => {
      const body = bodyRef.current;
      if (!body) return false;
      const hit = resolveAnchor(doc, anchor);
      if (!hit) {
        setNotice(`The passage “${anchor}” is not in this edition of the ${PAPER_NAMES[stage].short.toLowerCase()}, so it opens at the top.`);
        return false;
      }
      setNotice(null);
      await body.ensure([hit.part - 1, hit.part, hit.part + 1]);
      const root = paperRef.current;
      const target = hit.id
        ? root?.querySelector<HTMLElement>(`#${CSS.escape(hit.id)}`)
        : body.partElement(hit.part);
      if (!target) return false;
      const distance = Math.abs(target.getBoundingClientRect().top);
      const smooth = !!options.smooth && !prefersReducedMotion() && distance < window.innerHeight * 1.5;
      target.scrollIntoView({ block: "start", behavior: smooth ? "smooth" : ("instant" as ScrollBehavior) });
      if (!smooth) body.hold(target);
      if (options.focus) {
        const heading = target.matches("h1,h2,h3,h4,h5,h6") ? target : target.nextElementSibling?.matches("h1,h2,h3,h4,h5,h6") ? (target.nextElementSibling as HTMLElement) : null;
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
    lastHref.current = window.location.href;
    return () => {
      const position = measurePosition();
      if (position && keyRef.current) savePosition(keyRef.current, position);
      window.history.scrollRestoration = previous;
      root.style.overflowAnchor = previousAnchor;
    };
    // Once per mounted paper.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  useEffect(() => {
    const onPop = () => (popRef.current = true);
    window.addEventListener("popstate", onPop);
    return () => window.removeEventListener("popstate", onPop);
  }, []);

  // Every history entry gets a key and the position the reader is at; an
  // anchor change scrolls only when the reader did not cause it here.
  useEffect(() => {
    const href = window.location.href;
    if (href === lastHref.current) return;
    lastHref.current = href;
    const fromPop = popRef.current;
    popRef.current = false;
    keyRef.current = historyKey();
    const anchorChanged = route.anchor !== lastAnchor.current;
    lastAnchor.current = route.anchor;
    const saved = fromPop ? loadPosition(keyRef.current) : null;
    if (fromPop && saved && saved.stage === stage && anchorChanged) {
      void restorePosition(saved);
    } else if (anchorChanged && route.anchor && route.anchor !== selfAnchor.current) {
      void jumpTo(route.anchor, { smooth: true });
    } else {
      const position = measurePosition();
      if (position) savePosition(keyRef.current, position);
    }
    selfAnchor.current = undefined;
  }, [route, stage, jumpTo, restorePosition, measurePosition]);

  // ---- Following the reader ------------------------------------------------------------

  const records = useCallback(
    (part: number) => {
      const p = doc.parts[part];
      if (!p || p.kind !== "passage" || !p.anchor) return [] as string[];
      return passageRecords(passageOf(structure, p.anchor)).filter((id) => graph.nodes.has(id));
    },
    [doc, structure, graph],
  );

  useEffect(() => {
    let frame = 0;
    let saveTimer = 0;
    const update = () => {
      frame = 0;
      const body = bodyRef.current;
      if (!body) return;
      const top = topbarHeight();
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
      saveTimer = window.setTimeout(() => {
        const position = measurePosition();
        if (position && keyRef.current) savePosition(keyRef.current, position);
      }, 200);
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
  }, [doc, outline, measurePosition]);

  // The pane follows the passage in view after the reader settles on it.
  const currentRecords = useMemo(() => records(currentPart), [records, currentPart]);
  useEffect(() => {
    const timer = window.setTimeout(() => {
      setEcho((prev) => (prev.length === currentRecords.length && prev.every((id, i) => id === currentRecords[i]) ? prev : currentRecords));
    }, 280);
    return () => window.clearTimeout(timer);
  }, [currentRecords]);

  const besideKey = route.beside ? `${route.beside.stage}:${route.beside.anchor}` : "";
  const mode: PaneMode = route.beside
    ? { kind: "beside", stage: route.beside.stage, anchor: route.beside.anchor }
    : route.node
      ? { kind: "record", node: route.node }
      : selection
        ? { kind: "selection", ...selection }
        : { kind: "map" };

  useEffect(() => {
    if (mode.kind !== "map") return;
    const timer = window.setTimeout(() => companionRef.current?.fitEcho(echo), 140);
    return () => window.clearTimeout(timer);
  }, [echo, mode.kind, sheet]);

  useEffect(() => {
    if (route.node || route.beside) setSelection(null);
  }, [route.node, besideKey, route.beside]);

  // On a phone the pane is a sheet the reader opens; a chosen record or a
  // passage opened beside opens it.
  useEffect(() => {
    if (!mid && (route.node || route.beside)) setSheet(true);
  }, [mid, route.node, besideKey, route.beside]);

  // ---- Links -------------------------------------------------------------------------

  const here: ReadRoute = useMemo(() => ({ view: "read", stage, anchor: route.anchor, node: route.node, beside: route.beside }), [stage, route.anchor, route.node, route.beside]);
  const links: Links = useMemo(
    () => ({
      node: (id) => routeHref({ ...here, node: id, beside: undefined }),
      beside: (s, anchor) => routeHref({ ...here, beside: { stage: s, anchor } }),
    }),
    [here],
  );

  const keepIds = useMemo(() => (route.node && graph.nodes.has(route.node) ? [route.node] : currentRecords), [route.node, graph, currentRecords]);
  const switchHref = useCallback(
    (s: Stage) => {
      if (s === stage) return routeHref({ view: "read", stage: s, node: route.node });
      const anchor = firstPassageFor(structures[s], keepIds) ?? undefined;
      return routeHref({ view: "read", stage: s, anchor, node: route.node });
    },
    [stage, structures, keepIds, route.node],
  );
  const keeping = useMemo(() => {
    const first = keepIds[0];
    if (!first) return null;
    const others = STAGE_ORDER.filter((s) => s !== stage && firstPassageFor(structures[s], keepIds));
    if (!others.length) return null;
    return `“${graph.nodes.get(first)?.label ?? first}”`;
  }, [keepIds, stage, structures, graph]);

  const closePane = useCallback(() => {
    if (route.beside) navigate({ ...here, beside: undefined });
    else if (route.node) navigate({ ...here, node: undefined });
    else setSelection(null);
  }, [route.beside, route.node, here]);

  // Esc closes the record, the passage beside or the selection, then the sheet.
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      if (document.querySelector("[data-modal-open]")) return;
      if (action) {
        setAction(null);
        return;
      }
      if (route.beside || route.node || selection) {
        event.preventDefault();
        closePane();
      } else if (sheet) setSheet(false);
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [route.beside, route.node, selection, sheet, action, closePane]);

  // ---- Clicks inside the paper ---------------------------------------------------------

  const onPaperClick = (event: React.MouseEvent) => {
    const a = (event.target as Element).closest?.("a");
    if (!a || event.button !== 0) return;
    const href = a.getAttribute("href") ?? "";
    if (a.dataset.companion !== undefined && a.closest(".part__text")) {
      if (event.metaKey || event.ctrlKey || event.shiftKey) return; // the browser opens it in a new tab or window
      event.preventDefault();
      if (event.altKey) {
        navigate(href);
        return;
      }
      const target = a.dataset.companion as Stage;
      const fragment = a.dataset.fragment || structures[target]?.paper.passages[0]?.anchor || "";
      void loadDocument(target).catch(() => undefined);
      navigate(links.beside(target, fragment));
      return;
    }
    if (href.startsWith("#") && href.length > 1 && !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey) {
      event.preventDefault();
      const anchor = decodeURIComponent(href.slice(1));
      selfAnchor.current = anchor;
      void jumpTo(anchor, { smooth: true });
      navigate({ ...here, anchor }, { replace: true });
    }
  };

  const onOutlineJump = (id: string) => {
    selfAnchor.current = id;
    void jumpTo(id, { smooth: true, focus: true });
    navigate({ ...here, anchor: id }, { replace: true });
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
      if (!a || !b || !root.contains(a) || !root.contains(b) || !a.querySelector(".part__text") && !a.closest(".part__text")) {
        setAction(null);
        return;
      }
      const rects = Array.from(range.getClientRects()).filter((r) => r.width > 0 && r.height > 0);
      const first = rects[0] ?? range.getBoundingClientRect();
      const top = topbarHeight();
      const below = first.top < top + 52;
      const anchorRect = below ? (rects[rects.length - 1] ?? first) : first;
      const rootRect = root.getBoundingClientRect();
      const x = Math.min(Math.max(anchorRect.left + anchorRect.width / 2 - rootRect.left, 90), rootRect.width - 90);
      const y = (below ? anchorRect.bottom + 10 : anchorRect.top - 10) - rootRect.top;
      const i = Number(a.dataset.part);
      const j = Number(b.dataset.part);
      const span = selectionSpan(doc.parts, i, j);
      const base = { start: span.start, end: span.end, parts: Math.abs(j - i) + 1 };
      const text = a.querySelector<HTMLElement>(".part__text");
      const gutter = text ? text.getBoundingClientRect().left - a.getBoundingClientRect().left : 0;
      if (gutter >= 120) {
        const top0 = (rects[0] ?? first).top;
        setAction({ ...base, x: a.getBoundingClientRect().left - rootRect.left, y: top0 - rootRect.top - 4, below: false, margin: { width: gutter - 32 } });
        return;
      }
      setAction({ ...base, x, y, below });
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
  }, [doc]);

  const askSelection = () => {
    if (!action) return;
    setSelection({ start: action.start, end: action.end, parts: action.parts });
    setAction(null);
    if (route.beside || route.node) navigate({ ...here, beside: undefined, node: undefined });
    if (!mid) setSheet(true);
  };

  // ---- Layout --------------------------------------------------------------------------

  const names = PAPER_NAMES[stage];
  const status = statusWords(structure.state, structure.review_state);
  const currentAnchor = doc.parts[currentPart]?.kind === "passage" ? doc.parts[currentPart].anchor : undefined;
  const currentPassage = currentAnchor ? passageOf(structure, currentAnchor) : undefined;
  const echoMapped = !!currentPassage && passageRecords(currentPassage).length > 0;
  const outlineProps = { stage, entries: outline, current: currentHeading, switchHref, keeping, onJump: onOutlineJump };
  const claimCount = currentRecords.length ? recordCount(
    currentRecords.filter((id) => graph.nodes.get(id)?.kind !== "assumption").length,
    currentRecords.filter((id) => graph.nodes.get(id)?.kind === "assumption").length,
  ) : null;

  const companion = (
    <Companion
      ref={companionRef}
      stage={stage}
      mode={mode}
      echo={echo}
      echoMapped={echoMapped}
      structures={structures}
      links={links}
      node={route.node}
      onClose={closePane}
      onSelect={(id) => navigate({ ...here, node: id, beside: undefined })}
      header={mid && !wide ? <OutlineMenu {...outlineProps} placement="pane" /> : undefined}
    />
  );

  return (
    <div className={`reader${wide ? " reader--wide" : ""}${mid ? " reader--mid" : " reader--narrow"}${action ? " reader--selecting" : ""}`}>
      {wide && (
        <aside className="reader__outline">
          <OutlineColumn {...outlineProps} />
        </aside>
      )}

      <div className="reader__paper" ref={paperRef} onClick={onPaperClick}>
        <header className="account-line">
          <p>
            <span className="account-line__name">{names.short}.</span> {names.job}
          </p>
          <p className="account-line__more">
            {names.reader}
            {status && <> {status}</>}
          </p>
        </header>
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
          links={links}
          initial={initial.parts}
          topInset={topbarHeight()}
        />
        {action && (
          <button
            type="button"
            className={`select-action${action.below ? " select-action--below" : ""}${action.margin ? " select-action--margin" : ""}`}
            style={{ left: action.x, top: action.y, ...(action.margin ? { width: action.margin.width } : {}) }}
            onMouseDown={(event) => event.preventDefault()}
            onClick={askSelection}
          >
            What does this map to?
          </button>
        )}
      </div>

      {mid && <aside className="reader__pane" aria-label="Companion">{companion}</aside>}

      {!mid && (
        <>
          <div className="reader-bar">
            <OutlineMenu {...outlineProps} placement="bar" />
            <button type="button" className="control reader-bar__pane" aria-expanded={sheet} onClick={() => setSheet((v) => !v)}>
              {mode.kind === "map" ? (echoMapped && claimCount ? claimCount : "The map") : "Companion"}
            </button>
          </div>
          {sheet && (
            <div className="sheet" role="dialog" aria-label="Companion">
              <div className="sheet__grip">
                <button type="button" className="control control--plain" onClick={() => setSheet(false)}>
                  Hide
                </button>
              </div>
              {companion}
            </div>
          )}
        </>
      )}
    </div>
  );
}

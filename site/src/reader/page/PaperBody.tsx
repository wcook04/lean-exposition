// The paper itself, part by part. Every prepared part is its own element;
// parts near the viewport are rendered, the rest wait as placeholders sized
// from their byte length and are rendered in idle time. Heights that change
// above the reading line are compensated, so the line a reader is on never
// moves. A mapped passage carries a slim rule in the margin (amber while it is
// in the inspector) and, under its heading, a quiet bar: the records it discusses
// by name, a Lean mark where they have Lean, and its linked passages.

import { createContext, forwardRef, memo, useCallback, useContext, useEffect, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState } from "react";
import { createPortal } from "react-dom";
import { shortTitle } from "../../compare/useAlignment";
import type { Stage } from "../../api/types";
import type { ArgGraph } from "../../model/graph";
import type { PreparedDocument, PreparedPart } from "../engine";
import { mountFigures } from "../mount";
import { authoredRoutes, chipSplit, chipTitle, estimateHeight, idleOrder, leanRecord, linkedCount, passageOf, passageRecords, type Structures } from "./model";

export interface Links {
  node(id: string): string;
  beside(stage: Stage, anchor: string): string;
}

/** What a passage's bar needs from the page; a context, so that a change re-renders the bars and no text. */
export interface PassageBar {
  /** The record open in its sheet. */
  open: string | null;
  /** The records of the statement under the reading line. */
  inView: ReadonlySet<string>;
  onRecord(id: string, opener: HTMLElement, lean?: boolean): void;
  /** Light this record on the map beside the paper, or nothing. */
  onHover(id: string | null): void;
}

export const PassageBarContext = createContext<PassageBar>({ open: null, inView: new Set(),  onRecord() {}, onHover() {} });

export interface BodyHandle {
  /** Render these parts (and wait until they are laid out). */
  ensure(parts: number[]): Promise<void>;
  partElement(index: number): HTMLElement | null;
  /** Take the current reading position as the one to hold (after a scripted scroll). */
  reanchor(force?: boolean): void;
  /** Hold this element where it is now (the target of a jump). */
  hold(el: Element): void;
}

interface Props {
  stage: Stage;
  doc: PreparedDocument;
  structures: Structures;
  graph: ArgGraph;
  initial: number[];
  /** The passage open in the inspector, whose margin rule is lit. */
  inspected: string | null;
  onInspect(anchor: string, opener: HTMLElement): void;
  onSameTopic(anchor: string, opener: HTMLElement): void;
  /** The reading line, in viewport pixels from the top, used for height compensation. */
  topInset: number;
}

/** Rendered text runs this much taller than a placeholder's estimate (long record, 1440px). */
const TEXT_SCALE = 1.3;
const NEAR_MARGIN = "1500px 0px";
const IDLE_DELAY_MS = 1200;

type Idle = (cb: (deadline: { timeRemaining(): number }) => void) => number;
const requestIdle: Idle =
  typeof window !== "undefined" && "requestIdleCallback" in window
    ? (cb) => (window as unknown as { requestIdleCallback: Idle }).requestIdleCallback(cb)
    : (cb) => window.setTimeout(() => cb({ timeRemaining: () => 12 }), 120);
const cancelIdle = (id: number) => {
  const w = window as unknown as { cancelIdleCallback?: (id: number) => void; clearTimeout(id: number): void };
  if (w.cancelIdleCallback) w.cancelIdleCallback(id);
  else w.clearTimeout(id);
};

export const PaperBody = forwardRef<BodyHandle, Props>(function PaperBody(props, ref) {
  const { stage, doc, structures, graph, initial, topInset, inspected, onInspect, onSameTopic } = props;
  const [rendered, setRendered] = useState<ReadonlySet<number>>(() => new Set(initial));
  const elements = useRef(new Map<number, HTMLElement>());
  const waiters = useRef<{ parts: number[]; resolve: () => void }[]>([]);
  const renderedRef = useRef(rendered);
  renderedRef.current = rendered;
  const topRef = useRef(topInset);
  topRef.current = topInset;

  const add = useCallback((parts: number[]) => {
    const fresh = parts.filter((i) => i >= 0 && i < doc.parts.length);
    setRendered((prev) => {
      if (fresh.every((i) => prev.has(i))) return prev;
      const next = new Set(prev);
      fresh.forEach((i) => next.add(i));
      return next;
    });
  }, [doc]);

  // Scroll anchoring, done here so every browser behaves alike: the first
  // part starting inside the window (or the one straddling its top) keeps its
  // place when anything above it changes height (a part rendered, a figure
  // mounted, a route line arriving), so the text under the reader's eyes
  // never moves.
  const anchor = useRef<{ el: Element; top: number } | null>(null);
  // A jump's target stays the anchor until the reader scrolls by hand.
  const pinned = useRef(false);
  // The size of each part as the resize observer last reported it.
  const sizes = useRef(new Map<Element, number>());
  const reanchor = useCallback((force?: boolean, observed = false) => {
    const line = topRef.current;
    if (force) {
      elements.current.forEach((el) => sizes.current.set(el, el.getBoundingClientRect().height));
    } else if (!observed) {
      // A part has changed size and the observer has not yet heard it: keep
      // the anchor as it was, so the observer can move the page by the change.
      for (const [el, size] of sizes.current) if (Math.abs(el.getBoundingClientRect().height - size) > 0.5) return;
    }
    if (window.scrollY <= 0) {
      anchor.current = null;
      return;
    }
    const sorted = [...elements.current.entries()].sort((a, b) => a[0] - b[0]);
    // Binary search for the first part whose bottom is below the line.
    let lo = 0;
    let hi = sorted.length - 1;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (sorted[mid][1].getBoundingClientRect().bottom <= line) lo = mid + 1;
      else hi = mid;
    }
    let held: Element | null = null;
    for (let i = lo; i < sorted.length && !held; i++) {
      const part = sorted[i][1];
      const r = part.getBoundingClientRect();
      if (r.height === 0) continue;
      held = part;
      if (r.top >= line - 1) break;
      // The part straddles the line: hold the block the reader's eyes are on.
      // Its routes or end padding may be all that crosses it; then the
      // reader's eyes are on the next part.
      const text = part.querySelector(":scope > .part__text");
      if (text) {
        held = null;
        for (const child of Array.from(text.children)) {
          if (child.getBoundingClientRect().bottom > line) {
            held = child;
            break;
          }
        }
      }
    }
    anchor.current = held ? { el: held, top: held.getBoundingClientRect().top } : null;
  }, []);

  useImperativeHandle(
    ref,
    () => ({
      ensure: (parts) =>
        new Promise<void>((resolve) => {
          const wanted = parts.filter((i) => i >= 0 && i < doc.parts.length);
          if (wanted.every((i) => renderedRef.current.has(i))) {
            requestAnimationFrame(() => resolve());
            return;
          }
          waiters.current.push({ parts: wanted, resolve });
          add(wanted);
        }),
      partElement: (index) => elements.current.get(index) ?? null,
      reanchor,
      hold: (el) => {
        reanchor(true);
        anchor.current = { el, top: el.getBoundingClientRect().top };
        pinned.current = true;
      },
    }),
    [add, doc, reanchor],
  );

  // Resolve waiters once their parts are in the DOM and laid out.
  useLayoutEffect(() => {
    const ready = waiters.current.filter((w) => w.parts.every((i) => rendered.has(i)));
    if (!ready.length) return;
    waiters.current = waiters.current.filter((w) => !ready.includes(w));
    requestAnimationFrame(() => ready.forEach((w) => w.resolve()));
  }, [rendered]);

  // Parts within ~1500px of the viewport are rendered and kept.
  const nearObserver = useRef<IntersectionObserver | null>(null);
  useEffect(() => {
    const observer = new IntersectionObserver(
      (entries) => {
        const hits = entries.filter((e) => e.isIntersecting).map((e) => Number((e.target as HTMLElement).dataset.part));
        if (hits.length) add(hits);
      },
      { rootMargin: NEAR_MARGIN },
    );
    nearObserver.current = observer;
    elements.current.forEach((el) => observer.observe(el));
    return () => observer.disconnect();
  }, [add]);

  useEffect(() => {
    let frame = 0;
    const onScroll = () => {
      if (pinned.current || frame) return;
      frame = requestAnimationFrame(() => {
        frame = 0;
        if (!pinned.current) reanchor();
      });
    };
    const release = () => (pinned.current = false);
    window.addEventListener("scroll", onScroll, { passive: true });
    for (const type of ["wheel", "touchstart", "keydown", "pointerdown"]) window.addEventListener(type, release, { passive: true, capture: true });
    return () => {
      cancelAnimationFrame(frame);
      window.removeEventListener("scroll", onScroll);
      for (const type of ["wheel", "touchstart", "keydown", "pointerdown"]) window.removeEventListener(type, release, { capture: true });
    };
  }, [reanchor]);

  const resizeObserver = useRef<ResizeObserver | null>(null);
  useEffect(() => {
    // Parts keep their margins inside (display: flow-root), so any change in
    // the room a part takes is a size change this observer hears.
    const observer = new ResizeObserver((entries) => {
      for (const entry of entries) sizes.current.set(entry.target, entry.target.getBoundingClientRect().height);
      const held = anchor.current;
      if (held && held.el.isConnected) {
        const delta = held.el.getBoundingClientRect().top - held.top;
        if (Math.abs(delta) >= 0.5) window.scrollBy({ top: delta, behavior: "instant" as ScrollBehavior });
      }
      if (pinned.current && held?.el.isConnected) {
        anchor.current = { el: held.el, top: held.el.getBoundingClientRect().top };
      } else {
        // Delivered entries already update every changed part's cached size.
        // Reading all the other parts again makes each background insertion
        // scan the entire long paper; only locating the new anchor is needed.
        reanchor(false, true);
      }
    });
    resizeObserver.current = observer;
    elements.current.forEach((el) => observer.observe(el));
    return () => observer.disconnect();
  }, [reanchor]);

  const register = useCallback((index: number, el: HTMLElement | null) => {
    const map = elements.current;
    const prior = map.get(index);
    if (prior && prior !== el) {
      nearObserver.current?.unobserve(prior);
      resizeObserver.current?.unobserve(prior);
      sizes.current.delete(prior);
    }
    if (el) {
      map.set(index, el);
      nearObserver.current?.observe(el);
      resizeObserver.current?.observe(el);
    } else map.delete(index);
  }, []);

  // Idle time renders the rest, nearest the reader first. The costly step
  // (typesetting) runs inside the idle callback; React only inserts the HTML.
  useEffect(() => {
    let handle = 0;
    let stopped = false;
    const step = (deadline: { timeRemaining(): number }) => {
      if (stopped) return;
      const current = renderedRef.current;
      const centre = nearestPart(elements.current, topRef.current);
      const todo = idleOrder(doc.parts.length, centre).filter((i) => !current.has(i));
      if (!todo.length) return;
      const batch: number[] = [];
      while (todo.length && (batch.length === 0 || deadline.timeRemaining() > 10) && batch.length < 3) {
        const i = todo.shift()!;
        doc.render(i);
        batch.push(i);
      }
      add(batch);
      handle = requestIdle(step);
    };
    const timer = window.setTimeout(() => (handle = requestIdle(step)), IDLE_DELAY_MS);
    return () => {
      stopped = true;
      window.clearTimeout(timer);
      cancelIdle(handle);
    };
  }, [doc, add]);

  return (
    <div className="paper prose" data-stage={stage}>
      {doc.parts.map((part) => (
        <Part
          key={part.index}
          part={part}
          stage={stage}
          doc={doc}
          rendered={rendered.has(part.index)}
          structures={structures}
          graph={graph}
          lit={!!part.anchor && part.anchor === inspected}
          onInspect={onInspect}
          onSameTopic={onSameTopic}
          register={register}
        />
      ))}
    </div>
  );
});

export function nearestPart(elements: Map<number, HTMLElement>, line: number): number {
  const ordered = [...elements.entries()].sort((a, b) => a[0] - b[0]);
  if (!ordered.length) return 0;
  const rects = new Map<number, DOMRect>();
  const rect = (index: number) => {
    let value = rects.get(index);
    if (!value) {
      value = ordered[index][1].getBoundingClientRect();
      rects.set(index, value);
    }
    return value;
  };
  const firstEndingAt = (y: number) => {
    let lo = 0;
    let hi = ordered.length;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (rect(mid).bottom < y) lo = mid + 1;
      else hi = mid;
    }
    return lo;
  };
  // Parts remain in document order, including the placeholders. Locate the
  // reading line without laying out every part on each idle-rendering batch.
  const after = firstEndingAt(line);
  if (after === 0) return ordered[0][0];
  const before = rect(after - 1);
  if (after < ordered.length && Math.max(0, rect(after).top - line) < line - before.bottom) return ordered[after][0];
  // A blank part can share an end with its predecessor; keep the earlier part
  // on a tie, just as the former linear scan did.
  return ordered[firstEndingAt(before.bottom)][0];
}

interface PartProps {
  part: PreparedPart;
  stage: Stage;
  doc: PreparedDocument;
  rendered: boolean;
  structures: Structures;
  graph: ArgGraph;
  lit: boolean;
  onInspect(anchor: string, opener: HTMLElement): void;
  onSameTopic(anchor: string, opener: HTMLElement): void;
  register(index: number, el: HTMLElement | null): void;
}

const Part = memo(function Part({ part, stage, doc, rendered, structures, graph, lit, onInspect, onSameTopic, register }: PartProps) {
  const textRef = useRef<HTMLDivElement>(null);
  const html = useMemo(() => (rendered && !part.blank ? doc.render(part.index).html : null), [rendered, part, doc]);
  const anchor = part.kind === "passage" ? part.anchor : undefined;
  const passage = anchor ? passageOf(structures[stage], anchor) : undefined;
  const records = useMemo(() => passageRecords(passage), [passage]);
  const routed = useMemo(() => !!anchor && authoredRoutes(structures, stage, anchor).length > 0, [structures, stage, anchor]);
  const mapped = !!anchor && records.length > 0;
  const tools = !!anchor && (mapped || routed);

  useLayoutEffect(() => {
    if (!html || !textRef.current) return;
    const unmount = mountFigures(freshSlots(textRef.current));
    const unmark = markWideMaths(textRef.current);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);

  // The passage's controls sit under its opening heading (or above its first
  // line), inside the rendered text, so they read as part of the passage.
  const [slot, setSlot] = useState<HTMLElement | null>(null);
  useLayoutEffect(() => {
    const text = textRef.current;
    if (!html || !text || !tools) {
      setSlot(null);
      return;
    }
    const el = document.createElement("div");
    el.className = "passage-tools";
    let first = text.firstElementChild;
    while (first && first.matches("a.anchor")) first = first.nextElementSibling;
    if (first && /^H[1-6]$/.test(first.tagName)) first.after(el);
    else text.insertBefore(el, text.firstChild);
    setSlot(el);
    return () => el.remove();
  }, [html, tools]);

  const setRef = useCallback((el: HTMLElement | null) => register(part.index, el), [register, part.index]);
  const textSize = useMemo(() => ({ "--part-h": `${Math.round(estimateHeight(part, 680) * TEXT_SCALE)}px` }) as React.CSSProperties, [part]);

  if (part.blank) return <div ref={setRef} data-part={part.index} className="part part--blank" />;

  return (
    <section
      ref={setRef}
      data-part={part.index}
      data-passage={anchor}
      data-lit={lit ? "" : undefined}
      className={`part${mapped ? " part--mapped" : ""}${html ? "" : " part--pending"}`}
    >
      {html ? (
        <div ref={textRef} className="part__text" style={textSize} dangerouslySetInnerHTML={{ __html: html }} />
      ) : (
        <div className="part__placeholder" style={{ height: estimateHeight(part, 680) }} aria-hidden="true" />
      )}
      {slot &&
        anchor &&
        createPortal(
          <PassageTools stage={stage} anchor={anchor} records={records} structures={structures} graph={graph} lit={lit} onInspect={onInspect} onSameTopic={onSameTopic} />,
          slot,
        )}
    </section>
  );
});

function PassageTools({
  stage,
  anchor,
  records,
  structures,
  graph,
  lit,
  onInspect,
  onSameTopic,
}: {
  stage: Stage;
  anchor: string;
  records: string[];
  structures: Structures;
  graph: ArgGraph;
  lit: boolean;
  onInspect(anchor: string, opener: HTMLElement): void;
  onSameTopic(anchor: string, opener: HTMLElement): void;
}) {
  const { open, inView, onRecord, onHover } = useContext(PassageBarContext);
  const { shown, more } = chipSplit(records);
  const lean = useMemo(() => leanRecord(records, graph), [records, graph]);
  const linked = useMemo(() => linkedCount(structures, { stage, anchor }), [structures, stage, anchor]);
  return (
    <>
      {shown.map((id) => {
        const node = graph.nodes.get(id);
        const label = node?.label ?? id;
        return (
          <button
            key={id}
            type="button"
            className={`record-chip${node?.kind === "assumption" ? " record-chip--assumption" : ""}${node?.kind === "declaration" ? " lean" : ""}${inView.has(id) ? " is-here" : ""}`}
            aria-pressed={open === id}
            title={label}
            aria-label={`${label}. Open its record`}
            onClick={(event) => onRecord(id, event.currentTarget)}
            onPointerEnter={() => onHover(id)}
            onPointerLeave={() => onHover(null)}
            onFocus={() => onHover(id)}
            onBlur={() => onHover(null)}
          >
            {chipTitle(shortTitle(id, label))}
          </button>
        );
      })}
      {more > 0 && (
        <button
          type="button"
          className="passage-tools__records"
          aria-pressed={lit}
          aria-label={`All ${records.length} records linked to this passage`}
          onClick={(event) => onInspect(anchor, event.currentTarget)}
        >
          and {more} more
        </button>
      )}
      {lean && (
        <button type="button" className="passage-tools__lean" aria-label={`Lean for ${graph.nodes.get(lean)?.label ?? "this record"}`} onClick={(event) => onRecord(lean, event.currentTarget, true)}>
          Lean
        </button>
      )}
      <button type="button" className="passage-tools__topic" aria-haspopup="dialog" onClick={(event) => onSameTopic(anchor, event.currentTarget)}>
        {linked === 0 ? "Linked passages" : linked === 1 ? "1 linked passage" : `${linked} linked passages`}
      </button>
    </>
  );
}

/**
 * A display formula wider than its box scrolls inside it, natively, and keeps
 * its focus ring and MathML. Nothing is faded: the last condition is part of
 * the statement. Under an overflowing display a quiet row says it scrolls
 * ("Scroll formula →", "←" at the end, "↔" between) and offers "Expand",
 * a labelled dialog with the formula at full width.
 */
/** A display may shrink to this share of its size; past it, it breaks at a relation sign instead. */
const FIT_FLOOR = 0.8;
/** A numbered display cannot break without losing its number, so it may shrink further. */
const TAGGED_FLOOR = 0.72;
/** Space kept between a formula and its equation number, in pixels at full size. */
const TAG_GAP = 16;
/** Last resort before scrolling: a single unbreakable piece may shrink this far. */
const PIECE_FLOOR = 0.62;

interface Natural {
  /** The formula's width at full size, number excluded. */
  formula: number;
  /** The equation number's width at full size, or 0. */
  tag: number;
  /** The widest piece KaTeX cannot break, at full size. */
  widest: number;
  /** The runs between relation signs (groupRelationSegments), each with its width at full size. */
  segments: { el: HTMLElement; w: number }[];
}

/** A run between relation signs shorter than this many ems stays with the run before it ("n ≥ 1."). */
const TAIL_EM = 2.5;

/**
 * KaTeX splits a display into pieces after each relation sign, and a breaking
 * display wraps between them. A piece that starts inside brackets is joined to the
 * piece before it, so a bracketed condition such as "(0 ≤ t₁ < t₂ < 1)" never splits.
 * Runs once per formula; joined pieces render exactly as before when nothing wraps.
 */
export function joinBracketedPieces(math: HTMLElement): void {
  const html = math.querySelector<HTMLElement>(":scope > .katex-html");
  if (!html || html.dataset.joined) return;
  html.dataset.joined = "true";
  let depth = 0;
  let previous: HTMLElement | null = null;
  for (const piece of Array.from(html.querySelectorAll<HTMLElement>(":scope > .katex-base"))) {
    const inside = depth > 0;
    for (const mark of Array.from(piece.querySelectorAll(".mopen, .mclose"))) depth = Math.max(0, depth + (mark.classList.contains("mopen") ? 1 : -1));
    if (inside && previous) {
      while (piece.firstChild) previous.appendChild(piece.firstChild);
      piece.remove();
    } else previous = piece;
  }
}

/**
 * A breaking display breaks after a relation sign, not after a plus or minus: the pieces
 * between two relation signs are wrapped in one run (.math-seg), which stays on one line
 * while it fits ("1 − Ke^{−n/K}" never splits at its minus), and a run shorter than
 * `tail` pixels stays with the run before it. A run wider than the line opens and breaks
 * at its operators after all (fitDisplay). Runs once per formula, after joinBracketedPieces;
 * the runs change nothing while the display does not break.
 */
export function groupRelationRuns(math: HTMLElement, tail: number): void {
  const html = math.querySelector<HTMLElement>(":scope > .katex-html");
  if (!html || html.dataset.runs) return;
  html.dataset.runs = "true";
  const runs: HTMLElement[][] = [];
  let run: HTMLElement[] = [];
  const close = () => {
    if (run.length) runs.push(run);
    run = [];
  };
  for (const child of Array.from(html.children) as HTMLElement[]) {
    // An explicit line break or the equation number ends a run.
    if (!child.classList.contains("katex-base")) {
      close();
      continue;
    }
    run.push(child);
    if (endsWithRelation(child)) close();
  }
  close();
  const width = (r: HTMLElement[]) => r.reduce((sum, p) => sum + p.getBoundingClientRect().width, 0);
  for (let i = runs.length - 1; i > 0; i--) {
    const a = runs[i - 1];
    const b = runs[i];
    if (width(b) < tail && a[a.length - 1].nextElementSibling === b[0]) {
      a.push(...b);
      runs.splice(i, 1);
    }
  }
  for (const r of runs) {
    if (r.length < 2) continue;
    const seg = document.createElement("span");
    seg.className = "math-seg";
    r[0].before(seg);
    seg.append(...r);
  }
}

function endsWithRelation(piece: HTMLElement): boolean {
  const atoms = Array.from(piece.children).filter((c) => !c.classList.contains("mspace") && !c.classList.contains("katex-strut"));
  return !!atoms.length && atoms[atoms.length - 1].classList.contains("mrel");
}

function measureNatural(box: HTMLElement, math: HTMLElement): Natural {
  box.style.fontSize = "";
  delete box.dataset.fit;
  delete box.dataset.align;
  joinBracketedPieces(math);
  groupRelationRuns(math, TAIL_EM * (parseFloat(getComputedStyle(math).fontSize) || 16));
  const tag = box.querySelector<HTMLElement>(".katex-tag, .tag");
  const pieces = Array.from(math.querySelectorAll<HTMLElement>(":scope > .katex-html > .katex-base, :scope > .katex-html > .math-seg > .katex-base"));
  const widths = pieces.map((piece) => piece.getBoundingClientRect().width);
  const widest = Math.max(0, ...widths);
  const segments = Array.from(math.querySelectorAll<HTMLElement>(":scope > .katex-html > .math-seg")).map((el) => ({
    el,
    w: Array.from(el.children).reduce((sum, p) => sum + p.getBoundingClientRect().width, 0),
  }));
  if (!tag) return { formula: math.scrollWidth, tag: 0, widest, segments };
  // KaTeX stretches a numbered display to the full width and pins the number to
  // the right, so the formula's own width is the sum of its pieces.
  const formula = widths.reduce((sum, w) => sum + w, 0);
  return { formula, tag: tag.getBoundingClientRect().width, widest, segments };
}

/** At a breaking size, each run stays whole while it fits the line; a wider one opens to break at its operators. */
function openRuns(size: Natural, scale: number, available: number): void {
  for (const s of size.segments) s.el.toggleAttribute("data-open", s.w * scale > available);
}

/**
 * Fit a display formula to its column. An unnumbered display shrinks if that
 * keeps it at or above FIT_FLOOR of its size; otherwise it shrinks to the floor
 * and KaTeX breaks it between relation signs. A numbered display keeps its
 * formula clear of the number: it is centred when there is room, set flush
 * left when that is enough, and shrunk only as far as needed beyond that; if
 * even that is not enough, its number moves to a line of its own and the
 * formula breaks like an unnumbered one.
 * Widths are measured once at full size so repeated calls do not oscillate.
 */
function fitDisplay(box: HTMLElement, natural: WeakMap<HTMLElement, Natural>): void {
  const math = box.querySelector<HTMLElement>(":scope > .katex-display > .katex");
  // Two per cent of slack absorbs rounding in KaTeX's spacing, so a shrunk display really fits.
  const available = box.clientWidth * 0.98;
  if (!math || !available) return;
  let size = natural.get(box);
  if (!size) {
    size = measureNatural(box, math);
    natural.set(box, size);
  }
  if (size.tag) {
    const centred = size.formula + 2 * (size.tag + TAG_GAP);
    const flush = size.formula + size.tag + TAG_GAP;
    if (centred <= available + 1) {
      box.style.fontSize = "";
      delete box.dataset.fit;
      delete box.dataset.align;
      return;
    }
    box.dataset.align = "start";
    if (flush <= available + 1) {
      box.style.fontSize = "";
      delete box.dataset.fit;
      return;
    }
    const scale = available / flush;
    if (scale >= TAGGED_FLOOR) {
      box.style.fontSize = `${Math.floor(scale * 1000) / 1000}em`;
      box.dataset.fit = "scaled";
      return;
    }
    if (unbreakable(math)) return keepWhole(box);
    // Too wide even beside a small number: the number takes its own line under
    // the formula, and the formula breaks between relation signs.
    const tagged = breakSize(size, available);
    box.style.fontSize = `${tagged}em`;
    box.dataset.fit = "wrap-tagged";
    openRuns(size, tagged, available);
    return;
  }
  if (size.formula <= available + 1) {
    box.style.fontSize = "";
    delete box.dataset.fit;
    return;
  }
  const scale = available / size.formula;
  if (scale >= FIT_FLOOR) {
    box.style.fontSize = `${Math.floor(scale * 1000) / 1000}em`;
    box.dataset.fit = "scaled";
    return;
  }
  if (unbreakable(math)) return keepWhole(box);
  const wrap = breakSize(size, available);
  box.style.fontSize = `${wrap}em`;
  box.dataset.fit = "wrap";
  openRuns(size, wrap, available);
}

/** A cases or aligned block has rows and a brace: breaking it inline tears them apart. */
const unbreakable = (math: HTMLElement) => !!math.querySelector(".mtable");

/** Such a block keeps its shape at the smallest fitted size, and scrolls in its own box. */
function keepWhole(box: HTMLElement): void {
  box.style.fontSize = `${FIT_FLOOR}em`;
  box.dataset.fit = "scaled";
}

/** The size for a display that breaks: FIT_FLOOR, or smaller if its widest piece would still not fit. */
function breakSize(size: Natural, available: number): number {
  if (!size.widest || size.widest * FIT_FLOOR <= available) return FIT_FLOOR;
  return Math.max(Math.floor((available / size.widest) * 1000) / 1000, PIECE_FLOOR);
}

/** How far from the screen a formula is fitted, so it is ready before it arrives. */
const FIT_MARGIN = "900px 0px";

export function markWideMaths(root: HTMLElement): () => void {
  const boxes = Array.from(root.querySelectorAll<HTMLElement>(".math-display"));
  if (!boxes.length) return () => {};
  const cues = new Map<HTMLElement, HTMLElement>();
  const natural = new WeakMap<HTMLElement, Natural>();
  const widths = new WeakMap<HTMLElement, number>();
  let live = true;
  const update = (box: HTMLElement, force = false) => {
    const width = box.clientWidth;
    // Fitting can change a display's height, which the observer reports back.
    // Only a different available width (or newly loaded fonts) needs another
    // fit; scrolling a formula only changes its cue.
    if (force || widths.get(box) !== width) {
      fitDisplay(box, natural);
      widths.set(box, width);
    }
    // Only a formula that still does not fit after shrinking and breaking scrolls.
    const wide = box.scrollWidth > box.clientWidth + 1;
    if (box.dataset.overflow !== String(wide)) box.dataset.overflow = String(wide);
    const atStart = box.scrollLeft <= 1;
    const atEnd = box.scrollLeft + box.clientWidth >= box.scrollWidth - 2;
    if (box.dataset.scrolledEnd !== String(atEnd)) box.dataset.scrolledEnd = String(atEnd);
    let cue = cues.get(box);
    if (wide && !cue) {
      cue = makeCue(box);
      cues.set(box, cue);
      box.after(cue);
    }
    if (wide && !box.hasAttribute("tabindex")) {
      box.tabIndex = 0;
      box.setAttribute("role", "group");
      box.setAttribute("aria-label", "Formula wider than the column, scroll sideways to read it");
    }
    if (!cue) return;
    if (cue.hidden !== !wide) cue.hidden = !wide;
    const where = atStart ? "start" : atEnd ? "end" : "between";
    if (cue.dataset.at !== where) {
      cue.dataset.at = where;
      const scroll = cue.querySelector<HTMLButtonElement>(".math-cue__scroll")!;
      scroll.textContent = where === "start" ? "Scroll formula →" : where === "end" ? "← Scroll formula" : "Scroll formula ↔";
      scroll.setAttribute("aria-label", where === "end" ? "Scroll the formula back to its start" : "Scroll the formula to its end");
    }
  };
  const onScroll = (event: Event) => update(event.currentTarget as HTMLElement);
  boxes.forEach((b) => b.addEventListener("scroll", onScroll, { passive: true }));
  const observer = new ResizeObserver((entries) => entries.forEach((e) => update(e.target as HTMLElement)));
  const fitted = new Set<HTMLElement>();
  const fit = (box: HTMLElement) => {
    fitted.add(box);
    observer.observe(box);
    update(box);
  };
  // Each measurement forces a layout, so a formula is fitted as it comes near the screen.
  const near =
    typeof IntersectionObserver === "undefined"
      ? null
      : new IntersectionObserver(
          (entries) => {
            for (const entry of entries) {
              if (!entry.isIntersecting) continue;
              near?.unobserve(entry.target);
              fit(entry.target as HTMLElement);
            }
          },
          // scrollMargin reaches the same way through a scrolling column or sheet.
          { rootMargin: FIT_MARGIN, scrollMargin: FIT_MARGIN },
        );
  boxes.forEach((box) => (near ? near.observe(box) : fit(box)));
  // KaTeX's fonts can arrive after the first measurement; measure again once they have.
  if (document.fonts && document.fonts.status !== "loaded") {
    void document.fonts.ready.then(() => {
      if (!live) return;
      fitted.forEach((b) => natural.delete(b));
      fitted.forEach((box) => update(box, true));
    });
  }
  return () => {
    live = false;
    near?.disconnect();
    observer.disconnect();
    boxes.forEach((b) => b.removeEventListener("scroll", onScroll));
    cues.forEach((cue) => cue.remove());
  };
}

function makeCue(box: HTMLElement): HTMLElement {
  const cue = document.createElement("span");
  cue.className = "math-cue";
  const scroll = document.createElement("button");
  scroll.type = "button";
  scroll.className = "math-cue__scroll";
  scroll.addEventListener("click", () => {
    const atEnd = box.scrollLeft + box.clientWidth >= box.scrollWidth - 2;
    const smooth = !window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    box.scrollTo({ left: atEnd ? 0 : box.scrollWidth, behavior: smooth ? "smooth" : ("instant" as ScrollBehavior) });
  });
  const expand = document.createElement("button");
  expand.type = "button";
  expand.className = "math-cue__expand";
  expand.textContent = "Expand";
  expand.setAttribute("aria-haspopup", "dialog");
  expand.addEventListener("click", () => expandFormula(box, expand));
  cue.append(scroll, expand);
  return cue;
}

/** The formula alone, at full width, in a labelled modal dialog. */
function expandFormula(box: HTMLElement, opener: HTMLElement): void {
  const dialog = document.createElement("dialog");
  dialog.className = "modal modal--centre modal--formula";
  const id = `formula-${Math.random().toString(36).slice(2, 8)}`;
  dialog.setAttribute("aria-labelledby", id);
  dialog.dataset.modalOpen = "";
  const inner = document.createElement("div");
  inner.className = "modal__box";
  inner.innerHTML = `<header class="modal__bar"><h2 id="${id}" class="modal__title" tabindex="-1">Formula</h2><button type="button" class="modal__close" aria-label="Close the formula"><svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true"><path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg></button></header>`;
  const body = document.createElement("div");
  body.className = "modal__body prose formula-full";
  const copy = box.cloneNode(true) as HTMLElement;
  copy.removeAttribute("tabindex");
  copy.removeAttribute("role");
  copy.removeAttribute("aria-label");
  copy.querySelectorAll("[id]").forEach((el) => el.removeAttribute("id"));
  copy.className = "math-display";
  body.append(copy);
  inner.append(body);
  dialog.append(inner);
  // Inside the page's theme and type, next to the formula's own styles.
  (box.closest(".reader, .panel, .pane") ?? document.body).append(dialog);
  const close = () => {
    dialog.close();
    dialog.remove();
    if (opener.isConnected) opener.focus({ preventScroll: true });
  };
  dialog.addEventListener("cancel", (event) => {
    event.preventDefault();
    close();
  });
  dialog.addEventListener("click", (event) => event.target === dialog && close());
  inner.querySelector<HTMLButtonElement>(".modal__close")!.addEventListener("click", close);
  dialog.showModal();
  inner.querySelector<HTMLElement>(".modal__title")!.focus({ preventScroll: true });
}

/**
 * Give every figure slot not currently mounted a fresh element: a root being
 * unmounted after a tick (strict mode runs effects twice) still owns the old one.
 */
export function freshSlots(root: HTMLElement): HTMLElement {
  root.querySelectorAll<HTMLElement>("[data-figure-slot]").forEach((slot) => {
    if (slot.dataset.mounted) return;
    slot.replaceWith(slot.cloneNode(false));
  });
  return root;
}

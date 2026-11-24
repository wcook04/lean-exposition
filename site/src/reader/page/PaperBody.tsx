// The paper itself, part by part. Every prepared part is its own element;
// parts near the viewport are rendered, the rest wait as placeholders sized
// from their byte length and are rendered in idle time. Heights that change
// above the reading line are compensated, so the line a reader is on never
// moves. Each tied statement carries a tick in the margin (statements.ts), and nothing else
// stands between the paragraphs: a passage's steps and links are on the right page.

import { forwardRef, memo, useCallback, useEffect, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../../api/types";
import type { ArgGraph } from "../../model/graph";
import type { PreparedDocument, PreparedPart } from "../engine";
import { renderTex } from "../math";
import { mountFigures } from "../mount";
import { checksMentionedBy, LaterCheckNote } from "../../lean/ours";
import { breakForms, splitDisplay } from "../texBreaks";
import { useReferences } from "./RefInset";
import { DESKTOP_MEASURE, estimateHeight, idleOrder, passageOf, passageRecords, type Structures } from "./model";
import { sectionAidFor } from "../engine";
import site from "@instance/site";
import type { Statements } from "./statements";

export interface Links {
  node(id: string): string;
  beside(stage: Stage, anchor: string): string;
}

export interface BodyHandle {
  /** Render these parts (and wait until they are laid out). */
  ensure(parts: number[]): Promise<void>;
  partElement(index: number): HTMLElement | null;
  /** Take the current reading position as the one to hold (after a scripted scroll). */
  reanchor(force?: boolean): void;
  /** Hold this element where it is now (the target of a jump). */
  hold(el: Element): void;
  /** Lay out the jump's parts at their real height. The scroll anchor holds through formula fitting. */
  settle(parts: number[]): void;
}

interface Props {
  stage: Stage;
  doc: PreparedDocument;
  structures: Structures;
  /** Kept for the callers that build the page around it. */
  graph?: ArgGraph;
  initial: number[];
  /** The passage open in the inspector, whose margin rule is lit. */
  inspected: string | null;
  /** Told when a part's text reaches the page, for its ties. */
  statements?: Statements;
  /** "See its Lean" in a reference's inset: open this record's slice as a click on its statement would. */
  onReferenceLean?(record: string, at: string | undefined): void;
  /** The reading line, in viewport pixels from the top, used for height compensation. */
  topInset: number;
}

const NEAR_MARGIN = "1500px 0px";
const IDLE_DELAY_MS = 300;
/** How many parts each side of the reader idle time prepares ahead. */
const AHEAD_PARTS = 2;
/** Laying out ahead of the reader waits until the page has been still this long. */
const STILL_MS = 250;
/** Fitting ahead takes this long at a time: an idle period can run to 50ms, and a task that long is one a reader can feel. */
const AHEAD_BUDGET_MS = 10;

type IdleDeadline = { timeRemaining(): number };
type Idle = (cb: (deadline: IdleDeadline) => void) => number;
const requestIdle: Idle =
  typeof window !== "undefined" && "requestIdleCallback" in window
    ? (cb) => (window as unknown as { requestIdleCallback: Idle }).requestIdleCallback(cb)
    : (cb) => window.setTimeout(() => cb({ timeRemaining: () => 12 }), 120);
const cancelIdle = (id: number) => {
  const w = window as unknown as { cancelIdleCallback?: (id: number) => void; clearTimeout(id: number): void };
  if (w.cancelIdleCallback) w.cancelIdleCallback(id);
  else w.clearTimeout(id);
};

const noLean = () => {};

export const PaperBody = forwardRef<BodyHandle, Props>(function PaperBody(props, ref) {
  const { stage, doc, structures, initial, topInset, inspected, statements, onReferenceLean } = props;
  const handle = useRef<BodyHandle | null>(null);
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
  // `scroll` is where the page stood when `top` was read: only a change of layout moves the
  // page back, never a scroll that arrived in the same frame as a change of height.
  const anchor = useRef<{ el: Element; top: number; scroll: number } | null>(null);
  // A jump's target stays the anchor until the reader scrolls by hand.
  const pinned = useRef(false);
  // The size of each part as the resize observer last reported it.
  const sizes = useRef(new Map<Element, number>());
  const scrolledAt = useRef(0);
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
    anchor.current = held ? { el: held, top: held.getBoundingClientRect().top, scroll: window.scrollY } : null;
  }, []);

  useImperativeHandle(
    ref,
    () => {
      const value: BodyHandle = {
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
        anchor.current = { el, top: el.getBoundingClientRect().top, scroll: window.scrollY };
        pinned.current = true;
      },
      settle: (parts) => {
        for (const index of parts) {
          const text = elements.current.get(index)?.querySelector(":scope > .part__text");
          if (text) layOutWhole(stage, index);
        }
      },
      };
      handle.current = value;
      return value;
    },
    [add, doc, reanchor, stage],
  );
  const references = useReferences(stage, doc, handle, useCallback(() => topRef.current, []), onReferenceLean ?? noLean);

  // The parts in the window when the paper first mounts are laid out whole from the first frame.
  // Content-visibility decides a part is on screen only after a first layout at its reserved height,
  // and then lays it out again at its real one: under the first screen that moved the text below.
  useLayoutEffect(() => {
    const top = -window.innerHeight / 2;
    const bottom = window.innerHeight * 1.5;
    elements.current.forEach((el, index) => {
      const r = el.getBoundingClientRect();
      if (r.bottom > top && r.top < bottom) layOutWhole(stage, index);
    });
    // Once, for the paper as it first stands.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

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
      scrolledAt.current = performance.now();
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
        const delta = held.el.getBoundingClientRect().top + window.scrollY - held.top - held.scroll;
        if (Math.abs(delta) >= 0.5) window.scrollBy({ top: delta, behavior: "instant" as ScrollBehavior });
      }
      if (pinned.current && held?.el.isConnected) {
        anchor.current = { el: held.el, top: held.el.getBoundingClientRect().top, scroll: window.scrollY };
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

  // Idle time works outwards from the reader, one part at a time: it renders the part, then
  // lays it out and fits its formulas while the page is still. A part's first layout is the
  // longest single task the paper has, and taking it here keeps it out of a fast scroll.
  // Nothing moves: a part held off the screen keeps its reserved height until it comes near.
  // The costly step (typesetting) runs inside the idle callback; React only inserts the HTML.
  useEffect(() => {
    let handle = 0;
    let stopped = false;
    let waiting = 0;
    const prepared = new Set<number>();
    const still = () => performance.now() - scrolledAt.current >= STILL_MS;
    const step = (deadline: IdleDeadline) => {
      if (stopped) return;
      const current = renderedRef.current;
      const centre = nearestPart(elements.current, topRef.current);
      // Only the parts around the reader are prepared ahead; the rest render as they come near
      // (nearObserver) or when a jump asks for them (ensure), so a long paper is soon still.
      const order = idleOrder(doc.parts.length, centre).filter((i) => Math.abs(i - centre) <= AHEAD_PARTS);
      const next = order.find((i) => !prepared.has(i));
      if (next === undefined) return;
      if (current.has(next) && still()) {
        const text = elements.current.get(next)?.querySelector<HTMLElement>(":scope > .part__text");
        const until = performance.now() + AHEAD_BUDGET_MS;
        if (!text || layOutAhead(text, () => performance.now() < until && deadline.timeRemaining() > 1 && still())) prepared.add(next);
        handle = requestIdle(step);
        return;
      }
      const todo = order.filter((i) => !current.has(i));
      if (!todo.length) {
        // All rendered, and the reader is moving: what is left waits for them to stop.
        waiting = window.setTimeout(() => (handle = requestIdle(step)), STILL_MS);
        return;
      }
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
      window.clearTimeout(waiting);
      cancelIdle(handle);
    };
  }, [doc, add]);

  return (
    <div
      className="paper prose"
      data-stage={stage}
      onClick={references.onClick}
      onPointerOver={references.onPointerOver}
      onPointerOut={references.onPointerOut}
      onFocus={references.onFocus}
      onBlur={references.onBlur}
    >
      {doc.parts.map((part) => (
        <Part
          key={part.index}
          part={part}
          stage={stage}
          doc={doc}
          rendered={rendered.has(part.index)}
          structures={structures}
          lit={!!part.anchor && part.anchor === inspected}
          statements={statements}
          register={register}
        />
      ))}
      {references.portals}
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
  lit: boolean;
  statements?: Statements;
  register(index: number, el: HTMLElement | null): void;
}

const Part = memo(function Part({ part, stage, doc, rendered, structures, lit, statements, register }: PartProps) {
  const textRef = useRef<HTMLDivElement>(null);
  // Tones, hints and bracket-joined formula pieces go into the markup before it is placed, so a part
  // arriving on the page is written once and then left still.
  // Every part's words are on the page from the start, so the browser's own find reaches the whole
  // paper: a part not yet typeset shows its formulas as TeX source, and content-visibility keeps it
  // out of layout and paint until it comes near (or find reveals it), when it is typeset once.
  const html = useMemo(() => {
    if (part.blank) return null;
    if (!rendered) return statements ? statements.decorate(doc.renderPlain(part.index).html) : doc.renderPlain(part.index).html;
    const raw = doc.render(part.index).html;
    return prepareMarkup(statements ? statements.decorate(raw) : raw);
  }, [rendered, part, doc, statements]);
  const anchor = part.kind === "passage" ? part.anchor : undefined;
  const passage = anchor ? passageOf(structures[stage], anchor) : undefined;
  const records = useMemo(() => passageRecords(passage), [passage]);
  const mapped = !!anchor && records.length > 0;
  // A later check this passage mentions (a library paper's checks, read before the first render), shown
  // after it from the start, so the part never grows once it is on the page.
  const checks = useMemo(() => (part.blank ? [] : checksMentionedBy(doc.renderPlain(part.index).html.replace(/<[^>]*>/g, " "))), [part, doc]);

  useLayoutEffect(() => {
    if (!html || !rendered || !textRef.current) return;
    const unmount = mountFigures(freshSlots(textRef.current));
    const unmark = markWideMaths(textRef.current);
    statements?.adopt(part.index, textRef.current.parentElement);
    return () => {
      statements?.adopt(part.index, null);
      unmount();
      unmark();
    };
  }, [html, rendered, statements, part.index]);

  const setRef = useCallback((el: HTMLElement | null) => register(part.index, el), [register, part.index]);
  // The same height before and after the text arrives, so rendering a part far away moves nothing.
  const reserved = useMemo(() => {
    const aids = site.sectionAids?.[doc.stage];
    const aided = aids ? part.headings.filter((heading) => heading.level >= 2 && sectionAidFor(aids, heading.title)).length : 0;
    // The column's width as the page is laid out now: half the window beside the pane from 1024 to 1359px.
    const wide = typeof window === "undefined" ? DESKTOP_MEASURE : window.innerWidth;
    const measure = wide >= 1024 && wide < 1360 ? Math.min(DESKTOP_MEASURE, wide / 2) : DESKTOP_MEASURE;
    return estimateHeight(part, aided, measure);
  }, [part, doc.stage]);
  const textSize = useMemo(() => ({ "--part-h": `${reserved}px` }) as React.CSSProperties, [reserved]);

  if (part.blank) return <div ref={setRef} data-part={part.index} data-passage={anchor} className="part part--blank" />;

  return (
    <section
      ref={setRef}
      data-part={part.index}
      data-passage={anchor}
      data-lit={lit ? "" : undefined}
      className={`part${mapped ? " part--mapped" : ""}${rendered ? "" : " part--pending"}`}
    >
      {html ? (
        <div ref={textRef} className="part__text" style={textSize} dangerouslySetInnerHTML={{ __html: html }} />
      ) : (
        <div className="part__placeholder" style={{ height: reserved }} aria-hidden="true" />
      )}
      {checks.map((check) => <LaterCheckNote key={check.constant} check={check} />)}
    </section>
  );
});

/**
 * A display formula never scrolls sideways and is never cut off. Fitted to its column it
 *  1. stays as written when it fits: centred beside its number, or flush left when that is enough;
 *  2. else shrinks, to no less than FIT_FLOOR of its size, its number keeping its own size;
 *  3. else takes the first of its broken forms that fits at FIT_FLOOR or above: independent
 *     formulas stacked, then a line per relation sign, then long sums split at plus and minus
 *     (texBreaks.ts), its number on the last line;
 *  4. else, with no form that fits, shrinks its best form below the floor until it fits, and
 *     offers "Expand": a dialog with the formula as large as the window allows.
 * Each form is typeset and measured once, at full size, so a refit never oscillates.
 */
/** A display may shrink to this share of its size before it breaks. */
const FIT_FLOOR = 0.88;
/** Space kept between a formula and its equation number, in pixels. */
const TAG_GAP = 16;

interface Natural {
  /** The formula's width at full size, number excluded, in pixels. */
  formula: number;
  /** The equation number's width, or 0. */
  tag: number;
  /** The formula's font size at full size, in pixels. */
  font: number;
}

interface Forms {
  /** Each form's KaTeX markup (its .katex-display): the display as written, then its broken forms once typeset. */
  html: (string | null | undefined)[];
  /** The broken forms' TeX, without the number (texBreaks.ts). */
  tex: string[];
  natural: (Natural | undefined)[];
  shown: number;
}

const formsOf = new WeakMap<HTMLElement, Forms>();

/**
 * Set a display up for fitting, once. A display with one equation number gets that number as
 * its own element beside the formula (.math-number), so the formula can shrink or break while
 * the number keeps its size and sits on the formula's last line; KaTeX's own number is hidden.
 */
function formsFor(box: HTMLElement): Forms {
  let forms = formsOf.get(box);
  if (forms) return forms;
  const display = box.querySelector<HTMLElement>(":scope > .katex-display");
  const tex = box.querySelector('.katex-mathml annotation[encoding="application/x-tex"]')?.textContent ?? "";
  const tags = display ? display.querySelectorAll(".katex-tag, .tag") : [];
  // The engine sets a plain number up already (engine.ts); one with markup is set up here.
  const set = !!box.querySelector(":scope > .math-number");
  const single = set || (tags.length === 1 && (tex.match(/\\tag\b/g) ?? []).length === 1 && !!splitDisplay(tex).tag);
  if (single && !set) {
    const number = document.createElement("span");
    number.className = "katex math-number";
    number.textContent = (tags[0].textContent ?? "").replace(/[​\s]+/g, "");
    box.append(number);
    box.dataset.number = "";
  }
  forms = { html: [display?.outerHTML ?? null], tex: tex ? breakForms(tex, { number: !single }) : [], natural: [], shown: 0 };
  formsOf.set(box, forms);
  return forms;
}

/** Show form `k` (typesetting it the first time). False when that form cannot be typeset. */
function showForm(box: HTMLElement, forms: Forms, k: number): boolean {
  if (forms.html[k] === undefined) {
    const result = renderTex(forms.tex[k - 1], true);
    forms.html[k] = result.error ? null : result.html;
  }
  const html = forms.html[k];
  if (html == null) return false;
  if (forms.shown !== k) {
    const display = box.querySelector(":scope > .katex-display");
    if (!display) return false;
    const holder = document.createElement("template");
    holder.innerHTML = html;
    display.replaceWith(holder.content);
    forms.shown = k;
  }
  // A broken form's number sits on its last line.
  const lines = k > 0 ? "" : undefined;
  if (box.dataset.lines !== lines) {
    if (lines === undefined) delete box.dataset.lines;
    else box.dataset.lines = lines;
  }
  return true;
}

const mathOf = (box: HTMLElement) => box.querySelector<HTMLElement>(":scope > .katex-display > .katex");
const numberOf = (box: HTMLElement) =>
  box.querySelector<HTMLElement>(":scope > .math-number") ?? box.querySelector<HTMLElement>(".katex-tag, .tag");

function setScale(box: HTMLElement, size: Natural, scale: number): void {
  const math = mathOf(box);
  const font = scale >= 1 ? "" : `${Math.floor(size.font * scale * 100) / 100}px`;
  if (math && math.style.fontSize !== font) math.style.fontSize = font;
}

function measureNatural(box: HTMLElement, forms: Forms, k: number): Natural | undefined {
  if (forms.natural[k]) return forms.natural[k];
  if (!showForm(box, forms, k)) return undefined;
  const math = mathOf(box);
  if (!math) return undefined;
  math.style.fontSize = "";
  delete box.dataset.align;
  if (k === 0) joinBracketedPieces(math);
  const font = parseFloat(getComputedStyle(math).fontSize) || 16;
  const number = numberOf(box);
  let size: Natural;
  if (!number || box.dataset.number !== undefined) {
    // The formula alone: its own number, if any, is a separate element.
    size = { formula: math.scrollWidth, tag: number ? number.getBoundingClientRect().width : 0, font };
    // The space a centred formula keeps free on its left, the number's width (reader-content.css).
    const free = number ? `${Math.ceil(size.tag)}px` : "";
    if (box.style.getPropertyValue("--number-w") !== free) box.style.setProperty("--number-w", free);
  } else {
    // KaTeX's own number (a display with several): KaTeX stretches the display to the full
    // width and pins the numbers to the right, so the formula's width is the sum of its pieces.
    const pieces = Array.from(math.querySelectorAll<HTMLElement>(":scope > .katex-html > .katex-base"));
    const formula = pieces.reduce((sum, piece) => sum + piece.getBoundingClientRect().width, 0);
    size = { formula, tag: number.getBoundingClientRect().width, font };
  }
  forms.natural[k] = size;
  return size;
}

/** The scale at which a form fits `available` pixels, its number at full size, and where it sits. */
export function scaleToFit(size: Pick<Natural, "formula" | "tag">, available: number): { scale: number; start: boolean } {
  if (!size.formula) return { scale: 1, start: false };
  if (!size.tag) return { scale: Math.min(1, available / size.formula), start: false };
  if (size.formula + 2 * (size.tag + TAG_GAP) <= available + 1) return { scale: 1, start: false };
  const room = available - size.tag - TAG_GAP;
  return { scale: Math.min(1, Math.max(0, room) / size.formula), start: true };
}

/** Choose a display's form and size for its column (see above). */
function fitDisplay(box: HTMLElement): void {
  // Two per cent of slack absorbs rounding in KaTeX's spacing, so a shrunk display really fits.
  const available = box.clientWidth * 0.98;
  if (!available || !mathOf(box)) return;
  const forms = formsFor(box);
  let choice: { k: number; scale: number; start: boolean; size: Natural } | null = null;
  for (let k = 0; k <= forms.tex.length; k++) {
    const size = measureNatural(box, forms, k);
    if (!size) continue;
    const fit = scaleToFit(size, available);
    if (fit.scale >= FIT_FLOOR) {
      choice = { k, ...fit, size };
      break;
    }
    if (!choice || fit.scale > choice.scale) choice = { k, ...fit, size };
  }
  if (!choice) return;
  showForm(box, forms, choice.k);
  let scale = Math.floor(choice.scale * 1000) / 1000;
  setScale(box, choice.size, scale);
  // What is drawn must lie inside the column: if KaTeX's spacing still reaches past it, shrink
  // the formula by what remains, once.
  // Font sizes round to whole device pixels and KaTeX's spacing does not scale exactly, so check
  // again after each step, a few times at most.
  for (let step = 0; step < 4; step++) {
    const extent = formulaExtent(box);
    if (!(extent > box.clientWidth + 0.5 && extent > 0)) break;
    const tagPart = choice.size.tag ? choice.size.tag + TAG_GAP : 0;
    scale = Math.floor(scale * Math.max(0, box.clientWidth - tagPart) / Math.max(1, extent - tagPart) * 0.99 * 1000) / 1000;
    setScale(box, choice.size, scale);
  }
  const fit = scale >= 1 ? undefined : scale >= FIT_FLOOR ? "scaled" : "squeezed";
  if (box.dataset.fit !== fit) {
    if (fit) box.dataset.fit = fit;
    else delete box.dataset.fit;
  }
  const form = choice.k ? String(choice.k) : undefined;
  if (box.dataset.form !== form) {
    if (form) box.dataset.form = form;
    else delete box.dataset.form;
  }
  if (choice.start) {
    if (box.dataset.align !== "start") box.dataset.align = "start";
  } else if (box.dataset.align) delete box.dataset.align;
}

/** Measure again (the fonts changed): every form's natural size is stale. */
function forgetSizes(box: HTMLElement): void {
  const forms = formsOf.get(box);
  if (forms) forms.natural = [];
}

/**
 * KaTeX splits a display into pieces after each relation sign. A piece that starts inside
 * brackets is joined to the piece before it, so a bracketed condition such as
 * "(0 ≤ t₁ < t₂ < 1)" is one piece. Runs once per formula; joined pieces render exactly as before.
 */
/** Join bracketed formula pieces in a part's markup, before it is placed (see joinBracketedPieces). */
function prepareMarkup(html: string): string {
  if (typeof document === "undefined" || !html.includes("katex-display")) return html;
  const box = document.createElement("template");
  box.innerHTML = html;
  for (const math of Array.from(box.content.querySelectorAll<HTMLElement>(".math-display > .katex-display > .katex"))) joinBracketedPieces(math);
  return box.innerHTML;
}

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
 * Whether one of KaTeX's faces is still on its way. A formula measured in a fallback face is
 * measured wrong, so fitting waits for KaTeX's own faces; other faces (the Lean's mono, the
 * serif's italic) arriving later do not change a formula's width and do not hold it up.
 */
function katexLoading(): boolean {
  if (typeof document === "undefined" || !document.fonts) return false;
  if (document.fonts.status === "loaded") return false;
  // Without a list of faces, any face loading counts.
  if (typeof (document.fonts as unknown as Iterable<FontFace>)[Symbol.iterator] !== "function") return true;
  for (const face of document.fonts) if (face.status === "loading" && face.family.replace(/["']/g, "").startsWith("KaTeX")) return true;
  return false;
}

/** Resolves once no KaTeX face is loading (checked again after each arrives). */
function katexReady(): Promise<void> {
  if (typeof (document.fonts as unknown as Iterable<FontFace>)[Symbol.iterator] !== "function") return document.fonts.ready as unknown as Promise<void>;
  const loading = [...document.fonts].filter((face) => face.status === "loading" && face.family.replace(/["']/g, "").startsWith("KaTeX"));
  if (!loading.length) return Promise.resolve();
  return Promise.allSettled(loading.map((face) => face.loaded)).then(() => (katexLoading() ? katexReady() : undefined));
}

/**
 * Parts laid out whole whatever their distance from the window, as rules of a stylesheet of their
 * own rather than marks on the page, so that laying a part out changes nothing a reader (or a
 * check for stillness) could see in the document. They keep the containment content-visibility
 * gives every other part, so nothing in them reaches past the column and widens the page.
 */
let wholeSheet: CSSStyleSheet | null = null;
const laidWhole = new Set<string>();
function layOutWhole(stage: string, index: number): void {
  const key = `${stage}:${index}`;
  if (laidWhole.has(key) || typeof CSSStyleSheet === "undefined" || !("adoptedStyleSheets" in document)) return;
  if (!wholeSheet) {
    wholeSheet = new CSSStyleSheet();
    document.adoptedStyleSheets = [...document.adoptedStyleSheets, wholeSheet];
  }
  laidWhole.add(key);
  wholeSheet.insertRule(`.paper[data-stage="${CSS.escape(stage)}"] .part[data-part="${index}"] > .part__text { content-visibility: visible; contain: layout style paint; }`);
}

/** How far from the window idle time fits a part's formulas ahead of the reader, in pixels. */
const AHEAD_REACH = 2400;

/** How far from the screen a formula is fitted, so it is ready before it arrives. */
const FIT_MARGIN = "900px 0px";

/** A display's width read forces layout. Share a frame budget across all paper parts and quotes. */
const visibleFits: (() => void)[] = [];
const aheadFits: (() => void)[] = [];
let fitFrame = 0;
const FIT_BUDGET_MS = 12;

function onScreen(rect: DOMRectReadOnly): boolean {
  return rect.height > 0 && rect.bottom > 0 && rect.top < window.innerHeight;
}

function queueFit(work: () => void, visible: boolean): void {
  (visible ? visibleFits : aheadFits).push(work);
  fitFrame ||= requestAnimationFrame(drainFits);
}

function drainFits() {
  const until = performance.now() + FIT_BUDGET_MS;
  while ((visibleFits.length || aheadFits.length) && performance.now() < until) (visibleFits.shift() ?? aheadFits.shift())!();
  fitFrame = visibleFits.length || aheadFits.length ? requestAnimationFrame(drainFits) : 0;
}

/** Each part's formulas not yet fitted; it stops when `more` says so and reports whether it finished. */
const fitters = new WeakMap<HTMLElement, (more: () => boolean, everywhere?: boolean) => boolean>();
const laidOut = new WeakSet<HTMLElement>();

/**
 * Do now what a part would otherwise need the moment it comes near. Reading a position inside
 * it lays it out, even while it is held off the screen. That first layout is also what asks for
 * any new KaTeX face, so when it does, its formulas are fitted on a later visit, once the fonts have settled:
 * a width measured in a fallback font is wrong for good. Reading again leaves nothing to redo.
 * True when the part is finished.
 */
function layOutAhead(text: HTMLElement, more: () => boolean): boolean {
  const first = text.firstElementChild;
  if (!laidOut.has(text)) {
    laidOut.add(text);
    first?.getBoundingClientRect();
    // A layout that asked for no new KaTeX face can be fitted at once, in this same visit.
    if (katexLoading()) return false;
  }
  if (katexLoading()) return false;
  const fitter = fitters.get(text);
  if (fitter && !fitter(more)) return false;
  first?.getBoundingClientRect();
  return true;
}

/**
 * How far right a display's formula and its equation number reach, from the start of the
 * box's scrolled content. The box's scrollWidth is not this: KaTeX draws each vertical list
 * with a 2px strut past its edge (.vlist-s), so a number set flush against the right edge
 * reports a scrollWidth 2px wider than the column although every glyph fits. A display
 * KaTeX did not render (a fallback) has only its scrollWidth.
 */
export function formulaExtent(box: HTMLElement): number {
  const html = box.querySelector<HTMLElement>(":scope > .katex-display > .katex > .katex-html");
  if (!html) return box.scrollWidth;
  const parts = [
    ...Array.from(html.querySelectorAll<HTMLElement>(":scope > .katex-base, :scope > .katex-tag, :scope > .tag")),
    ...Array.from(box.querySelectorAll<HTMLElement>(":scope > .math-number")),
  ];
  if (!parts.length) return box.scrollWidth;
  const start = box.getBoundingClientRect().left + box.clientLeft - box.scrollLeft;
  let right = 0;
  for (const part of Array.from(parts)) right = Math.max(right, part.getBoundingClientRect().right - start);
  return right;
}

/**
 * A display as a quotation (a phrase card's quote): the formula as written, with its number,
 * free of the sizes and forms its column chose, so the card fits it to its own width.
 */
export function quoteOfDisplay(box: HTMLElement): string {
  let display = formsOf.get(box)?.html[0];
  if (!display) {
    const copy = box.querySelector<HTMLElement>(":scope > .katex-display")?.cloneNode(true) as HTMLElement | undefined;
    copy?.querySelectorAll<HTMLElement>("[style]").forEach((el) => el.style.removeProperty("font-size"));
    display = copy?.outerHTML ?? "";
  }
  const number = box.querySelector(":scope > .math-number")?.outerHTML ?? "";
  return `<div class="math-display"${number ? ' data-number=""' : ""}>${display}${number}</div>`;
}

/** A display drawn, as it stands, past its column's edge (formula or number). */
function overflowsColumn(box: HTMLElement): boolean {
  const math = mathOf(box);
  return Math.max(formulaExtent(box), math ? math.scrollWidth : 0) > box.clientWidth + 1;
}

/** Displays fitted at least once, across mounts. */
const widthsSeen = new WeakSet<HTMLElement>();

/** KaTeX's main faces, the ones most formulas are drawn in, are loaded (or there is no font API). */
function katexFacesReady(): boolean {
  const fonts = typeof document === "undefined" ? undefined : document.fonts;
  if (!fonts) return true;
  if (typeof fonts.check === "function") {
    try {
      return fonts.check("1em KaTeX_Main") && fonts.check("italic 1em KaTeX_Math");
    } catch {
      /* fall through */
    }
  }
  return fonts.status === "loaded";
}

function katexFacesLoaded(): Promise<unknown> {
  const fonts = document.fonts;
  if (typeof fonts?.load !== "function") return fonts?.ready ?? Promise.resolve();
  return Promise.all([fonts.load("1em KaTeX_Main"), fonts.load("italic 1em KaTeX_Math")]).catch(() => undefined);
}

/** Fit every display under a root markWideMaths has set up, now, wherever it is. */
export function fitNow(root: HTMLElement): void {
  fitters.get(root)?.(() => true, true);
}

export function markWideMaths(root: HTMLElement, offerExpand = true): () => void {
  const boxes = Array.from(root.querySelectorAll<HTMLElement>(".math-display"));
  if (!boxes.length) return () => {};
  // Until it is first fitted a display is hidden, so a formula wider than its column is never
  // seen cut off by the column's edge before the fitter has shrunk or broken it.
  // Only a display wider than its column is hidden: one that already fits is shown as it is, and
  // fitting it later writes nothing, so a display that needs no change never changes the page.
  // (All the widths are read before any is written, in one layout.)
  const wide = boxes.filter((box) => !widthsSeen.has(box) && box.dataset.unfitted === undefined && overflowsColumn(box));
  for (const box of wide) box.dataset.unfitted = "";
  const cues = new Map<HTMLElement, HTMLElement>();
  const widths = new WeakMap<HTMLElement, { now: number; before: number | null; at: number }>();
  let live = true;
  /** Displays last measured while a KaTeX face was loading: the only ones a font's arrival refits. */
  const stale = new Set<HTMLElement>();
  const refitStale = () => {
    const boxes = [...stale];
    stale.clear();
    boxes.forEach((box) => {
      queueFit(() => {
        if (!live) return;
        forgetSizes(box);
        update(box, true);
      }, onScreen(box.getBoundingClientRect()));
    });
  };
  const update = (box: HTMLElement, force = false) => {
    const width = box.clientWidth;
    // Fitting can change a display's height, which the observer reports back, and a height can
    // bring a scroll bar to the column, which narrows it. Only a different available width (or
    // newly loaded fonts) needs another fit, and a width that returns within a second to the one
    // before the last is that loop answering itself: the last decision stands.
    const seen = widths.get(box);
    const changed = !seen || Math.abs(seen.now - width) > 1;
    const flipBack = !!seen && seen.before !== null && Math.abs(seen.before - width) <= 1 && performance.now() - seen.at < 1000;
    if (force || (changed && !flipBack)) {
      fitDisplay(box);
      // Measured while a KaTeX face was still on its way: fitted again once it is in.
      if (katexLoading()) stale.add(box);
      else stale.delete(box);
      widths.set(box, { now: width, before: seen?.now ?? null, at: performance.now() });
      // Shown from its first fit on, never before (reader-content.css).
      widthsSeen.add(box);
      if (box.dataset.unfitted !== undefined) delete box.dataset.unfitted;
    }
    // A display shrunk below the floor offers its full size in a dialog. It sits under the
    // display, outside the measured box, so showing it changes no width.
    const squeezed = offerExpand && box.dataset.fit === "squeezed";
    let cue = cues.get(box);
    if (squeezed && !cue) {
      cue = makeCue(box);
      cues.set(box, cue);
      box.after(cue);
    }
    if (cue && cue.hidden !== !squeezed) cue.hidden = !squeezed;
  };
  // A viewport resize can report every display at once. Queue one current-width read per box.
  const resized = new Set<HTMLElement>();
  const observer = new ResizeObserver((entries) => {
    for (const entry of entries) {
      const box = entry.target as HTMLElement;
      if (resized.has(box)) continue;
      resized.add(box);
      queueFit(() => {
        resized.delete(box);
        if (live) update(box);
      }, onScreen(box.getBoundingClientRect()));
    }
  });
  const fitted = new Set<HTMLElement>();
  const fit = (box: HTMLElement) => {
    fitted.add(box);
    observer.observe(box);
    // A width measured in a fallback font is wrong: a display reached before KaTeX's main faces
    // load waits for them, hidden (data-unfitted), and is fitted the moment they arrive.
    if (!katexFacesReady()) {
      waiting.add(box);
      stale.add(box);
      return;
    }
    update(box);
  };
  const waiting = new Set<HTMLElement>();
  // The browser's find selects a match: one inside a display not yet fitted fits it now, so the
  // reader sees the formula it found, not an empty space.
  const onSelect = () => {
    const node = document.getSelection()?.anchorNode;
    const el = node && (node.nodeType === 1 ? (node as Element) : node.parentElement);
    const box = el?.closest<HTMLElement>(".math-display[data-unfitted]");
    if (!box || !boxes.includes(box)) return;
    near?.unobserve(box);
    if (!fitted.has(box)) fit(box);
    else update(box, true);
    if (box.dataset.unfitted !== undefined) {
      // Not even KaTeX's main faces are in yet: show it as it is rather than not at all.
      delete box.dataset.unfitted;
    }
  };
  document.addEventListener("selectionchange", onSelect);
  // Each measurement forces a layout, so a formula is fitted as it comes near the screen.
  const near =
    typeof IntersectionObserver === "undefined"
      ? null
      : new IntersectionObserver(
          (entries) => {
            for (const entry of entries) {
              if (!entry.isIntersecting) continue;
              near?.unobserve(entry.target);
              const box = entry.target as HTMLElement;
              queueFit(() => {
                if (live && !fitted.has(box)) fit(box);
              }, onScreen(entry.boundingClientRect));
            }
          },
          // scrollMargin reaches the same way through a scrolling column or sheet.
          { rootMargin: FIT_MARGIN, scrollMargin: FIT_MARGIN },
        );
  // The displays on the first screen are fitted now, before the page paints (this runs in a layout
  // effect), so nothing about them changes once it is shown; the rest are fitted as they come near.
  // Read visibility for the whole batch before any fit changes the layout.
  const firstScreen = near ? new Set(boxes.filter((box) => onScreen(box.getBoundingClientRect()))) : null;
  for (const box of boxes) {
    if (!firstScreen || firstScreen.has(box)) fit(box);
    else near?.observe(box);
  }
  let refitting = false;
  fitters.set(root, (more, everywhere) => {
    for (const box of boxes) {
      if (fitted.has(box)) continue;
      // A formula far from the window is left to the observer, which fits it as it comes near:
      // fitting it now would change the page, unseen, while the reader has only just arrived.
      const r = box.getBoundingClientRect();
      if (!everywhere && (r.bottom < -AHEAD_REACH || r.top > window.innerHeight + AHEAD_REACH)) continue;
      if (!more()) return false;
      near?.unobserve(box);
      fit(box);
    }
    // Measuring may have asked for a KaTeX face not yet loaded (a large brace, a script letter):
    // what was fitted in its stand-in is fitted again once it is in.
    if (katexLoading() && !refitting) {
      refitting = true;
      void katexReady().then(() => {
        refitting = false;
        if (live) refitStale();
      });
    }
    return true;
  });
  if (!katexFacesReady()) {
    // KaTeX's main faces are preloaded (vite.config.ts); fit what waited as soon as they are in,
    // or after three seconds in whatever font the browser fell back to.
    void Promise.race([katexFacesLoaded(), new Promise((resolve) => setTimeout(resolve, 3000))]).then(() => {
      if (!live) return;
      waiting.forEach((box) => {
        queueFit(() => {
          if (live) update(box, true);
        }, onScreen(box.getBoundingClientRect()));
      });
      waiting.clear();
    });
  }
  // Any other KaTeX face (AMS, Size3, …) can still change a width: measure again once they are in.
  // Other faces (the Lean's mono, the serif's italic) change no formula's width and are not awaited.
  if (katexLoading()) {
    void katexReady().then(() => {
      if (live) refitStale();
    });
  }
  return () => {
    live = false;
    document.removeEventListener("selectionchange", onSelect);
    fitters.delete(root);
    near?.disconnect();
    observer.disconnect();
    cues.forEach((cue) => cue.remove());
  };
}

function makeCue(box: HTMLElement): HTMLElement {
  const cue = document.createElement("span");
  cue.className = "math-cue";
  const expand = document.createElement("button");
  expand.type = "button";
  expand.className = "math-cue__expand";
  expand.textContent = "Expand";
  expand.setAttribute("aria-haspopup", "dialog");
  expand.setAttribute("aria-label", "Show the formula larger");
  expand.addEventListener("click", () => expandFormula(box, expand));
  cue.append(expand);
  return cue;
}

/**
 * The formula alone, as large as the window allows, in a labelled modal dialog across the
 * window's width. It is fitted like any display (fitDisplay) and never scrolls; Escape closes it.
 */
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
  const copy = document.createElement("div");
  copy.className = "math-display";
  // The display as written, at full size, not the form the column chose.
  copy.innerHTML = formsOf.get(box)?.html[0] ?? box.innerHTML;
  copy.querySelectorAll("[id]").forEach((el) => el.removeAttribute("id"));
  body.append(copy);
  inner.append(body);
  dialog.append(inner);
  // Inside the page's theme and type, next to the formula's own styles.
  (box.closest(".reader, .panel, .pane") ?? document.body).append(dialog);
  let unfit = () => {};
  const close = () => {
    unfit();
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
  // Fitted like the paper's displays, and again if the dialog settles at another width.
  unfit = markWideMaths(body, false);
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

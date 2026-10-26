// The paper itself, part by part. Every prepared part is its own element;
// parts near the viewport are rendered, the rest wait as placeholders sized
// from their byte length and are rendered in idle time. Heights that change
// above the reading line are compensated, so the line a reader is on never
// moves. Mapped passages carry a margin rule in their region's ink, their
// claims in the margin on hover or focus, and their routes to other accounts.

import { forwardRef, memo, useCallback, useEffect, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../../api/types";
import type { ArgGraph } from "../../model/graph";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { useReading } from "../../app/data";
import type { PreparedDocument, PreparedPart } from "../engine";
import { mountFigures } from "../mount";
import {
  authoredRoutes,
  estimateHeight,
  idleOrder,
  majorityRegion,
  passageOf,
  passageRecords,
  placeName,
  routeLead,
  routeTarget,
  sharedPlaces,
  type Route,
  type Structures,
} from "./model";

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
}

interface Props {
  stage: Stage;
  doc: PreparedDocument;
  structures: Structures;
  graph: ArgGraph;
  links: Links;
  initial: number[];
  /** The reading line, in viewport pixels from the top, used for height compensation. */
  topInset: number;
}

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
  const { stage, doc, structures, graph, links, initial, topInset } = props;
  const [rendered, setRendered] = useState<ReadonlySet<number>>(() => new Set(initial));
  const [near, setNear] = useState<ReadonlySet<number>>(() => new Set(initial));
  const elements = useRef(new Map<number, HTMLElement>());
  const waiters = useRef<{ parts: number[]; resolve: () => void }[]>([]);
  const renderedRef = useRef(rendered);
  renderedRef.current = rendered;
  const topRef = useRef(topInset);
  topRef.current = topInset;

  const add = useCallback((parts: number[], also?: "near") => {
    const fresh = parts.filter((i) => i >= 0 && i < doc.parts.length);
    setRendered((prev) => {
      if (fresh.every((i) => prev.has(i))) return prev;
      const next = new Set(prev);
      fresh.forEach((i) => next.add(i));
      return next;
    });
    if (also)
      setNear((prev) => {
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
  const reanchor = useCallback((force?: boolean) => {
    const line = topRef.current;
    if (force) {
      elements.current.forEach((el) => sizes.current.set(el, el.getBoundingClientRect().height));
    } else {
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
          add(wanted, "near");
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
        if (hits.length) add(hits, "near");
      },
      { rootMargin: NEAR_MARGIN },
    );
    nearObserver.current = observer;
    elements.current.forEach((el) => observer.observe(el));
    return () => observer.disconnect();
  }, [add]);

  useEffect(() => {
    const onScroll = () => {
      if (!pinned.current) reanchor();
    };
    const release = () => (pinned.current = false);
    window.addEventListener("scroll", onScroll, { passive: true });
    for (const type of ["wheel", "touchstart", "keydown", "pointerdown"]) window.addEventListener(type, release, { passive: true, capture: true });
    return () => {
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
        elements.current.forEach((el) => sizes.current.set(el, el.getBoundingClientRect().height));
        anchor.current = { el: held.el, top: held.el.getBoundingClientRect().top };
      } else reanchor(true);
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

  const regionOf = useCallback((id: string) => graph.nodes.get(id)?.region || graph.regionOf.get(id), [graph]);

  return (
    <div className="paper prose" data-stage={stage}>
      {doc.parts.map((part) => (
        <Part
          key={part.index}
          part={part}
          stage={stage}
          doc={doc}
          rendered={rendered.has(part.index)}
          near={near.has(part.index)}
          structures={structures}
          graph={graph}
          links={links}
          regionOf={regionOf}
          register={register}
        />
      ))}
    </div>
  );
});

function nearestPart(elements: Map<number, HTMLElement>, line: number): number {
  let best = 0;
  let bestDistance = Infinity;
  elements.forEach((el, index) => {
    const r = el.getBoundingClientRect();
    const d = r.top <= line && r.bottom >= line ? 0 : Math.min(Math.abs(r.top - line), Math.abs(r.bottom - line));
    if (d < bestDistance) [best, bestDistance] = [index, d];
  });
  return best;
}

interface PartProps {
  part: PreparedPart;
  stage: Stage;
  doc: PreparedDocument;
  rendered: boolean;
  near: boolean;
  structures: Structures;
  graph: ArgGraph;
  links: Links;
  regionOf(id: string): string | undefined;
  register(index: number, el: HTMLElement | null): void;
}

const Part = memo(function Part({ part, stage, doc, rendered, near, structures, graph, links, regionOf, register }: PartProps) {
  const textRef = useRef<HTMLDivElement>(null);
  const html = useMemo(() => (rendered && !part.blank ? doc.render(part.index).html : null), [rendered, part, doc]);
  const anchor = part.kind === "passage" ? part.anchor : undefined;
  const passage = anchor ? passageOf(structures[stage], anchor) : undefined;
  const records = useMemo(() => passageRecords(passage).filter((id) => graph.nodes.has(id)), [passage, graph]);
  const region = useMemo(() => majorityRegion(records, regionOf), [records, regionOf]);
  const routes = useMemo(() => (anchor ? authoredRoutes(structures, stage, anchor) : []), [structures, stage, anchor]);

  useLayoutEffect(() => {
    if (!html || !textRef.current) return;
    const unmount = mountFigures(freshSlots(textRef.current));
    const unmark = markWideMaths(textRef.current);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);

  const setRef = useCallback((el: HTMLElement | null) => register(part.index, el), [register, part.index]);

  if (part.blank) return <div ref={setRef} data-part={part.index} className="part part--blank" />;

  const mapped = !!anchor && records.length > 0;
  return (
    <section
      ref={setRef}
      data-part={part.index}
      data-passage={anchor}
      data-region={mapped ? (region ?? undefined) : undefined}
      className={`part${mapped ? " part--mapped" : ""}${html ? "" : " part--pending"}`}
      aria-label={undefined}
    >
      {mapped && html && <MarginClaims ids={records} graph={graph} links={links} />}
      {html ? (
        <div ref={textRef} className="part__text" dangerouslySetInnerHTML={{ __html: html }} />
      ) : (
        <div className="part__placeholder" style={{ height: estimateHeight(part) }} aria-hidden="true" />
      )}
      {html && anchor && (routes.length > 0 || mapped) && (
        <PassageRoutes stage={stage} anchor={anchor} routes={routes} structures={structures} links={links} near={near} mapped={mapped} />
      )}
    </section>
  );
});

const MARGIN_MAX = 4;

function MarginClaims({ ids, graph, links }: { ids: string[]; graph: ArgGraph; links: Links }) {
  const [all, setAll] = useState(false);
  const shown = all ? ids : ids.slice(0, MARGIN_MAX);
  return (
    <div className="part__margin">
      <div className="margin-claims" role="group" aria-label="Recorded claims this passage discusses">
        <ul>
          {shown.map((id) => {
            const node = graph.nodes.get(id)!;
            return (
              <li key={id}>
                <a className="claim-chip" href={links.node(id)} data-region={node.region}>
                  <span className="region-dot" aria-hidden="true" />
                  <span className={node.kind === "declaration" ? "lean" : undefined}>{node.label}</span>
                </a>
              </li>
            );
          })}
        </ul>
        {ids.length > MARGIN_MAX && (
          <button type="button" className="margin-claims__more" aria-expanded={all} onClick={() => setAll((v) => !v)}>
            {all ? "Fewer" : `and ${ids.length - MARGIN_MAX} more`}
          </button>
        )}
      </div>
    </div>
  );
}

const SHARED_MAX = 4;

function PassageRoutes({
  stage,
  anchor,
  routes,
  structures,
  links,
  near,
  mapped,
}: {
  stage: Stage;
  anchor: string;
  routes: Route[];
  structures: Structures;
  links: Links;
  near: boolean;
  mapped: boolean;
}) {
  const here = { stage, anchor };
  return (
    <div className="routes">
      {routes.length > 0 && (
        <ul className="routes__authored" aria-label="Routes the authors wrote from this passage">
          {routes.map((route) => (
            <RouteLine key={`${route.relation}:${route.kind}:${route.stage}:${route.anchor}`} route={route} here={here} structures={structures} links={links} />
          ))}
        </ul>
      )}
      {mapped && near && <SharedLine here={here} routes={routes} structures={structures} links={links} />}
    </div>
  );
}

function RouteLine({ route, here, structures, links }: { route: Route; here: { stage: Stage; anchor: string }; structures: Structures; links: Links }) {
  const [open, setOpen] = useState(false);
  const id = `why-${here.stage}-${here.anchor}-${route.relation}-${route.stage}-${route.anchor}`;
  return (
    <li className="route">
      <span className="route__lead">{routeLead(route, here, structures)}:</span>{" "}
      <a className="route__link" href={links.beside(route.stage, route.anchor)} data-beside="">
        {routeTarget(route, here, structures)}
      </a>
      {route.rationale && (
        <>
          {" "}
          <button type="button" className="route__why" aria-expanded={open} aria-controls={id} onClick={() => setOpen((v) => !v)}>
            Why
          </button>
          <p id={id} className="route__rationale" hidden={!open}>
            {route.rationale}
          </p>
        </>
      )}
    </li>
  );
}

function SharedLine({ here, routes, structures, links }: { here: { stage: Stage; anchor: string }; routes: Route[]; structures: Structures; links: Links }) {
  const reading = useReading(here.stage, here.anchor);
  const [all, setAll] = useState(false);
  const places = useMemo(() => {
    if (reading.status !== "ready") return [];
    const exclude = new Set(routes.map((r) => `${r.stage}:${r.anchor}`));
    return sharedPlaces(reading.value.items, here, exclude);
  }, [reading, routes, here]);
  if (!places.length) return null;
  const shown = all ? places : places.slice(0, SHARED_MAX);
  const groups = STAGE_ORDER.map((s) => ({ stage: s, places: shown.filter((p) => p.stage === s) })).filter((g) => g.places.length);
  if (groups.length && shown.some((p) => p.stage === here.stage)) {
    groups.sort((a, b) => (a.stage === here.stage ? -1 : b.stage === here.stage ? 1 : 0));
  }
  return (
    <p className="routes__shared">
      <span className="routes__shared-lead" title="Found because these passages map a claim this one maps. A shared claim is not the same argument.">
        Also discussing the same claims:
      </span>{" "}
      {groups.map((g, gi) => (
        <span key={g.stage} className="routes__group">
          <span className="routes__account">{g.stage === here.stage ? "In this account" : PAPER_NAMES[g.stage].short}</span>{" "}
          {g.places.map((p, i) => (
            <span key={p.anchor}>
              <a href={links.beside(p.stage, p.anchor)} data-beside="">
                {placeName(structures, p.stage, p.stage, p.anchor)}
              </a>
              {i < g.places.length - 1 ? ", " : ""}
            </span>
          ))}
          {gi < groups.length - 1 ? "; " : ""}
        </span>
      ))}
      {places.length > SHARED_MAX && (
        <>
          {" "}
          <button type="button" className="routes__more" aria-expanded={all} onClick={() => setAll((v) => !v)}>
            {all ? "fewer" : `and ${places.length - SHARED_MAX} more`}
          </button>
        </>
      )}
    </p>
  );
}

/** Mark display maths wider than its box, so its edge can say it scrolls. */
export function markWideMaths(root: HTMLElement): () => void {
  const boxes = Array.from(root.querySelectorAll<HTMLElement>(".math-display"));
  const mark = () => {
    for (const box of boxes) {
      const wide = box.scrollWidth > box.clientWidth + 1;
      box.dataset.overflow = String(wide);
      box.dataset.scrolledEnd = String(box.scrollLeft + box.clientWidth >= box.scrollWidth - 2);
      if (wide && !box.hasAttribute("tabindex")) {
        box.tabIndex = 0;
        box.setAttribute("role", "group");
        box.setAttribute("aria-label", "Formula, scrolls sideways");
      }
    }
  };
  const onScroll = (event: Event) => {
    const box = event.currentTarget as HTMLElement;
    box.dataset.scrolledEnd = String(box.scrollLeft + box.clientWidth >= box.scrollWidth - 2);
  };
  boxes.forEach((b) => b.addEventListener("scroll", onScroll, { passive: true }));
  const observer = new ResizeObserver(mark);
  boxes.forEach((b) => observer.observe(b));
  mark();
  return () => {
    observer.disconnect();
    boxes.forEach((b) => b.removeEventListener("scroll", onScroll));
  };
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

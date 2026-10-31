// The paper's tied statements as they stand on the page. Everything here is an attribute
// written straight onto what is already there, because all of it happens while the reader
// scrolls or moves the pointer: no React state, and nothing that invalidates layout.

import type { PreparedPart } from "../engine";
import type { TieModel } from "../ties";

export type Light = "on" | "point" | "pin";

interface Mark {
  el: HTMLElement;
  segment: number;
}

/** How far from a part's edge a tick layer is laid out before it can be seen. */
const NEAR = "900px 0px";

export class Statements {
  private sections = new Map<number, HTMLElement>();
  private marks = new Map<number, Mark[]>();
  private ticks = new Map<number, HTMLElement[]>();
  private lit: Record<Light, number | null> = { on: null, point: null, pin: null };
  private partOfSegment: number[];
  private near: IntersectionObserver | null = null;
  private resized: ResizeObserver | null = null;
  private queued = new Set<number>();
  private frame = 0;
  private widths = new Map<number, number>();

  constructor(
    private model: TieModel,
    parts: readonly PreparedPart[],
  ) {
    let at = 0;
    this.partOfSegment = model.index.segments.map(([start]) => {
      while (at + 1 < parts.length && parts[at].span.end <= start) at++;
      return at;
    });
    if (typeof IntersectionObserver !== "undefined") {
      this.near = new IntersectionObserver((entries) => {
        for (const entry of entries) if (entry.isIntersecting) this.queue(Number((entry.target as HTMLElement).dataset.part));
      }, { rootMargin: NEAR });
    }
    if (typeof ResizeObserver !== "undefined") {
      this.resized = new ResizeObserver((entries) => {
        for (const entry of entries) {
          const part = Number((entry.target as HTMLElement).dataset.part);
          // Only parts that have ticks need new ones.
          if (this.widths.has(part)) this.queue(part);
        }
      });
    }
    void document.fonts?.ready?.then(() => this.widths.forEach((_, part) => this.queue(part)));
  }

  dispose() {
    this.near?.disconnect();
    this.resized?.disconnect();
    cancelAnimationFrame(this.frame);
  }

  /** A part's text has been placed on the page, or has left it. */
  adopt(part: number, section: HTMLElement | null) {
    const old = this.sections.get(part);
    if (old) {
      this.near?.unobserve(old);
      this.resized?.unobserve(old);
    }
    this.sections.delete(part);
    this.marks.delete(part);
    this.ticks.delete(part);
    this.widths.delete(part);
    if (!section) return;
    this.sections.set(part, section);
    const found = Array.from(section.querySelectorAll<HTMLElement>(":scope > .part__text [data-t]")).map((el) => ({ el, segment: Number(el.dataset.t) }));
    if (!found.length) return;
    this.marks.set(part, found);
    this.near?.observe(section);
    this.resized?.observe(section);
    for (const kind of ["on", "point", "pin"] as Light[]) {
      const t = this.lit[kind];
      if (t !== null) this.write(kind, t, true, part);
    }
  }

  private queue(part: number) {
    this.queued.add(part);
    this.frame ||= requestAnimationFrame(() => {
      this.frame = 0;
      const parts = [...this.queued];
      this.queued.clear();
      parts.forEach((p) => this.drawTicks(p));
    });
  }

  /** The margin ticks of one part: one per segment, from where its words actually fell. */
  private drawTicks(part: number) {
    const section = this.sections.get(part);
    const marks = this.marks.get(part);
    if (!section || !marks) return;
    const box = section.getBoundingClientRect();
    const rows = new Map<number, { top: number; bottom: number }>();
    for (const { el, segment } of marks) {
      const r = el.getBoundingClientRect();
      if (!r.height) continue;
      const row = rows.get(segment);
      if (row) {
        row.top = Math.min(row.top, r.top);
        row.bottom = Math.max(row.bottom, r.bottom);
      } else rows.set(segment, { top: r.top, bottom: r.bottom });
    }
    let layer = section.querySelector<HTMLElement>(":scope > .part__ticks");
    if (!layer) {
      layer = document.createElement("div");
      layer.className = "part__ticks";
      layer.setAttribute("aria-hidden", "true");
      section.append(layer);
    }
    const made: HTMLElement[] = [];
    const fragment = document.createDocumentFragment();
    for (const [segment, row] of rows) {
      const tick = document.createElement("i");
      tick.className = "tick";
      tick.dataset.s = String(segment);
      if (this.model.segmentLean[segment]) tick.dataset.lean = "";
      tick.style.top = `${Math.round(row.top - box.top)}px`;
      tick.style.height = `${Math.round(row.bottom - row.top)}px`;
      made.push(tick);
      fragment.append(tick);
    }
    layer.replaceChildren(fragment);
    this.ticks.set(part, made);
    this.widths.set(part, box.width);
    for (const kind of ["on", "point", "pin"] as Light[]) {
      const t = this.lit[kind];
      if (t !== null) this.write(kind, t, true, part);
    }
  }

  private write(kind: Light, t: number, on: boolean, only?: number) {
    const name = `data-${kind}`;
    const segments = new Set(this.model.segmentsOf[t] ?? []);
    const parts = new Set([...segments].map((segment) => this.partOfSegment[segment]));
    for (const part of parts) {
      if (only !== undefined && part !== only) continue;
      for (const mark of this.marks.get(part) ?? []) {
        if (!segments.has(mark.segment)) continue;
        if (on) mark.el.setAttribute(name, "");
        else mark.el.removeAttribute(name);
      }
      for (const tick of this.ticks.get(part) ?? []) {
        if (!segments.has(Number(tick.dataset.s))) continue;
        if (on) tick.setAttribute(name, "");
        else tick.removeAttribute(name);
      }
    }
  }

  /** Light one statement in one way; the statement lit that way before goes out. */
  light(kind: Light, t: number | null) {
    const was = this.lit[kind];
    if (was === t) return;
    if (was !== null) this.write(kind, was, false);
    this.lit[kind] = t;
    if (t !== null) this.write(kind, t, true);
    if (kind === "on") {
      if (was !== null) this.first(was)?.removeAttribute("tabindex");
      if (t !== null) this.first(t)?.setAttribute("tabindex", "0");
    }
  }

  /** The statement's marks on the page, in reading order; empty while its parts wait to render. */
  spans(t: number): HTMLElement[] {
    const segments = new Set(this.model.segmentsOf[t] ?? []);
    const parts = new Set([...segments].map((segment) => this.partOfSegment[segment]));
    return [...parts].flatMap((part) => (this.marks.get(part) ?? []).filter((m) => segments.has(m.segment)).map((m) => m.el));
  }

  first(t: number): HTMLElement | null {
    return this.spans(t)[0] ?? null;
  }

  partOf(t: number): number {
    return this.partOfSegment[this.model.segmentsOf[t]?.[0] ?? 0] ?? 0;
  }

  /** The vertical extent of a statement on screen, or null while it is not rendered. */
  extent(t: number): { top: number; bottom: number } | null {
    const spans = this.spans(t);
    if (!spans.length) return null;
    let top = Infinity;
    let bottom = -Infinity;
    for (const el of spans) {
      const r = el.getBoundingClientRect();
      top = Math.min(top, r.top);
      bottom = Math.max(bottom, r.bottom);
    }
    return { top, bottom };
  }

  /**
   * The segment for a reading line: the one under it, else the nearest within `reach`,
   * and one above the line wins a near tie, because it is what was just read.
   */
  atLine(line: number, reach: number, part: number): number | null {
    let best: number | null = null;
    let score = Infinity;
    for (let p = part - 1; p <= part + 1; p++) {
      const marks = this.marks.get(p);
      if (!marks) continue;
      for (const { el, segment } of marks) {
        const r = el.getBoundingClientRect();
        if (!r.height) continue;
        if (r.top <= line && r.bottom >= line) return segment;
        const gap = r.bottom < line ? line - r.bottom : (r.top - line) * 1.5;
        if (gap < score && gap <= reach) {
          score = gap;
          best = segment;
        }
      }
    }
    return best;
  }
}

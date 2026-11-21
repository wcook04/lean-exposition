// The paper's tied statements as they stand on the page. Everything here is an attribute
// written straight onto what is already there, because all of it happens while the reader
// scrolls or moves the pointer: no React state, and nothing that invalidates layout.

import type { PreparedPart } from "../engine";
import { phraseHint, type TieModel } from "../ties";

export type Light = "on" | "point" | "pin";

interface Mark {
  el: HTMLElement;
  segment: number;
}

/**
 * What a paragraph's margin control selects: the block of text that holds its links. A displayed
 * formula set inside a paragraph belongs to that paragraph; one that stands alone is its own block.
 */
const PICK_PROSE = "p, li, figure, table, blockquote";
const PICK_DISPLAY = ".math-display";
const PICK_LABEL = "Select this paragraph’s links";

/** How far from a part's edge a tick layer is laid out before it can be seen. */
const NEAR = "900px 0px";

export class Statements {
  private sections = new Map<number, HTMLElement>();
  private marks = new Map<number, Mark[]>();
  private ticks = new Map<number, HTMLElement[]>();
  /** Each paragraph's control in the margin, and the paragraph it selects. */
  private picks = new WeakMap<HTMLElement, HTMLElement>();
  private heldBlock: HTMLElement | null = null;
  private lit: Record<Light, number | null> = { on: null, point: null, pin: null };
  /** A declaration pointed at in the Lean pane: its phrases are lit. */
  private decl: string | null = null;
  private partOfSegment: number[];
  private near: IntersectionObserver | null = null;
  private resized: ResizeObserver | null = null;
  private queued = new Set<number>();
  private frame = 0;
  private widths = new Map<number, number>();

  /** The one tab stop among the statements. */
  private stop: number | null = null;

  constructor(
    private model: TieModel,
    parts: readonly PreparedPart[],
    /** What a screen reader hears at the tab stop. */
    private label: (t: number) => string = () => "Open this statement",
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

  /**
   * A part's HTML with each phrase's topic tone and pointer hint already in its markup, so placing it
   * on the page writes nothing afterwards (adopt then finds every attribute in place).
   */
  decorate(html: string): string {
    if (typeof document === "undefined" || !html.includes("data-t=")) return html;
    const box = document.createElement("template");
    box.innerHTML = html;
    for (const el of Array.from(box.content.querySelectorAll<HTMLElement>("[data-t]"))) {
      const t = this.model.index.segments[Number(el.dataset.t)]?.[2][0];
      const tie = t === undefined ? undefined : this.model.index.ties[t];
      if (tie?.tone === undefined) continue;
      el.dataset.tone = String(tie.tone);
      el.title = phraseHint(this.model, t!);
    }
    return box.innerHTML;
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
    // A phrase carries its topic's colour, and says its topic and its Lean under the pointer.
    for (const { el, segment } of found) {
      const t = this.model.index.segments[segment]?.[2][0];
      const tie = t === undefined ? undefined : this.model.index.ties[t];
      if (tie?.tone === undefined) continue;
      // Written only when they change: an identical write still records a mutation and invalidates
      // style, and a part is adopted again each time its text is placed.
      const tone = String(tie.tone);
      if (el.dataset.tone !== tone) el.dataset.tone = tone;
      const hint = phraseHint(this.model, t!);
      if (el.title !== hint) el.title = hint;
      if (this.decl && !el.hasAttribute("data-decl") && tie.rows?.some((row) => row.name === this.decl)) el.setAttribute("data-decl", "");
    }
    this.near?.observe(section);
    this.resized?.observe(section);
    for (const kind of ["on", "point", "pin"] as Light[]) {
      const t = this.lit[kind];
      if (t !== null) this.write(kind, t, true, part);
    }
    if (this.stop !== null && this.partOf(this.stop) === part) this.markStop(this.stop, true);
  }

  /** One tab stop, which keys and the reading line move. It stays where it was between statements. */
  rove(t: number) {
    if (this.stop === t) return;
    if (this.stop !== null) this.markStop(this.stop, false);
    this.stop = t;
    this.markStop(t, true);
  }

  private markStop(t: number, on: boolean) {
    const el = this.first(t);
    if (!el) return;
    if (on) {
      el.setAttribute("tabindex", "0");
      el.setAttribute("role", "button");
      el.setAttribute("aria-label", this.label(t));
    } else if (document.activeElement !== el) {
      // The element being read aloud keeps its place until focus moves on.
      el.removeAttribute("tabindex");
      el.removeAttribute("role");
      el.removeAttribute("aria-label");
    }
  }

  /** A line under a statement's last words, for what has no Lean to open. Returns its removal. */
  noteUnder(t: number, text: string): () => void {
    const spans = this.spans(t);
    const block = spans[spans.length - 1]?.closest("p, li, td, blockquote, figcaption, .math-display");
    if (!block) return () => undefined;
    const note = document.createElement("p");
    note.className = "tie-note";
    note.setAttribute("role", "status");
    note.textContent = text;
    block.after(note);
    return () => note.remove();
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
    this.drawPicks(section, marks, box);
    this.ticks.set(part, made);
    this.widths.set(part, box.width);
    for (const kind of ["on", "point", "pin"] as Light[]) {
      const t = this.lit[kind];
      if (t !== null) this.write(kind, t, true, part);
    }
  }

  /**
   * One control in the margin beside each paragraph that has links: it selects the paragraph, so
   * that a click on the paragraph's plain words can stay what it is in any document. A real button
   * in its own layer, at the paragraph's first line; the paper's own markup is not touched.
   */
  private drawPicks(section: HTMLElement, marks: readonly Mark[], box: DOMRect) {
    // Each block of text and the links in it. A displayed formula that only continues a sentence
    // (every link in it also has words in a paragraph) is reached through that paragraph's control.
    const linksOf = new Map<HTMLElement, Set<number>>();
    for (const { el, segment } of marks) {
      const prose = el.closest<HTMLElement>(PICK_PROSE);
      const block = prose && section.contains(prose) ? prose : el.closest<HTMLElement>(PICK_DISPLAY);
      if (!block || !section.contains(block)) continue;
      const t = this.model.index.segments[segment]?.[2][0];
      if (t === undefined) continue;
      if (!linksOf.has(block)) linksOf.set(block, new Set());
      linksOf.get(block)!.add(t);
    }
    const inProse = new Set<number>();
    for (const [block, links] of linksOf) if (!block.matches(".math-display")) links.forEach((t) => inProse.add(t));
    const blocks = [...linksOf].filter(([block, links]) => !block.matches(".math-display") || [...links].some((t) => !inProse.has(t))).map(([block]) => block);
    let layer = section.querySelector<HTMLElement>(":scope > .part__picks");
    if (!layer) {
      layer = document.createElement("div");
      layer.className = "part__picks";
      section.append(layer);
    }
    const fragment = document.createDocumentFragment();
    for (const block of blocks) {
      const top = block.getClientRects()[0] ?? block.getBoundingClientRect();
      if (!top.height) continue;
      const pick = document.createElement("button");
      pick.type = "button";
      pick.className = "para-pick";
      pick.title = PICK_LABEL;
      pick.setAttribute("aria-label", PICK_LABEL);
      pick.style.top = `${Math.round(top.top - box.top)}px`;
      this.picks.set(pick, block);
      fragment.append(pick);
      if (block !== this.heldBlock) continue;
      // The selected paragraph: the selection's amber rule down its whole height, in the ticks' column.
      pick.setAttribute("aria-pressed", "true");
      const whole = block.getBoundingClientRect();
      const rail = document.createElement("i");
      rail.className = "para-rail";
      rail.setAttribute("aria-hidden", "true");
      rail.style.top = `${Math.round(whole.top - box.top)}px`;
      rail.style.height = `${Math.round(whole.height)}px`;
      fragment.append(rail);
    }
    layer.replaceChildren(fragment);
  }

  /** The paragraph a margin control selects. */
  blockOf(pick: HTMLElement): HTMLElement | null {
    return this.picks.get(pick) ?? null;
  }

  /** Mark one paragraph as the selected one, or none. */
  holdBlock(block: HTMLElement | null) {
    if (this.heldBlock === block) return;
    const was = this.heldBlock;
    this.heldBlock = block;
    // Redraw the margin of the part that held the mark and of the part that takes it.
    for (const [part, section] of this.sections) {
      if ((was && section.contains(was)) || (block && section.contains(block))) this.drawTicks(part);
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

  /** Light every phrase one declaration states, from its card in the Lean pane; null puts them out. */
  lightDecl(name: string | null) {
    if (this.decl === name) return;
    this.decl = name;
    for (const marks of this.marks.values()) {
      for (const { el, segment } of marks) {
        const t = this.model.index.segments[segment]?.[2][0];
        const on = name !== null && t !== undefined && !!this.model.index.ties[t]?.rows?.some((row) => row.name === name);
        if (on) el.setAttribute("data-decl", "");
        else el.removeAttribute("data-decl");
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
    if (kind !== "point" && t !== null) this.rove(t);
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

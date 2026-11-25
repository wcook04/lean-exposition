// The paper's tied statements as they stand on the page. Everything here is an attribute
// written straight onto what is already there, because all of it happens while the reader
// scrolls or moves the pointer: no React state, and nothing that invalidates layout.

import type { PreparedPart } from "../engine";
import type { TieModel } from "../ties";

/** `ahead` marks the link Next would land on while the reading line is between links. */
export type Light = "on" | "point" | "pin" | "follow" | "ahead";

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

interface Fragment {
  block: HTMLElement | null;
  pick: HTMLElement | null;
  segment: number;
  tone?: string;
  top: number;
  bottom: number;
  left: number;
}

interface SegmentTicks {
  top: number;
  bottom: number;
  lines: HTMLElement[];
}

/** Inline boxes on a baseline can differ in height, especially around inline mathematics. */
function visualLines(fragments: Fragment[]) {
  const lines: Fragment[][] = [];
  let line: Fragment[] = [];
  let commonTop = 0, commonBottom = 0;
  fragments.sort((a, b) => (a.top + a.bottom) - (b.top + b.bottom) || a.left - b.left);
  for (const f of fragments) {
    // Require a substantial common vertical slice. A tall fraction must not join two adjacent lines.
    const overlap = Math.min(commonBottom, f.bottom) - Math.max(commonTop, f.top);
    if (!line.length || overlap < Math.min(commonBottom - commonTop, f.bottom - f.top) / 2) {
      line = [];
      lines.push(line);
      commonTop = f.top;
      commonBottom = f.bottom;
    } else {
      commonTop = Math.max(commonTop, f.top);
      commonBottom = Math.min(commonBottom, f.bottom);
    }
    line.push(f);
  }
  const placed = lines.map(words => {
    words.sort((a, b) => a.left - b.left);
    let top = Infinity, bottom = -Infinity;
    for (const word of words) {
      top = Math.min(top, word.top);
      bottom = Math.max(bottom, word.bottom);
    }
    return { words, top, bottom, joinsAbove: false, joinsBelow: false };
  });
  const leading = new Map<HTMLElement, number>();
  for (let i = 1; i < placed.length; i++) {
    const above = placed[i - 1], below = placed[i];
    const blocks = new Set(above.words.map(f => f.block));
    const block = below.words.find(f => f.block && blocks.has(f.block))?.block;
    if (!block) continue;
    let lineHeight = leading.get(block);
    if (lineHeight === undefined) {
      lineHeight = parseFloat(getComputedStyle(block).lineHeight) || (below.bottom - below.top) * 1.25;
      leading.set(block, lineHeight);
    }
    // getClientRects describes the ink box, without its leading. Share the intervening leading
    // between two adjacent marked lines in the same block. A whole unmarked line stays clear.
    const gap = below.top - above.bottom;
    if (gap > Math.max(lineHeight * 0.45, lineHeight - Math.min(above.bottom - above.top, below.bottom - below.top) + 2)) continue;
    const edge = (above.bottom + below.top) / 2;
    above.bottom = below.top = edge;
    above.joinsBelow = below.joinsAbove = true;
  }
  return placed;
}

/** The blocks a statement's words can stand in. */
const BLOCKS = "p, li, td, th, blockquote, figcaption, .math-display";

/**
 * Whether selected words are a block rather than a phrase: they stand in more than one block (a
 * statement with its displays, or several paragraphs), or they are the whole of a paragraph longer
 * than a sentence or two. A display alone is a display: it takes its own rule.
 */
export function isBlock(spans: readonly HTMLElement[]): boolean {
  const blocks = new Set(spans.map((el) => (el.matches(".math-display") ? el : (el.closest(BLOCKS) ?? el))));
  if (blocks.size !== 1) return blocks.size > 1;
  const [only] = blocks;
  if (only.matches(".math-display")) return false;
  const whole = (only.textContent ?? "").replace(/\s+/g, "").length;
  const words = spans.reduce((n, el) => n + (el.textContent ?? "").replace(/\s+/g, "").length, 0);
  return whole > 160 && words >= whole * 0.9;
}

/** How far from a part's edge a tick layer is laid out before it can be seen. */
const NEAR = "900px 0px";

export class Statements {
  private sections = new Map<number, HTMLElement>();
  private marks = new Map<number, Mark[]>();
  /** Mounted marks by part and tie, in manuscript order. */
  private marksByTie = new Map<number, Map<number, HTMLElement[]>>();
  private ticks = new Map<number, Map<number, SegmentTicks>>();
  /** Each paragraph's control in the margin, and the paragraph it selects. */
  private picks = new WeakMap<HTMLElement, HTMLElement>();
  private heldBlock: HTMLElement | null = null;
  private lit: Record<Light, number | null> = { on: null, point: null, pin: null, follow: null, ahead: null };
  /** A declaration pointed at in the Lean pane: its phrases are lit. */
  private decl: string | null = null;
  private partOfSegment: number[];
  private near: IntersectionObserver | null = null;
  private resized: ResizeObserver | null = null;
  private queued = new Set<number>();
  private frame = 0;
  private nearby = new Set<number>();
  private measured = new Set<number>();
  private fontsChanged = () => {
    this.measured.clear();
    this.nearby.forEach((part) => this.queue(part));
  };

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
        for (const entry of entries) {
          const part = Number((entry.target as HTMLElement).dataset.part);
          if (this.sections.get(part) !== entry.target) continue;
          if (entry.isIntersecting) {
            this.nearby.add(part);
            if (!this.measured.has(part)) this.queue(part);
          } else this.nearby.delete(part);
        }
      }, { rootMargin: NEAR });
    }
    if (typeof ResizeObserver !== "undefined") {
      this.resized = new ResizeObserver((entries) => {
        for (const entry of entries) {
          const part = Number((entry.target as HTMLElement).dataset.part);
          if (this.sections.get(part) !== entry.target) continue;
          this.measured.delete(part);
          if (this.nearby.has(part)) this.queue(part);
        }
      });
    }
    document.fonts?.addEventListener?.("loadingdone", this.fontsChanged);
    void document.fonts?.ready?.then(this.fontsChanged);
  }

  dispose() {
    this.near?.disconnect();
    this.resized?.disconnect();
    this.nearby.clear();
    document.fonts?.removeEventListener?.("loadingdone", this.fontsChanged);
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
    this.marksByTie.delete(part);
    this.ticks.delete(part);
    this.nearby.delete(part);
    this.measured.delete(part);
    if (!section) return;
    this.sections.set(part, section);
    const found = Array.from(section.querySelectorAll<HTMLElement>(":scope > .part__text [data-t]")).map((el) => ({ el, segment: Number(el.dataset.t) }));
    if (!found.length) return;
    this.marks.set(part, found);
    const byTie = new Map<number, HTMLElement[]>();
    this.marksByTie.set(part, byTie);
    for (const { el, segment } of found) {
      const members = this.model.index.segments[segment]?.[2];
      if (!members?.length) continue;
      for (const member of members) {
        const spans = byTie.get(member);
        if (spans) spans.push(el);
        else byTie.set(member, [el]);
      }
      // A phrase carries its topic's colour.
      const t = members[0];
      const tie = t === undefined ? undefined : this.model.index.ties[t];
      if (tie?.tone === undefined) continue;
      // Write the tone only when it changes. An identical write still records a mutation and invalidates
      // style, and a part is adopted again each time its text is placed.
      const tone = String(tie.tone);
      if (el.dataset.tone !== tone) el.dataset.tone = tone;
      if (this.decl && !el.hasAttribute("data-decl") && tie.rows?.some((row) => row.name === this.decl)) el.setAttribute("data-decl", "");
    }
    if (this.near) this.near.observe(section);
    else {
      this.nearby.add(part);
      this.queue(part);
    }
    this.resized?.observe(section);
    for (const kind of ["on", "point", "pin", "follow", "ahead"] as Light[]) {
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
      for (const p of parts) if (this.nearby.has(p)) this.drawTicks(p);
    });
  }

  /** One tick per physical line. Its topics follow the words from left to right. */
  private drawTicks(part: number) {
    const section = this.sections.get(part);
    const marks = this.marks.get(part);
    if (!section || !marks) return;
    const box = section.getBoundingClientRect();
    const sectionTop = box.top;
    const fragments: Fragment[] = [];
    const bySegment = new Map<number, SegmentTicks>();
    const hits = new Map<HTMLElement, { top: number; bottom: number }[]>();
    for (const { el, segment } of marks) {
      const prose = el.closest<HTMLElement>(PICK_PROSE);
      const pick = prose && section.contains(prose) ? prose : el.closest<HTMLElement>(PICK_DISPLAY);
      const block = el.closest<HTMLElement>(BLOCKS);
      for (const rect of el.getClientRects()) {
        if (!rect.width || !rect.height) continue;
        const top = rect.top - sectionTop, bottom = rect.bottom - sectionTop;
        fragments.push({ pick, block, segment, tone: el.dataset.tone, top, bottom, left: rect.left });
        const bounds = bySegment.get(segment);
        if (bounds) {
          bounds.top = Math.min(bounds.top, top);
          bounds.bottom = Math.max(bounds.bottom, bottom);
        } else bySegment.set(segment, { top, bottom, lines: [] });
      }
    }
    let layer = section.querySelector<HTMLElement>(":scope > .part__ticks");
    if (!layer) {
      layer = document.createElement("div");
      layer.className = "part__ticks";
      layer.setAttribute("aria-hidden", "true");
      section.append(layer);
    }
    const fragment = document.createDocumentFragment();
    for (const line of visualLines(fragments)) {
      const tick = document.createElement("i");
      tick.className = "tick";
      if (line.joinsAbove) tick.dataset.joinsAbove = "";
      if (line.joinsBelow) tick.dataset.joinsBelow = "";
      const tones = new Set<string>();
      const owners = new Map<string | undefined, HTMLElement>();
      for (const f of line.words) {
        const lines = bySegment.get(f.segment)!.lines;
        if (lines[lines.length - 1] !== tick) lines.push(tick);
        if (this.model.segmentLean[f.segment]) tick.dataset.lean = "";
        if (f.tone !== undefined) tones.add(f.tone);
        if (f.pick && !owners.has(f.tone)) owners.set(f.tone, f.pick);
      }
      if (tones.size === 1) {
        tick.dataset.tone = [...tones][0];
      } else if (tones.size > 1) {
        tick.classList.add("tick--bands");
        for (const tone of tones) {
          const band = document.createElement("span");
          band.dataset.tone = tone;
          tick.append(band);
        }
      }
      const y = Math.round(line.top), height = Math.round(line.bottom) - y;
      tick.style.top = `${y}px`;
      tick.style.height = `${height}px`;
      const bands = tones.size ? [...tones] : [undefined];
      bands.forEach((tone, i) => {
        const block = owners.get(tone);
        if (!block) return;
        const start = y + (height * i) / bands.length;
        const end = y + (height * (i + 1)) / bands.length;
        let spans = hits.get(block);
        if (!spans) hits.set(block, spans = []);
        const last = spans[spans.length - 1];
        // Keep distinct lines independent: a gap in the printed marks remains a gap in the target.
        if (last && start <= last.bottom + 0.01) last.bottom = Math.max(last.bottom, end);
        else spans.push({ top: start, bottom: end });
      });
      fragment.append(tick);
    }
    layer.replaceChildren(fragment);
    this.drawPicks(section, hits, box.top);
    this.ticks.set(part, bySegment);
    this.measured.add(part);
    for (const kind of ["on", "point", "pin", "follow", "ahead"] as Light[]) {
      const t = this.lit[kind];
      if (t !== null) this.write(kind, t, true, part);
    }
  }

  /** Each paragraph has one native button. Its pointer targets sit over the lines it owns. */
  private drawPicks(section: HTMLElement, hits: Map<HTMLElement, { top: number; bottom: number }[]>, sectionTop: number) {
    let layer = section.querySelector<HTMLElement>(":scope > .part__picks");
    if (!layer) {
      layer = document.createElement("div");
      layer.className = "part__picks";
      section.append(layer);
    }
    const active = document.activeElement;
    const focusedBlock = active instanceof HTMLElement && layer.contains(active) ? this.picks.get(active) : null;
    let restore: HTMLButtonElement | undefined;
    const fragment = document.createDocumentFragment();
    for (const [block, [first, ...rest]] of hits) {
      const pick = document.createElement("button");
      pick.type = "button";
      pick.className = "para-pick";
      pick.title = PICK_LABEL;
      pick.setAttribute("aria-label", PICK_LABEL);
      pick.style.top = `${first.top}px`;
      pick.style.height = `${first.bottom - first.top}px`;
      for (const span of rest) {
        const area = document.createElement("span");
        area.style.top = `${span.top - first.top}px`;
        area.style.height = `${span.bottom - span.top}px`;
        pick.append(area);
      }
      this.picks.set(pick, block);
      if (block === focusedBlock) restore = pick;
      fragment.append(pick);
      if (block !== this.heldBlock) continue;
      pick.setAttribute("aria-pressed", "true");
      const whole = block.getBoundingClientRect();
      const rail = document.createElement("i");
      rail.className = "para-rail";
      rail.setAttribute("aria-hidden", "true");
      rail.style.top = `${Math.round(whole.top - sectionTop)}px`;
      rail.style.height = `${Math.round(whole.height)}px`;
      fragment.append(rail);
    }
    layer.replaceChildren(fragment);
    restore?.focus({ preventScroll: true });
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
      for (const el of this.marksByTie.get(part)?.get(t) ?? []) {
        if (on) el.setAttribute(name, "");
        else el.removeAttribute(name);
      }
      const bySegment = this.ticks.get(part);
      if (bySegment) for (const segment of segments) {
        for (const tick of bySegment.get(segment)?.lines ?? []) tick.toggleAttribute(name, on);
      }
    }
    if (kind === "pin" || kind === "follow") this.writeBlock(t, on);
  }

  /**
   * A selection that is a whole statement or paragraph is marked as a block (phrases.css): its
   * phrases keep their topic lines and one amber rule runs down the margin beside each of its parts,
   * from its first selected line to its last. A phrase or a sentence inside one paragraph is not.
   */
  private writeBlock(t: number, on: boolean) {
    const spans = this.spans(t);
    const block = on && isBlock(spans);
    for (const el of spans) {
      if (block) el.setAttribute("data-pin-block", "");
      else el.removeAttribute("data-pin-block");
    }
    const segments = new Set(this.model.segmentsOf[t] ?? []);
    for (const part of new Set([...segments].map((segment) => this.partOfSegment[segment]))) {
      const layer = this.sections.get(part)?.querySelector<HTMLElement>(":scope > .part__ticks");
      if (!layer) continue;
      layer.querySelector(":scope > .tick-run")?.remove();
      const bySegment = this.ticks.get(part);
      if (!block || !bySegment) continue;
      let top = Infinity, bottom = -Infinity;
      for (const segment of segments) {
        const bounds = bySegment.get(segment);
        if (bounds) {
          top = Math.min(top, Math.round(bounds.top));
          bottom = Math.max(bottom, Math.round(bounds.bottom));
        }
      }
      if (bottom <= top) continue;
      const run = document.createElement("i");
      run.className = "tick-run";
      run.style.top = `${top}px`;
      run.style.height = `${bottom - top}px`;
      layer.prepend(run);
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
    // Pointing and a preview of the next link leave the keyboard where it was.
    if (kind !== "point" && kind !== "ahead" && t !== null) this.rove(t);
  }

  /** The statement's marks on the page, in reading order; empty while its parts wait to render. */
  spans(t: number): HTMLElement[] {
    const segments = new Set(this.model.segmentsOf[t] ?? []);
    const parts = new Set([...segments].map((segment) => this.partOfSegment[segment]));
    return [...parts].flatMap((part) => this.marksByTie.get(part)?.get(t) ?? []);
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

// The authors' PDF in place of the typeset text (view=pdf), drawn by pdf.js as Proof Reader's
// PdfPane draws it: each page a canvas at the column's width, drawn when it comes near the
// screen. Each phrase tie placed on the PDF at build time (scripts/pdf_marks.py: the boxes of its
// own words) is a mark in its topic's colour; clicking one selects the same phrase as clicking
// it in the text. The view opens at the selected phrase's page, else at `page`, and reports
// the page in view so a switch back to the text lands at the same place.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import * as pdfjs from "pdfjs-dist";
import workerUrl from "pdfjs-dist/build/pdf.worker.min.mjs?url";
import type { PDFDocumentProxy } from "pdfjs-dist";
import { prefersReducedMotion } from "../../app/theme";
import type { ReaderSignals } from "../page/rightPage";
import "./pdf-view.css";

pdfjs.GlobalWorkerOptions.workerSrc = workerUrl;

export interface PdfMark { at: string; tone: number | null; record: string | null; boxes: [number, number, number, number, number][] }
export interface PdfSection { section: string; title: string; page: number; y: number; topic: string }
export const pdfSectionId = (section: string) => `pdf-section-${section}`;
type PdfAnchor = [byte: number, page: number, y: number];
export interface PdfLocation { page: number; y: number }
export interface PdfMarks { pages: [number, number][]; marks: Record<string, PdfMark>; sections?: PdfSection[]; pageStarts?: number[]; positions?: PdfAnchor[] }

const marksLoaded = new Map<string, Promise<PdfMarks | null>>();
/** The marks of a paper's PDF, or null when the build placed none. */
export function loadPdfMarks(url: string): Promise<PdfMarks | null> {
  let value = marksLoaded.get(url);
  if (!value) {
    value = fetch(url).then((r) => (r.ok ? r.json() : null)).catch(() => null);
    marksLoaded.set(url, value);
  }
  return value;
}

/** Search the monotone PDF correspondence, with older mark-only editions as a fallback. */
function anchorAfter(rows: readonly PdfAnchor[], before: (row: PdfAnchor) => boolean): number {
  let lo = 0, hi = rows.length;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (before(rows[mid])) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

export function pdfLocationAtByte(marks: PdfMarks, byte: number): PdfLocation | null {
  const rows = marks.positions;
  if (rows?.length) {
    const i = anchorAfter(rows, ([b]) => b < byte);
    const left = rows[i - 1], right = rows[i];
    if (left && right && left[1] === right[1]) {
      return { page: left[1], y: left[2] + (right[2] - left[2]) * (byte - left[0]) / (right[0] - left[0]) };
    }
    const [, page, y] = !right || (left && byte - left[0] < right[0] - byte) ? left : right;
    return { page, y };
  }
  let best: PdfLocation | null = null;
  let distance = Infinity;
  for (const mark of Object.values(marks.marks)) {
    const [start, end] = mark.at.slice(1).split("-").map(Number);
    const box = mark.boxes[0];
    const gap = Math.max(0, start - byte, byte - (end ?? start));
    if (!box || gap >= distance) continue;
    distance = gap;
    best = { page: box[0], y: box[2] };
  }
  return best;
}

export function pageAtByte(marks: PdfMarks, byte: number): number | null {
  return pdfLocationAtByte(marks, byte)?.page ?? null;
}

function byteAtPdfLocation(marks: PdfMarks, page: number, y: number): number | undefined {
  const rows = marks.positions;
  if (!rows?.length) return undefined;
  const i = anchorAfter(rows, ([, p, top]) => p < page || (p === page && top < y));
  const left = rows[i - 1], right = rows[i];
  if (left?.[1] !== page) return right?.[1] === page ? right[0] : undefined;
  if (right?.[1] !== page) return left[0];
  return Math.round(left[0] + (right[0] - left[0]) * (y - left[2]) / (right[2] - left[2]));
}

/** The first mark on a page, as a place in the text (`b<start>-<end>`). */
export function atOnPage(marks: PdfMarks, page: number): string | null {
  let best: { start: number; at: string } | null = null;
  for (const mark of Object.values(marks.marks)) {
    if (mark.boxes[0][0] !== page) continue;
    const start = Number(mark.at.slice(1).split("-")[0]);
    if (!best || start < best.start) best = { start, at: mark.at };
  }
  return best?.at ?? null;
}

interface Props {
  url: string;
  label?: string;
  marks: PdfMarks;
  /** The selected phrase's place in the text (`b<start>-<end>`), if any. */
  at?: string;
  pinned: boolean;
  shownTie: ReaderSignals["shownTie"];
  /** With no mark at the reading line: the mark Next lands on, outlined without moving the page. */
  ahead?: ReaderSignals["shownTie"];
  page?: number;
  position?: PdfLocation;
  section?: PdfSection;
  onPick(id: string, mark: PdfMark, page: number): void;
  readingLine(): number;
  onPosition(page: number, at: string | undefined, section: string | undefined, y: number, byte?: number): void;
}

export function PdfView({ url, marks, at, pinned, shownTie, ahead, page, position, section, label, onPick, readingLine, onPosition }: Props) {
  const box = useRef<HTMLDivElement>(null);
  const [pdf, setPdf] = useState<PDFDocumentProxy | null>(null);
  const [failed, setFailed] = useState(false);
  const [width, setWidth] = useState(0);
  const byPage = useMemo(() => {
    const out = new Map<number, [string, PdfMark][]>();
    for (const [id, mark] of Object.entries(marks.marks)) for (const p of new Set(mark.boxes.map((b) => b[0]))) out.set(p, [...(out.get(p) ?? []), [id, mark]]);
    return out;
  }, [marks]);
  const selected = useMemo(() => Object.entries(marks.marks).find(([, m]) => m.at === at)?.[0] ?? null, [marks, at]);

  useEffect(() => {
    let live = true;
    const task = pdfjs.getDocument({ url });
    task.promise.then((doc) => live && setPdf(doc), () => live && setFailed(true));
    return () => {
      live = false;
      // PDF.js can report a worker error if interrupted while it parses the header.
      // Let an in-flight open settle, with a deadline for a stalled request.
      const release = () => {
        window.clearTimeout(deadline);
        if (!task.destroyed) void task.destroy().catch(() => {});
      };
      const deadline = window.setTimeout(release, 30_000);
      void task.promise.then(release, release);
    };
  }, [url]);

  useEffect(() => {
    const el = box.current;
    if (!el) return;
    const measure = () => setWidth(el.clientWidth);
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, []);

  // Open at the selected phrase, else at the page asked for.
  const opened = useRef(false);
  /** The page and section last landed on: letting go of a phrase there is no reason to move. */
  const landedOn = useRef<{ page?: number; section?: string }>({});
  useEffect(() => {
    if (!width || !pdf) return;
    const was = landedOn.current;
    landedOn.current = { page, section: section?.section };
    // A selection let go of, or made away from the page (from the graph), leaves the page where it is.
    if (opened.current && !selected && !position && was.page === page && was.section === section?.section) return;
    const target = !position && selected ? box.current?.querySelector<HTMLElement>(`[data-mark="${CSS.escape(selected)}"]`) : null;
    const sectionEl = section ? box.current?.querySelector<HTMLElement>(`[data-section="${CSS.escape(section.section)}"]`) : null;
    const pageEl = page ? box.current?.querySelector<HTMLElement>(`[data-page="${page}"]`) : null;
    const el = position ? pageEl : target ?? sectionEl ?? pageEl;
    const first = !opened.current;
    opened.current = true;
    if (!el) return;
    const landAt = (behavior: ScrollBehavior) => {
      if (position) {
        const y = position.y * width / marks.pages[position.page - 1][0];
        window.scrollTo({ top: window.scrollY + el.getBoundingClientRect().top + y - readingLine(), behavior });
      } else if (target) window.scrollBy({ top: target.getBoundingClientRect().top - readingLine() + 1, behavior });
      else el.scrollIntoView({ block: "start", behavior });
    };
    landAt(first || prefersReducedMotion() ? "instant" : "smooth");
    // On first opening the reader is still settling its own place and may move the window; land
    // again until the target is in view, unless the reader has started scrolling by hand.
    if (!first) return;
    let touched = false;
    const touch = () => (touched = true);
    window.addEventListener("wheel", touch, { passive: true, once: true });
    window.addEventListener("keydown", touch, { once: true });
    window.addEventListener("touchstart", touch, { passive: true, once: true });
    const land = () => {
      const r = el.getBoundingClientRect();
      if (!touched && (r.bottom < 0 || r.top > window.innerHeight)) landAt("instant");
    };
    let frame = 0;
    const onScroll = () => {
      cancelAnimationFrame(frame);
      frame = requestAnimationFrame(land);
    };
    window.addEventListener("scroll", onScroll, { passive: true });
    const timers = [300, 800, 1500, 2500, 4000].map((ms) => window.setTimeout(land, ms));
    const stop = window.setTimeout(() => window.removeEventListener("scroll", onScroll), 4000);
    return () => {
      timers.forEach((t) => window.clearTimeout(t));
      window.clearTimeout(stop);
      cancelAnimationFrame(frame);
      window.removeEventListener("scroll", onScroll);
      window.removeEventListener("wheel", touch);
      window.removeEventListener("keydown", touch);
      window.removeEventListener("touchstart", touch);
    };
  }, [width, pdf, selected, page, section, position?.page, position?.y, marks, readingLine]);

  // Report the page at the reading line.
  useEffect(() => {
    const el = box.current;
    if (!el || !width) return;
    const pages = Array.from(el.querySelectorAll<HTMLElement>(".pdf-view__page"));
    if (!pages.length) return;
    let frame = 0;
    const read = () => {
      frame = 0;
      const line = readingLine();
      let lo = 0, hi = pages.length - 1;
      while (lo < hi) {
        const mid = (lo + hi) >>> 1;
        if (pages[mid].getBoundingClientRect().bottom < line) lo = mid + 1;
        else hi = mid;
      }
      const page = lo + 1;
      const rect = pages[lo].getBoundingClientRect();
      const scale = width / marks.pages[lo][0];
      const y = (line - rect.top) / scale;
      let best: PdfMark | undefined;
      let distance = Infinity;
      for (const [, mark] of byPage.get(page) ?? []) {
        for (const [p, , top, , bottom] of mark.boxes) {
          if (p !== page || rect.top + bottom * scale <= 0 || rect.top + top * scale >= window.innerHeight) continue;
          const gap = Math.max(0, top - y, y - bottom) * scale;
          if (gap < distance && gap <= window.innerHeight * 0.32) {
            distance = gap;
            best = mark;
          }
        }
      }
      const section = marks.sections?.filter((s) => s.page < page || (s.page === page && s.y <= y + 2)).at(-1);
      onPosition(page, best?.at, section?.section, y, byteAtPdfLocation(marks, page, y));
    };
    const schedule = () => { if (!frame) frame = requestAnimationFrame(read); };
    read();
    window.addEventListener("scroll", schedule, { passive: true });
    window.addEventListener("resize", schedule);
    return () => {
      cancelAnimationFrame(frame);
      window.removeEventListener("scroll", schedule);
      window.removeEventListener("resize", schedule);
    };
  }, [width, byPage, marks, readingLine, onPosition]);

  // Paint the existing click targets without re-rendering the pages or landing again.
  useLayoutEffect(() => {
    const el = box.current;
    if (!el || !width) return;
    let lit: NodeListOf<HTMLElement> | undefined;
    let currentAt: string | undefined;
    const paint = () => {
      const next = pinned ? at : shownTie.get()?.at;
      if (next === currentAt) return;
      lit?.forEach((mark) => mark.classList.remove("is-selected"));
      currentAt = next;
      lit = next ? el.querySelectorAll<HTMLElement>(`[data-at="${CSS.escape(next)}"]`) : undefined;
      lit?.forEach((mark) => mark.classList.add("is-selected"));
    };
    paint();
    const unsubscribe = shownTie.subscribe(paint);
    return () => {
      unsubscribe();
      lit?.forEach((mark) => mark.classList.remove("is-selected"));
    };
  }, [width, marks, pinned, at, shownTie]);

  useLayoutEffect(() => {
    const el = box.current;
    if (!el || !width || !ahead) return;
    let lit: NodeListOf<HTMLElement> | undefined;
    let currentAt: string | undefined;
    const paint = () => {
      const next = pinned ? undefined : ahead.get()?.at;
      if (next === currentAt) return;
      lit?.forEach((mark) => mark.classList.remove("is-ahead"));
      currentAt = next;
      lit = next ? el.querySelectorAll<HTMLElement>(`[data-at="${CSS.escape(next)}"]`) : undefined;
      lit?.forEach((mark) => mark.classList.add("is-ahead"));
    };
    paint();
    const unsubscribe = ahead.subscribe(paint);
    return () => {
      unsubscribe();
      lit?.forEach((mark) => mark.classList.remove("is-ahead"));
    };
  }, [width, marks, pinned, ahead]);

  if (failed) return <p className="pdf-view__failed">The PDF could not be opened here. Open PDF opens it in a new tab.</p>;
  return (
    <div className="pdf-view" ref={box} aria-label={label ?? "The authors’ PDF"}>
      {width > 0 &&
        marks.pages.map(([w, h], i) => {
          const scale = width / w;
          return (
            <section key={i} className="pdf-view__page" data-page={i + 1} style={{ height: Math.round(h * scale) }} aria-label={`Page ${i + 1}`}>
              {pdf && <PdfCanvas pdf={pdf} number={i + 1} width={width} />}
              {marks.sections?.filter((heading) => heading.page === i + 1).map((heading) =>
                <span key={heading.section} className="pdf-view__section" data-section={heading.section} style={{ top: heading.y * scale }} aria-hidden="true" />
              )}
              {(byPage.get(i + 1) ?? []).map(([id, mark]) =>
                mark.boxes
                  .filter((b) => b[0] === i + 1)
                  .map((b, k) => (
                    <button
                      key={`${id}-${k}`}
                      type="button"
                      className="pdf-view__mark tie"
                      data-at={mark.at}
                      data-mark={k === 0 ? id : undefined}
                      data-tone={mark.tone ?? undefined}
                      style={{ left: b[1] * scale - 1, top: b[2] * scale - 1, width: (b[3] - b[1]) * scale + 2, height: (b[4] - b[2]) * scale + 2 }}
                      aria-label="Open the Lean this phrase is tied to"
                      onClick={() => onPick(id, mark, i + 1)}
                    />
                  )),
              )}
            </section>
          );
        })}
    </div>
  );
}

/** One page, drawn when it comes within a screen of the view. */
function PdfCanvas({ pdf, number, width }: { pdf: PDFDocumentProxy; number: number; width: number }) {
  const canvas = useRef<HTMLCanvasElement>(null);
  const [near, setNear] = useState(false);
  useEffect(() => {
    const el = canvas.current;
    if (!el) return;
    const observer = new IntersectionObserver((entries) => entries.some((e) => e.isIntersecting) && setNear(true), { rootMargin: "1200px 0px" });
    observer.observe(el);
    return () => observer.disconnect();
  }, []);
  useEffect(() => {
    if (!near) return;
    let task: ReturnType<Awaited<ReturnType<PDFDocumentProxy["getPage"]>>["render"]> | null = null;
    let live = true;
    void pdf.getPage(number).then((page) => {
      const el = canvas.current;
      if (!live || !el) return;
      const ratio = window.devicePixelRatio || 1;
      const viewport = page.getViewport({ scale: (width / page.getViewport({ scale: 1 }).width) * ratio });
      el.width = Math.floor(viewport.width);
      el.height = Math.floor(viewport.height);
      task = page.render({ canvasContext: el.getContext("2d")!, viewport });
      task.promise.catch(() => {});
    }, (error: unknown) => {
      if (live) console.error("Could not load PDF page", error);
    });
    return () => {
      live = false;
      task?.cancel();
    };
  }, [near, pdf, number, width]);
  return <canvas ref={canvas} className="pdf-view__canvas" />;
}

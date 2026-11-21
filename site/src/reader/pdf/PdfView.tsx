// The authors' PDF in place of the typeset text (view=pdf), drawn by pdf.js as Proof Reader's
// PdfPane draws it: each page a canvas at the column's width, drawn when it comes near the
// screen. Each phrase tie placed on the PDF at build time (scripts/pdf_marks.py: the boxes of its
// own words) is a mark in its topic's colour; clicking one selects the same phrase as clicking
// it in the text. The view opens at the selected phrase's page, else at `page`, and reports
// the page in view so a switch back to the text lands at the same place.

import { useEffect, useMemo, useRef, useState } from "react";
import * as pdfjs from "pdfjs-dist";
import workerUrl from "pdfjs-dist/build/pdf.worker.min.mjs?url";
import type { PDFDocumentProxy } from "pdfjs-dist";
import "./pdf-view.css";

pdfjs.GlobalWorkerOptions.workerSrc = workerUrl;

export interface PdfMark { at: string; tone: number | null; record: string | null; boxes: [number, number, number, number, number][] }
export interface PdfMarks { pages: [number, number][]; marks: Record<string, PdfMark> }

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

/** The first page of the mark at or after a byte of the text, from the marks' places. */
export function pageAtByte(marks: PdfMarks, byte: number): number | null {
  let best: { start: number; page: number } | null = null;
  for (const mark of Object.values(marks.marks)) {
    const start = Number(mark.at.slice(1).split("-")[0]);
    if (start >= byte && (!best || start < best.start)) best = { start, page: mark.boxes[0][0] };
  }
  return best?.page ?? null;
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
  marks: PdfMarks;
  /** The selected phrase's place in the text (`b<start>-<end>`), if any. */
  at?: string;
  page?: number;
  onPick(id: string, mark: PdfMark, page: number): void;
  onPage(page: number): void;
}

export function PdfView({ url, marks, at, page, onPick, onPage }: Props) {
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
      void task.destroy();
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
  useEffect(() => {
    if (!width || !pdf) return;
    const target = selected ? box.current?.querySelector<HTMLElement>(`[data-mark="${CSS.escape(selected)}"]`) : null;
    const pageEl = !target && page ? box.current?.querySelector<HTMLElement>(`[data-page="${page}"]`) : null;
    const el = target ?? pageEl;
    if (!el) return;
    const first = !opened.current;
    opened.current = true;
    el.scrollIntoView({ block: target ? "center" : "start", behavior: first ? "auto" : "smooth" });
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
      if (!touched && (r.bottom < 0 || r.top > window.innerHeight)) el.scrollIntoView({ block: target ? "center" : "start" });
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
  }, [width, pdf, selected, page]);

  // Report the page at the reading line.
  useEffect(() => {
    const el = box.current;
    if (!el || !width) return;
    const observer = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) if (entry.isIntersecting) onPage(Number((entry.target as HTMLElement).dataset.page));
      },
      { rootMargin: "-30% 0px -60% 0px" },
    );
    el.querySelectorAll(".pdf-view__page").forEach((page) => observer.observe(page));
    return () => observer.disconnect();
  }, [width, onPage]);

  if (failed) return <p className="pdf-view__failed">The PDF could not be opened here. Open PDF opens it in a new tab.</p>;
  return (
    <div className="pdf-view" ref={box} aria-label="The authors’ PDF">
      {width > 0 &&
        marks.pages.map(([w, h], i) => {
          const scale = width / w;
          return (
            <section key={i} className="pdf-view__page" data-page={i + 1} style={{ height: Math.round(h * scale) }} aria-label={`Page ${i + 1}`}>
              {pdf && <PdfCanvas pdf={pdf} number={i + 1} width={width} />}
              {(byPage.get(i + 1) ?? []).map(([id, mark]) =>
                mark.boxes
                  .filter((b) => b[0] === i + 1)
                  .map((b, k) => (
                    <button
                      key={`${id}-${k}`}
                      type="button"
                      className={`pdf-view__mark tie${id === selected ? " is-selected" : ""}`}
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
    });
    return () => {
      live = false;
      task?.cancel();
    };
  }, [near, pdf, number, width]);
  return <canvas ref={canvas} className="pdf-view__canvas" />;
}

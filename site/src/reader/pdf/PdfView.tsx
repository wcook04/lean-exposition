// The authors' PDF in place of the typeset text (view=pdf), drawn by pdf.js as Proof Reader's
// PdfPane draws it: each page a canvas at the column's width, drawn when it comes near the
// screen. Each phrase tie placed on the PDF at build time (scripts/pdf_marks.py: the boxes of its
// own words) is a mark in its topic's colour; clicking one selects the same phrase as clicking
// it in the text. The view opens at the selected phrase's page, else at `page`, and reports
// the page in view so a switch back to the text lands at the same place.

import { useEffect, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState, type Ref } from "react";
import * as pdfjs from "pdfjs-dist";
import workerUrl from "pdfjs-dist/build/pdf.worker.min.mjs?url";
import type { PDFDocumentProxy } from "pdfjs-dist";
import { prefersReducedMotion } from "../../app/theme";
import type { ReaderSignals } from "../page/rightPage";
import "./pdf-view.css";

pdfjs.GlobalWorkerOptions.workerSrc = workerUrl;

export interface PdfMark { at: string; tone: number | null; record: string | null; boxes: [number, number, number, number, number][] }
type PdfAnchor = [byte: number, page: number, y: number];
export interface PdfLocation { page: number; y: number }
export interface PdfMarks { pages: [number, number][]; marks: Record<string, PdfMark>; positions?: PdfAnchor[] }

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

const ZOOM_FACTORS = [0.75, 0.9, 1, 1.15, 1.3, 1.5, 1.75, 2];
export const PDF_FIT = { factor: 1 };
export interface PdfZoomState {
  factor: number;
  textFit?: number;
}

export function PdfZoom({ zoom, onChange }: { zoom: PdfZoomState; onChange(zoom: PdfZoomState): void }) {
  const lower = ZOOM_FACTORS.filter((factor) => factor < zoom.factor - 0.005).at(-1);
  const higher = ZOOM_FACTORS.find((factor) => factor > zoom.factor + 0.005);
  return (
    <span className="view-toggle pdf-zoom" role="group" aria-label="PDF zoom">
      <button type="button" aria-label="Zoom out PDF" disabled={lower === undefined} onClick={() => lower !== undefined && onChange({ factor: lower })}>−</button>
      <button type="button" aria-label="Fit PDF to width" title="Fit the full page width" onClick={() => onChange(PDF_FIT)}>
        {Math.round(zoom.factor * 100)}%
      </button>
      <button type="button" aria-label="Zoom in PDF" disabled={higher === undefined} onClick={() => higher !== undefined && onChange({ factor: higher })}>+</button>
      <button type="button" aria-pressed={zoom.textFit !== undefined} onClick={() => onChange({ factor: zoom.factor, textFit: (zoom.textFit ?? 0) + 1 })}>Fit text</button>
    </span>
  );
}

/** Measure the visible ink, including graphics, on a small white-backed rendering of the page. */
async function renderInk(pdf: PDFDocumentProxy, page: number) {
  const sheet = await pdf.getPage(page);
  const scale = 180 / sheet.getViewport({ scale: 1 }).width;
  const viewport = sheet.getViewport({ scale });
  const canvas = document.createElement("canvas");
  canvas.width = Math.ceil(viewport.width);
  canvas.height = Math.ceil(viewport.height);
  const context = canvas.getContext("2d", { willReadFrequently: true });
  if (!context) throw new Error("The PDF needs a canvas to measure its printed area");
  await sheet.render({ canvasContext: context, viewport, background: "#fff" }).promise;
  return { image: context.getImageData(0, 0, canvas.width, canvas.height), scale };
}

function inkBounds({ width, height, data }: ImageData, first = 0, last = height) {
  const top = Math.max(0, Math.floor(first));
  const bottom = Math.min(height, Math.ceil(last));
  const minimum = Math.max(bottom - top > 20 ? 2 : 1, Math.round((bottom - top) * 0.006));
  let left = width;
  let right = 0;
  for (let x = 0; x < width; x++) {
    let pixels = 0;
    for (let y = top; y < bottom && pixels < minimum; y++) {
      const i = (y * width + x) * 4;
      if (Math.min(data[i], data[i + 1], data[i + 2]) < 223) pixels++;
    }
    if (pixels < minimum) continue;
    left = Math.min(left, x);
    right = x + 1;
  }
  return right > left ? { left: left / width, right: right / width } : null;
}

interface ReadingPoint extends PdfLocation {
  x: number;
}

function readingPointAt(view: HTMLElement, pages: ArrayLike<HTMLElement>, marks: PdfMarks, line: number): ReadingPoint | null {
  if (!pages.length) return null;
  let lo = 0;
  let hi = pages.length - 1;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (pages[mid].getBoundingClientRect().bottom < line) lo = mid + 1;
    else hi = mid;
  }
  const rect = pages[lo].getBoundingClientRect();
  if (!rect.width) return null;
  return { page: lo + 1, y: (line - rect.top) * marks.pages[lo][0] / rect.width,
    x: (view.getBoundingClientRect().left + view.clientWidth / 2 - rect.left) / rect.width };
}

export interface PdfViewHandle {
  captureZoom(): void;
}

interface Props {
  ref?: Ref<PdfViewHandle>;
  zoom: PdfZoomState;
  onTextFit(factor: number): void;
  url: string;
  label?: string;
  marks: PdfMarks;
  /** The selected phrase's place in the text (`b<start>-<end>`), if any. */
  at?: string;
  pinned: boolean;
  /** A temporary selection for the highlights, independent of the address that opens the PDF. */
  selectionAt?: string;
  shownTie: ReaderSignals["shownTie"];
  page?: number;
  position?: PdfLocation;
  reference?: PdfLocation & { tone?: number };
  onPick(id: string, mark: PdfMark, page: number): void;
  readingLine(): number;
  onPosition(page: number, at: string | undefined, byte?: number): void;
}

export function PdfView({ ref, url, marks, at, pinned, selectionAt, shownTie, page, position, reference, label, onPick, readingLine, onPosition, zoom, onTextFit }: Props) {
  const box = useRef<HTMLDivElement>(null);
  const [pdf, setPdf] = useState<PDFDocumentProxy | null>(null);
  const [failed, setFailed] = useState(false);
  const [fitWidth, setFitWidth] = useState(0);
  const width = Math.round(fitWidth * zoom.factor);
  const readingPoint = useRef<ReadingPoint | null>(null);
  const zoomAnchor = useRef<{ point: ReadingPoint; requested: boolean } | null>(null);
  const previousWidth = useRef(width);
  const [fitCentre, setFitCentre] = useState<{ request: number; x: number } | null>(null);
  const centre = fitCentre && fitCentre.request === zoom.textFit ? fitCentre.x : undefined;
  const previousCentre = useRef(centre);
  const previousFit = useRef(zoom.textFit);

  useImperativeHandle(ref, () => ({
    captureZoom() {
      const view = box.current;
      if (!view || zoomAnchor.current?.requested) return;
      const point = readingPointAt(view, view.querySelectorAll<HTMLElement>(".pdf-view__page"), marks, readingLine());
      if (point) zoomAnchor.current = { point, requested: true };
    },
  }), [marks, readingLine]);

  useLayoutEffect(() => {
    const changed = previousWidth.current !== width || previousCentre.current !== centre || previousFit.current !== zoom.textFit;
    previousWidth.current = width;
    previousCentre.current = centre;
    previousFit.current = zoom.textFit;
    if (!changed || !width) return;
    const view = box.current;
    const anchor = zoomAnchor.current;
    const point = anchor?.point ?? readingPoint.current;
    const pageEl = point && view?.querySelector<HTMLElement>(`[data-page="${point.page}"]`);
    if (!view || !point || !pageEl) return;
    const place = () => {
      const scale = pageEl.clientWidth / marks.pages[point.page - 1][0];
      window.scrollTo({
        top: window.scrollY + pageEl.getBoundingClientRect().top + point.y * scale - readingLine(),
        behavior: "instant",
      });
      view.scrollLeft = Math.max(0, (centre ?? point.x) * pageEl.clientWidth - view.clientWidth / 2);
    };
    zoomAnchor.current = { point, requested: anchor?.requested ?? false };
    // The paper can still report its old dimensions while the canvases resize.
    const expectedHeight = Math.round(marks.pages[point.page - 1][1] * width / marks.pages[point.page - 1][0]);
    const deadline = performance.now() + 1000;
    let frame = 0;
    const afterResize = (now: number) => {
      if (now < deadline && (pageEl.clientWidth !== width || pageEl.clientHeight !== expectedHeight)) {
        frame = requestAnimationFrame(afterResize);
        return;
      }
      place();
      frame = requestAnimationFrame(() => {
        place();
        const x = (view.getBoundingClientRect().left + view.clientWidth / 2 - pageEl.getBoundingClientRect().left) / pageEl.clientWidth;
        readingPoint.current = { ...point, x };
        if (zoom.textFit === undefined || centre !== undefined) zoomAnchor.current = null;
      });
    };
    frame = requestAnimationFrame(afterResize);
    return () => cancelAnimationFrame(frame);
  }, [centre, width, zoom.textFit, marks, readingLine]);

  const pageInk = useMemo(() => {
    if (!pdf) return null;
    const recent = new Map<number, ReturnType<typeof renderInk>>();
    return (page: number) => {
      if (!recent.has(page)) {
        if (recent.size >= 8) recent.delete(recent.keys().next().value!);
        recent.set(page, renderInk(pdf, page).catch((error) => {
          recent.delete(page);
          throw error;
        }));
      }
      return recent.get(page)!;
    };
  }, [pdf]);

  useEffect(() => {
    const request = zoom.textFit;
    if (request === undefined || !pageInk) {
      if (request === undefined) setFitCentre(null);
      return;
    }
    let cancelled = false;
    const currentPage = (zoomAnchor.current?.point ?? readingPoint.current)?.page ?? 1;
    const fit = (bounds: ReturnType<typeof inkBounds>) => {
      if (cancelled) return;
      const { left, right } = bounds ?? { left: 0, right: 1 };
      const x = (left + right) / 2;
      const factor = Math.max(1, Math.min(ZOOM_FACTORS.at(-1)!, 1 / (right - left + 0.05)));
      setFitCentre({ request, x });
      onTextFit(factor);
    };
    void pageInk(currentPage).then(({ image }) => fit(inkBounds(image)), () => fit(null));
    return () => { cancelled = true; };
  }, [pageInk, zoom.textFit, onTextFit]);

  const [referenceInk, setReferenceInk] = useState<(PdfLocation & { left: number; right: number }) | null>(null);
  const referencePage = reference?.page;
  const referenceY = reference?.y;
  useEffect(() => {
    if (!pageInk || referencePage === undefined || referenceY === undefined) return;
    let live = true;
    void pageInk(referencePage).then(({ image, scale }) => {
      const bounds = inkBounds(image, (referenceY - 2) * scale, (referenceY + 17) * scale) ?? inkBounds(image);
      if (live && bounds) setReferenceInk({ page: referencePage, y: referenceY, ...bounds });
    }, () => {});
    return () => { live = false; };
  }, [pageInk, referencePage, referenceY]);
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
    const measure = () => setFitWidth(el.clientWidth);
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, []);

  // Open at the selected phrase, else at the page asked for.
  const opened = useRef(false);
  const measured = fitWidth > 0;
  useLayoutEffect(() => {
    if (!measured || !pdf) return;
    const target = !position && selected ? box.current?.querySelector<HTMLElement>(`[data-mark="${CSS.escape(selected)}"]`) : null;
    const pageEl = !target && page ? box.current?.querySelector<HTMLElement>(`[data-page="${page}"]`) : null;
    const el = target ?? pageEl;
    const first = !opened.current;
    opened.current = true;
    if (!el) return;
    const landOn = (behavior: ScrollBehavior) => {
      if (position) {
        const y = position.y * el.clientWidth / marks.pages[position.page - 1][0];
        window.scrollTo({ top: window.scrollY + el.getBoundingClientRect().top + y - readingLine(), behavior });
      } else {
        el.scrollIntoView({ block: target ? "center" : "start", behavior });
      }
    };
    landOn(first || prefersReducedMotion() ? "instant" as ScrollBehavior : "smooth");
  }, [measured, pdf, selected, page, position?.page, position?.y, marks, readingLine]);

  // Report the page at the reading line.
  useEffect(() => {
    const el = box.current;
    if (!el || !width) return;
    const pages = el.querySelectorAll<HTMLElement>(".pdf-view__page");
    if (!pages.length) return;
    let frame = 0;
    const read = () => {
      frame = 0;
      const point = readingPointAt(el, pages, marks, readingLine());
      if (!point) return;
      readingPoint.current = point;
      const { page } = point;
      const scale = width / marks.pages[page - 1][0];
      const pageTop = pages[page - 1].getBoundingClientRect().top;
      const y = Math.max(0, Math.min(marks.pages[page - 1][1], point.y));
      let best: PdfMark | undefined;
      let distance = Infinity;
      for (const [, mark] of byPage.get(page) ?? []) {
        for (const [p, , top, , bottom] of mark.boxes) {
          if (p !== page || pageTop + bottom * scale <= 0 || pageTop + top * scale >= window.innerHeight) continue;
          const gap = Math.max(0, top - y, y - bottom) * scale;
          if (gap < distance && gap <= window.innerHeight * 0.32) {
            distance = gap;
            best = mark;
          }
        }
      }
      onPosition(page, best?.at, byteAtPdfLocation(marks, page, y));
    };
    const schedule = () => { if (!frame) frame = requestAnimationFrame(read); };
    read();
    window.addEventListener("scroll", schedule, { passive: true });
    window.addEventListener("resize", schedule);
    el.addEventListener("scroll", schedule, { passive: true });
    return () => {
      cancelAnimationFrame(frame);
      window.removeEventListener("scroll", schedule);
      window.removeEventListener("resize", schedule);
      el.removeEventListener("scroll", schedule);
    };
  }, [width, byPage, marks, readingLine, onPosition]);

  // Paint the existing click targets without re-rendering the pages or landing again.
  useLayoutEffect(() => {
    const el = box.current;
    if (!el || !width) return;
    let lit: NodeListOf<HTMLElement> | undefined;
    let currentAt: string | undefined;
    const paint = () => {
      const next = pinned ? selectionAt ?? at : shownTie.get()?.at;
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
  }, [width, marks, pinned, at, selectionAt, shownTie]);

  if (failed) return <p className="pdf-view__failed">The PDF could not be opened here. Open PDF opens it in a new tab.</p>;
  return (
    <div className="pdf-view" ref={box} aria-label={label ?? "The authors’ PDF"}
      aria-busy={zoom.textFit !== undefined && centre === undefined || undefined}>
      <div className="pdf-view__pages" style={{ width }}>
      {width > 0 &&
        marks.pages.map(([w, h], i) => {
          const scale = width / w;
          return (
            <section key={i} className="pdf-view__page" data-page={i + 1} style={{ height: Math.round(h * scale) }} aria-label={`Page ${i + 1}`}>
              {pdf && <PdfCanvas pdf={pdf} number={i + 1} width={width} />}
              {reference?.page === i + 1 && referenceInk?.page === reference.page && referenceInk.y === reference.y && (
                <div aria-hidden="true" className="pdf-view__reference-landing" data-reference-landing="" data-tone={reference.tone}
                  style={{ top: Math.max(0, reference.y - 4) * scale, height: 22 * scale,
                    left: `${Math.max(0, referenceInk.left * 100 - 1.2)}%`,
                    right: `${Math.max(0, 98.8 - referenceInk.right * 100)}%` }} />
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

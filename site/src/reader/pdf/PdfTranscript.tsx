// Reflow the full text of a PDF when an edition has no matching source manuscript.
// Take links from the same PDF rectangles as the facsimile, never from notes
// or from a new search for a similar-looking phrase.
import { Fragment, useEffect, useRef, useState } from "react";
import type { PDFDocumentProxy } from "pdfjs-dist";
import type { PdfMark } from "./PdfView";

interface WordRun { text: string; left: number; right: number; top: number; bottom: number }
interface Line { runs: WordRun[]; top: number; bottom: number; left: number }

async function readPage(pdf: PDFDocumentProxy, number: number): Promise<Line[]> {
  const page = await pdf.getPage(number);
  const { height } = page.getViewport({ scale: 1 });
  const lines: Line[] = [];
  for (const item of (await page.getTextContent()).items) {
    if (!("str" in item) || !item.str.trim()) continue;
    const [, , , , left, baseline] = item.transform;
    const bottom = height - baseline;
    const run = { text: item.str, left, right: left + item.width,
      top: bottom - item.height, bottom };
    const previous = lines.at(-1);
    if (previous && Math.abs(previous.bottom - bottom) < Math.max(2, item.height * 0.44)) {
      previous.runs.push(run);
      previous.top = Math.min(previous.top, run.top);
      previous.left = Math.min(previous.left, left);
    } else {
      lines.push({ runs: [run], top: run.top, bottom, left });
    }
  }
  return lines.sort((a, b) => a.bottom - b.bottom || a.left - b.left);
}

export function usePdfTranscript(pdf: PDFDocumentProxy | null, enabled: boolean) {
  const [result, setResult] = useState<{ pdf: PDFDocumentProxy; pages: Line[][] } | null>(null);
  const [failed, setFailed] = useState<PDFDocumentProxy | null>(null);
  useEffect(() => {
    if (!pdf || !enabled || result?.pdf === pdf) return;
    let active = true;
    const load = async () => {
      const pages: Line[][] = [];
      for (let start = 1; start <= pdf.numPages && active; start += 8) {
        const numbers = Array.from({ length: Math.min(8, pdf.numPages - start + 1) }, (_, i) => start + i);
        pages.push(...await Promise.all(numbers.map((number) => readPage(pdf, number))));
      }
      if (active) setResult({ pdf, pages });
    };
    void load().catch(() => { if (active) setFailed(pdf); });
    return () => { active = false; };
  }, [pdf, enabled, result]);
  return { pages: result?.pdf === pdf ? result.pages : null, failed: !!pdf && failed === pdf };
}

/** Group adjacent words with the same verified rectangle into one keyboard stop. */
function linkedLine(line: Line, marks: [string, PdfMark][], page: number) {
  const spans: { text: string; mark?: [string, PdfMark] }[] = [];
  const append = (text: string, mark?: [string, PdfMark]) => {
    const last = spans.at(-1);
    if (last && last.mark === mark) last.text += text;
    else spans.push({ text, mark });
  };
  const runs = [...line.runs].sort((a, b) => a.left - b.left);
  for (const [index, run] of runs.entries()) {
    if (index > 0 && run.left - runs[index - 1].right > 1.5) append(" ");
    let offset = 0;
    for (const text of run.text.match(/\S+\s*|\s+/gu) ?? []) {
      const middle = run.left + (run.right - run.left) * (offset + text.trimEnd().length / 2) / run.text.length;
      offset += text.length;
      const mark = marks.find(([, mark]) => mark.boxes.some(([p, x0, y0, x1, y1]) =>
        p === page && middle >= x0 - 1 && middle <= x1 + 1 && run.bottom >= y0 && run.top <= y1
        && run.bottom <= y1 + 4));
      append(text, mark);
    }
  }
  return spans;
}

function printedLine(line: Line) {
  return line.runs.map((run) => run.text).join(" ");
}

function needsOriginal(line: Line) {
  const text = printedLine(line);
  const prose = text.match(/\p{L}{3,}/gu)?.length ?? 0;
  return /[\u0000-\u001f\ufffd\ue000-\uf8ff]/u.test(text)
    || (prose < 3 && /[=∑≤≥∫√∏+−⋅∈∞→⊢λ]/u.test(text));
}

// A PDF's extractable glyph order cannot reproduce a fraction or a multi-line
// display. Paint that strip using the same PDF engine as the facsimile.
function OriginalStrip({ pdf, page, width, low, high }: {
  pdf: PDFDocumentProxy; page: number; width: number; low: number; high: number;
}) {
  const canvas = useRef<HTMLCanvasElement>(null);
  useEffect(() => {
    const el = canvas.current;
    if (!el) return;
    let active = true;
    let task: ReturnType<Awaited<ReturnType<PDFDocumentProxy["getPage"]>>["render"]> | null = null;
    const observer = new IntersectionObserver((entries) => {
      if (!entries.some((entry) => entry.isIntersecting)) return;
      observer.disconnect();
      void pdf.getPage(page).then((doc) => {
        if (!active) return;
        const ratio = window.devicePixelRatio || 1;
        const scale = ratio * el.clientWidth / width;
        if (!scale) return;
        const viewport = doc.getViewport({ scale });
        el.width = Math.ceil(viewport.width);
        el.height = Math.ceil((high - low) * scale);
        task = doc.render({ canvasContext: el.getContext("2d")!, viewport,
          transform: [1, 0, 0, 1, 0, -low * scale], background: "#fff" });
        void task.promise.catch(() => {});
      }).catch(() => {});
    }, { rootMargin: "400px 0px" });
    observer.observe(el);
    return () => { active = false; observer.disconnect(); task?.cancel(); };
  }, [pdf, page, width, low, high]);
  return <canvas ref={canvas} aria-hidden="true" style={{ aspectRatio: `${width} / ${high - low}` }} />;
}

export function TranscriptPage({ pdf, lines, page, pageWidth, pageHeight, marks, onPick }: {
  pdf: PDFDocumentProxy; lines: Line[]; page: number; pageWidth: number; pageHeight: number;
  marks: [string, PdfMark][]; onPick(id: string, mark: PdfMark, page: number): void;
}) {
  const first = new Set<string>();
  const markId = (id: string) => {
    const result = first.has(id) ? undefined : id;
    first.add(id);
    return result;
  };
  const paragraphs: { original: boolean; lines: Line[] }[] = [];
  for (const line of lines) {
    const original = needsOriginal(line);
    const paragraph = paragraphs.at(-1);
    const previous = paragraph?.lines.at(-1);
    if (paragraph && previous && original === paragraph.original &&
      line.top - previous.bottom <= (original ? 14 : 7) &&
      (original || Math.abs(line.left - previous.left) < 17)) {
      paragraph.lines.push(line);
    } else {
      paragraphs.push({ original, lines: [line] });
    }
  }
  return (
    <>
      <div className="pdf-transcript__page-label">Page {page}</div>
      {paragraphs.map(({ original, lines: wrapped }, index) => {
        const top = Math.min(...wrapped.map((line) => line.top));
        if (original && wrapped.length > 0) {
          const low = Math.max(0, top - 2);
          const high = Math.min(pageHeight, Math.max(...wrapped.map((line) => line.bottom)) + 5);
          return (
            <div key={index} className="pdf-transcript__original" data-pdf-y={top}>
              <span className="visually-hidden">{wrapped.map(printedLine).join(" ")}</span>
              <OriginalStrip pdf={pdf} page={page} width={pageWidth} low={low} high={high} />
              {marks.flatMap(([id, tie]) => tie.boxes.filter(([p, , y0, , y1]) =>
                p === page && y0 < high && y1 > low).map(([, x0, y0, x1, y1], i) => (
                <button key={`${id}-${i}`} type="button" className="pdf-view__mark tie"
                  data-mark={markId(id)} data-at={tie.at} data-tone={tie.tone ?? undefined}
                  aria-label="Open the Lean this phrase is tied to"
                  style={{ left: `${x0 / pageWidth * 100}%`, top: `${(Math.max(y0, low) - low) / (high - low) * 100}%`,
                    width: `${(x1 - x0) / pageWidth * 100}%`, height: `${(Math.min(y1, high) - Math.max(y0, low)) / (high - low) * 100}%` }}
                  onClick={() => onPick(id, tie, page)} />
              )))}
            </div>
          );
        }
        return (
          <p key={index}>
            {wrapped.map((line, lineIndex) => (
              <Fragment key={lineIndex}>
                {lineIndex > 0 && " "}
                <span data-pdf-y={line.top}>
                  {linkedLine(line, marks, page).map(({ text, mark }, i) => {
                    if (!mark || !text.trim()) return <Fragment key={i}>{text}</Fragment>;
                    const [id, tie] = mark;
                    return <button key={i} type="button" className="pdf-transcript__mark tie"
                      data-mark={markId(id)} data-at={tie.at} data-tone={tie.tone ?? undefined}
                      onClick={() => onPick(id, tie, page)}>{text}</button>;
                  })}
                </span>
              </Fragment>
            ))}
          </p>
        );
      })}
    </>
  );
}

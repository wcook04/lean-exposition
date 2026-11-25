// Prepared documents, shared by every view that shows paper text: the reader,
// the theorem plate, the record panel and passages opened beside another.

import { useEffect, useState } from "react";
import type { Stage } from "../api/types";
import { discoveryInfo } from "../api/client";
import site from "@instance/site";
import { loadPaper, type PaperData } from "../app/data";
import { prepareDocument, type PreparedDocument } from "./engine";
import type { TieIndex } from "../api/lean";
import { loadReferenceTable, type ReferenceTable } from "./references";
import { loadTies, tieModel, type TieModel } from "./ties";
import { PAPER_PDFS } from "virtual:paper-pdfs";

const escapeHtml = (text: string) => text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

const ADAPTED_PROCESS_NOTE = 'See the <a href="https://www.youtube.com/watch?v=QIMDizV8u_I">2:12 funnel video</a> for how the edition was made.';

export function adaptedDisclosureHtml(stage: Stage): string | null {
  const words = site.frontCredit?.[stage];
  return words && site.adapted?.slot === stage ? `${escapeHtml(words)} ${ADAPTED_PROCESS_NOTE}` : null;
}

/** The credit line under a paper's authors, as HTML: the site's words, then About and the authors' PDF. */
export function frontCreditHtml(stage: Stage): string | null {
  const words = site.frontCredit?.[stage];
  if (!words) return null;
  const pdf = PAPER_PDFS[stage] as { path: string; pages: number } | undefined;
  const adapted = site.adapted?.slot === stage ? site.adapted : undefined;
  const base = import.meta.env.BASE_URL;
  if (adapted) {
    // An adapted edition: its line, the authors' paper and the edition's marked PDFs.
    const pdfs = [
      ...(pdf ? [`<a class="pdf-link" href="${escapeHtml(`${base}${pdf.path}`)}" target="_blank" rel="noopener">${escapeHtml(adapted.pdfs[0]?.label ?? "Open PDF")}, ${pdf.pages} ${pdf.pages === 1 ? "page" : "pages"}</a>`] : []),
      ...adapted.pdfs.slice(1).map((p) => `<a class="pdf-link" href="${escapeHtml(`${base}pdf/${p.name}`)}" target="_blank" rel="noopener">${escapeHtml(p.label)}</a>`),
    ];
    return `${adaptedDisclosureHtml(stage)} <a href="${escapeHtml(`${base}${adapted.of === site.library?.main ? "" : `read/${adapted.of}/`}`)}">Read the authors’ paper</a>.${pdfs.length ? ` ${pdfs.join(" · ")}.` : ""}`;
  }
  const pdfLink = pdf
    ? ` <a class="pdf-link" href="${escapeHtml(`${import.meta.env.BASE_URL}${pdf.path}`)}" target="_blank" rel="noopener">Open PDF, ${pdf.pages} ${pdf.pages === 1 ? "page" : "pages"}</a>.`
    : "";
  return `${escapeHtml(words)} <a href="${escapeHtml(`${import.meta.env.BASE_URL}about/#about-credit`)}">Full credit</a>.${pdfLink}`;
}

export interface LoadedDocument {
  paper: PaperData;
  doc: PreparedDocument;
  /** What the paper's words are tied to. Arrives with the paper, so the marks are there at first paint. */
  ties: TieModel;
}

const DEFAULT_PATHS: Record<Stage, string> = {
  long: "long/reasoning-record.md",
  short: "short/paper.md",
  expository: "expository/main.md",
};

// A library paper's companion documents, each at <id>/paper.md as in its source, so a link from one
// companion to another (../<id>/paper.md) opens that companion.
const COMPANION_PATHS: Record<string, string> = Object.fromEntries(
  (site.library?.companions ?? []).map((c) => [c.slot, `${c.id ?? c.slot}/paper.md`]),
);

export function documentPaths(): Record<string, string> {
  const configured = discoveryInfo()?.companion_resolution;
  if (configured?.configured) return { ...DEFAULT_PATHS, ...COMPANION_PATHS, ...configured.document_paths } as Record<string, string>;
  return { ...DEFAULT_PATHS, ...COMPANION_PATHS };
}

const prepared = new Map<Stage, Promise<LoadedDocument>>();

/** A paper's bytes, parts, ties and reference table as the page renders them. The build's first screen uses this too. */
export function preparePaper(paper: PaperData, index: TieIndex | null, referenceTable: ReferenceTable | null): PreparedDocument {
  const paths = documentPaths();
  const stage = paper.stage;
  const parts = paper.structure.paper.document_parts.map((part) => ({
    kind: part.kind,
    span: { start_byte: part.span.start_byte, end_byte: part.span.end_byte },
    passageAnchor: part.passage_ref ? part.passage_ref.slice(part.passage_ref.lastIndexOf("/") + 1) : undefined,
  }));
  return prepareDocument({ stage, bytes: paper.bytes, parts, documentPath: paths[stage], documentPaths: paths, ties: index?.segments, tieTones: index?.segments.map(([, , ids]) => index.ties[ids[0]]?.tone), referenceTable, sectionAids: site.sectionAids?.[stage] ?? null, frontCredit: frontCreditHtml(stage), frontCreditNote: site.frontCreditNote?.[stage] ?? null, frontCreditNoteSuffix: site.adapted?.slot === stage ? ADAPTED_PROCESS_NOTE : null });
}

export function loadDocument(stage: Stage): Promise<LoadedDocument> {
  let pending = prepared.get(stage);
  if (!pending) {
    pending = Promise.all([loadPaper(stage), loadTies(stage), loadReferenceTable(stage)]).then(([paper, index, referenceTable]) => {
      return { paper, doc: preparePaper(paper, index, referenceTable), ties: tieModel(index) };
    });
    pending.catch(() => prepared.delete(stage));
    prepared.set(stage, pending);
  }
  return pending;
}

type State = { status: "loading" } | { status: "ready"; value: LoadedDocument } | { status: "error"; error: unknown };

export function useDocument(stage: Stage | null): State {
  const [state, setState] = useState<State>({ status: "loading" });
  useEffect(() => {
    if (!stage) return;
    let alive = true;
    setState({ status: "loading" });
    loadDocument(stage).then(
      (value) => alive && setState({ status: "ready", value }),
      (error: unknown) => alive && setState({ status: "error", error }),
    );
    return () => {
      alive = false;
    };
  }, [stage]);
  return stage ? state : { status: "loading" };
}

/** The part index holding a passage, or -1. */
export function partOfPassage(doc: PreparedDocument, anchor: string): number {
  return doc.parts.findIndex((p) => p.kind === "passage" && p.anchor === anchor);
}

/**
 * The heading a reader would land on for a passage: the first heading inside
 * the passage when it opens with one, otherwise the section containing it.
 * The document title is never used as a section name.
 */
export function sectionTitleOf(paper: PaperData, anchor: string): string | null {
  const passage = paper.structure.paper.passages.find((p) => p.anchor === anchor);
  if (!passage) return null;
  const sections = paper.structure.paper.sections;
  const inside = sections.find(
    (s) => s.heading_span.start_byte >= passage.block_span.start_byte && s.heading_span.start_byte < passage.content_span.end_byte,
  );
  if (inside && inside.level > 1) return inside.title;
  const containing = sections.find((s) => s.ref === passage.section_ref);
  return containing && containing.level > 1 ? containing.title : null;
}

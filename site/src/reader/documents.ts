// Prepared documents, shared by every view that shows paper text: the reader,
// the theorem plate, the record panel and passages opened beside another.

import { useEffect, useState } from "react";
import type { Stage } from "../api/types";
import { discoveryInfo } from "../api/client";
import { loadPaper, type PaperData } from "../app/data";
import { prepareDocument, type PreparedDocument } from "./engine";
import { loadTies, tieModel, type TieModel } from "./ties";

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

export function documentPaths(): Record<string, string> {
  const configured = discoveryInfo()?.companion_resolution;
  if (configured?.configured) return { ...DEFAULT_PATHS, ...configured.document_paths } as Record<string, string>;
  return DEFAULT_PATHS;
}

const prepared = new Map<Stage, Promise<LoadedDocument>>();

export function loadDocument(stage: Stage): Promise<LoadedDocument> {
  let pending = prepared.get(stage);
  if (!pending) {
    pending = Promise.all([loadPaper(stage), loadTies(stage)]).then(([paper, index]) => {
      const paths = documentPaths();
      const parts = paper.structure.paper.document_parts.map((part) => ({
        kind: part.kind,
        span: { start_byte: part.span.start_byte, end_byte: part.span.end_byte },
        passageAnchor: part.passage_ref ? part.passage_ref.slice(part.passage_ref.lastIndexOf("/") + 1) : undefined,
      }));
      const doc = prepareDocument({ stage, bytes: paper.bytes, parts, documentPath: paths[stage], documentPaths: paths, ties: index?.segments });
      return { paper, doc, ties: tieModel(index) };
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

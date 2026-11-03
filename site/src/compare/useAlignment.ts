// The record alignment, loaded once when a page first needs it and never at startup.
// An edition without the sidecar answers null, and every caller falls back to the
// graph's own labels and passages.
//
// There are four depths, and a page asks for the shallowest that serves it. The core has
// every record's Lean and every statement's place, and it is what `useAlignment` gives. A
// panel adds the one record it opens on, and a paper's reader adds that paper's statements.
// Only a page that quotes the statements of all three papers needs the whole, and each depth
// reuses what the one before it fetched.

import { useEffect, useState } from "react";
import { RECORD_INDEX, type RecordLine } from "virtual:record-index";
import { loadAlignment, loadAlignmentCore, loadAlignmentPaper, loadAlignmentRecord, withPapers, type Alignment, type AlignmentCore, type AlignmentPaper, type RecordAlignment } from "../api/lean";
import type { Stage } from "../api/types";

const STAGES: readonly Stage[] = ["long", "short", "expository"];
const split = import.meta.env.VITE_STATIC_EDITION === "true";

/** A server, or a static edition from before the split, has one file and it is the whole. */
const whole = (): Promise<Alignment | null> => loadAlignment().catch(() => null);

let core: Promise<AlignmentCore | null> | null = null;
let settledCore: AlignmentCore | null | undefined;
let full: Promise<Alignment | null> | null = null;
let settledFull: Alignment | null | undefined;
const papers = new Map<Stage, Promise<AlignmentPaper>>();
const forPaper = new Map<Stage, Promise<Alignment | null>>();

const settleCore = (value: AlignmentCore | null) => (settledCore = value);

/** Every record's Lean and every statement's place, and no statement's words. */
export function alignmentResource(): Promise<AlignmentCore | null> {
  core ??= (full ?? (split ? loadAlignmentCore().catch(() => whole()) : whole())).then(settleCore);
  return core;
}

function paperFile(stage: Stage): Promise<AlignmentPaper> {
  let pending = papers.get(stage);
  if (!pending) {
    pending = loadAlignmentPaper(stage);
    pending.catch(() => papers.delete(stage));
    papers.set(stage, pending);
  }
  return pending;
}

async function withWords(stages: readonly Stage[]): Promise<Alignment | null> {
  // Started together, so one depth costs one wait. An edition without the split refuses these.
  const files = split ? Promise.all(stages.map(paperFile)) : Promise.resolve([]);
  files.catch(() => undefined);
  const value = await alignmentResource();
  if (!value || value.representation !== "alignment_core") return value as Alignment | null;
  return withPapers(value, await files) as Alignment;
}

/**
 * The alignment as a reader of one paper needs it: that paper's statements in full, the
 * others' places and Lean names, which are what its links to another paper read.
 */
export function paperAlignmentResource(stage: Stage): Promise<Alignment | null> {
  let pending = forPaper.get(stage);
  if (!pending) {
    pending = withWords([stage]).catch(() => null);
    forPaper.set(stage, pending);
  }
  return pending;
}

/** Everything, for a page that quotes all three papers. */
export function fullAlignmentResource(): Promise<Alignment | null> {
  // Nothing fetched yet: the one file is smaller than its parts.
  full ??= (core || papers.size ? withWords(STAGES) : whole()).then(
    (value) => {
      settledFull = value;
      if (value) settledCore ??= value;
      return value;
    },
    () => (settledFull = null),
  );
  return full;
}

function useLoaded<T>(settled: () => T | null | undefined, load: () => Promise<T | null>, wanted = true): T | null {
  const [value, setValue] = useState<T | null>(settled() ?? null);
  useEffect(() => {
    if (!wanted) return;
    if (settled() !== undefined) return setValue(settled() ?? null);
    let alive = true;
    void load().then((loaded) => alive && setValue(loaded));
    return () => {
      alive = false;
    };
    // The loaders are module functions; only `wanted` changes.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [wanted]);
  return value;
}

/** The core, or null while it loads and for an edition that has none. */
export function useAlignment(): AlignmentCore | null {
  return useLoaded(() => settledFull ?? settledCore, alignmentResource);
}

/** The whole alignment, or null while it loads and for an edition that has none. */
export function useFullAlignment(wanted = true): Alignment | null {
  return useLoaded(() => settledFull, fullAlignmentResource, wanted);
}

const records = new Map<string, Promise<RecordAlignment | null>>();

function recordResource(id: string): Promise<RecordAlignment | null> {
  let pending = records.get(id);
  if (!pending) {
    const file = split ? loadAlignmentRecord(id).catch(() => null) : null;
    pending = alignmentResource().then((value) => {
      if (value?.representation === "alignment_core") return file;
      return (value as Alignment | null)?.records[id] ?? null;
    });
    records.set(id, pending);
  }
  return pending;
}

/** One record whole, the core's depth plus its own statements. A record the alignment does not hold has none. */
export function useRecordAlignment(id: string | null | undefined): RecordAlignment | null {
  const [loaded, setLoaded] = useState<{ id: string; row: RecordAlignment | null } | null>(null);
  useEffect(() => {
    if (!id || settledFull !== undefined) return;
    let alive = true;
    void recordResource(id).then((row) => alive && setLoaded({ id, row }));
    return () => {
      alive = false;
    };
  }, [id]);
  if (!id) return null;
  return settledFull?.records[id] ?? (loaded?.id === id ? loaded.row : null);
}

/** A record's short title for tiles. It ships in the bundle, so it is there at first paint. */
export function shortTitle(id: string, label: string): string {
  return RECORD_INDEX[id]?.short || label;
}

/** What each level does with a record, for its marks. Also in the bundle. */
export function recordLine(id: string): RecordLine | undefined {
  return RECORD_INDEX[id];
}

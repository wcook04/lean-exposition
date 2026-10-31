// The record alignment, loaded once when a page first needs it and never at startup.
// An edition without the sidecar answers null, and every caller falls back to the
// graph's own labels and passages.

import { useEffect, useState } from "react";
import { RECORD_INDEX, type RecordLine } from "virtual:record-index";
import { loadAlignment, type Alignment, type RecordAlignment } from "../api/lean";

let pending: Promise<Alignment | null> | null = null;
let settled: Alignment | null | undefined;

export function alignmentResource(): Promise<Alignment | null> {
  pending ??= loadAlignment().then(
    (value) => (settled = value),
    () => (settled = null),
  );
  return pending;
}

/** The alignment, or null while it loads and for an edition that has none. */
export function useAlignment(): Alignment | null {
  const [value, setValue] = useState<Alignment | null>(settled ?? null);
  useEffect(() => {
    if (settled !== undefined) return;
    let alive = true;
    void alignmentResource().then((loaded) => alive && setValue(loaded));
    return () => {
      alive = false;
    };
  }, []);
  return value;
}

export function useRecordAlignment(id: string | null | undefined): RecordAlignment | null {
  const alignment = useAlignment();
  return (id && alignment?.records[id]) || null;
}

/** A record's short title for tiles. It ships in the bundle, so it is there at first paint. */
export function shortTitle(id: string, label: string): string {
  return RECORD_INDEX[id]?.short || label;
}

/** What each level does with a record, for its marks. Also in the bundle. */
export function recordLine(id: string): RecordLine | undefined {
  return RECORD_INDEX[id];
}

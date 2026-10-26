// Full evidence records, fetched in batches of at most 32 refs and kept for
// the session. Only the records a reader asks to see are requested.

import { useEffect, useState } from "react";
import { get } from "../api/client";
import type { Page } from "../api/types";

export interface EvidenceRecord {
  id: string;
  kind: string;
  status: string;
  tool?: string;
  details?: string;
  command?: string[];
  subject_ids?: string[];
  source_ids?: string[];
  receipt_path?: string;
  receipt_sha256?: string;
}

interface RecordItem {
  ref: string;
  table: string;
  record: EvidenceRecord;
}

export const BATCH = 32;

const cache = new Map<string, Promise<EvidenceRecord>>();

/** Split refs into batches of at most `size`. */
export function batches<T>(items: readonly T[], size = BATCH): T[][] {
  const out: T[][] = [];
  for (let i = 0; i < items.length; i += size) out.push(items.slice(i, i + size));
  return out;
}

export function loadEvidence(refs: readonly string[]): Promise<Map<string, EvidenceRecord>> {
  const missing = [...new Set(refs.filter((ref) => !cache.has(ref)))];
  for (const group of batches(missing)) {
    const request = get<Page<RecordItem>>("/records", { ref: group, limit: group.length }).then((r) => {
      const found = new Map(r.data.items.map((item) => [item.ref, item.record]));
      return found;
    });
    for (const ref of group) {
      const one = request.then((found) => {
        const record = found.get(ref);
        if (!record) throw new Error(`The edition has no evidence record ${ref}.`);
        return record;
      });
      one.catch(() => cache.delete(ref));
      cache.set(ref, one);
    }
  }
  return Promise.all(refs.map((ref) => cache.get(ref)!.then((record) => [ref, record] as const))).then((pairs) => new Map(pairs));
}

type State = { status: "idle" } | { status: "loading" } | { status: "ready"; records: Map<string, EvidenceRecord> } | { status: "error"; error: unknown };

/** Records for `refs`, or idle when `refs` is null (the reader has not asked). */
export function useEvidence(refs: readonly string[] | null): State {
  const key = refs ? refs.join("\n") : null;
  const [state, setState] = useState<State>({ status: "idle" });
  useEffect(() => {
    if (key === null) {
      setState({ status: "idle" });
      return;
    }
    let alive = true;
    const list = key ? key.split("\n") : [];
    setState((prev) => (prev.status === "ready" ? prev : { status: "loading" }));
    loadEvidence(list).then(
      (records) => alive && setState({ status: "ready", records }),
      (error: unknown) => alive && setState({ status: "error", error }),
    );
    return () => {
      alive = false;
    };
  }, [key]);
  return state;
}

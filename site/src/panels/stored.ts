// The stored edge and evidence records, read through the same pinned, cached
// requests the edition loader made, so this costs no new network round trip.
// The panels use them for what the site model does not (yet) keep: an
// application's shared objects, status and source span, how many relations
// share one recorded explanation, and the dated history of each check.

import { useState } from "react";
import { get } from "../api/client";
import type { EdgeRecord, EvidenceRecord, FullRecordItem, RecordDetail } from "../api/types";
import { useResource } from "../app/data";

async function allRecords<T>(table: string): Promise<T[]> {
  const out: T[] = [];
  for (let offset = 0; ; offset += 200) {
    const page = await get<{ items: FullRecordItem<T>[]; total: number }>("/records", { table, limit: 200, offset });
    out.push(...page.data.items.map((i) => i.record));
    if (page.data.items.length < 200 || out.length >= page.data.total) return out;
  }
}

export interface Stored {
  edges: Map<string, EdgeRecord>; // keyed "from→to→kind" with the stored kind
  evidence: Map<string, EvidenceRecord>;
  /** How many stored relations cite each evidence record. */
  uses: Map<string, number>;
}

export function useStored() {
  return useResource<Stored>("panel:stored", async () => {
    const [edges, evidence] = await Promise.all([allRecords<EdgeRecord>("edges"), allRecords<EvidenceRecord>("evidence")]);
    const uses = new Map<string, number>();
    for (const e of edges) for (const id of e.evidence_ids) uses.set(id, (uses.get(id) ?? 0) + 1);
    return {
      edges: new Map(edges.map((e) => [`${e.from}→${e.to}→${e.kind}`, e])),
      evidence: new Map(evidence.map((e) => [e.id, e])),
      uses,
    };
  });
}

/**
 * One record's detail with a retry that asks again on the same pinned
 * edition. A response for another record is never returned as this one's.
 */
export function useRecordDetail(ref: string | null) {
  const [attempt, setAttempt] = useState(0);
  const key = ref ? `record:${ref}${attempt ? `#${attempt}` : ""}` : null;
  const state = useResource<RecordDetail>(key, () => get<RecordDetail>("/record", { ref: ref! }).then((r) => r.data));
  const fresh = state.status === "ready" && state.value.ref !== ref ? ({ status: "loading" } as const) : state;
  return { state: fresh, retry: () => setAttempt((n) => n + 1) };
}

/** "not found" when the edition has no such record, else a generic failure. */
export function failureKind(error: unknown): "missing" | "failed" {
  const e = error as { status?: number; code?: string } | null;
  return e && (e.status === 404 || e.code === "record_not_found") ? "missing" : "failed";
}

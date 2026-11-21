// The source and citation collections, fetched once per edition and shared by
// every record panel.

import { get } from "../api/client";
import type { FullRecordItem, SourceRecord } from "../api/types";
import { useResource } from "../app/data";

export interface CitationRecord {
  id: string;
  title?: string;
  locator?: string;
  source_id?: string;
  url?: string;
}

export interface Provenance {
  sources: Map<string, SourceRecord>;
  citations: Map<string, CitationRecord>;
}

/** Every page of one table: the #257 graph has more than one page of citations. */
async function every<T>(table: string): Promise<T[]> {
  const out: T[] = [];
  for (let offset = 0; ; offset += 200) {
    const page = await get<{ items: FullRecordItem<T>[]; total: number }>("/records", { table, limit: 200, offset });
    out.push(...page.data.items.map((i) => i.record));
    if (page.data.items.length < 200 || out.length >= page.data.total) return out;
  }
}

export function useProvenance() {
  return useResource<Provenance>("panel:provenance", async () => {
    const [sources, citations] = await Promise.all([every<SourceRecord>("sources"), every<CitationRecord>("citations")]);
    return {
      sources: new Map(sources.map((r) => [r.id, r])),
      citations: new Map(citations.map((r) => [r.id, r])),
    };
  });
}

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

export function useProvenance() {
  return useResource<Provenance>("panel:provenance", async () => {
    const [sources, citations] = await Promise.all([
      get<{ items: FullRecordItem<SourceRecord>[] }>("/records", { table: "sources", limit: 200 }),
      get<{ items: FullRecordItem<CitationRecord>[] }>("/records", { table: "citations", limit: 200 }),
    ]);
    return {
      sources: new Map(sources.data.items.map((i) => [i.record.id, i.record])),
      citations: new Map(citations.data.items.map((i) => [i.record.id, i.record])),
    };
  });
}

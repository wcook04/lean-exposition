// The three accounts as reading-order strips: every mapped passage with its
// byte extent, claims and authored treatments, and the reading links between
// passages. Loaded from /papers/reading (cards cover every mapped passage
// when no selector is given) and /papers/{stage}/sections.

import { useEffect, useState } from "react";
import { get } from "../api/client";
import type { PassageCard, ReadingItem, ReadingResponse, Section, Stage } from "../api/types";
import { useEdition } from "../app/data";
import { STAGE_ORDER } from "../app/papers";

export interface Strip {
  stage: Stage;
  length: number; // bytes
  passages: StripPassage[];
  sections: Section[];
}

export interface StripPassage {
  key: string; // `${stage}:${anchor}`
  stage: Stage;
  anchor: string;
  start: number;
  end: number;
  claims: string[]; // node ids
  region: string | null; // majority region of its claims
  treatments: string[];
  section: string | null;
}

export interface Thread {
  from: string; // passage key
  to: string;
  kind: string; // expands | illustrates | answers | shared_claim
  derived: boolean;
  rationale?: string;
  shared?: string[];
}

export interface Readings {
  strips: Strip[];
  threads: Thread[];
  byKey: Map<string, StripPassage>;
}

let cached: Promise<Readings> | null = null;

function nodeIdOfRef(ref: string): string {
  return ref.slice(ref.lastIndexOf("/nodes/") + "/nodes/".length);
}

function passageKeyOfRef(ref: string): string | null {
  const match = ref.match(/papers\/(long|short|expository)\.json\/passages\/(.+)$/);
  return match ? `${match[1]}:${match[2]}` : null;
}

export function useReadings(): { status: "loading" } | { status: "ready"; value: Readings } | { status: "error"; error: unknown } {
  const edition = useEdition();
  const [state, setState] = useState<{ status: "loading" } | { status: "ready"; value: Readings } | { status: "error"; error: unknown }>({
    status: "loading",
  });
  useEffect(() => {
    let alive = true;
    if (!cached) {
      cached = (async () => {
        const responses = await Promise.all(
          STAGE_ORDER.map(async (stage) => {
            const [reading, sections] = await Promise.all([
              get<ReadingResponse>("/papers/reading", { paper: stage, limit: 200 }),
              get<{ items: Section[] }>(`/papers/${stage}/sections`, { limit: 200 }),
            ]);
            return { stage, reading: reading.data, sections: sections.data.items };
          }),
        );
        const strips: Strip[] = [];
        const byKey = new Map<string, StripPassage>();
        const threads = new Map<string, Thread>();
        for (const { stage, reading, sections } of responses) {
          const summary = edition.overview.papers.find((p) => p.stage === stage);
          const length =
            (summary?.coverage.mapped_content_bytes ?? 0) +
            (summary?.coverage.unmapped_bytes ?? 0) +
            (((summary?.coverage as unknown as { marker_bytes?: number })?.marker_bytes) ?? 0);
          const own = reading.passage_cards.filter((c: PassageCard) => c.stage === stage);
          const passages = own
            .map((card) => toPassage(card, sections, edition.graph.regionOf))
            .sort((a, b) => a.start - b.start);
          passages.forEach((p) => byKey.set(p.key, p));
          strips.push({ stage, length: Math.max(length, passages.at(-1)?.end ?? 1), passages, sections });
          for (const item of reading.items as ReadingItem[]) {
            const from = passageKeyOfRef(item.from);
            const to = passageKeyOfRef(item.to);
            if (!from || !to) continue;
            const key = `${from}|${to}|${item.kind}`;
            if (!threads.has(key))
              threads.set(key, {
                from,
                to,
                kind: item.kind,
                derived: item.derived,
                rationale: item.rationale,
                shared: item.shared_claim_refs?.map(nodeIdOfRef),
              });
          }
        }
        return { strips, threads: [...threads.values()], byKey };
      })();
      cached.catch(() => {
        cached = null;
      });
    }
    cached.then(
      (value) => alive && setState({ status: "ready", value }),
      (error: unknown) => alive && setState({ status: "error", error }),
    );
    return () => {
      alive = false;
    };
  }, [edition]);
  return state;
}

function toPassage(card: PassageCard, sections: Section[], regionOf: Map<string, string>): StripPassage {
  const claims = card.claim_refs.map(nodeIdOfRef);
  const votes = new Map<string, number>();
  for (const id of claims) {
    const r = regionOf.get(id);
    if (r) votes.set(r, (votes.get(r) ?? 0) + 1);
  }
  const region = [...votes.entries()].sort((a, b) => b[1] - a[1])[0]?.[0] ?? null;
  const section = sections.find((s) => s.ref === card.section_ref)?.title ?? null;
  return {
    key: `${card.stage}:${card.anchor}`,
    stage: card.stage,
    anchor: card.anchor,
    start: card.content_span.start_byte,
    end: card.content_span.end_byte,
    claims,
    region,
    treatments: [...new Set((card.treatments ?? []).flatMap((t) => t.kinds))],
    section,
  };
}

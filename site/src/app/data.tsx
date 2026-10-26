// Loads one pinned edition and the per-view data the pages ask for.

import { createContext, useContext, useEffect, useMemo, useState, type ReactNode } from "react";
import { ApiError, documentBytes, get, onEditionChanged, openEdition } from "../api/client";
import type {
  EdgeRecord,
  EvidenceRecord,
  FullRecordItem,
  NodeRecord,
  SourceRecord,
  Discovery,
  GraphMap,
  Overview,
  PaperStructure,
  ReadingResponse,
  RecordDetail,
  Snapshot,
  Stage,
  SummaryCard,
} from "../api/types";
import { buildGraph, type ArgGraph } from "../model/graph";

export interface Edition {
  snapshot: Snapshot;
  discovery: Discovery;
  overview: Overview;
  map: GraphMap;
  graph: ArgGraph;
}

type EditionState =
  | { status: "loading" }
  | { status: "ready"; edition: Edition }
  | { status: "error"; error: unknown };

const EditionContext = createContext<Edition | null>(null);
const ChangedContext = createContext<boolean>(false);

/** Every record of one table, following the API's pages (at most 200 each). */
async function allRecords<T>(table: string): Promise<T[]> {
  const out: T[] = [];
  for (let offset = 0; ; offset += 200) {
    const page = await get<{ items: FullRecordItem<T>[]; total: number }>("/records", { table, limit: 200, offset });
    out.push(...page.data.items.map((i) => i.record));
    if (page.data.items.length < 200 || out.length >= page.data.total) return out;
  }
}

export async function loadEdition(): Promise<Edition> {
  const { snapshot, discovery } = await openEdition();
  const [overview, map, summaries, records, sources, edges, evidence] = await Promise.all([
    get<Overview>("/overview"),
    get<GraphMap>("/graph", { view: "arguments", representation: "map", scope: "corpus", assumptions: "true" }),
    get<{ items: SummaryCard[] }>("/records", { table: "nodes", representation: "summary", limit: 200 }),
    allRecords<NodeRecord>("nodes"),
    allRecords<SourceRecord>("sources"),
    allRecords<EdgeRecord>("edges"),
    allRecords<EvidenceRecord>("evidence"),
  ]);
  const long = overview.data.papers.find((p) => p.stage === "long");
  const goals = long?.paper_scope.selected_goal_ids ?? map.data.selected_goals;
  const graph = buildGraph(map.data, summaries.data.items, goals, records, sources, { edges, evidence });
  return { snapshot, discovery, overview: overview.data, map: map.data, graph };
}

export function EditionProvider({ children, fallback }: { children: ReactNode; fallback: (state: EditionState, retry: () => void) => ReactNode }) {
  const [state, setState] = useState<EditionState>({ status: "loading" });
  const [changed, setChanged] = useState(false);
  const [attempt, setAttempt] = useState(0);
  useEffect(() => {
    let alive = true;
    setState({ status: "loading" });
    loadEdition().then(
      (edition) => alive && setState({ status: "ready", edition }),
      (error: unknown) => alive && setState({ status: "error", error }),
    );
    return () => {
      alive = false;
    };
  }, [attempt]);
  useEffect(() => onEditionChanged(() => setChanged(true)), []);
  if (state.status !== "ready") return <>{fallback(state, () => setAttempt((n) => n + 1))}</>;
  return (
    <EditionContext.Provider value={state.edition}>
      <ChangedContext.Provider value={changed}>{children}</ChangedContext.Provider>
    </EditionContext.Provider>
  );
}

export function useEdition(): Edition {
  const edition = useContext(EditionContext);
  if (!edition) throw new Error("useEdition outside a ready edition");
  return edition;
}

export function useEditionChanged(): boolean {
  return useContext(ChangedContext);
}

/** A tiny async-resource hook keyed by a string; results are cached per key. */
type Resource<T> = { status: "loading" } | { status: "ready"; value: T } | { status: "error"; error: unknown };
const resources = new Map<string, Promise<unknown>>();

export function useResource<T>(key: string | null, load: () => Promise<T>): Resource<T> {
  const [state, setState] = useState<Resource<T>>({ status: "loading" });
  useEffect(() => {
    if (!key) return;
    let alive = true;
    let pending = resources.get(key) as Promise<T> | undefined;
    if (!pending) {
      pending = load();
      resources.set(key, pending);
      pending.catch(() => resources.delete(key));
    }
    setState({ status: "loading" });
    pending.then(
      (value) => alive && setState({ status: "ready", value }),
      (error: unknown) => alive && setState({ status: "error", error }),
    );
    return () => {
      alive = false;
    };
    // `load` is intentionally keyed by `key`.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [key]);
  return key ? state : { status: "loading" };
}

export interface PaperData {
  stage: Stage;
  structure: PaperStructure;
  bytes: Uint8Array;
}

export function loadPaper(stage: Stage): Promise<PaperData> {
  return Promise.all([get<PaperStructure>(`/papers/${stage}/structure`), documentBytes(stage)]).then(
    ([structure, bytes]) => ({ stage, structure: structure.data, bytes }),
  );
}

export function usePaper(stage: Stage | null): Resource<PaperData> {
  return useResource(stage ? `paper:${stage}` : null, () => loadPaper(stage!));
}

export function useRecord(ref: string | null): Resource<RecordDetail> {
  return useResource(ref ? `record:${ref}` : null, () => get<RecordDetail>("/record", { ref: ref! }).then((r) => r.data));
}

export function useReading(stage: Stage | null, anchor: string | null): Resource<ReadingResponse> {
  const key = stage && anchor ? `reading:${stage}:${anchor}` : null;
  return useResource(key, () =>
    get<ReadingResponse>("/papers/reading", { paper: stage!, passage: anchor!, limit: 200 }).then((r) => r.data),
  );
}

export function describeError(error: unknown): { title: string; detail: string } {
  if (error instanceof ApiError) {
    if (error.status === 0)
      return {
        title: "The reading server is not answering",
        detail: "Start it with `lean-exposition serve <bundle>` and reload this page.",
      };
    if (error.status === 409)
      return { title: "The edition changed", detail: "The server now serves a different edition. Reload to read it." };
    if (error.status === 404) return { title: "Not in this edition", detail: error.message };
    return { title: `The server answered ${error.status}`, detail: error.message };
  }
  return { title: "Something went wrong", detail: error instanceof Error ? error.message : String(error) };
}

export function useStableMemo<T>(factory: () => T, deps: unknown[]): T {
  // eslint-disable-next-line react-hooks/exhaustive-deps
  return useMemo(factory, deps);
}

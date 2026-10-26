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
  /**
   * The stored edges and evidence records that give `graph` its warrants,
   * theorem applications and citation links. While "loading", `graph` has the
   * full set of records and relations but no `edge.warrant`, no
   * `edge.application` and an empty `graph.cites`; when it becomes "ready"
   * those are attached to the same graph object (its identity never changes)
   * and every `useEdition()` consumer re-renders.
   */
  context: "loading" | "ready" | "error";
  /** Why the stored edges and evidence could not be read, when `context` is "error". */
  contextError?: unknown;
}

type EditionState =
  | { status: "loading" }
  | { status: "ready"; edition: Edition }
  | { status: "error"; error: unknown };

const EditionContext = createContext<Edition | null>(null);
const ChangedContext = createContext<boolean>(false);
const RetryContext = createContext<() => void>(() => undefined);

const PAGE_SIZE = 200;

/**
 * Every record of one table, following the API's pages (at most 200 each).
 * The first page states the total, so the remaining pages are asked for
 * together rather than one after another.
 */
async function allRecords<T>(table: string): Promise<T[]> {
  type P = { items: FullRecordItem<T>[]; total: number };
  const first = await get<P>("/records", { table, limit: PAGE_SIZE, offset: 0 });
  const rest: Promise<{ data: P }>[] = [];
  for (let offset = PAGE_SIZE; offset < first.data.total; offset += PAGE_SIZE) {
    rest.push(get<P>("/records", { table, limit: PAGE_SIZE, offset }));
  }
  const pages = [first, ...(await Promise.all(rest))];
  return pages.flatMap((page) => page.data.items.map((i) => i.record));
}

interface Core {
  overview: Overview;
  map: GraphMap;
  summaries: SummaryCard[];
  records: NodeRecord[];
  sources: SourceRecord[];
  goals: string[];
}

interface Stored {
  edges: EdgeRecord[];
  evidence: EvidenceRecord[];
}

function loadCore(): Promise<Core> {
  return Promise.all([
    get<Overview>("/overview"),
    get<GraphMap>("/graph", { view: "arguments", representation: "map", scope: "corpus", assumptions: "true" }),
    get<{ items: SummaryCard[] }>("/records", { table: "nodes", representation: "summary", limit: PAGE_SIZE }),
    allRecords<NodeRecord>("nodes"),
    allRecords<SourceRecord>("sources"),
  ]).then(([overview, map, summaries, records, sources]) => {
    const long = overview.data.papers.find((p) => p.stage === "long");
    const goals = long?.paper_scope.selected_goal_ids ?? map.data.selected_goals;
    return { overview: overview.data, map: map.data, summaries: summaries.data.items, records, sources, goals };
  });
}

function loadStored(): Promise<Stored> {
  return Promise.all([allRecords<EdgeRecord>("edges"), allRecords<EvidenceRecord>("evidence")]).then(([edges, evidence]) => ({ edges, evidence }));
}

function coreGraph(core: Core, stored?: Stored): ArgGraph {
  return buildGraph(core.map, core.summaries, core.goals, core.records, core.sources, stored ?? { edges: [], evidence: [] });
}

/**
 * Attach warrants, applications and citation links to an existing graph,
 * keeping its identity (and every edge object's identity), so layouts and
 * memos keyed on the graph survive the late arrival of the evidence table.
 */
function enrich(graph: ArgGraph, core: Core, stored: Stored): void {
  const full = coreGraph(core, stored);
  const byKey = new Map(full.edges.map((e) => [e.key, e]));
  for (const edge of graph.edges) {
    const source = byKey.get(edge.key);
    if (!source) continue;
    if (source.warrant) edge.warrant = source.warrant;
    if (source.application) edge.application = source.application;
  }
  graph.cites.splice(0, graph.cites.length, ...full.cites);
}

/** Start fetching what the reader of one account needs first: its bytes and structure. */
function primePaper(stage: Stage): void {
  void loadPaper(stage).catch(() => undefined);
}

/** The whole edition in one promise (core and stored records), for tests and tools. */
export async function loadEdition(): Promise<Edition> {
  const { snapshot, discovery } = await openEdition();
  const [core, stored] = await Promise.all([loadCore(), loadStored()]);
  return { snapshot, discovery, overview: core.overview, map: core.map, graph: coreGraph(core, stored), context: "ready" };
}

/**
 * Loading contract:
 * 1. Discovery pins the edition (manifest hash); every later request carries it.
 * 2. In parallel: the core (overview, corpus map, node summaries, node and
 *    source records), the stored tables (edges, evidence), and, when the page
 *    opened on an account (`paperFirst`), that account's bytes and structure.
 *    Record tables are paged in parallel once their first page gives a total.
 * 3. Children render as soon as the core is ready, with `context: "loading"`.
 * 4. When edges and evidence arrive, warrants are attached to the same graph
 *    and `context` becomes "ready" (or "error", with a retry).
 */
export function EditionProvider({
  children,
  fallback,
  paperFirst,
}: {
  children: ReactNode;
  fallback: (state: EditionState, retry: () => void) => ReactNode;
  /** The account the page opened on, fetched alongside the core. */
  paperFirst?: Stage | null;
}) {
  const [state, setState] = useState<EditionState>({ status: "loading" });
  const [changed, setChanged] = useState(false);
  const [attempt, setAttempt] = useState(0);
  useEffect(() => {
    let alive = true;
    setState({ status: "loading" });
    openEdition().then(
      ({ snapshot, discovery }) => {
        if (!alive) return;
        if (paperFirst) primePaper(paperFirst);
        const core = loadCore();
        const stored = loadStored();
        let ready: { graph: ArgGraph; core: Core } | null = null;
        let storedValue: Stored | null = null;
        core.then(
          (value) => {
            if (!alive) return;
            // When the stored tables won the race, build the full graph at once.
            const graph = coreGraph(value, storedValue ?? undefined);
            ready = { graph, core: value };
            setState({
              status: "ready",
              edition: { snapshot, discovery, overview: value.overview, map: value.map, graph, context: storedValue ? "ready" : "loading" },
            });
          },
          (error: unknown) => alive && setState({ status: "error", error }),
        );
        stored.then(
          (value) => {
            if (!alive) return;
            storedValue = value;
            if (!ready) return;
            enrich(ready.graph, ready.core, value);
            setState((prev) => (prev.status === "ready" ? { status: "ready", edition: { ...prev.edition, context: "ready" } } : prev));
          },
          (error: unknown) => {
            if (!alive) return;
            // Wait for the core so the error lands on a ready edition.
            void core.then(() => {
              if (!alive) return;
              setState((prev) =>
                prev.status === "ready" ? { status: "ready", edition: { ...prev.edition, context: "error", contextError: error } } : prev,
              );
            }, () => undefined);
          },
        );
      },
      (error: unknown) => alive && setState({ status: "error", error }),
    );
    return () => {
      alive = false;
    };
    // The first account is only primed on the first attempt's route.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [attempt]);
  useEffect(() => onEditionChanged(() => setChanged(true)), []);
  const retry = () => setAttempt((n) => n + 1);
  if (state.status !== "ready") return <>{fallback(state, retry)}</>;
  return (
    <EditionContext.Provider value={state.edition}>
      <RetryContext.Provider value={retry}>
        <ChangedContext.Provider value={changed}>{children}</ChangedContext.Provider>
      </RetryContext.Provider>
    </EditionContext.Provider>
  );
}

/** Load the edition again from discovery (after an error). */
export function useEditionRetry(): () => void {
  return useContext(RetryContext);
}

export function useEdition(): Edition {
  const edition = useContext(EditionContext);
  if (!edition) throw new Error("useEdition outside a ready edition");
  return edition;
}

/** The edition once its core is ready, or null before (for the frame around the pages). */
export function useMaybeEdition(): Edition | null {
  return useContext(EditionContext);
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
        title: "The site cannot reach the server that holds the records",
        detail: "Start the server with the command lean-exposition serve <bundle>, then reload this page.",
      };
    if (error.status === 409)
      return {
        title: "The server is serving a different edition",
        detail: "An edition is one fixed set of records and papers, and the server has switched to another one. Reload this page to read it.",
      };
    if (error.status === 404) return { title: "The server has no such item in this edition", detail: error.message };
    return { title: `The server returned an error (HTTP status ${error.status})`, detail: error.message };
  }
  return { title: "The page stopped with an error", detail: error instanceof Error ? error.message : String(error) };
}

export function useStableMemo<T>(factory: () => T, deps: unknown[]): T {
  // eslint-disable-next-line react-hooks/exhaustive-deps
  return useMemo(factory, deps);
}

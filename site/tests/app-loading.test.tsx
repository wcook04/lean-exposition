// The loading contract: pages render on the core tables; the stored edges and
// evidence attach warrants to the same graph object when they arrive.
import { afterEach, describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import type { EvidenceRecord, GraphMap, Overview, SummaryCard } from "../src/api/types";
import { closure, type ArgGraph } from "../src/model/graph";
import { fixture, tableFixture } from "./fixtures";

const snapshot = { bundle_id: "b", bundle_version: "1", cache_key: "c", graph_sha256: "g", manifest_sha256: "abc123", ref: "r" };
const held: (() => void)[] = [];
const releaseEvidence = () => held.splice(0).forEach((release) => release());
const asked: string[] = [];
let evidenceRows: EvidenceRecord[] | undefined;

function pageOf<T>(rows: T[], offset: number, limit: number) {
  return { items: rows.slice(offset, offset + limit).map((record) => ({ record })), total: rows.length };
}

vi.mock("../src/api/client", () => {
  class ApiError extends Error {
    status = 500;
  }
  return {
    ApiError,
    onEditionChanged: () => () => undefined,
    documentBytes: () => Promise.resolve(new Uint8Array()),
    openEdition: () => Promise.resolve({ snapshot, discovery: {} }),
    get: (path: string, params: Record<string, unknown> = {}) => {
      const key = `${path}:${params.table ?? ""}:${params.representation ?? ""}:${params.offset ?? 0}`;
      asked.push(key);
      const wrap = (data: unknown) => Promise.resolve({ snapshot, data });
      if (path === "/overview") return wrap({ papers: fixture("papers.json") } as unknown as Overview);
      if (path === "/graph") return wrap(fixture<GraphMap>("graph-map.json"));
      if (path.startsWith("/papers/")) return wrap({});
      const offset = Number(params.offset ?? 0);
      const limit = Number(params.limit ?? 200);
      if (params.representation === "summary") return wrap({ items: fixture<SummaryCard[]>("node-summaries.json") });
      const table = String(params.table);
      const rows: unknown[] = table === "evidence" && evidenceRows ? evidenceRows : tableFixture(table as "nodes");
      if (table === "evidence") return new Promise((resolve) => held.push(() => resolve({ snapshot, data: pageOf(rows, offset, limit) })));
      return wrap(pageOf(rows, offset, limit));
    },
  };
});

const { EditionProvider, useEdition, loadPaperStructure } = await import("../src/app/data");

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
  releaseEvidence();
  asked.length = 0;
  evidenceRows = undefined;
});

describe("loading contract", () => {
  it("requests the smaller paper structure only for static editions", async () => {
    try {
      vi.stubEnv("VITE_STATIC_EDITION", "true");
      await loadPaperStructure("short");
      expect(asked.at(-1)).toBe("/papers/short/structure::reader:0");
      vi.stubEnv("VITE_STATIC_EDITION", "false");
      await loadPaperStructure("short");
      expect(asked.at(-1)).toBe("/papers/short/structure:::0");
    } finally { vi.unstubAllEnvs(); }
  });
  it("renders on the core, then attaches warrants to the same graph", async () => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    const seen: { context: string; graph: unknown; warrants: number; cites: number }[] = [];
    function Probe() {
      const edition = useEdition();
      seen.push({
        context: edition.context,
        graph: edition.graph,
        warrants: edition.graph.edges.filter((e) => e.warrant).length,
        cites: edition.graph.cites.length,
      });
      return null;
    }
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<EditionProvider fallback={() => <p>booting</p>}><Probe /></EditionProvider>));
    await act(async () => new Promise((r) => setTimeout(r, 20)));
    expect(seen.length).toBeGreaterThan(0);
    expect(seen.at(-1)!.context).toBe("loading");
    expect(seen.at(-1)!.warrants).toBe(0);
    // Every page of a table after the first is asked for together, once the first gives a total.
    expect(asked.filter((k) => k.startsWith("/records:edges:")).length).toBe(Math.ceil(tableFixture("edges").length / 200));

    for (let i = 0; i < 3; i++) {
      await act(async () => {
        releaseEvidence();
        await new Promise((r) => setTimeout(r, 20));
      });
    }
    const last = seen.at(-1)!;
    expect(last.context).toBe("ready");
    expect(last.graph).toBe(seen[0].graph);
    expect(last.warrants).toBeGreaterThan(0);
  });

  it.each([
    { kind: "extraction", status: "passed", retained: true },
    { kind: "extraction", status: "not_run", retained: false },
    { kind: "extraction", status: "failed", retained: false },
    { kind: "source_hash", status: "passed", retained: false },
  ])("hydrates $kind/$status scope when an older compact map omits subjects", async ({ kind, status, retained }) => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    const subject = "support.full_relative_support";
    const premise = "scalar.paper_minimizer";
    evidenceRows = [...tableFixture("evidence"), {
      id: "synthetic-late-scope", kind, status, subject_ids: [subject],
      source_ids: [], command: [], tool: "Synthetic fixture", details: "No actual Lean run.",
    }];
    const seen: { context: string; graph: ArgGraph; retained: boolean; extracted: boolean }[] = [];
    function Probe() {
      const edition = useEdition();
      seen.push({ context: edition.context, graph: edition.graph,
        retained: closure(edition.graph, "support.near_ground_pairs", "prerequisites").has(premise),
        extracted: edition.graph.nodes.get(subject)!.passedExtraction });
      return null;
    }
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<EditionProvider fallback={() => <p>booting</p>}><Probe /></EditionProvider>));
    await act(async () => new Promise((resolve) => setTimeout(resolve, 20)));
    expect(seen.at(-1)?.context).toBe("loading");
    expect(seen.at(-1)?.retained).toBe(false);
    expect(seen.at(-1)?.extracted).toBe(false);
    const nodeBefore = seen[0].graph.nodes.get(subject);
    for (let i = 0; i < 3; i++) {
      await act(async () => {
        releaseEvidence();
        await new Promise((resolve) => setTimeout(resolve, 20));
      });
    }
    const last = seen.at(-1)!;
    expect(last.context).toBe("ready");
    expect(last.graph).toBe(seen[0].graph);
    expect(last.graph.nodes.get(subject)).toBe(nodeBefore);
    expect(last.extracted).toBe(retained);
    expect(last.retained).toBe(retained);
  });
});

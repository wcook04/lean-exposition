// The loading contract: pages render on the core tables; the stored edges and
// evidence attach warrants to the same graph object when they arrive.
import { afterEach, describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import type { GraphMap, Overview, SummaryCard } from "../src/api/types";
import { fixture, tableFixture } from "./fixtures";

const snapshot = { bundle_id: "b", bundle_version: "1", cache_key: "c", graph_sha256: "g", manifest_sha256: "abc123", ref: "r" };
const held: (() => void)[] = [];
const releaseEvidence = () => held.splice(0).forEach((release) => release());
const asked: string[] = [];

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
      const rows = tableFixture(table as "nodes");
      if (table === "evidence") return new Promise((resolve) => held.push(() => resolve({ snapshot, data: pageOf(rows, offset, limit) })));
      return wrap(pageOf(rows, offset, limit));
    },
  };
});

const { EditionProvider, useEdition } = await import("../src/app/data");

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
});

describe("loading contract", () => {
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
});

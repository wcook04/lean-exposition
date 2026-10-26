// Load the captured fixtures for tests (see scripts/capture-fixtures.mjs).
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import type { EdgeRecord, EvidenceRecord, GraphMap, NodeRecord, PaperStructure, SourceRecord, Stage, SummaryCard } from "../src/api/types";
import { buildGraph, type ArgGraph } from "../src/model/graph";

const root = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures");

export function fixture<T>(name: string): T {
  return JSON.parse(readFileSync(path.join(root, name), "utf8")) as T;
}

export function documentFixture(stage: Stage): Uint8Array {
  return new Uint8Array(readFileSync(path.join(root, `document-${stage}.md`)));
}

export function structureFixture(stage: Stage): PaperStructure {
  return fixture<PaperStructure>(`structure-${stage}.json`);
}

export function graphFixture(): ArgGraph {
  const map = fixture<GraphMap>("graph-map.json");
  const summaries = fixture<SummaryCard[]>("node-summaries.json");
  const papers = fixture<{ stage: Stage; paper_scope: { selected_goal_ids: string[] } }[]>("papers.json");
  const long = papers.find((p) => p.stage === "long")!;
  return buildGraph(map, summaries, long.paper_scope.selected_goal_ids);
}

/** The full tables captured with the map: nodes, stored edges, evidence and sources. */
export function tableFixture(name: "nodes"): NodeRecord[];
export function tableFixture(name: "edges"): EdgeRecord[];
export function tableFixture(name: "evidence"): EvidenceRecord[];
export function tableFixture(name: "sources"): SourceRecord[];
export function tableFixture(name: string): unknown[] {
  return fixture<unknown[]>(`table-${name}.json`);
}

/** The graph as the site builds it from a loaded edition: origins, warrants and applications included. */
export function editionGraphFixture(): ArgGraph {
  const map = fixture<GraphMap>("graph-map.json");
  const summaries = fixture<SummaryCard[]>("node-summaries.json");
  const papers = fixture<{ stage: Stage; paper_scope: { selected_goal_ids: string[] } }[]>("papers.json");
  const long = papers.find((p) => p.stage === "long")!;
  return buildGraph(map, summaries, long.paper_scope.selected_goal_ids, tableFixture("nodes"), tableFixture("sources"), {
    edges: tableFixture("edges"),
    evidence: tableFixture("evidence"),
  });
}

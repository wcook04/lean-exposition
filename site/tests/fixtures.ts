// Load the captured fixtures for tests (see scripts/capture-fixtures.mjs).
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import type { GraphMap, PaperStructure, Stage, SummaryCard } from "../src/api/types";
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

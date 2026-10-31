// The Lean graph of an argument, for the map page and the reader's pane: the same engine,
// another graph. Nothing here runs until a page asks for the Lean: it fetches the alignment,
// then the modules of the linked declarations and of the helpers between them (about 120 of
// the 349), all on first use, and keeps the result.
//
//   const lean = useLeanGraph({ enabled, graph, goal, records });
//   lean.status === "ready" && <ArgumentTree graph={lean.graph} goal={goal} statusOf={lean.markOf} mode="overview" />
//
// A card's id is the declaration's full name; the goal stays the argument's own record.

import { useCallback, useEffect, useMemo, useState } from "react";
import type { LeanModule, LeanModules } from "../api/lean";
import { alignmentResource, useAlignment } from "../compare/useAlignment";
import type { ArgGraph, ArgNode } from "../model/graph";
import { buildLeanGraph, linkedDeclarations, type LeanFacts, type LeanGraph } from "../model/leanGraph";
import { markOfDeclaration, type LeanMark } from "../model/leanStatus";
import { recordMark } from "./leanMarks";

export interface LeanGraphOptions {
  /** Load only once this is true. */
  enabled: boolean;
  graph: ArgGraph;
  goal: string;
  /** The records whose declarations are drawn: the argument, or what a paper uses of it. */
  records: ReadonlySet<string>;
}

export type LeanGraphState =
  | { status: "idle" | "loading"; done: number }
  | { status: "failed" }
  | {
      status: "ready";
      graph: LeanGraph;
      markOf(id: string, node: ArgNode): LeanMark | null;
      /** "source_text" today; "elaborated" once the compiler's report has replaced the scan. */
      source: LeanModules["dependency_source"];
      /** What that way of finding names can miss, in the index's words. */
      note?: string;
    };

/** Facts are cut once per declaration; a module can be large and each walk asks many times. */
const factsMemo = new WeakMap<LeanModule, Map<string, LeanFacts>>();
type Locate = (name: string, near: string) => string | undefined;

function factsOf(module: LeanModule, locate: Locate): Map<string, LeanFacts> {
  let map = factsMemo.get(module);
  if (!map) {
    const lines = module.source.split("\n");
    map = new Map();
    for (const d of module.declarations) {
      if (map.has(d.name)) continue;
      // The index names a use's module only where the name is declared twice; the rest are looked up.
      const named = (d as { uses_modules?: Record<string, string> }).uses_modules;
      const usesModules: Record<string, string> = {};
      for (const use of d.uses) {
        const at = named?.[use] ?? locate(use, module.module);
        if (at) usesModules[use] = at;
      }
      map.set(d.name, {
        name: d.name,
        short: d.short,
        kind: d.kind,
        module: module.module,
        line: d.line,
        uses: d.uses,
        usesModules,
        statement: lines.slice(d.line - 1, d.signature_end_line).join("\n"),
        text: lines.slice(d.line - 1, d.end_line).join("\n"),
      });
    }
    factsMemo.set(module, map);
  }
  return map;
}

/** Fetch every module the linked names reach, in rounds, a round at a time. */
async function loadReach(linked: ReadonlyMap<string, string>, locate: Locate, progress: (modules: number) => void) {
  const { fetchModule } = await import("../lean/data");
  const modules = new Map<string, LeanModule>();
  const seen = new Set<string>();
  let frontier: [string, string][] = [...linked];
  while (frontier.length) {
    const wanted = [...new Set(frontier.map(([, module]) => module))].filter((m) => !modules.has(m));
    await Promise.all(
      wanted.map((name) =>
        fetchModule(name).then(
          (module) => void modules.set(name, module),
          () => undefined,
        ),
      ),
    );
    progress(modules.size);
    const next: [string, string][] = [];
    for (const [name, module] of frontier) {
      const key = `${module}:${name}`;
      if (seen.has(key)) continue;
      seen.add(key);
      const m = modules.get(module);
      const fact = m && factsOf(m, locate).get(name);
      if (fact) for (const use of fact.uses) if (fact.usesModules?.[use]) next.push([use, fact.usesModules[use]]);
    }
    frontier = next;
  }
  return modules;
}

export function useLeanGraph({ enabled, graph, goal, records }: LeanGraphOptions): LeanGraphState {
  const alignment = useAlignment();
  const [state, setState] = useState<LeanGraphState>({ status: "idle", done: 0 });
  const key = useMemo(() => `${goal}|${[...records].sort().join(" ")}`, [goal, records]);
  useEffect(() => {
    if (!enabled) return;
    let alive = true;
    setState((s) => (s.status === "ready" ? s : { status: "loading", done: 0 }));
    void (async () => {
      const aligned = alignment ?? (await alignmentResource());
      if (!aligned) throw new Error("no alignment");
      const rows = (id: string) => aligned.records[id]?.lean ?? [];
      const linked = linkedDeclarations(records, rows);
      const { shellResource } = await import("../lean/data");
      const { findDecl } = await import("../lean/resolve");
      const { modules: index, index: names } = await shellResource();
      const locate: Locate = (name, near) => findDecl(names, name, near)?.module;
      const reached = await loadReach(linked, locate, (done) => alive && setState((s) => (s.status === "ready" ? s : { status: "loading", done })));
      const files = new Map(index.folders.flatMap((f) => f.modules.map((row) => [row.module, row.path.slice(row.path.lastIndexOf("/") + 1)] as const)));
      const facts = (name: string, module: string) => {
        const m = reached.get(module);
        return m && factsOf(m, locate).get(name);
      };
      const lean = buildLeanGraph({
        goal,
        goalLabel: graph.nodes.get(goal)?.label ?? goal,
        linked,
        main: rows(goal).filter((r) => r.relation === "states").map((r) => r.name),
        facts,
        fileOf: (module) => files.get(module),
        origin: { family: "lean", label: "Lean formalisation", slot: 3, place: null, locator: null, url: null },
      });
      const marks = new Map<string, LeanMark>();
      for (const [name, module] of linked) {
        const fact = facts(name, module);
        if (fact) marks.set(name, markOfDeclaration(fact.kind, /\bsorry\b/.test(fact.text)));
      }
      const markOf = (id: string, node: ArgNode) => marks.get(id) ?? (node.kind === "goal" ? recordMark(id, node) : null);
      if (alive) setState({ status: "ready", graph: lean, markOf, source: index.dependency_source, note: index.dependency_note });
    })().catch(() => alive && setState({ status: "failed" }));
    return () => {
      alive = false;
    };
    // The records and the goal are compared through `key`.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [enabled, key, alignment]);
  return state;
}

/** The argument's marks, for the pane's own ArgumentTree. */
export const useRecordMarks = () => useCallback(recordMark, []);

// The Lean behind an argument, as the graph the map's engine draws: one card per declaration
// linked from the argument's records, and a line wherever the Lean index says one uses
// another. Blueprint habits come across directly: a use in the statement and a use in the
// proof are different lines, and a definition and a result are different shapes.
//
// The linked declarations are joined mostly through helpers nobody linked: about half of
// them cannot be reached from the main theorem by direct uses alone. So a walk from each
// declaration passes through unlinked names and stops at the next linked one, and a line
// found that way says how many helpers it stands for. They stay collapsed; the sheet of
// either end lists every use. A card goes by its plain title (declTitle.ts), and only a
// declaration with none shows its name.
//
// `uses` is what the Lean index holds. Today that is a scan of the source text, so a name
// reached through notation or tactics is missing, and the split between statement and proof
// is whether the name's text sits in the statement's lines. leanGraphSource says which.

import type { ArgEdge, ArgGraph, ArgNode, LinkKind, Origin } from "./graph";

export interface LeanFacts {
  name: string;
  /** The name after its namespaces. */
  short: string;
  kind: string;
  module: string;
  line: number;
  uses: readonly string[];
  /** The module of each use declared elsewhere. */
  usesModules?: Readonly<Record<string, string>>;
  /** The lines of its statement, for telling a statement's uses from a proof's. */
  statement: string;
  /** Its whole text. */
  text: string;
}

export interface LeanInput {
  goal: string;
  goalLabel: string;
  /** The linked declarations: name to module. */
  linked: ReadonlyMap<string, string>;
  /** The goal's own declarations, in the order they should sit under it. */
  main: readonly string[];
  facts(name: string, module: string): LeanFacts | undefined;
  /** The plain title of a declaration, where it has one. */
  titleOf?(name: string): string | null;
  /** A file name for the caption, from a module. */
  fileOf?(module: string): string | undefined;
  origin: Origin;
}

const KIND_WORDS: Record<string, string> = {
  theorem: "Theorem",
  lemma: "Lemma",
  def: "Definition",
  abbrev: "Abbreviation",
  structure: "Structure",
  class: "Class",
  instance: "Instance",
  inductive: "Inductive type",
  opaque: "Opaque definition",
  axiom: "Axiom",
};

export const leanKindWord = (kind: string) => KIND_WORDS[kind] ?? kind;

const escapeRe = (text: string) => text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

/** Whether a use's name is written in this text, under any of its namespaces. */
export function namedIn(text: string, name: string): boolean {
  const short = name.slice(name.lastIndexOf(".") + 1);
  return new RegExp(`(?<![\\w.'])(?:[\\w']+\\.)*${escapeRe(short)}(?![\\w'])`, "u").test(text);
}

export interface LeanUse {
  from: string;
  to: string;
  kind: LinkKind;
  /** The unlinked names between them, shortest chain, nearest first. */
  helpers: string[];
}

/** Every use between linked declarations, direct or through unlinked helpers. */
export function leanUses(input: Pick<LeanInput, "linked" | "facts">): LeanUse[] {
  const { linked, facts } = input;
  const uses: LeanUse[] = [];
  for (const [from, module] of linked) {
    const start = facts(from, module);
    if (!start) continue;
    const seen = new Set([from]);
    let frontier: { fact: LeanFacts; path: string[] }[] = [{ fact: start, path: [] }];
    while (frontier.length) {
      const next: typeof frontier = [];
      for (const { fact, path } of frontier) {
        for (const name of fact.uses) {
          if (seen.has(name)) continue;
          seen.add(name);
          if (linked.has(name)) {
            uses.push({ from, to: name, helpers: path, kind: path.length ? "lean_via" : namedIn(start.statement, name) ? "lean_type_dependency" : "supports" });
            continue;
          }
          const inner = facts(name, fact.usesModules?.[name] ?? fact.module);
          if (inner) next.push({ fact: inner, path: [...path, name] });
        }
      }
      frontier = next;
    }
  }
  return uses;
}

/** Drop what closes a cycle (a text scan can find one through a shadowed name), then what a longer chain already says. */
export function simplifyUses(ids: readonly string[], uses: readonly LeanUse[]): { kept: LeanUse[]; left: number } {
  const out = new Map<string, LeanUse[]>(ids.map((id) => [id, []]));
  const state = new Map<string, 1 | 2>();
  const acyclic: LeanUse[] = [];
  const visit = (id: string) => {
    state.set(id, 1);
    for (const use of out.get(id) ?? []) {
      const s = state.get(use.to);
      if (s === 1) continue;
      acyclic.push(use);
      if (!s) visit(use.to);
    }
    state.set(id, 2);
  };
  for (const use of uses) out.get(use.from)?.push(use);
  for (const id of ids) if (!state.has(id)) visit(id);

  const after = new Map<string, LeanUse[]>(ids.map((id) => [id, []]));
  for (const use of acyclic) after.get(use.from)!.push(use);
  const below = new Map<string, Set<string>>();
  const reach = (id: string): Set<string> => {
    let set = below.get(id);
    if (set) return set;
    set = new Set();
    below.set(id, set);
    for (const use of after.get(id)!) {
      set.add(use.to);
      for (const d of reach(use.to)) set.add(d);
    }
    return set;
  };
  const kept = acyclic.filter((use) => !after.get(use.from)!.some((other) => other.to !== use.to && reach(other.to).has(use.to)));
  return { kept, left: uses.length - kept.length };
}

/** Tiles show the short name; two declarations that share one keep the namespace that tells them apart. */
export function tileNames(names: Iterable<string>): Map<string, string> {
  const list = [...names];
  const count = new Map<string, number>();
  const last = (name: string) => name.slice(name.lastIndexOf(".") + 1);
  for (const name of list) count.set(last(name), (count.get(last(name)) ?? 0) + 1);
  return new Map(list.map((name) => [name, count.get(last(name))! > 1 ? name.split(".").slice(-2).join(".") : last(name)]));
}

const phrase = (use: LeanUse, tile: (name: string) => string): string => {
  const [from, to] = [tile(use.from), tile(use.to)];
  if (use.kind === "lean_type_dependency") return `The statement of ${from} uses ${to}`;
  if (use.kind === "supports") return `The proof of ${from} uses ${to}`;
  const n = use.helpers.length;
  return `${from} reaches ${to} through ${n === 1 ? "one helper" : `${n} helpers`}`;
};

export interface LeanGraph extends ArgGraph {
  /** Definitions: nearly every result uses them, so they sit on a shelf under the drawing, in plain words. */
  shelf: { name: string; module: string; title: string }[];
  /** Uses found that the drawing leaves out, because a longer chain says the same or they would close a cycle. */
  leftOut: number;
  /** How many linked declarations the index could not find. */
  missing: string[];
}

export function buildLeanGraph(input: LeanInput): LeanGraph {
  const { goal, goalLabel, linked, main, facts, origin } = input;
  const missing: string[] = [];
  const present = new Map<string, string>();
  for (const [name, module] of linked) {
    if (facts(name, module)) present.set(name, module);
    else missing.push(name);
  }
  const blank = { papers: {}, region: goal, passedExtraction: false, status: "unverified", origin };
  const nodes = new Map<string, ArgNode>();
  nodes.set(goal, { ...blank, id: goal, ref: goal, kind: "goal", label: goalLabel });
  const raw = tileNames(present.keys());
  const tiles = new Map([...present.keys()].map((name) => [name, input.titleOf?.(name) ?? raw.get(name)!]));
  for (const [name, module] of present) {
    const fact = facts(name, module)!;
    const file = input.fileOf?.(module) ?? module;
    nodes.set(name, {
      ...blank,
      id: name,
      ref: name,
      kind: "declaration",
      label: tiles.get(name)!,
      declaration: name,
      tile: tiles.get(name),
      tilePlain: !!input.titleOf?.(name),
      leanNote: `${leanKindWord(fact.kind)}, ${file} line ${fact.line}`,
    });
  }
  // A definition is not drawn: a walk passes through it like a helper, and it goes on the shelf.
  const results = new Map([...present].filter(([name, module]) => RESULT_KINDS.has(facts(name, module)!.kind)));
  const shelf = [...present].filter(([name]) => !results.has(name)).map(([name, module]) => ({ name, module, title: tiles.get(name)! }));
  for (const { name } of shelf) nodes.delete(name);
  const ids = [...results.keys()];
  const all = leanUses({ linked: results, facts });
  const { kept, left } = simplifyUses(ids, all);
  const edges: ArgEdge[] = [];
  const add = (from: string, to: string, kind: LinkKind, note: string) =>
    edges.push({ key: `${from}→${to}→${kind}`, from, to, kind, linkIds: [], scoped: false, semanticClass: kind, note });
  // What nothing drawn uses hangs from the goal: the argument links it, and that is all the line says.
  const used = new Set(kept.map((use) => use.to));
  const tops = [...main.filter((name) => results.has(name) && !used.has(name)), ...ids.filter((name) => !used.has(name) && !main.includes(name))];
  for (const name of tops) {
    const isMain = main.includes(name);
    add(goal, name, "formalizes", isMain ? `${tiles.get(name)} is linked as the statement of this result` : `This argument links ${tiles.get(name)}, and no drawn declaration uses it by name`);
  }
  for (const use of kept) add(use.from, use.to, use.kind, phrase(use, (name) => tiles.get(name) ?? name));
  const out = new Map<string, ArgEdge[]>();
  const into = new Map<string, ArgEdge[]>();
  for (const id of nodes.keys()) {
    out.set(id, []);
    into.set(id, []);
  }
  for (const edge of edges) {
    out.get(edge.from)!.push(edge);
    into.get(edge.to)!.push(edge);
  }
  const members = [...nodes.keys()];
  return {
    origins: [],
    cites: [],
    nodes,
    order: members,
    edges,
    out,
    in: into,
    regions: [{ id: goal, title: goalLabel, goal, members }],
    regionOf: new Map(members.map((id) => [id, goal])),
    goals: [goal],
    cyclic: new Set(),
    boundaries: new Map(),
    plain: true,
    leftOut: left,
    missing,
    shelf,
  };
}

/** Which declarations each set of records links, by name; the order is the records' own. */
export function linkedDeclarations(records: Iterable<string>, rows: (id: string) => readonly { name: string; module: string }[]): Map<string, string> {
  const linked = new Map<string, string>();
  for (const id of records) for (const row of rows(id)) if (!linked.has(row.name)) linked.set(row.name, row.module);
  return linked;
}

const RESULT_KINDS = new Set(["theorem", "lemma"]);

/** The part of the graph around these declarations: each with what uses it and what it uses. */
export function neighbourhood(graph: LeanGraph, goal: string, focus: readonly string[]): LeanGraph {
  const inGraph = focus.filter((id) => graph.nodes.has(id));
  const centre = inGraph.length ? inGraph : [goal];
  const keep = new Set([goal, ...centre]);
  const near = (id: string) => {
    for (const e of graph.out.get(id) ?? []) keep.add(e.to);
    for (const e of graph.in.get(id) ?? []) keep.add(e.from);
  };
  centre.forEach(near);
  // From the goal, one row more: its own declarations alone say little.
  if (centre[0] === goal) for (const e of graph.out.get(goal) ?? []) for (const u of graph.out.get(e.to) ?? []) keep.add(u.to);
  const edges = graph.edges.filter((e) => keep.has(e.from) && keep.has(e.to) && (e.from !== goal || !graph.in.get(e.to)?.some((u) => u.from !== goal && keep.has(u.from))));
  const held = new Set(edges.map((e) => e.to));
  for (const id of keep) {
    if (id === goal || held.has(id)) continue;
    const tile = graph.nodes.get(id)?.tile ?? id;
    edges.push({ key: `${goal}→${id}→formalizes`, from: goal, to: id, kind: "formalizes", linkIds: [], scoped: false, semanticClass: "formalizes", note: `${tile}: what uses it is not drawn here. Fit shows the whole graph` });
  }
  const members = [...graph.order.filter((id) => keep.has(id))];
  const out = new Map(members.map((id) => [id, [] as ArgEdge[]]));
  const into = new Map(members.map((id) => [id, [] as ArgEdge[]]));
  for (const edge of edges) {
    out.get(edge.from)!.push(edge);
    into.get(edge.to)!.push(edge);
  }
  return {
    ...graph,
    nodes: new Map(members.map((id) => [id, graph.nodes.get(id)!])),
    order: members,
    edges,
    out,
    in: into,
    regions: [{ id: goal, title: graph.regions[0]?.title ?? "", goal, members }],
    regionOf: new Map(members.map((id) => [id, goal])),
  };
}

/** About how wide the whole drawing runs in world pixels: its fullest row of cards, with a margin for lines. */
export function leanWidth(graph: ArgGraph, goal: string, tile: number): number {
  const rank = new Map<string, number>([[goal, 0]]);
  const queue = [goal];
  while (queue.length) {
    const id = queue.shift()!;
    for (const e of graph.out.get(id) ?? []) {
      const r = rank.get(id)! + 1;
      if ((rank.get(e.to) ?? -1) < r && r <= graph.order.length) {
        rank.set(e.to, r);
        queue.push(e.to);
      }
    }
  }
  const rows = new Map<number, number>();
  for (const r of rank.values()) rows.set(r, (rows.get(r) ?? 0) + 1);
  return Math.max(...rows.values()) * (tile + 10) * 1.2;
}

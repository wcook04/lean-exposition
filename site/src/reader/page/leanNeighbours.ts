// A declaration that is no step of the argument map, drawn with its Lean neighbours, for the
// top of the split pane. The map's engine draws it like any other graph: the declaration is the
// root, and under it up to eight declarations of the project that it uses, those its statement
// names first, then those its proof names, with "and N more" for the rest. The declarations that
// use it are listed beside the drawing, up to eight and "and N more", because the engine draws a
// graph downward from its root. The facts are the Lean index's, the same the Lean card lists
// under "Names its statement uses", "Names its proof uses" and "Declarations that use it".

import type { ArgEdge, ArgGraph, ArgNode, LinkKind, Origin } from "../../model/graph";
import { leanKindWord, namedIn } from "../../model/leanGraph";

export interface NeighbourRow {
  kind: string;
  module: string;
  line: number;
}

export interface NeighbourInput {
  name: string;
  title: string;
  kind: string;
  /** Its statement's text, to tell a use in the statement from one in the proof. */
  statement: string;
  uses: readonly string[];
  usedBy: readonly string[];
  /** A declaration of the project, or undefined for one from outside it (Mathlib, core). */
  rowOf(name: string): NeighbourRow | undefined;
  /** The plain title, or null where none is written: the card then shows the Lean name as code. */
  titleOf(name: string): string | null;
  origin: Origin;
}

export interface Neighbourhood {
  graph: ArgGraph;
  /** Declarations of the project that use it, at most `cap`, and how many more. */
  users: { name: string; title: string; plain: boolean }[];
  moreUsers: number;
  /** How many project declarations it uses that are not drawn. */
  moreUses: number;
}

export const NEIGHBOUR_CAP = 8;

const lastName = (name: string) => name.slice(name.lastIndexOf(".") + 1);

/**
 * A step of the argument map with its neighbours on the map, in the same shape, for a pane too
 * small to draw them whole: the steps it uses below it and the steps that use it.
 */
export function stepNeighbourhood(graph: ArgGraph, id: string, drawn: ReadonlySet<string>, titleOf: (id: string) => string, cap = NEIGHBOUR_CAP): Neighbourhood {
  const blank = { papers: {}, region: id, passedExtraction: false, status: "unverified", origin: graph.nodes.get(id)!.origin };
  const uses = [...new Set((graph.out.get(id) ?? []).map((e) => e.to))].filter((to) => to !== id && drawn.has(to));
  const usedBy = [...new Set((graph.in.get(id) ?? []).map((e) => e.from))].filter((from) => from !== id && drawn.has(from));
  const nodes = new Map<string, ArgNode>();
  nodes.set(id, { ...blank, id, ref: id, kind: "goal", label: titleOf(id), tile: titleOf(id), tilePlain: true, leanNote: "" });
  const shown = uses.slice(0, cap);
  for (const to of shown) nodes.set(to, { ...blank, id: to, ref: to, kind: "declaration", label: titleOf(to), tile: titleOf(to), tilePlain: true });
  const edges: ArgEdge[] = shown.map((to) => ({ key: `${id}→${to}→supports`, from: id, to, kind: "supports" as LinkKind, linkIds: [], scoped: false, semanticClass: "supports", note: `${titleOf(id)} uses ${titleOf(to)}` }));
  if (uses.length > cap) {
    const more = `${id}#more`;
    const label = `and ${uses.length - cap} more it uses`;
    nodes.set(more, { ...blank, id: more, ref: more, kind: "declaration", label, tile: label, tilePlain: true });
    edges.push({ key: `${id}→${more}→supports`, from: id, to: more, kind: "supports", linkIds: [], scoped: false, semanticClass: "supports", note: label });
  }
  const members = [...nodes.keys()];
  const out = new Map<string, ArgEdge[]>(members.map((m) => [m, []]));
  const into = new Map<string, ArgEdge[]>(members.map((m) => [m, []]));
  for (const edge of edges) {
    out.get(edge.from)!.push(edge);
    into.get(edge.to)!.push(edge);
  }
  return {
    graph: { origins: [], cites: [], nodes, order: members, edges, out, in: into, regions: [{ id, title: titleOf(id), goal: id, members }], regionOf: new Map(members.map((m) => [m, id])), goals: [id], cyclic: new Set(), boundaries: new Map(), plain: true },
    users: usedBy.slice(0, cap).map((from) => ({ name: from, title: titleOf(from), plain: true })),
    moreUsers: Math.max(0, usedBy.length - cap),
    moreUses: Math.max(0, uses.length - cap),
  };
}

export function declarationNeighbourhood(input: NeighbourInput, cap = NEIGHBOUR_CAP): Neighbourhood {
  const { name, title, origin } = input;
  const project = (list: readonly string[]) => [...new Set(list)].filter((other) => other !== name && input.rowOf(other));
  const uses = project(input.uses);
  const inStatement = uses.filter((other) => namedIn(input.statement, other));
  const inProof = uses.filter((other) => !inStatement.includes(other));
  const drawn = [...inStatement, ...inProof].slice(0, cap);
  const moreUses = uses.length - drawn.length;
  const blank = { papers: {}, region: name, passedExtraction: false, status: "unverified", origin };
  const nodes = new Map<string, ArgNode>();
  nodes.set(name, { ...blank, id: name, ref: name, kind: "goal", label: title, declaration: name, tile: title, tilePlain: true, leanNote: leanKindWord(input.kind) });
  for (const other of drawn) {
    const row = input.rowOf(other)!;
    const tile = input.titleOf(other) ?? lastName(other);
    nodes.set(other, { ...blank, id: other, ref: other, kind: "declaration", label: tile, declaration: other, tile, tilePlain: input.titleOf(other) !== null, leanNote: `${leanKindWord(row.kind)}, line ${row.line}` });
  }
  const edges: ArgEdge[] = [];
  const add = (to: string, kind: LinkKind, note: string) =>
    edges.push({ key: `${name}→${to}→${kind}`, from: name, to, kind, linkIds: [], scoped: false, semanticClass: kind, note });
  for (const other of drawn) {
    const stated = inStatement.includes(other);
    add(other, stated ? "lean_type_dependency" : "supports", `The ${stated ? "statement" : "proof"} of ${title} uses ${input.titleOf(other) ?? lastName(other)}`);
  }
  if (moreUses > 0) {
    const more = `${name}#more`;
    const label = `and ${moreUses} more it uses`;
    nodes.set(more, { ...blank, id: more, ref: more, kind: "declaration", label, tile: label, tilePlain: true, leanNote: "Listed on the Lean card below" });
    add(more, "supports", `${moreUses} more declarations of the project that ${title} uses are listed on the Lean card`);
  }
  const out = new Map<string, ArgEdge[]>([...nodes.keys()].map((id) => [id, []]));
  const into = new Map<string, ArgEdge[]>([...nodes.keys()].map((id) => [id, []]));
  for (const edge of edges) {
    out.get(edge.from)!.push(edge);
    into.get(edge.to)!.push(edge);
  }
  const members = [...nodes.keys()];
  const users = project(input.usedBy);
  return {
    graph: {
      origins: [],
      cites: [],
      nodes,
      order: members,
      edges,
      out,
      in: into,
      regions: [{ id: name, title, goal: name, members }],
      regionOf: new Map(members.map((id) => [id, name])),
      goals: [name],
      cyclic: new Set(),
      boundaries: new Map(),
      plain: true,
    },
    users: users.slice(0, cap).map((other) => ({ name: other, title: input.titleOf(other) ?? lastName(other), plain: input.titleOf(other) !== null })),
    moreUsers: Math.max(0, users.length - cap),
    moreUses,
  };
}

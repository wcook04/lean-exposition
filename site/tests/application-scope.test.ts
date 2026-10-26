import { describe, expect, it } from "vitest";
import type { GraphMap, MapLink } from "../src/api/types";
import { argumentContexts, argumentProjection, buildGraph, closure, inducedEdges, suppliedPremises } from "../src/model/graph";
import { fixture, graphFixture } from "./fixtures";

// The backend's own scoped closure for every node (scripts/capture-closures.py).
interface Oracle {
  graph_sha256: string;
  roots: Record<string, { closure: string[]; flat: string[]; states: [string, string[]][]; live: string[] }>;
}
const oracle = fixture<Oracle>("closures.json");
const map = fixture<GraphMap>("graph-map.json");
const graph = graphFixture();

describe("application scope against the backend", () => {
  it("was captured from the same graph as the map fixture", () => {
    expect(map.links[0].from).toContain(`sha256:${oracle.graph_sha256}/`);
    expect(Object.keys(oracle.roots).sort()).toEqual([...graph.nodes.keys()].sort());
    expect(graph.nodes.size).toBe(129);
  });

  it("follows each node's own assumptions exactly as the records list them", () => {
    const nodes = fixture<{ id: string; assumption_ids: string[] }[]>("table-nodes.json");
    for (const node of nodes)
      expect((graph.out.get(node.id) ?? []).filter((e) => e.kind === "assumes").map((e) => e.to).sort()).toEqual([...node.assumption_ids].sort());
  });

  it("keeps every application as served, including shared bindings, status and source span", () => {
    const applied = graph.edges.filter((e) => e.application);
    expect(applied.length).toBe(map.links.filter((l) => l.application).length);
    for (const edge of applied) {
      const link = map.links.find((l) => l.application && l.from_node_id === edge.from && l.to_node_id === edge.to)!;
      expect(edge.application!.record).toEqual(link.application);
      expect(edge.application!.shared).toEqual(link.application!.shared_bindings);
      expect(edge.application!.status).toBe("authored");
      expect(edge.application!.sourceSpan?.sourceId).toBe(link.application!.source_span.source_id);
      expect(suppliedPremises(edge)).toEqual(link.application!.premise_bindings.map((b) => b.assumption_id));
      expect(edge.scoped).toBe(true);
    }
  });

  it("gives the backend's closure, contexts and live relations for all 129 roots", () => {
    for (const [root, expected] of Object.entries(oracle.roots)) {
      expect([...closure(graph, root, "prerequisites")].sort(), root).toEqual(expected.closure);
      const { states } = argumentContexts(graph, root);
      expect([...states.values()].map((s) => [s.node, s.discharged]).sort(), root).toEqual(
        expected.states.map(([n, d]) => [n, [...d].sort()]).sort(),
      );
      const projection = argumentProjection(graph, root);
      expect([...projection.nodes].sort(), root).toEqual(expected.closure);
      expect([...projection.edges].sort(), root).toEqual(expected.live);
    }
  });

  it("no longer restores supplied premises for the roots that apply a theorem", () => {
    const differ = Object.entries(oracle.roots).filter(([, r]) => r.closure.length !== r.flat.length);
    expect(differ.length).toBeGreaterThan(0);
    for (const [root, r] of differ) {
      const flat = new Set(r.flat);
      expect(flat.size).toBeGreaterThan(r.closure.length);
      expect(closure(graph, root, "prerequisites").size, root).toBe(r.closure.length);
    }
    expect(closure(graph, "support.near_ground_pairs", "prerequisites").size).toBe(oracle.roots["support.near_ground_pairs"].closure.length);
    expect(closure(graph, "qaoa_thermodynamic_first", "prerequisites").size).toBe(oracle.roots.qaoa_thermodynamic_first.closure.length);
  });

  it("finds consumers whose scoped argument contains the record, and no others", () => {
    for (const target of graph.order) {
      const expected = Object.entries(oracle.roots)
        .filter(([, r]) => r.closure.includes(target))
        .map(([root]) => root)
        .sort();
      expect([...closure(graph, target, "consumers")].sort(), target).toEqual(expected);
    }
  });

  it("reports the counts the map will show for the three goals", () => {
    const counts = Object.fromEntries(
      ["full_support", "scalar_value", "qaoa_thermodynamic_first"].map((goal) => {
        const p = argumentProjection(graph, goal);
        const flat = new Set(oracle.roots[goal].flat);
        return [goal, { records: p.nodes.size, live: p.edges.size, induced: inducedEdges(graph, p.nodes).length, flatRecords: flat.size, flatEdges: inducedEdges(graph, flat).length }];
      }),
    );
    expect(counts).toEqual({
      full_support: { records: 30, live: 73, induced: 73, flatRecords: 30, flatEdges: 73 },
      scalar_value: { records: 24, live: 67, induced: 67, flatRecords: 24, flatEdges: 67 },
      qaoa_thermodynamic_first: { records: 60, live: 122, induced: 122, flatRecords: 62, flatEdges: 139 },
    });
  });
});

// A conditional theorem T has premise P. C1 uses T freely; C2 applies T and
// supplies P through S; C3 applies T supplying P but T also needs Q.
function synthetic() {
  const node = (id: string, kind = "claim") => ({ id, kind, label: id, ref: `r/${id}`, status: "recorded" });
  const link = (from: string, to: string, kind: string, extra: Partial<MapLink> = {}): MapLink => ({
    id: `${from}>${to}>${kind}`,
    record_ref: `e/${from}>${to}`,
    kind,
    semantic_class: kind,
    from: `r/${from}`,
    to: `r/${to}`,
    from_node_id: from,
    to_node_id: to,
    derived: kind === "assumption_ids",
    ...extra,
  });
  const app = (premises: string[], remaining: string[]) => ({
    premise_bindings: premises.map((p) => ({ assumption_id: p, binding_names: ["x"], rationale: "r", supplier_id: "S" })),
    rationale: "applied",
    remaining_assumption_ids: remaining,
    shared_bindings: { x: "the fixed object" },
    source_span: { source_id: "src", start_line: 1, end_line: 2 },
    status: "authored",
  });
  const map: GraphMap = {
    view: "arguments",
    representation: "map",
    graph_id: "g",
    graph_sha256: "0",
    selected_goals: [],
    records: { nodes: ["T", "S", "C1", "C2", "C3", "U"].map((id) => node(id)).concat([node("P", "assumption"), node("Q", "assumption")]), edges: [], citations: [], evidence: [], sources: [] },
    links: [
      link("T", "P", "assumption_ids"),
      link("U", "T", "supports"),
      link("U", "Q", "assumption_ids"),
      link("C1", "T", "supports"),
      link("C2", "T", "supports", { application: app(["P"], []) }),
      link("C2", "S", "supports"),
      link("C3", "U", "supports", { application: app(["P"], ["Q"]) }),
      link("C3", "S", "supports"),
    ],
    components: [],
    coverage: { boundaries: [], claim: "", empty_result_meaning: "", query_truncated: false },
    records_href: "",
  };
  return buildGraph(map, [], []);
}

describe("application scope on a small graph", () => {
  const g = synthetic();

  it("keeps the premise of a free use of a conditional theorem", () => {
    expect([...closure(g, "C1", "prerequisites")].sort()).toEqual(["C1", "P", "T"]);
  });

  it("does not restore a premise that an application supplies", () => {
    expect([...closure(g, "C2", "prerequisites")].sort()).toEqual(["C2", "S", "T"]);
    const p = argumentProjection(g, "C2");
    expect(p.edges.has("T→P→assumes")).toBe(false);
    expect(p.edges.has("C2→T→supports")).toBe(true);
  });

  it("keeps a remaining premise", () => {
    expect([...closure(g, "C3", "prerequisites")].sort()).toEqual(["C3", "Q", "S", "T", "U"]);
  });

  it("keeps an independently reached free use alongside a supplied one", () => {
    const both = closure(g, ["C1", "C2"], "prerequisites");
    expect(both.has("P")).toBe(true);
    const { states } = argumentContexts(g, ["C1", "C2"]);
    expect([...states.values()].filter((s) => s.node === "T").map((s) => s.discharged)).toEqual(expect.arrayContaining([[], ["P"]]));
  });

  it("lists as consumers only records whose argument still contains the premise", () => {
    expect([...closure(g, "P", "consumers")].sort()).toEqual(["C1", "P", "T", "U"]);
  });
});

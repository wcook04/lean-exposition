import { describe, expect, it } from "vitest";
import type { EdgeRecord, EvidenceRecord, GraphMap, MapLink, NodeRecord } from "../src/api/types";
import { argumentContexts, argumentProjection, buildGraph, closure, inducedEdges, suppliedPremises } from "../src/model/graph";
import { relationName, relationPhrase } from "../src/map/labels";
import { editionGraphFixture, fixture, graphFixture } from "./fixtures";

// The backend's own scoped closure for every node (scripts/capture-closures.py).
interface Oracle {
  graph_sha256: string;
  roots: Record<string, { closure: string[]; flat: string[]; states: [string, string[]][]; live: string[] }>;
}
const oracle = fixture<Oracle>("closures.json");
const oracleRootIds = Object.keys(oracle.roots).sort();
const map = fixture<GraphMap>("graph-map.json");

describe.each([
  { mode: "compact map", graph: graphFixture() },
  { mode: "full records", graph: editionGraphFixture() },
])("application scope against the backend ($mode)", ({ graph }) => {
  it("was captured from the same graph as the map fixture", () => {
    expect(map.links[0].from).toContain(`sha256:${oracle.graph_sha256}/`);
    expect(oracleRootIds.length).toBeGreaterThan(0);
    expect([...graph.nodes.keys()].sort()).toEqual(oracleRootIds);
    expect(graph.nodes.size).toBe(oracleRootIds.length);
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

  it(`gives the backend's closure, contexts and live relations for all ${oracleRootIds.length} captured roots`, () => {
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

type RecordMode = "compact" | "full";

// The cases in tests/test_application_obligations.py: a retained formal result
// and an ordinary conditional result share a premise ID, each applied locally.
// Compact mode uses only the API's map cards; full mode deliberately omits the
// new compact metadata and hydrates from the exact node/evidence tables.
function obligationFixture(mode: RecordMode, options: {
  premise?: string;
  declaration?: string;
  premiseKind?: string;
  dependency?: string;
  evidence?: Pick<EvidenceRecord, "kind" | "status" | "subject_ids"> | null;
  secondPremise?: boolean;
} = {}) {
  const premise = options.premise ?? "Classical.choice";
  const dependency = options.dependency ?? "assumption_ids";
  const node = (id: string, kind = "claim", assumption_ids: string[] = []): NodeRecord => ({
    id, kind, label: id, status: "unverified", assumption_ids, evidence_ids: [],
  });
  const records = [
    { ...node("result", "declaration", dependency === "assumption_ids" ? [premise] : []), declaration: "Formal.result", evidence_ids: ["check"] },
    node("consumer"), node("supplier"), node("ordinary-result", "claim", [premise]), node("ordinary-goal"),
    { ...node(premise, options.premiseKind ?? "assumption"), declaration: options.declaration ?? premise },
  ];
  const evidence: EvidenceRecord[] = options.evidence === null ? [] : [{
    id: "check", kind: "extraction", status: "passed", subject_ids: ["result"],
    source_ids: [], command: [], tool: "Synthetic fixture", details: "No actual Lean run.",
    ...options.evidence,
  }];
  const link = (from: string, to: string, kind: string, extra: Partial<MapLink> = {}): MapLink => ({
    id: `${from}>${to}>${kind}`, kind,
    semantic_class: kind.startsWith("lean_") ? "lean_syntactic_dependency" : kind === "assumption_ids" ? "explicit_assumption_reference" : "curated_argument_support",
    from: `r/${from}`, to: `r/${to}`, from_node_id: from, to_node_id: to,
    derived: kind === "assumption_ids", ...extra,
  });
  const applied = (premises: string[]) => ({
    premise_bindings: premises.map((assumption_id) => ({ assumption_id, supplier_id: "supplier", binding_names: ["x"], rationale: "Synthetic binding." })),
    remaining_assumption_ids: [], shared_bindings: { x: "a supplied witness" },
    rationale: "Synthetic binding, not a Lean substitution.", status: "authored",
    source_span: { source_id: "src", start_line: 1, end_line: 1 },
  });
  const links = [
    link("result", premise, dependency),
    link("consumer", "result", "supports", { application: applied([premise, ...(options.secondPremise ? ["Q"] : [])]) }),
    link("consumer", "supplier", "supports"),
    link("ordinary-result", premise, "assumption_ids"),
    link("ordinary-goal", "ordinary-result", "supports", { application: applied([premise]) }),
    link("ordinary-goal", "supplier", "supports"),
  ];
  if (options.secondPremise) {
    records.push(node("Q", "assumption"), node("ordinary-Q", "claim", ["Q"]));
    links.push(link("result", "ordinary-Q", "supports"), link("ordinary-Q", "Q", "assumption_ids"));
  }
  const map: GraphMap = {
    view: "arguments", representation: "map", graph_id: "synthetic-obligations", graph_sha256: "0", selected_goals: ["consumer"],
    records: {
      nodes: records.map((record) => ({ id: record.id, kind: record.kind, label: record.label, status: record.status, ref: `r/${record.id}`,
        ...(mode === "compact" && record.declaration ? { declaration: record.declaration } : {}) })),
      evidence: evidence.map((record) => ({ id: record.id, kind: record.kind, status: record.status, label: record.id, ref: `e/${record.id}`, relevant: true,
        ...(mode === "compact" && record.kind === "extraction" ? { subject_ids: record.subject_ids } : {}) })),
      edges: [], citations: [], sources: [],
    },
    links, components: [], records_href: "",
    coverage: { boundaries: [], claim: "", empty_result_meaning: "", query_truncated: false },
  };
  const edges: EdgeRecord[] = links.filter((row) => !row.derived).map((row) => ({
    from: row.from_node_id, to: row.to_node_id, kind: row.kind, evidence_ids: [], application: row.application,
  }));
  return mode === "compact" ? buildGraph(map, [], []) : buildGraph(map, [], [], records, [], { edges, evidence });
}

describe.each<RecordMode>(["compact", "full"])("formal obligations in %s records", (mode) => {
  it.each(["Classical.choice", "sorryAx"])("retains extracted %s despite an authored binding", (premise) => {
    const graph = obligationFixture(mode, { premise });
    expect(graph.nodes.get("result")?.passedExtraction).toBe(true);
    expect([...closure(graph, "consumer", "prerequisites")].sort()).toEqual([premise, "consumer", "result", "supplier"].sort());
    const { states, transitions } = argumentContexts(graph, "consumer");
    expect([...states.values()].map((state) => [state.node, state.discharged])).toEqual(expect.arrayContaining([
      ["result", [premise]], [premise, []],
    ]));
    expect(transitions.some((step) => step.edge.from === "result" && step.edge.to === premise)).toBe(true);
  });

  it.each([
    { premise: "sorryAx", declaration: "another-declaration" },
    { premise: "renamed-sorry", declaration: "sorryAx" },
  ])("retains the actual proof-hole identity $premise / $declaration without extraction", (identity) => {
    const graph = obligationFixture(mode, { ...identity, evidence: null });
    expect(graph.nodes.get(identity.premise)?.declaration).toBe(identity.declaration);
    expect(closure(graph, "consumer", "prerequisites").has(identity.premise)).toBe(true);
  });

  it.each([
    null,
    { kind: "source_hash", status: "passed", subject_ids: ["result"] },
    { kind: "extraction", status: "not_run", subject_ids: ["result"] },
    { kind: "extraction", status: "failed", subject_ids: ["result"] },
    { kind: "extraction", status: "passed", subject_ids: ["supplier"] },
  ])("does not infer formal scope from names, declaration kind or cited evidence: %j", (evidence) => {
    const graph = obligationFixture(mode, { evidence });
    expect(graph.nodes.get("result")?.passedExtraction).toBe(false);
    expect(closure(graph, "consumer", "prerequisites").has("Classical.choice")).toBe(false);
  });

  it("does not identify a proof hole by a qualified suffix or label", () => {
    const graph = obligationFixture(mode, { premise: "User.sorryAx", evidence: null });
    expect(closure(graph, "consumer", "prerequisites").has("User.sorryAx")).toBe(false);
  });

  it("lets an ordinary use discharge the same ID as a disconnected formal obligation", () => {
    const graph = obligationFixture(mode);
    expect(closure(graph, "ordinary-goal", "prerequisites").has("Classical.choice")).toBe(false);
    expect(closure(graph, "consumer", "prerequisites").has("Classical.choice")).toBe(true);
    expect([...closure(graph, "Classical.choice", "consumers")].sort()).toEqual(["Classical.choice", "consumer", "ordinary-result", "result"].sort());
    const projection = argumentProjection(graph, ["consumer", "ordinary-goal"]);
    expect(projection.edges.has("result→Classical.choice→assumes")).toBe(true);
    expect(projection.edges.has("ordinary-result→Classical.choice→assumes")).toBe(false);
  });

  it("restores only the formal obligation in its own context", () => {
    const graph = obligationFixture(mode, { secondPremise: true });
    const { states } = argumentContexts(graph, "consumer");
    expect([...states.values()].filter((state) => state.node === "Classical.choice").map((state) => state.discharged)).toEqual([["Q"]]);
    expect(closure(graph, "consumer", "prerequisites").has("Q")).toBe(false);
  });

  it.each(["lean_type_dependency", "lean_value_dependency", "lean_structural_dependency"])("retains a typed %s occurrence even without passed extraction", (dependency) => {
    const graph = obligationFixture(mode, { dependency, evidence: null });
    const projection = argumentProjection(graph, "consumer");
    expect(projection.nodes.has("Classical.choice")).toBe(true);
    expect(projection.edges.has(`result→Classical.choice→${dependency}`)).toBe(true);
    expect(graph.edges.find((edge) => edge.from === "result")?.semanticClass).toBe("lean_syntactic_dependency");
    expect(relationName(dependency)).toContain("Lean");
    expect(relationPhrase(dependency, "result", "Classical.choice")).toContain("Lean");
    expect(closure(graph, "consumer", "prerequisites", ["supports", "assumes"]).has("Classical.choice")).toBe(false);
    expect(closure(obligationFixture(mode, { dependency, premiseKind: "claim", evidence: null }), "consumer", "prerequisites").has("Classical.choice")).toBe(false);
  });

  it.each(["supports", "formalizes"])("does not turn a curated %s occurrence into a Lean dependency", (dependency) => {
    const graph = obligationFixture(mode, { dependency });
    expect(graph.nodes.get("result")?.passedExtraction).toBe(true);
    expect(closure(graph, "consumer", "prerequisites").has("Classical.choice")).toBe(false);
  });

  it.each(["cites", "platform_decomposition"])("keeps %s outside default argument traversal", (dependency) => {
    const graph = obligationFixture(mode, { dependency, evidence: null });
    expect([...closure(graph, "result", "prerequisites")]).toEqual(["result"]);
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

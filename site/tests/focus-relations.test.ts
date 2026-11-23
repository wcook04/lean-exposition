// The graph pane's words state what the data records, and never turn missing data into a claim
// about the mathematics. A declaration with no recorded route is "no route recorded", not "not a
// step of the argument"; and every edge and count says which relation it is: a link the paper
// states, a link derived from the Lean, an assumption, or a Lean statement, proof or unsplit use.
import { describe, expect, it } from "vitest";
import { graphFixture } from "./fixtures";
import type { LeanDeclaration, LeanModule } from "../src/api/lean";
import type { LeanShell } from "../src/lean/data";
import type { DeclRow, LeanIndex } from "../src/lean/resolve";
import { relationCounts, type FGRelation } from "../src/map/FocusGraph";
import { focusOn, LEAN_DEPENDENCIES, relationOf, routeWords, type FocusInput, type PaperPlaces } from "../src/reader/page/focusModel";

const places = (): PaperPlaces => ({ recordAt: new Map(), declAt: new Map(), recordTone: new Map(), declTone: new Map(), recordTopic: new Map(), declTopic: new Map(), sections: [] });

function decl(name: string, over: Partial<LeanDeclaration> & Record<string, unknown> = {}): LeanDeclaration {
  return { name, short: name.split(".").pop()!, kind: "theorem", namespace: "A", line: 1, signature_end_line: 1, end_line: 1, doc: null, private: false, uses: [], used_by: [], ...over } as LeanDeclaration;
}

/** A Lean shell over one module, and that module. */
function lean(decls: LeanDeclaration[], linked: Record<string, { id: string }[]> = {}) {
  const rows: DeclRow[] = decls.map((d) => ({ name: d.name, short: d.short, kind: d.kind, module: "A", line: 1, endLine: 1 }));
  const index: LeanIndex = { byName: new Map(rows.map((r) => [r.name, [r]])), rows, lower: rows.map((r) => r.name.toLowerCase()) };
  const shell = {
    index,
    linked: new Map(Object.entries(linked).map(([name, ids]) => [name, ids.map(({ id }) => ({ id, title: id, relation: "states", note: "" }))])),
    plain: new Map(),
    paths: new Map(),
    terms: new Map(),
    modules: {},
  } as unknown as LeanShell;
  const module: LeanModule = { module: "A", path: "A.lean", sha256: "", imports: [], source: "theorem x : True := trivial\n", declarations: decls };
  return { shell, module };
}

function input(over: Partial<FocusInput>): FocusInput {
  const graph = graphFixture();
  return { graph, stage: "long", home: graph.goals[0], onMap: () => true, alignment: null, shell: null, module: () => undefined, places: places(), readAt: null, ...over };
}

describe("where an argument link comes from", () => {
  it("calls a supports link read off the Lean's dependencies derived, never the paper's", () => {
    expect(relationOf({ from: "a", to: "b", kind: "supports", warrant: { evidenceId: LEAN_DEPENDENCIES } as never })).toBe("derived");
    expect(relationOf({ from: "a", to: "b", kind: "supports", warrant: { evidenceId: "review.a-b" } as never })).toBe("argument");
    expect(relationOf({ from: "a", to: "b", kind: "supports" })).toBe("argument");
    // An assumption is its own relation, not a Lean statement use.
    expect(relationOf({ from: "a", to: "b", kind: "assumes" })).toBe("assumes");
  });

  it("says how many links a route has and which kind each is", () => {
    expect(routeWords(["argument"], true)).toBe("The main result uses this directly, by a link the paper states:");
    expect(routeWords(["derived"], true)).toBe("The main result uses this directly, by a link derived from the Lean:");
    expect(routeWords(["derived", "derived"], true)).toBe("2 links to the main result, each derived from the Lean:");
    expect(routeWords(["argument", "derived", "argument"], false)).toBe("3 links to one of the paper’s main results, 2 stated by the paper and 1 derived from the Lean:");
  });

  it("counts each relation apart, in words that name it", () => {
    const counts = new Map<FGRelation, number>([["proof", 3], ["argument", 1], ["derived", 2], ["statement", 1], ["use", 4]]);
    expect(relationCounts(counts)).toBe(
      "1 by a link the paper states, 2 by a link derived from the Lean, 3 in a Lean proof or body, 1 in a Lean statement, 4 in the Lean, statement or proof not recorded",
    );
  });
});

describe("a declaration with no recorded route", () => {
  it("says the route is not recorded, and makes no claim that it is not a step", () => {
    const { shell, module } = lean([decl("A.x")]);
    const focus = focusOn({ kind: "decl", name: "A.x" }, input({ shell, module: () => module }));
    expect(focus.route).toBeNull();
    expect(focus.routeNote).toMatch(/^No paper-argument route is recorded for this declaration/);
    expect(focus.routeNote).not.toMatch(/not a step/i);
  });

  it("says so too when it states a result that no recorded link joins to the main result", () => {
    const base = input({});
    const lonely = [...base.graph.nodes.values()].find((n) => n.kind !== "goal" && !(base.graph.in.get(n.id) ?? []).some((e) => e.kind === "supports" || e.kind === "assumes"));
    expect(lonely).toBeDefined();
    if (!lonely) return;
    const { shell, module } = lean([decl("A.x")], { "A.x": [{ id: lonely.id }] });
    const focus = focusOn({ kind: "decl", name: "A.x" }, { ...base, shell, module: () => module });
    expect(focus.routeNote).toMatch(/^No paper-argument route is recorded for this declaration: no recorded link/);
  });

  it("does not count the correspondence with the result it states as a link of the route", () => {
    const base = input({});
    const goal = base.home;
    const { shell, module } = lean([decl("A.x")], { "A.x": [{ id: goal }] });
    const focus = focusOn({ kind: "decl", name: "A.x" }, { ...base, shell, module: () => module });
    expect(focus.route).toEqual([goal]);
    expect(focus.routeLabel).toBe("This declaration states the main result:");
  });
});

describe("Lean uses are split as Lean records them", () => {
  it("shows typed dependencies beyond the paper catalogue and reports the size of a limited view", () => {
    const ref = (name: string, kinds: string[]) => ({ name, kinds, display_title: name, kind: "definition", origin: "project" });
    const x = decl("A.x", { neighbourhood: {
      source: "compiled_lean", scope: "riemann_hypothesis_closure", limit: 2,
      dependencies: [ref("PropX", ["type"]), ref("proofOfX", ["value"])],
      users: [ref("A.user", ["type", "value"])], counts: { dependencies: 2, users: 3 },
    } });
    const { shell, module } = lean([x]);
    const focus = focusOn({ kind: "decl", name: "A.x" }, input({ shell, module: () => module }));
    expect(focus.subjects).toEqual(["decl:A.x"]);
    expect(focus.cards.get("decl:proofOfX")?.reference?.name).toBe("proofOfX");
    expect(focus.edges.map(({ from, to, kind }) => [from, to, kind])).toEqual([
      ["decl:A.x", "decl:PropX", "statement"], ["decl:A.x", "decl:proofOfX", "proof"],
      ["decl:A.user", "decl:A.x", "statement"], ["decl:A.user", "decl:A.x", "proof"],
    ]);
    expect(focus.neighbourhoodNote).toContain("1 of 3 users");
  });

  it("takes statement and proof uses, and users, from the compiled facts", () => {
    const x = decl("A.x", {
      uses: ["A.s", "A.p"],
      statement_uses: ["A.s"],
      proof_uses: ["A.p"],
      used_by: ["A.u1", "A.u2"],
      statement_used_by: ["A.u1"],
      proof_used_by: ["A.u2"],
    });
    const { shell, module } = lean([x, decl("A.s"), decl("A.p"), decl("A.u1"), decl("A.u2")]);
    const focus = focusOn({ kind: "decl", name: "A.x" }, input({ shell, module: () => module }));
    const kind = (from: string, to: string) => focus.edges.filter((e) => e.from === `decl:${from}` && e.to === `decl:${to}`).map((e) => e.kind);
    expect(kind("A.x", "A.s")).toEqual(["statement"]);
    expect(kind("A.x", "A.p")).toEqual(["proof"]);
    expect(kind("A.u1", "A.x")).toEqual(["statement"]);
    expect(kind("A.u2", "A.x")).toEqual(["proof"]);
  });

  it("calls a user an unsplit Lean use where no record says statement or proof", () => {
    const x = decl("A.x", { used_by: ["A.u"] });
    const { shell, module } = lean([x, decl("A.u")]);
    const focus = focusOn({ kind: "decl", name: "A.x" }, input({ shell, module: () => module }));
    expect(focus.edges.find((e) => e.from === "decl:A.u")?.kind).toBe("use");
  });
});

describe("a record's argument neighbours", () => {
  it("are paper-stated, derived from the Lean or assumptions, each as recorded", () => {
    const base = input({});
    const { graph } = base;
    const subject = [...graph.nodes.keys()].find((id) => (graph.out.get(id) ?? []).filter((e) => e.kind === "supports").length >= 2)!;
    const supports = graph.out.get(subject)!.filter((e) => e.kind === "supports");
    supports[0].warrant = { evidenceId: LEAN_DEPENDENCIES } as never;
    const focus = focusOn({ kind: "records", ids: [subject] }, base);
    const kindTo = (to: string) => focus.edges.find((e) => e.from === subject && e.to === to)?.kind;
    expect(kindTo(supports[0].to)).toBe("derived");
    expect(kindTo(supports[1].to)).toBe("argument");
    for (const e of graph.out.get(subject)!.filter((e) => e.kind === "assumes")) expect(kindTo(e.to)).toBe("assumes");
    // No argument edge is called a Lean statement use.
    const argumentTargets = new Set(graph.out.get(subject)!.filter((e) => e.kind === "supports" || e.kind === "assumes").map((e) => e.to));
    for (const e of focus.edges) if (e.from === subject && argumentTargets.has(e.to)) expect(["argument", "derived", "assumes"]).toContain(e.kind);
  });

  it("qualifies its route by the kind of each link", () => {
    const base = input({});
    const { graph } = base;
    const subject = [...graph.nodes.keys()].find((id) => id !== base.home && (graph.in.get(id) ?? []).some((e) => e.kind === "supports"))!;
    const focus = focusOn({ kind: "records", ids: [subject] }, base);
    expect(focus.route?.length).toBeGreaterThan(0);
    expect(focus.routeLabel).toMatch(/stated by the paper|the paper states|derived from the Lean/);
  });
});

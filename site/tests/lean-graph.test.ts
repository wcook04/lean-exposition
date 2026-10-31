import { describe, expect, it } from "vitest";
import { buildLeanGraph, leanUses, linkedDeclarations, namedIn, neighbourhood, simplifyUses, tileNames, type LeanFacts } from "../src/model/leanGraph";
import { declTitle } from "../src/model/declTitle";
import type { Origin } from "../src/model/graph";

const origin: Origin = { family: "lean", label: "Lean", slot: 3, place: null, locator: null, url: null };

function fact(name: string, uses: string[], statement = ""): LeanFacts {
  return { name, short: name.split(".").pop()!, kind: "theorem", module: "M", line: 1, uses, statement, text: statement };
}

const table = (...facts: LeanFacts[]) => {
  const map = new Map(facts.map((f) => [f.name, f]));
  return (name: string) => map.get(name);
};

describe("the Lean graph", () => {
  it("tells a statement's use from a proof's by where the name is written", () => {
    expect(namedIn("theorem a (x : Foo.bar) : baz x", "Ns.Foo.bar")).toBe(true);
    expect(namedIn("theorem a : foobar", "Ns.bar")).toBe(false);
    expect(namedIn("theorem a : bar'", "Ns.bar")).toBe(false);
    const facts = table(fact("a", ["b", "c"], "theorem a : b"), fact("b", []), fact("c", []));
    const linked = new Map([["a", "M"], ["b", "M"], ["c", "M"]]);
    const kinds = Object.fromEntries(leanUses({ linked, facts }).map((u) => [u.to, u.kind]));
    expect(kinds).toEqual({ b: "lean_type_dependency", c: "supports" });
  });

  it("walks through unlinked helpers and stops at the next linked name", () => {
    const facts = table(fact("a", ["h1"]), fact("h1", ["h2"]), fact("h2", ["b"]), fact("b", ["c"]), fact("c", []));
    const uses = leanUses({ linked: new Map([["a", "M"], ["b", "M"], ["c", "M"]]), facts });
    expect(uses).toContainEqual({ from: "a", to: "b", kind: "lean_via", helpers: ["h1", "h2"] });
    expect(uses.some((u) => u.from === "a" && u.to === "c")).toBe(false);
  });

  it("leaves out what a longer chain says and anything that closes a cycle", () => {
    const u = (from: string, to: string) => ({ from, to, kind: "supports" as const, helpers: [] });
    const { kept, left } = simplifyUses(["a", "b", "c"], [u("a", "b"), u("b", "c"), u("a", "c"), u("c", "a")]);
    expect(kept.map((e) => `${e.from}${e.to}`).sort()).toEqual(["ab", "bc"]);
    expect(left).toBe(2);
  });

  it("hangs what nothing drawn uses from the goal, and says what that line means", () => {
    const graph = buildLeanGraph({
      goal: "goal",
      goalLabel: "The result",
      linked: new Map([["main", "M"], ["used", "M"], ["alone", "M"]]),
      main: ["main"],
      facts: table(fact("main", ["used"]), fact("used", []), fact("alone", [])),
      origin,
    });
    expect(graph.nodes.get("goal")?.kind).toBe("goal");
    expect(graph.out.get("goal")?.map((e) => [e.to, e.kind])).toEqual([["main", "formalizes"], ["alone", "formalizes"]]);
    expect(graph.out.get("goal")?.[1].note).toContain("no drawn declaration uses it");
    expect(graph.plain).toBe(true);
  });

  it("says when a linked name is not in the index", () => {
    const graph = buildLeanGraph({ goal: "goal", goalLabel: "G", linked: new Map([["gone", "M"]]), main: [], facts: () => undefined, origin });
    expect(graph.missing).toEqual(["gone"]);
    expect(graph.nodes.size).toBe(1);
  });

  it("keeps the namespace that tells two short names apart", () => {
    const tiles = tileNames(["A.B.Order", "A.C.Order", "A.B.other"]);
    expect(tiles.get("A.B.Order")).toBe("B.Order");
    expect(tiles.get("A.C.Order")).toBe("C.Order");
    expect(tiles.get("A.B.other")).toBe("other");
  });

  it("counts each declaration once across records", () => {
    const rows = (id: string) => (id === "r1" ? [{ name: "a", module: "M" }, { name: "b", module: "M" }] : [{ name: "a", module: "M" }]);
    expect([...linkedDeclarations(["r1", "r2"], rows).keys()]).toEqual(["a", "b"]);
  });
});

describe("a declaration's plain title", () => {
  const sources = {
    records: {
      weak: { short: "A part of it", lean: [{ name: "n.a", relation: "part" }, { name: "n.c", relation: "part" }] },
      strong: { short: "The result", lean: [{ name: "n.a", relation: "states" }] },
    },
    dictionary: [{ name: "n.b", words: "The Parisi functional." }, { name: "n.c", words: "Other words." }],
  };

  it("takes the record that links it most directly, then the dictionary, and has none after that", () => {
    expect(declTitle(sources, "n.a")).toBe("The result");
    expect(declTitle(sources, "n.c")).toBe("A part of it");
    expect(declTitle(sources, "n.b")).toBe("The Parisi functional");
    expect(declTitle(sources, "n.gone")).toBeNull();
  });

  it("puts an authored title first", () => {
    expect(declTitle({ ...sources, names: { "n.a": "Authored" } }, "n.a")).toBe("Authored");
  });

  it("puts the plain title on the card and says when there is none", () => {
    const graph = buildLeanGraph({
      goal: "goal",
      goalLabel: "G",
      linked: new Map([["ns.approx_uniform", "M"], ["ns.raw", "M"]]),
      main: [],
      facts: table(fact("ns.approx_uniform", ["h"]), fact("h", ["ns.raw"]), fact("ns.raw", [])),
      titleOf: (name) => (name === "ns.approx_uniform" ? "Derivative bound" : null),
      origin,
    });
    expect(graph.nodes.get("ns.approx_uniform")).toMatchObject({ label: "Derivative bound", tile: "Derivative bound", tilePlain: true, declaration: "ns.approx_uniform" });
    expect(graph.nodes.get("ns.raw")).toMatchObject({ tile: "raw", tilePlain: false });
    const via = graph.edges.find((e) => e.kind === "lean_via");
    expect(via?.note).toBe("Derivative bound reaches raw through one helper");
  });
});

describe("the part of the graph around a step", () => {
  const build = () =>
    buildLeanGraph({
      goal: "goal",
      goalLabel: "G",
      linked: new Map([["top", "M"], ["mid", "M"], ["low", "M"], ["deep", "M"], ["Def", "M"]]),
      main: ["top"],
      facts: table(fact("top", ["mid", "Def"]), fact("mid", ["low"]), fact("low", ["deep"]), fact("deep", []), { ...fact("Def", []), kind: "structure" }),
      origin,
    });

  it("puts definitions on the shelf, not on the drawing", () => {
    const graph = build();
    expect(graph.nodes.has("Def")).toBe(false);
    expect(graph.shelf.map((d) => d.name)).toEqual(["Def"]);
  });

  it("keeps the step with what uses it and what it uses, joined to the goal", () => {
    const part = neighbourhood(build(), "goal", ["low"]);
    expect([...part.nodes.keys()].sort()).toEqual(["deep", "goal", "low", "mid"]);
    expect(part.out.get("goal")?.map((e) => e.to)).toEqual(["mid"]);
    expect(part.out.get("low")?.map((e) => e.to)).toEqual(["deep"]);
  });

  it("falls back to the goal for a name that is not drawn", () => {
    const part = neighbourhood(build(), "goal", ["Def"]);
    expect(part.nodes.has("top")).toBe(true);
  });
});

describe("the definitions under the drawing", () => {
  it("says which model defines a title that repeats", () => {
    const def = (name: string, module: string) => ({ ...fact(name, []), kind: "def", module });
    const graph = buildLeanGraph({
      goal: "goal",
      goalLabel: "G",
      linked: new Map([["a.IsMin", "OAI.Probability.SKSupport.Model"], ["b.IsMin", "OAI.Probability.SKValue.Model"], ["c", "OAI.Probability.SKValue.Model"]]),
      main: [],
      facts: table(def("a.IsMin", "OAI.Probability.SKSupport.Model"), def("b.IsMin", "OAI.Probability.SKValue.Model"), def("c", "OAI.Probability.SKValue.Model")),
      titleOf: (name) => (name.endsWith("IsMin") ? "γ minimises" : "Other"),
      origin,
    });
    expect(graph.shelf.map((d) => d.model)).toEqual(["support model", "value model", undefined]);
  });
});

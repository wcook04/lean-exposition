import { describe, expect, it } from "vitest";
import { buildLeanGraph, leanUses, linkedDeclarations, namedIn, simplifyUses, tileNames, type LeanFacts } from "../src/model/leanGraph";
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

import { describe, expect, it } from "vitest";
import type { SearchItem } from "../src/api/types";
import { addressProblem, atFits } from "../src/app/address";
import { orderStatements } from "../src/search/corpus";
import { searchLean, searchModules } from "../src/search/leanNames";
import { bestMatches, leanShaped, numberedQuery, opensAs, plainSteps, type StepTitles } from "../src/search/order";
import { canonicalWord, rankRows, spellings } from "../src/search/rank";

const step = (id: string): SearchItem => ({ ref: `x/nodes/${id}`, table: "nodes", label: id });
const statement = (paper: string, excerpt: string, role = "statement"): SearchItem => ({ ref: `s:${paper}:${excerpt}`, table: "statements", label: "Step", excerpt, excerpt_start_character: 0, papers: [paper], role });
const titles: Record<string, string[]> = { main: ["Full support of SK minimisers"], qaoa: ["Weighted finite-tree theorem 1"], lean: ["full_support"] };
const steps: StepTitles = { main: "main", titles: (id) => titles[id] ?? [], idOf: (item) => item.ref.split("/").pop()!, isDeclaration: (id) => id === "lean" };

describe("what comes first", () => {
  it("puts a theorem's own statement before anything that mentions it", () => {
    const wanted = numberedQuery("Theorem 1")!;
    expect(opensAs(statement("short", "**Theorem 1 (full support; ...).** If"), wanted)).toBe(true);
    expect(opensAs(statement("long", "**Theorem 1.1 (other)**"), wanted)).toBe(false);
    expect(opensAs(statement("long", "**Theorem 11**"), wanted)).toBe(false);
    const best = bestMatches({ q: "Theorem 1", steps: [step("qaoa")], statements: [statement("long", "As in Theorem 1"), statement("short", "**Theorem 1 (full support)**")], text: [] }, steps);
    expect(best.map((item) => item.excerpt)).toEqual(["**Theorem 1 (full support)**"]);
  });

  it("puts an exact title first and then the main result", () => {
    const best = bestMatches({ q: "weighted finite-tree theorem 1", steps: [step("qaoa"), step("main")], statements: [], text: [] }, steps);
    expect(best.map((item) => item.label)).toEqual(["qaoa"]);
    expect(bestMatches({ q: "full support of sk minimizers", steps: [step("main")], statements: [], text: [] }, steps).map((item) => item.label)).toEqual(["main"]);
  });

  it("leaves the main result out when its title lacks the words, or the query is a Lean name", () => {
    expect(bestMatches({ q: "gap", steps: [step("main")], statements: [], text: [] }, steps)).toEqual([]);
    expect(bestMatches({ q: "IsMinimizer", steps: [step("main")], statements: [], text: [] }, steps)).toEqual([]);
    expect(bestMatches({ q: "minimizer", steps: [step("main")], statements: [], text: [] }, steps).map((item) => item.label)).toEqual(["main"]);
  });

  it("keeps steps that are bare Lean names after plain ones", () => {
    expect(plainSteps([step("lean"), step("qaoa")], steps).map((item) => item.label)).toEqual(["qaoa", "lean"]);
  });

  it("knows a Lean name by its shape, and plain words as plain", () => {
    for (const q of ["full_support", "IsMinimizer", "SKValue.parisi", "SKFullSupport"]) expect(leanShaped(q)).toBe(true);
    for (const q of ["Parisi", "parisi", "full support", "minimizer", "Theorem 1"]) expect(leanShaped(q)).toBe(false);
  });

  it("orders statements by title, then by role, then by where the word falls", () => {
    const row = (ref: string, label: string, role: string, at: number): SearchItem => ({ ref, table: "statements", label, role, matches: [{ token: "parisi", start_character: at, end_character: at + 6 }] });
    expect(orderStatements([row("a", "Other", "explanation", 0), row("b", "Other", "statement", 200), row("c", "Other", "statement", 3), row("d", "Parisi value", "derivation", 9)], "parisi").map((item) => item.ref)).toEqual(["d", "c", "b", "a"]);
  });
});

describe("British and American spelling", () => {
  it("gives each word its other form", () => {
    expect(spellings("minimizer")).toContain("minimiser");
    expect(spellings("minimiser")).toContain("minimizer");
    expect(spellings("neighbourhood")).toContain("neighborhood");
    expect(spellings("promise")).toEqual(["promise"]);
    expect(canonicalWord("minimizer")).toBe(canonicalWord("minimiser"));
  });

  it("finds either spelling in text and in Lean names", () => {
    const rows = [{ ref: "1", table: "paper", text: "every minimiser here" }];
    expect(rankRows(rows, "minimizer").get("paper")).toHaveLength(1);
    const names = { modules: ["OAI.M", "ComparatorChallenges.SKFullSupport"], names: [["OAI.IsMinimizer", "def", 0, 1, 2]] } as never;
    expect(searchLean(names, "minimiser").map((hit) => hit.short)).toEqual(["IsMinimizer"]);
    expect(searchModules(names, "SKFullSupport")).toEqual([{ module: "ComparatorChallenges.SKFullSupport", file: "SKFullSupport.lean", challenge: true }]);
    expect(searchModules(names, "full support")).toEqual([]);
  });
});

describe("addresses that name nothing", () => {
  const has = (id: string) => id === "real";

  it("says so once, and only for what is missing", () => {
    expect(addressProblem({ view: "map", node: "nope" }, has)).toContain("No step named “nope”");
    expect(addressProblem({ view: "map", node: "real" }, has)).toBeNull();
    expect(addressProblem({ view: "read", stage: "short", node: "nope" }, has)).toContain("This is the paper");
    expect(addressProblem({ view: "read", stage: "short", at: "banana" }, has)).toContain("No place “banana”");
  });

  it("checks a place against the paper it lands in", () => {
    expect(atFits("b10-20", 100, 9)).toBe(true);
    expect(atFits("b10-200", 100, 9)).toBe(false);
    expect(atFits("b20-10", 100, 9)).toBe(false);
    expect(atFits("3-5", 100, 9)).toBe(true);
    expect(atFits("30", 100, 9)).toBe(false);
    expect(addressProblem({ view: "read", stage: "short", at: "30" }, has, { bytes: 100, lines: 9 })).toContain("No place");
  });
});

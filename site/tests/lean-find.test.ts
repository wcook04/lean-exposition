import { describe, expect, it } from "vitest";
import { compareNames, inMainTree, isChallengeCopy, matchName, rankNames } from "../src/lean/find";
import { buildIndex } from "../src/lean/resolve";
import { markedPieces, searchLean } from "../src/search/leanNames";
import { splitUses } from "../src/lean/resolve";
import { tokenize } from "../src/lean/tokenize";

const names = {
  modules: ["OAI.Probability.SKSupport.Model", "OAI.Probability.SKValue.Model", "ComparatorChallenges.SKFullSupport", "OAI.Probability.SKValue.Variation.X"],
  names: [
    ["OAI.ZeroTemperatureSK.parisi_value", "def", 0, 1, 2],
    ["OAI.SKValue.parisi", "def", 1, 1, 2],
    ["OAI.ZeroTemperatureSK.parisi", "def", 0, 3, 4],
    ["OAI.ZeroTemperatureSK.parisi", "def", 2, 3, 4],
    ["OAI.SKValue.ground_state_parisi_target", "theorem", 3, 1, 2],
    ["OAI.ZeroTemperatureSK.IsMinimizer", "def", 0, 5, 6],
    ["OAI.SKValue.IsMinimizer", "def", 1, 5, 6],
    ["OAI.SKValue.notIsMinimizerHere", "lemma", 1, 7, 8],
  ],
} as never;

const index = buildIndex(names);
const rank = (q: string, rests?: (name: string) => boolean) => rankNames(index.rows, index.lower, q, 20, rests).rows.map((row) => `${row.short}@${row.module.split(".").at(-2)}`);

describe("the find box", () => {
  it("tiers exact, tail, prefix, full prefix, substring", () => {
    expect(matchName("a.b.parisi", "parisi", "parisi")).toBe(0);
    expect(matchName("a.sk.parisi", "parisi", "sk.parisi")).toBe(1);
    expect(matchName("a.parisi_value", "parisi_value", "parisi")).toBe(2);
    expect(matchName("a.b.c", "c", "a.b")).toBe(3);
    expect(matchName("a.ground_parisi", "ground_parisi", "parisi")).toBe(4);
    expect(matchName("sk.c", "c", "sk")).toBe(3);
    expect(matchName("a.sk.c", "c", "sk")).toBe(5);
    expect(matchName("a.b", "b", "zzz")).toBeNull();
  });

  it("puts the exact name first, then names that start with it, then names that hold it", () => {
    const order = rankNames(index.rows, index.lower, "parisi", 20).rows.map((row) => row.short);
    expect(order).toEqual(["parisi", "parisi", "parisi", "parisi_value", "ground_state_parisi_target"]);
  });

  it("prefers the proof tree of the main theorem, and a challenge copy last", () => {
    expect(rank("parisi").slice(0, 3)).toEqual(["parisi@SKSupport", "parisi@SKValue", "parisi@ComparatorChallenges"]);
    expect(isChallengeCopy("ComparatorChallenges.SKValue")).toBe(true);
    expect(inMainTree("OAI.Probability.SKValue.Model")).toBe(false);
  });

  it("prefers a declaration the papers rest on within a tier", () => {
    const rows = rankNames(index.rows, index.lower, "ismin", 20, (name) => name === "OAI.SKValue.IsMinimizer").rows;
    expect(rows[0].name).toBe("OAI.SKValue.IsMinimizer");
  });

  it("finds a dotted tail as well as a bare name, and all words of several", () => {
    expect(rank("SKValue.parisi")[0]).toBe("parisi@SKValue");
    expect(rankNames(index.rows, index.lower, "state target", 20).rows.map((row) => row.short)).toEqual(["ground_state_parisi_target"]);
    expect(rankNames(index.rows, index.lower, "  ", 20).total).toBe(0);
  });

  it("prefers the capitals as typed", () => {
    const a = { name: "x.Foo", short: "Foo", module: "m", tier: 0 };
    const b = { name: "x.foo", short: "foo", module: "m", tier: 0 };
    expect(compareNames(a, b, "foo", () => false)).toBeGreaterThan(0);
  });
});

describe("search over Lean names", () => {
  const terms = new Map([
    ["OAI.ZeroTemperatureSK.parisi", { name: "OAI.ZeroTemperatureSK.parisi", module: "m", line: 1, tex: "\\mathcal P(\\gamma)", words: "The Parisi functional." }],
    ["OAI.ZeroTemperatureSK.IsMinimizer", { name: "OAI.ZeroTemperatureSK.IsMinimizer", module: "m", line: 1, tex: null, words: "The coefficient minimises the functional." }],
  ]);

  it("gives the exact declaration first, in any case, with its notation", () => {
    const hits = searchLean(names, "Parisi", { terms });
    expect(hits[0].short).toBe("parisi");
    expect(hits[0].tier).toBe(0);
    expect(hits[0].term?.tex).toBe("\\mathcal P(\\gamma)");
    expect(searchLean(names, "IsMinimizer")[0].name).toBe("OAI.ZeroTemperatureSK.IsMinimizer");
  });

  it("leaves out a challenge copy when the proof tree has the name", () => {
    expect(searchLean(names, "parisi").filter((hit) => hit.name === "OAI.ZeroTemperatureSK.parisi").map((hit) => hit.module)).toEqual(["OAI.Probability.SKSupport.Model"]);
  });

  it("finds a declaration by what the dictionary says of it, after names", () => {
    const hits = searchLean(names, "coefficient minimises", { terms });
    expect(hits.map((hit) => hit.short)).toEqual(["IsMinimizer"]);
    expect(hits[0].marks).toEqual([]);
    expect(searchLean(names, "\\mathcal", { terms }).map((hit) => hit.short)).toEqual(["parisi"]);
  });

  it("marks only the match in a name", () => {
    const hit = searchLean(names, "ground")[0];
    expect(markedPieces(hit.name, hit.marks).filter((piece) => piece.mark).map((piece) => piece.text)).toEqual(["ground"]);
  });
});

describe("uses in the statement and in the proof", () => {
  it("reads which uses the statement names", () => {
    const statement = tokenize("theorem t (W : BrownianSystem Ω) (hmin : IsMinimizer W γ) : FullSupportConclusion W γ := by");
    const split = splitUses(["OAI.BrownianSystem", "OAI.IsMinimizer", "OAI.FullSupportConclusion", "OAI.helper_lemma"], statement);
    expect(split.statement).toEqual(["OAI.BrownianSystem", "OAI.IsMinimizer", "OAI.FullSupportConclusion"]);
    expect(split.proof).toEqual(["OAI.helper_lemma"]);
  });
});

import { describe, expect, it } from "vitest";
import { closestCluster, rankRows, scoreText, tokensOf, wordHits } from "../src/search/rank";
import { markedPieces, searchLean } from "../src/search/leanNames";

const row = (table: string, ref: string, text: string, label?: string) => ({ table, ref, text, label });
const marks = (item: { excerpt?: string; excerpt_start_character?: number; matches?: { start_character: number; end_character: number }[] }) =>
  item.matches!.map((m) => item.excerpt!.slice(m.start_character - item.excerpt_start_character!, m.end_character - item.excerpt_start_character!));

describe("real matches", () => {
  it("finds a short word only as a whole word", () => {
    const text = "atom candidate at the rate at";
    expect(wordHits(text, ["at"]).map((h) => h.start)).toEqual([15, 27]);
  });

  it("finds longer words at word starts, never inside a word", () => {
    expect(wordHits("curvatures and precurvature", ["curvature"]).map((h) => h.start)).toEqual([0]);
  });

  it("treats a number as a whole word, and math delimiters as boundaries", () => {
    expect(wordHits("$2$ then 25 then 1/4 and 21/4", ["2"]).map((h) => h.start)).toEqual([1]);
    expect(wordHits("scale $1/4$ and 21/4", ["1/4"]).map((h) => h.start)).toEqual([7]);
  });

  it("drops a row that has the letters but not the words, and never marks inside a word", () => {
    const by = rankRows([row("passages", "a", "the candidate atom"), row("passages", "b", "mass at zero and an atom")], "at");
    const items = by.get("passages")!;
    expect(items.map((i) => i.ref)).toEqual(["b"]);
    expect(marks(items[0])).toEqual(["at"]);
  });

  it("does not match the keys of a stored record", () => {
    const record = JSON.stringify({ statement: "Nothing here.", kind: "claim" });
    expect(scoreText("nodes", record.toLowerCase(), ["kind"])).toBeNull();
    expect(scoreText("nodes", record.toLowerCase(), ["claim"])).not.toBeNull();
  });

  it("sees a word after an escaped line break in stored JSON", () => {
    expect(wordHits(String.raw`first\nsecond`, ["second"]).length).toBe(1);
  });
});

describe("order of results", () => {
  it("puts words close together and in order above a passage that only mentions them", () => {
    const filler = "lorem ipsum ".repeat(30);
    const by = rankRows(
      [
        row("passages", "mention", `weight appears here. ${filler} A value 2 at last and then ${filler} the point 1/4 is named.`),
        row("passages", "example", `${filler}place weight 2 at 1/4 and weight one at 3/4.`),
      ],
      "weight 2 at 1/4",
    );
    expect(by.get("passages")!.map((i) => i.ref)).toEqual(["example", "mention"]);
    expect(marks(by.get("passages")![0])).toContain("1/4");
  });

  it("lets a number word place the excerpt without counting or marking it", () => {
    const filler = "lorem ipsum ".repeat(40);
    const item = rankRows([row("passages", "a", `$2$ ${filler} weight two at 1/4 ${filler}`)], "weight 2 at 1/4").get("passages")![0];
    expect(item.excerpt).toContain("weight two at 1/4");
    expect(marks(item)).not.toContain("two");
    expect(rankRows([row("passages", "a", "weight two at 1/4")], "weight 2 at 1/4").get("passages")).toBeUndefined();
  });

  it("ranks a match in the title above one in the body", () => {
    const body = JSON.stringify({ label: "Other", statement: "strict curvature appears here" });
    const title = JSON.stringify({ label: "Strict curvature", statement: "nothing" });
    const by = rankRows([row("nodes", "body", body), row("nodes", "title", title)], "strict curvature");
    expect(by.get("nodes")!.map((i) => i.ref)).toEqual(["title", "body"]);
  });

  it("prefers the typed order and keeps the given order on a tie", () => {
    const ordered = closestCluster(wordHits("a b c", ["a", "c"]), 2)!;
    expect(ordered.ordered).toEqual({ start: 0, end: 5, ordered: true });
    expect(closestCluster(wordHits("a b", ["a", "z"]), 2)).toBeNull();
    const by = rankRows([row("passages", "1", "same words"), row("passages", "2", "same words")], "same");
    expect(by.get("passages")!.map((i) => i.ref)).toEqual(["1", "2"]);
  });

  it("folds case and splits on whitespace", () => {
    expect(tokensOf("  Weight  2 ")).toEqual(["weight", "2"]);
  });

  it("offsets stay right past characters outside the basic plane", () => {
    const item = rankRows([row("passages", "a", "𝔼 and 𝟙 at the point")], "point").get("passages")![0];
    expect(item.matches![0].start_character).toBe([..."𝔼 and 𝟙 at the "].length);
  });
});

describe("Lean names", () => {
  const index = {
    modules: ["OAI.Main", "OAI.Other"],
    names: [
      ["OAI.ZeroTemperatureSK.full_support", "theorem", 0, 1, 2],
      ["OAI.ZeroTemperatureSK.minimizer_full_support_actual", "theorem", 0, 3, 4],
      ["OAI.Other.fullSupportHelper", "lemma", 1, 5, 6],
      ["OAI.Other.seatbelt", "def", 1, 7, 8],
    ],
  } as never;

  it("matches at parts of a name: after dots, underscores and capitals", () => {
    expect(searchLean(index, "full support").map((h) => h.short)).toEqual(["full_support", "fullSupportHelper", "minimizer_full_support_actual"]);
  });

  it("does not match inside a part, and a short word must be a whole part", () => {
    expect(searchLean(index, "belt")).toEqual([]);
    expect(searchLean(index, "se")).toEqual([]);
    expect(searchLean(index, "seat").map((h) => h.short)).toEqual(["seatbelt"]);
  });

  it("gives the module for the link and marks only the match", () => {
    const hit = searchLean(index, "minimizer")[0];
    expect(hit.module).toBe("OAI.Main");
    expect(markedPieces(hit.name, hit.marks).filter((p) => p.mark).map((p) => p.text)).toEqual(["minimizer"]);
  });
});

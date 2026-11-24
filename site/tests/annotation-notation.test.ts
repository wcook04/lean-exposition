import { expect, test } from "vitest";
import { unformattedAnnotationTokens } from "../scripts/annotation-notation";

const declarations = new Set(["eval", "support", "tokens"]);

test("finds bare identifiers, binders and symbolic expressions in a note", () => {
  expect(unformattedAnnotationTokens(
    "By A.Infinite, hE gives check_polyTime at x₁ and f(x). Its distance is ≤ 1/2 and it costs 6w.", declarations,
  )).toEqual(["A.Infinite", "hE", "check_polyTime", "₁", "≤", "f(x)", "1/2", "6w"]);
});

test("checks common names only when presented as exact Lean references", () => {
  expect(unformattedAnnotationTokens("The support of f is finite. Use the Lean lemma support.", declarations))
    .toEqual(["support"]);
  expect(unformattedAnnotationTokens("The proof includes a theorem about support and the identifier tokens.", declarations)).toEqual([]);
});

test("finds single-letter quantities in unambiguous mathematical phrases", () => {
  expect(unformattedAnnotationTokens("The weight is divided by c.", declarations)).toEqual(["c"]);
  expect(unformattedAnnotationTokens("The weight is divided by a positive scale.", declarations)).toEqual([]);
  expect(unformattedAnnotationTokens("The weight is divided by $c$.", declarations)).toEqual([]);
});

test("does not treat an unmatched backtick as the start of hidden code", () => {
  expect(unformattedAnnotationTokens("The proof uses `hE.", declarations)).toEqual(["hE", "`"]);
});

test("leaves rendered code, math and ordinary punctuation alone", () => {
  expect(unformattedAnnotationTokens(
    "From `A.Infinite` and `hE`, the estimate is $f(x_1)\u2264 1/2$ a.e., e.g. at $x=0$. Use LaTeX.", declarations,
  )).toEqual([]);
});

import { describe, expect, it } from "vitest";
import { joinBracketedPieces } from "../src/reader/page/PaperBody";

// KaTeX's output for "A = B (0 ≤ t_1 < t_2 < 1)." in outline: one piece after each relation sign.
function display(): HTMLElement {
  const math = document.createElement("span");
  math.className = "katex";
  math.innerHTML =
    '<span class="katex-html">' +
    '<span class="katex-base">A =</span>' +
    '<span class="katex-base">B <span class="mopen">(</span>0 ≤</span>' +
    '<span class="katex-base">t1 &lt;</span>' +
    '<span class="katex-base">t2 &lt; 1<span class="mclose">)</span>.</span>' +
    "</span>";
  return math;
}

describe("a breaking display", () => {
  it("keeps a bracketed condition in one piece and leaves the text unchanged", () => {
    const math = display();
    const before = math.textContent;
    joinBracketedPieces(math);
    const pieces = Array.from(math.querySelectorAll(".katex-base")).map((p) => p.textContent);
    expect(pieces).toEqual(["A =", "B (0 ≤t1 <t2 < 1)."]);
    expect(math.textContent).toBe(before);
  });

  it("runs once per formula", () => {
    const math = display();
    joinBracketedPieces(math);
    joinBracketedPieces(math);
    expect(math.querySelectorAll(".katex-base")).toHaveLength(2);
  });

  it("leaves balanced brackets inside a piece alone", () => {
    const math = document.createElement("span");
    math.innerHTML =
      '<span class="katex-html"><span class="katex-base">f<span class="mopen">(</span>x<span class="mclose">)</span> =</span><span class="katex-base">y</span></span>';
    joinBracketedPieces(math);
    expect(math.querySelectorAll(".katex-base")).toHaveLength(2);
  });
});

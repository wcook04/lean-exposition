// @vitest-environment jsdom
// The shell around a library paper: the credit once under its authors, no "Contents" block in the
// reading copy, and the short credit line built from the instance's own sentences.
import { describe, expect, it } from "vitest";
import { prepareDocument } from "../src/reader/engine";
import { frontCreditLine } from "../src/instances/library/site";

const paths = { long: "long/reasoning-record.md", short: "short/paper.md", expository: "expository/main.md" };

const PAPER = `<header class="front">

# A paper

<ul class="authors">
<li>A. Author</li>
<li>B. Author</li>
</ul>

</header>

## Contents

<!-- passage:sec-contents -->

|  |  |
| --- | --- |
| 1. Introduction | 1 |
| 2. The proof | 4 |
<!-- /passage:sec-contents -->

<a id="1"></a>

## 1 Introduction

Words of the introduction.
`;

function prepare(frontCredit: string | null) {
  const bytes = new TextEncoder().encode(PAPER);
  return prepareDocument({ stage: "short", bytes, documentPath: paths.short, documentPaths: paths, frontCredit });
}

describe("a library paper's front matter", () => {
  it("sets the credit line once, under the authors", () => {
    const doc = prepare("By A and B. Made with AI.");
    expect(doc.creditPart).toBe(0);
    const html = doc.renderAll().map((part) => part.html).join("");
    expect(html.match(/class="front-credit"/g)).toHaveLength(1);
    expect(html.indexOf("front-credit")).toBeGreaterThan(html.indexOf("</ul>"));
    expect(doc.renderPlain(0).html).toContain("front-credit");
  });

  it("has no credit line without one, and says so", () => {
    const doc = prepare(null);
    expect(doc.creditPart).toBeNull();
    expect(doc.renderAll().map((part) => part.html).join("")).not.toContain("front-credit");
  });

  it("leaves out the paper's Contents block and keeps the anchor after it", () => {
    const doc = prepare(null);
    const html = doc.renderAll().map((part) => part.html).join("");
    expect(html).not.toMatch(/<h2[^>]*>Contents/);
    expect(html).not.toContain("The proof | 4");
    expect(html).not.toContain("<table");
    expect(html).toContain('id="1"');
    expect(doc.parts.flatMap((part) => part.headings.map((h) => h.title))).not.toContain("Contents");
    expect(doc.textBlocks().some((block) => block.text.includes("Introduction | 1"))).toBe(false);
  });
});

describe("the short credit line", () => {
  it("does not end a sentence at an author's initial", () => {
    expect(frontCreditLine("Paper by A, B and Matei P. Coiculescu, from c/d at fd3a158. More.", "Made with AI.")).toBe("Paper by A, B and Matei P. Coiculescu, from c/d at fd3a158. Made with AI.");
  });

  it("takes the credit's first sentence and the review, whole", () => {
    const credit = "Paper and Lean by A and B, from their repository a/b at abc1234; their paper thanks Anthropic. The reading copy is set from their TeX.";
    const review = "The links were made with AI and have not been reviewed by the authors. No mathematician has reviewed them.";
    expect(frontCreditLine(credit, review)).toBe(
      "Paper and Lean by A and B, from their repository a/b at abc1234; their paper thanks Anthropic. The links were made with AI and have not been reviewed by the authors. No mathematician has reviewed them.",
    );
  });
});

describe("a section's title in the contents", async () => {
  const { plainTitle } = await import("../src/reader/page/Outline");
  it("says a heading's formula without its TeX", () => {
    expect(plainTitle("5 Blow-up on \\mathbb R^3")).toBe("5 Blow-up on ℝ³");
    expect(plainTitle("4 The equation linearized about u^*")).toBe("4 The equation linearized about u*");
    expect(plainTitle("Appendix A Proofs")).toBe("Appendix A Proofs");
  });
});

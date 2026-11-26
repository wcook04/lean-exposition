// @vitest-environment jsdom
// The shell around a library paper: the credit once under its authors, linked contents in the
// reading copy, and the short credit line built from the instance's own sentences.
import { describe, expect, it } from "vitest";
import { prepareDocument } from "../src/reader/engine";
import { editionCreditLine, frontCreditLine } from "../src/instances/library/site";

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

  it("links the paper's Contents and keeps the anchor after it", () => {
    const doc = prepare(null);
    const html = doc.renderAll().map((part) => part.html).join("");
    expect(html).toMatch(/<h2[^>]*>Contents/);
    expect(html).toMatch(/<table\b[^>]*class="paper-contents"/);
    expect(html).toMatch(/<a href="#introduction"[^>]*>1\. Introduction<\/a>/);
    expect(html).toContain('id="1"');
    expect(doc.anchorIndex.has("contents")).toBe(true);
  });
});

describe("an adapted edition's credit", () => {
  const EDITION = PAPER.replace("## Contents", `<div class="center">

*An adapted edition of the authors’ paper, prepared with AI assistance. Every change is marked.*

</div>

## Contents`);
  it("puts the edition's one short line in place of its long note, and nothing under the authors", () => {
    const bytes = new TextEncoder().encode(EDITION);
    const doc = prepareDocument({ stage: "adapted", bytes, documentPath: paths.short, documentPaths: paths, frontCredit: "An adapted edition; every change is marked.", frontCreditNote: "An adapted edition of" });
    expect(doc.creditPart).toBe(0);
    const html = doc.renderAll().map((part) => part.html).join("");
    expect(html).toContain('<p class="front-credit front-credit--edition">An adapted edition; every change is marked.</p>');
    expect(html).not.toContain("prepared with AI assistance");
    expect(html.match(/class="front-credit/g)).toHaveLength(1);
    expect(html.indexOf("front-credit")).toBeGreaterThan(html.indexOf("</ul>"));
  });
});

describe("the short credit lines", () => {
  it("does not end a sentence at an author's initial", () => {
    expect(frontCreditLine("Paper by A, B and Matei P. Coiculescu, from c/d at fd3a158. More.")).toBe("Paper by A, B and Matei P. Coiculescu, from c/d at fd3a158. Links, titles and notes made with AI.");
  });

  it("keeps the authors, repository and commit, and leaves Anthropic and the review to About", () => {
    const credit = "Paper and Lean by A and B, from their repository a/b at abc1234; their paper thanks Anthropic. The reading copy is set from their TeX.";
    expect(frontCreditLine(credit)).toBe("Paper and Lean by A and B, from their repository a/b at abc1234. Links, titles and notes made with AI.");
  });

  it("says an edition in one line", () => {
    const credit = "An adapted edition of A and B's paper, prepared by Will Cook with AI assistance. The mathematics and the original text are the authors'. Every change is marked.";
    expect(editionCreditLine(credit)).toBe("An adapted edition of A and B's paper, prepared by Will Cook with AI assistance; every change is marked.");
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

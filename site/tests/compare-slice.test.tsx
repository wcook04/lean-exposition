// @vitest-environment jsdom
import { describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot } from "react-dom/client";
import { hasReferenceLink, prepareDocument, renderSlice } from "../src/reader/engine";
import { documentFixture, structureFixture } from "./fixtures";
import type { AlignedStatement, StatementLean } from "../src/api/lean";

const paths = { long: "long/reasoning-record.md", short: "short/paper.md", expository: "expository/main.md" };
const input = { stage: "short", documentPath: paths.short, documentPaths: paths };

function prepared() {
  const structure = structureFixture("short");
  return prepareDocument({
    ...input,
    bytes: documentFixture("short"),
    parts: structure.paper.document_parts.map((p) => ({ kind: p.kind, span: { start_byte: p.span.start_byte, end_byte: p.span.end_byte } })),
  });
}

describe("rendering a slice", () => {
  const text = "As in [OpenAI (2026a), Theorem 1.1][FS], the set $[0,1)$ is the support.";

  it("shows a reference link's words when the paper is not loaded, never its brackets", () => {
    const { html } = renderSlice(text, input);
    expect(html).toContain("OpenAI (2026a), Theorem 1.1");
    expect(html).not.toContain("][FS]");
    expect(html).not.toMatch(/\[OpenAI/);
    expect(html).toContain("katex");
  });

  it("resolves a reference link from the paper's own definitions", () => {
    const doc = prepared();
    const key = Object.keys(doc.references)[0];
    const { html } = renderSlice(`See [the source][${key}].`, { ...input, references: doc.references });
    expect(html).toContain("<a ");
    expect(html).toContain(doc.references[key].href);
    expect(html).not.toContain(`][${key}]`);
  });

  it("drops the brackets of a reference the paper does not define", () => {
    const doc = prepared();
    const { html } = renderSlice("See [the source][no-such-key].", { ...input, references: doc.references });
    expect(html).toContain("See the source.");
  });

  it("leaves mathematics with brackets alone", () => {
    expect(hasReferenceLink("$a[b][c]$ plain")).toBe(true);
    const { html } = renderSlice("Take $\\mathbb E[a][b]$ here.", input);
    expect(html).toContain("katex");
    expect(html).not.toContain("[a][b]$");
  });

  it("typesets as the paper does: run-in leads and display formulas", () => {
    const { html, mathErrors } = renderSlice("**Theorem 1 (full support).** For every $t$,\n$$\nq(t)=t.\n$$", input);
    expect(html).toContain('data-run-in="theorem"');
    expect(html).toContain("math-display");
    expect(mathErrors).toEqual([]);
  });

  it("strips anything the sanitiser strips from a paper", () => {
    expect(renderSlice('Text <script>alert(1)</script><img src=x onerror="y">', input).html).not.toMatch(/script|onerror/);
  });
});

describe("LazyStatementSlice", () => {
  it("shows the raw text dimmed, then the typeset slice", async () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} unobserve() {} disconnect() {} });
    const { LazyStatementSlice } = await import("../src/compare/lazy");
    const statement: AlignedStatement = { paper: "short", role: "statement", markdown: "For every $t$ we have $q(t)=t$.", start_byte: 0, end_byte: 30, anchor: "x", section: "1. Start", heading_id: null };
    const container = document.createElement("div");
    const root = createRoot(container);
    await act(async () => root.render(<LazyStatementSlice statement={statement} />));
    await vi.waitFor(() => expect(container.querySelector(".slice-raw, .slice .katex")).not.toBeNull());
    const raw = container.querySelector(".slice-raw");
    if (raw) expect(raw.textContent).toContain("$q(t)=t$");
    await vi.waitFor(() => expect(container.querySelector(".slice .katex")).not.toBeNull(), { timeout: 8000 });
    expect(container.querySelector(".slice-raw")).toBeNull();
    act(() => root.unmount());
  });

  it("shows only the comparisons made against this slice, with the named declaration and source", async () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} unobserve() {} disconnect() {} });
    const { StatementSlice } = await import("../src/compare/StatementSlice");
    const lean: StatementLean = { name: "Main.riemannHypothesis", module: "Main", line: 4, end_line: 4, relation: "states", note: "",
      fidelity: "same", fidelity_source: "ai", fidelity_note: "Unfold `RiemannHypothesis` to read the conditions." };
    const statement: AlignedStatement = {
      paper: "short", role: "statement", markdown: "The zeros in the statement have real part $1/2$.",
      start_byte: 0, end_byte: 54, anchor: null, section: "2.3", heading_id: null, lean_source: "statement",
      lean: [lean, { ...lean, name: "Main.other", fidelity: undefined }, {
        ...lean, name: "Main.support", fidelity: undefined, source_review: true, note: "This lemma supplies one input.",
      }],
    };
    const container = document.createElement("div");
    const root = createRoot(container);
    await act(async () => root.render(<StatementSlice statement={statement} withComparisons />));
    expect(container.querySelectorAll("[data-fidelity]")).toHaveLength(1);
    expect(container.querySelector("a[title='Main.riemannHypothesis']")?.getAttribute("href")).toContain("riemannHypothesis");
    expect(container.querySelector("[data-fidelity='same'] code")?.textContent).toBe("RiemannHypothesis");
    expect(container.querySelector("[data-source='ai']")?.textContent).toContain("AI agent");
    expect(container.querySelector("[data-source-review='ai']")?.textContent).toContain("This lemma supplies one input.");
    expect(container.querySelector("a[title='Main.other']")).toBeNull();

    await act(async () => root.render(<StatementSlice statement={{ ...statement, lean_source: "record" }} withComparisons />));
    expect(container.querySelector("[data-fidelity]")).toBeNull();
    expect(container.querySelector("[data-source-review]")).toBeNull();
    act(() => root.unmount());
  });
});

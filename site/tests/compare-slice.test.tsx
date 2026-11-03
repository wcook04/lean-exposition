// @vitest-environment jsdom
import { describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot } from "react-dom/client";
import { hasReferenceLink, prepareDocument, renderSlice } from "../src/reader/engine";
import { documentFixture, structureFixture } from "./fixtures";
import type { AlignedStatement } from "../src/api/lean";

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
});

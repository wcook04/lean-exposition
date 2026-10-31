import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it, vi } from "vitest";
import katex from "katex";
import type { Stage } from "../src/api/types";
import { byteOffsetOf, figureKey, prepareDocument, sha256Hex, type PreparedDocument } from "../src/reader/engine";
import { protectMath } from "../src/reader/math";
import { prefixPaths } from "../src/reader/links";
import { documentFixture, structureFixture } from "./fixtures";

const here = path.dirname(fileURLToPath(import.meta.url));
const architectureBytes = new Uint8Array(readFileSync(path.join(here, "../../papers/architecture/paper.md")));

const DOCUMENT_PATHS: Record<Stage, string> = {
  long: "long/reasoning-record.md",
  short: "short/paper.md",
  expository: "expository/main.md",
};
const STAGES: Stage[] = ["long", "short", "expository"];

function prepareStage(stage: Stage): PreparedDocument {
  const structure = structureFixture(stage);
  const passages = new Map(structure.paper.passages.map((p) => [p.ref, p.anchor]));
  return prepareDocument({
    stage,
    bytes: documentFixture(stage),
    parts: structure.paper.document_parts.map((p) => ({
      kind: p.kind,
      span: p.span,
      passageAnchor: p.passage_ref ? passages.get(p.passage_ref) : undefined,
    })),
    documentPath: DOCUMENT_PATHS[stage],
    documentPaths: DOCUMENT_PATHS,
  });
}

function prepareArchitecture(): PreparedDocument {
  return prepareDocument({
    stage: "architecture",
    bytes: architectureBytes,
    documentPath: "architecture/paper.md",
    documentPaths: prefixPaths(DOCUMENT_PATHS, "qaoa-sk/"),
  });
}

const docs: Record<string, PreparedDocument> = {
  long: prepareStage("long"),
  short: prepareStage("short"),
  expository: prepareStage("expository"),
  architecture: prepareArchitecture(),
};

function dom(html: string): HTMLElement {
  const el = document.createElement("div");
  el.innerHTML = html;
  return el;
}

/** Visible text: KaTeX's MathML annotations and fallbacks removed. */
function visibleText(html: string): string {
  const el = dom(html);
  el.querySelectorAll("annotation, .tex-fallback, .katex-mathml").forEach((n) => n.remove());
  return el.textContent ?? "";
}

describe("math", () => {
  it("reuses identical typesetting across parts, separating display math and retaining every error", () => {
    const source = "$x$. $x$. $\\unknowncommand$\n\n";
    const tail = "$x$.\n\n$$x$$\n\n$\\unknowncommand$";
    const split = new TextEncoder().encode(source).length;
    const bytes = new TextEncoder().encode(source + tail);
    const doc = prepareDocument({
      stage: "long", bytes,
      parts: [
        { kind: "unmapped_text", span: { start_byte: 0, end_byte: split } },
        { kind: "unmapped_text", span: { start_byte: split, end_byte: bytes.length } },
      ],
      documentPath: DOCUMENT_PATHS.long, documentPaths: DOCUMENT_PATHS,
    });
    const typeset = vi.spyOn(katex, "renderToString");
    try {
      const first = doc.render(0);
      const second = doc.render(1);
      expect(typeset).toHaveBeenCalledTimes(3);
      expect(dom(first.html).querySelectorAll(".katex")).toHaveLength(2);
      expect(dom(second.html).querySelectorAll(".katex-display")).toHaveLength(1);
      expect(first.mathErrors).toHaveLength(1);
      expect(second.mathErrors).toEqual(first.mathErrors);
      expect(dom(second.html).querySelector(".tex-fallback")?.textContent).toBe("\\unknowncommand");
      expect(doc.render(0)).toBe(first);
      expect(typeset).toHaveBeenCalledTimes(3);
    } finally {
      typeset.mockRestore();
    }
  });

  it("every formula compiles with throwOnError", () => {
    for (const [name, bytes] of [
      ...STAGES.map((s) => [s, documentFixture(s)] as const),
      ["architecture", architectureBytes] as const,
    ]) {
      const { spans } = protectMath(new TextDecoder().decode(bytes));
      const failures: string[] = [];
      for (const s of spans) {
        try {
          katex.renderToString(s.tex, { displayMode: s.display, throwOnError: true, strict: "ignore" });
        } catch (e) {
          failures.push(`${s.tex}: ${(e as Error).message}`);
        }
      }
      expect(failures, name).toEqual([]);
    }
  });

  it("protects math the way Pandoc delimits it", () => {
    const { text, spans } = protectMath("a $x$ b $$\ny\n$$ c \\$5 and $ 1 $ `$q$` $1$2");
    expect(spans.map((s) => s.tex)).toEqual(["x", "y"]);
    expect(text).toContain("\\$5");
    expect(text).toContain("`$q$`");
  });
});

describe("rendering the papers", () => {
  const rendered = Object.fromEntries(Object.entries(docs).map(([k, d]) => [k, d.renderAll()]));

  it("renders every part with zero math errors", () => {
    const counts: Record<string, unknown> = {};
    for (const [name, doc] of Object.entries(docs)) {
      const errs = rendered[name].flatMap((r) => r.mathErrors);
      expect(errs, name).toEqual([]);
      expect(doc.issues, name).toEqual([]);
      counts[name] = {
        parts: doc.parts.length,
        formulas: doc.mathCount,
        anchors: doc.anchorIndex.size,
        headings: doc.parts.reduce((n, p) => n + p.headings.length, 0),
        explicit: doc.parts.reduce((n, p) => n + p.anchors.length, 0) - doc.parts.reduce((n, p) => n + p.headings.reduce((m, h) => m + 1 + h.aliases.length, 0), 0),
      };
    }
    console.log("[reader] per-paper counts", JSON.stringify(counts));
  });

  it("leaves no raw syntax in the output", { timeout: 15000 }, () => {
    for (const [name, parts] of Object.entries(rendered)) {
      for (const part of parts) {
        const text = visibleText(part.html);
        const where = `${name} part ${part.index}`;
        expect(text.includes("$"), where).toBe(false);
        expect(text.includes("\\begin{"), where).toBe(false);
        expect(text.includes("\\caption"), where).toBe(false);
        expect(text.includes("\\label"), where).toBe(false);
        expect(/\\[A-Za-z]+/.test(text), where).toBe(false);
        expect(/\]\[[^\]\s][^\]]*\]/.test(text), where).toBe(false);
        expect(part.html.includes("<!-- passage"), where).toBe(false);
        expect(part.html.includes("<!--"), where).toBe(false);
        expect(part.html.includes("data-pdf-target"), where).toBe(false);
        expect(part.html.includes("pdf-companion"), where).toBe(false);
        expect(/[-]/.test(part.html), where).toBe(false);
        expect(/Axes and dotted guides|upstream\/preprints|usepackage|tikzpicture/.test(text), where).toBe(false);
      }
    }
  });

  it("omits the exposition's print spacing while preserving prose and literal code", () => {
    const source = new TextDecoder().decode(documentFixture("expository"));
    const request = "\\Needspace{9\\baselineskip}";
    expect(source).toContain(request);
    const doc = prepareDocument({
      stage: "expository",
      bytes: new TextEncoder().encode([
        "Before.", request, "After.", `\`${request}\``, `\`\`\`tex\n${request}\n\`\`\``, `    ${request}`,
      ].join("\n\n")),
      documentPath: DOCUMENT_PATHS.expository,
      documentPaths: DOCUMENT_PATHS,
    });
    const el = dom(doc.renderAll().map((p) => p.html).join(""));
    expect([...el.querySelectorAll("p")].filter((p) => !p.querySelector("code")).map((p) => p.textContent)).toEqual(["Before.", "After."]);
    expect([...el.querySelectorAll("code")].map((c) => c.textContent?.trim())).toEqual([request, request, request]);
  });

  it("resolves every in-document and companion fragment", () => {
    const missing: string[] = [];
    const unresolved: string[] = [];
    let fragments = 0;
    let companions = 0;
    for (const [name, parts] of Object.entries(rendered)) {
      for (const part of parts) {
        const el = dom(part.html);
        for (const a of el.querySelectorAll<HTMLAnchorElement>("a[href^='#']")) {
          fragments++;
          const frag = decodeURIComponent(a.getAttribute("href")!.slice(1));
          if (!docs[name].anchorIndex.has(frag)) missing.push(`${name}: #${frag}`);
        }
        for (const a of el.querySelectorAll<HTMLAnchorElement>("a[data-companion]")) {
          companions++;
          const stage = a.dataset.companion!;
          const frag = a.dataset.fragment ?? "";
          expect(a.getAttribute("href")).toBe(`/read/${stage}${frag ? `#${frag}` : ""}`);
          if (frag && !docs[stage].anchorIndex.has(frag)) missing.push(`${name} -> ${stage}#${frag}`);
        }
        for (const s of el.querySelectorAll<HTMLElement>("[data-unresolved-href]")) unresolved.push(`${name}: ${s.dataset.unresolvedHref}`);
      }
    }
    console.log("[reader] links", JSON.stringify({ fragments, companions, unresolved, missing }));
    expect(missing).toEqual([]);
    expect(companions).toBeGreaterThan(0);
    // The architecture paper links to the GitHub-style slug.
    expect(docs.expository.anchorIndex.has("2-what-a-gap-means")).toBe(true);
    expect(docs.expository.anchorIndex.has("what-a-gap-means")).toBe(true);
    const archLinks = rendered.architecture.map((r) => r.html).join("");
    expect(archLinks).toContain('href="/read/expository#2-what-a-gap-means"');
  });

  it("makes whole-document reference definitions available to early parts", () => {
    const opening = docs.expository.parts.find((p) => p.anchor === "opening")!;
    const el = dom(docs.expository.render(opening.index).html);
    const link = [...el.querySelectorAll<HTMLAnchorElement>("a")].find((a) => a.textContent === "OpenAI (2026a)");
    expect(link).toBeDefined();
    expect(link!.getAttribute("href")).toMatch(/^https:\/\/github\.com\/openai\/math\/.*main\.pdf$/);
    expect(link!.getAttribute("rel")).toBe("noopener noreferrer");
    expect(link!.getAttribute("target")).toBe("_blank");
    expect(link!.classList.contains("ext")).toBe(true);
    expect(link!.hasAttribute("data-external")).toBe(true);
  });

  it("keeps $\\nu=\\mu|_K$ inside one table cell", () => {
    const html = rendered.long.map((r) => r.html).join("");
    const el = dom(html);
    const row = [...el.querySelectorAll("tr")].find((tr) => tr.textContent?.includes("Remove"));
    expect(row).toBeDefined();
    expect(row!.querySelectorAll("td").length).toBe(4);
    expect(row!.querySelector("td")!.querySelectorAll(".katex").length).toBeGreaterThanOrEqual(2);
    expect(el.querySelectorAll("table").length).toBe(2);
  });

  it("gives headings Pandoc ids and keeps explicit anchors", () => {
    const ex = docs.expository.parts.flatMap((p) => p.headings);
    expect(ex.find((h) => h.title === "2. What a gap means")?.id).toBe("what-a-gap-means");
    expect(docs.long.parts.flatMap((p) => p.anchors)).toContain("model-and-three-targets");
    const html = rendered.long.map((r) => r.html).join("");
    expect(html).toContain('<a id="model-and-three-targets" class="anchor" aria-hidden="true"></a>');
    expect(html).not.toMatch(/<p>\s*<a [^>]*class="anchor"/);
    for (const doc of Object.values(docs)) {
      for (const [id, index] of doc.anchorIndex) expect(doc.parts[index].anchors).toContain(id);
    }
  });

  it("keeps the TeX characters of heading math in ids, as Pandoc does", () => {
    const doc = prepareDocument({
      stage: "test",
      bytes: new TextEncoder().encode("## 3. The case $\\gamma(0)>0$\n\n## 3. The case $\\gamma(0)>0$\n"),
      documentPath: "x/doc.md",
      documentPaths: DOCUMENT_PATHS,
    });
    expect(doc.parts[0].headings.map((h) => h.id)).toEqual(["the-case-gamma00", "the-case-gamma00-1"]);
    expect(doc.parts[0].headings[0].aliases).toEqual(["3-the-case-gamma00"]);
    expect(doc.render(0).html).toMatch(/<a id="3-the-case-gamma00" class="anchor" aria-hidden="true"><\/a><h2 id="the-case-gamma00" data-line="\d+">3\. The case <span class="katex">/);
  });

  it("marks bold run-in paragraphs", () => {
    const html = rendered.short.map((r) => r.html).join("") + rendered.long.map((r) => r.html).join("");
    const el = dom(html);
    const leads = new Set([...el.querySelectorAll<HTMLElement>("p.run-in")].map((p) => p.dataset.runIn));
    expect(leads.has("theorem")).toBe(true);
    expect(leads.has("proof")).toBe(true);
  });

  it("extracts figures with stable keys and typeset captions", () => {
    for (const name of ["expository", "architecture"]) {
      const figures = docs[name].parts.flatMap((p) => p.figures);
      const sourceBytes = name === "architecture" ? architectureBytes : documentFixture("expository");
      const authoredCount = new TextDecoder().decode(sourceBytes).match(/\\begin\{figure\}/g)?.length ?? 0;
      expect(authoredCount, name).toBeGreaterThan(0);
      expect(figures.length, name).toBe(authoredCount);
      const html = rendered[name].map((r) => r.html).join("");
      const el = dom(html);
      const figs = el.querySelectorAll("figure.paper-figure");
      expect(figs.length).toBe(authoredCount);
      figs.forEach((f, i) => {
        const key = figures[i].key;
        expect(f.getAttribute("data-figure")).toBe(key);
        expect(f.querySelector(`.paper-figure__art[data-figure-slot="${key}"]`)).not.toBeNull();
        const cap = f.querySelector("figcaption")!;
        expect(cap.innerHTML).not.toContain("\\label");
        expect(figures[i].source.startsWith("\\begin{tikzpicture}")).toBe(true);
      });
      console.log(`[reader] ${name} figures`, JSON.stringify(figures.map((f) => ({ key: f.key, caption: f.caption.slice(0, 60) }))));
    }
    const ex = docs.expository.parts.flatMap((p) => p.figures);
    expect(ex[0].key).toBe("fig:support-increments");
    expect(ex[1].key).toMatch(/^fig-[0-9a-f]{10}$/);
    const exHtml = dom(rendered.expository.map((r) => r.html).join(""));
    const caps = exHtml.querySelectorAll("figcaption");
    expect(caps[0].querySelectorAll(".katex").length).toBeGreaterThan(0);
    expect(caps[1].querySelector("a.ext")?.getAttribute("href")).toMatch(/^https:\/\/github\.com\//);
    expect(exHtml.textContent).not.toContain("Modified 2026-10-25");
    // Stability of the KEY rule.
    expect(figureKey("\\begin{figure}  x\n y \\end{figure}")).toBe("fig-" + sha256Hex("\\begin{figure} x y \\end{figure}").slice(0, 10));
    expect(sha256Hex("abc")).toBe("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  });

  it("exposes front matter", () => {
    expect(docs.architecture.frontMatter).toMatchObject({
      title: "One argument, several ways to read it",
      subtitle: "An architectural companion to Lean Exposition",
      date: expect.stringMatching(/^\d{1,2} [A-Z][a-z]+ \d{4}$/),
      "portable-local-links": true,
    });
    expect(docs.expository.frontMatter?.["header-includes"]).toBeDefined();
    expect(visibleText(rendered.expository[0].html)).not.toContain("usepackage");
  });

  it("memoises render", () => {
    expect(docs.short.render(1)).toBe(docs.short.render(1));
  });
});

describe("parts", () => {
  it("tile the document and decode exactly", () => {
    for (const stage of STAGES) {
      const bytes = documentFixture(stage);
      const doc = docs[stage];
      let at = 0;
      let joined = "";
      const dec = new TextDecoder("utf-8", { ignoreBOM: true });
      for (const p of doc.parts) {
        expect(p.span.start).toBe(at);
        at = p.span.end;
        joined += dec.decode(bytes.subarray(p.span.start, p.span.end));
      }
      expect(at).toBe(bytes.length);
      expect(joined).toBe(dec.decode(bytes));
      expect(doc.parts.some((p) => p.blank)).toBe(true);
      for (const p of doc.parts.filter((q) => q.kind === "passage")) expect(p.anchor).toBeTruthy();
    }
  });

  it("byteOffsetOf matches TextEncoder", () => {
    const s = "a–b 𝔼 ü $x$";
    for (let i = 0; i <= s.length; i++) expect(byteOffsetOf(s, i)).toBe(new TextEncoder().encode(s.slice(0, i)).length);
  });
});

describe("sanitisation", () => {
  it("strips scripts, handlers, iframes and unsafe schemes", () => {
    const src = [
      "# Title",
      "",
      "<script>alert(1)</script>",
      "",
      '<img src="x" onerror="alert(2)">',
      "",
      '<iframe src="https://evil.example"></iframe>',
      "",
      "[bad](javascript:alert(3)) and <a href=\"javascript:alert(4)\">raw</a> and [d](data:text/html,hi)",
      "",
      '<p onclick="alert(5)" style="color:red">x</p>',
      "",
      "[rel](../secret/file.md) [ok](https://example.org)",
      "",
      "<form><input></form> <span style=\"position:fixed\">s</span>",
      "",
      "| a | b |",
      "|--:|---|",
      "| 1 | 2 |",
    ].join("\n");
    const doc = prepareDocument({
      stage: "test",
      bytes: new TextEncoder().encode(src),
      documentPath: "x/doc.md",
      documentPaths: DOCUMENT_PATHS,
    });
    const html = doc.render(0).html;
    expect(html).not.toMatch(/<script|<img|<iframe|<form|<input|onerror|onclick|alert\(1\)|alert\(4\)/i);
    const el = dom(html);
    for (const node of el.querySelectorAll("*")) {
      for (const attr of node.getAttributeNames()) expect(attr.startsWith("on"), attr).toBe(false);
    }
    for (const a of el.querySelectorAll("a[href]")) expect(a.getAttribute("href")).toMatch(/^(#|\/read\/|https?:)/);
    // Markdown links with unsafe schemes are not links at all (markdown-it validateLink).
    expect(el.querySelectorAll("a").length).toBe(2);
    expect(html).not.toContain("position:fixed");
    expect(html).not.toContain("color:red");
    expect(html).toContain('style="text-align:right"');
    expect(html).toContain('data-unresolved-href="../secret/file.md"');
    expect(html).not.toMatch(/\shref="\.\.\/secret/);
    expect(html).toContain('href="https://example.org"');
  });
});

describe("performance", () => {
  it("logs renderAll time for the long record", () => {
    const t0 = performance.now();
    const doc = prepareStage("long");
    const t1 = performance.now();
    doc.renderAll();
    const t2 = performance.now();
    console.log(`[reader] long record: prepare ${(t1 - t0).toFixed(0)} ms, renderAll ${(t2 - t1).toFixed(0)} ms`);
  });
});

describe("source lines", () => {
  const source = "---\ntitle: x\n---\n\n<!-- passage:one -->\n# Heading\n\nFirst paragraph\nruns on.\n\n$$\na + b\n$$\n\n- item one\n- item two\n\nLast paragraph.\n";
  const bytes = new TextEncoder().encode(source);
  const doc = prepareDocument({ stage: "short", bytes, documentPath: "short/paper.md", documentPaths: {} });
  const html = doc.render(0).html;
  const lineOf = (text: string) => source.split("\n").findIndex((l) => l.includes(text)) + 1;

  it("stamps each block with its line in the document, across dropped comments and folded formulas", () => {
    expect(html).toContain(`<h1 id="heading" data-line="${lineOf("# Heading")}"`);
    expect(html).toContain(`<p data-line="${lineOf("First paragraph")}">`);
    expect(html).toContain(`<div class="math-display" data-line="${lineOf("a + b")}">`);
    expect(html).toContain(`<li data-line="${lineOf("item two")}">`);
    expect(html).toContain(`<p data-line="${lineOf("Last paragraph")}">`);
  });

  it("resolves bytes to lines", () => {
    expect(doc.lineOfByte(source.indexOf("Last paragraph"))).toBe(lineOf("Last paragraph"));
    expect(doc.parts[0].lines.start).toBe(1);
  });
});

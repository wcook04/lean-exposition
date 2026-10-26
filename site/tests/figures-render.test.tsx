// Inspection for the redrawn paper figures: server-render each component,
// check its labels and accessibility, check registry matching against the
// real captions, and (with FIGURE_PREVIEW_DIR set) write standalone preview
// pages in both schemes at the reading-column and phone widths.
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import type { ComponentType } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import { AccountsFigure } from "../src/figures/AccountsFigure";
import { AreaFigure, AreaModelView, modelMean, PAPER_MODEL } from "../src/figures/AreaFigure";
import { GapFigure } from "../src/figures/GapFigure";
import { GapIngredientsFigure } from "../src/figures/GapIngredientsFigure";
import { ReadingJourneyFigure } from "../src/figures/ReadingJourneyFigure";
import { figureForKey } from "../src/figures/registry";

const site = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const repo = path.resolve(site, "..");

const FIGURES: { name: string; Component: ComponentType; math: number }[] = [
  { name: "gap", Component: GapFigure, math: 15 },
  { name: "area", Component: () => <AreaFigure explorable={false} />, math: 9 },
  { name: "accounts", Component: AccountsFigure, math: 0 },
  { name: "ingredients", Component: GapIngredientsFigure, math: 9 },
  { name: "journey", Component: ReadingJourneyFigure, math: 0 },
];

const EXPLORE_STATES = [
  { name: "explore-paper", model: PAPER_MODEL },
  { name: "explore-affine", model: { a: 1, b: 1, k: 0 } },
  { name: "explore-unequal", model: { a: 0.6, b: 0.9, k: 0.4 } },
];

/** The paper's figure captions, read from the exact Markdown. */
function captions(file: string): { label: string | null; caption: string }[] {
  const text = readFileSync(path.join(repo, file), "utf8");
  const out: { label: string | null; caption: string }[] = [];
  const re = /\\caption\{([\s\S]*?)\}\s*\n\s*(?:\\label\{([^}]*)\}|\\end\{figure\})/g;
  for (let m = re.exec(text); m; m = re.exec(text)) out.push({ caption: m[1], label: m[2] ?? null });
  return out;
}

describe("redrawn paper figures", () => {
  for (const { name, Component, math } of FIGURES) {
    it(`${name}: renders its KaTeX labels and an accessible image`, () => {
      const html = renderToStaticMarkup(<Component />);
      expect(html).not.toContain("katex-error");
      expect(html.match(/class="katex"/g)?.length ?? 0).toBe(math);
      const label = /role="img" aria-label="([^"]+)"/.exec(html);
      expect(label, "role img with aria-label").not.toBeNull();
      expect(label![1].trim().length).toBeGreaterThan(40);
      expect(html).not.toMatch(/#[0-9a-f]{3,6}\b/i);
    });
  }

  it("area: the default view is the paper's picture and offers Explore", () => {
    const html = renderToStaticMarkup(<AreaFigure />);
    expect(html).toContain("Change the values in this picture");
    expect(html).toContain('aria-expanded="false"');
    expect(html).toContain("endpoint chord");
  });

  it("area model: the paper's model has mean 5/6, the affine case loses nothing", () => {
    expect(modelMean(PAPER_MODEL)).toBeCloseTo(5 / 6, 12);
    expect(modelMean({ a: 1, b: 1, k: 0 })).toBe(1);
    for (const { model } of EXPLORE_STATES) {
      const html = renderToStaticMarkup(<AreaModelView model={model} />);
      expect(html).not.toContain("katex-error");
    }
  });

  it("area: Explore opens labelled range inputs and reports the shortfall", async () => {
    const { createRoot } = await import("react-dom/client");
    const { act } = await import("react");
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    const host = document.createElement("div");
    document.body.append(host);
    const root = createRoot(host);
    await act(async () => root.render(<AreaFigure />));
    const toggle = host.querySelector("button")!;
    await act(async () => toggle.click());
    expect(toggle.getAttribute("aria-expanded")).toBe("true");
    const inputs = [...host.querySelectorAll<HTMLInputElement>('input[type="range"]')];
    expect(inputs).toHaveLength(3);
    for (const input of inputs) expect(host.querySelector(`label[for="${input.id}"]`)).not.toBeNull();
    expect(host.textContent).toContain("a calculus model, not an SK moment curve");
    expect(host.textContent).toContain("shortfall is 0.167");
    await act(async () => root.unmount());
    host.remove();
  });

  it("journey: distinguishes two expansions, two direct maps and the citation chain", () => {
    const el = document.createElement("div");
    el.innerHTML = renderToStaticMarkup(<ReadingJourneyFigure />);
    const relations = (kind: string) => [...el.querySelectorAll<HTMLElement>(`[data-relation="${kind}"]`)]
      .map((edge) => [edge.dataset.from, edge.dataset.to]);
    expect(relations("expands")).toEqual([
      ["long:curvature", "short:curvature"],
      ["long:fixed-time-coercivity", "short:curvature"],
    ]);
    expect(relations("maps")).toEqual([
      ["short:curvature", "support.positive_curvature"],
      ["long:fixed-time-coercivity", "support.positive_curvature"],
    ]);
    expect(relations("citation_ids")).toEqual([["support.positive_curvature", "support_curvature_source"]]);
    expect(relations("source_id")).toEqual([["support_curvature_source", "support_tex_curvature"]]);
    expect(el.querySelectorAll(".arch-flow--up.arch-flow--dashed")).toHaveLength(2);
    expect(el.querySelectorAll(".arch-flow--dotted")).toHaveLength(2);
  });

  it("registry: matches every real figure and stable architecture label, and rejects others", () => {
    const qaoa = captions("papers/qaoa-sk/expository/main.md");
    const arch = captions("papers/architecture/paper.md");
    expect(qaoa).toHaveLength(2);
    expect(arch.length).toBeGreaterThanOrEqual(2);
    const [gap, area] = qaoa;
    expect(gap.label).toBe("fig:support-increments");
    expect(figureForKey(gap.label!, gap.caption)).toBe(GapFigure);
    expect(figureForKey("fig-0123456789", gap.caption)).toBe(GapFigure);
    expect(figureForKey("fig-0123456789", area.caption)).toBe(AreaFigure);
    expect(figureForKey("fig-abcdef0123", arch[0].caption)).toBe(AccountsFigure);
    expect(figureForKey("fig-abcdef0123", arch[1].caption)).toBe(GapIngredientsFigure);
    for (const figure of [...qaoa, ...arch]) {
      expect(figureForKey(figure.label ?? "fig-abcdef0123", figure.caption), figure.caption).not.toBeNull();
    }
    expect(figureForKey("fig:shared-claim", "")).toBe(AccountsFigure);
    expect(figureForKey("fig:joint-inputs", "")).toBe(GapIngredientsFigure);
    expect(figureForKey("fig:excursion-return", "")).toBe(ReadingJourneyFigure);
    expect(figureForKey("fig-ffffffffff", "A table of unrelated values.")).toBeNull();
    expect(figureForKey("fig:unknown", "")).toBeNull();
  });
});

// ---- Preview gallery -------------------------------------------------------

const previewDir = process.env.FIGURE_PREVIEW_DIR;

function dataUrl(file: string): string {
  const ext = path.extname(file).slice(1);
  return `url(data:font/${ext};base64,${readFileSync(file).toString("base64")}) format("${ext}")`;
}

function previewCss(): string {
  const nm = path.join(site, "node_modules");
  const katexDir = path.join(nm, "katex/dist");
  const katexCss = readFileSync(path.join(katexDir, "katex.min.css"), "utf8")
    .replace(/,url\(fonts\/[^)]+\.(?:woff|ttf)\) format\("[^"]+"\)/g, "")
    .replace(/url\((fonts\/[^)]+\.woff2)\) format\("woff2"\)/g, (_: string, f: string) => dataUrl(path.join(katexDir, f)));
  const stix = path.join(nm, "@fontsource/stix-two-text/files");
  const sans = path.join(nm, "@fontsource-variable/source-sans-3/files");
  const faces = [
    ["STIX Two Text", "normal", "400", path.join(stix, "stix-two-text-latin-400-normal.woff2")],
    ["STIX Two Text", "italic", "400", path.join(stix, "stix-two-text-latin-400-italic.woff2")],
    ["STIX Two Text", "normal", "600", path.join(stix, "stix-two-text-latin-600-normal.woff2")],
    ["Source Sans 3 Variable", "normal", "200 900", path.join(sans, "source-sans-3-latin-wght-normal.woff2")],
  ]
    .map(([family, style, weight, file]) => `@font-face{font-family:"${family}";font-style:${style};font-weight:${weight};src:${dataUrl(file)}}`)
    .join("\n");
  const own = ["src/styles/tokens.css", "src/styles/base.css", "src/figures/figures.css"]
    .map((f) => readFileSync(path.join(site, f), "utf8"))
    .join("\n");
  return `${faces}\n${katexCss}\n${own}\nbody{height:auto;padding:24px 16px}.frame{width:var(--w)}`;
}

describe.runIf(previewDir)("preview gallery", () => {
  it("writes one page per figure, scheme and width", () => {
    const dir = path.resolve(previewDir!);
    mkdirSync(dir, { recursive: true });
    const css = previewCss();
    const items: [string, string][] = [
      ...FIGURES.map(({ name, Component }) => [name, renderToStaticMarkup(<Component />)] as [string, string]),
      ["area-with-toggle", renderToStaticMarkup(<AreaFigure />)],
      ["area-explore-open", renderToStaticMarkup(<AreaFigure initialOpen />)],
      ...EXPLORE_STATES.map(({ name, model }) => [name, renderToStaticMarkup(<AreaModelView model={model} />)] as [string, string]),
    ];
    for (const theme of ["light", "dark"])
      for (const width of [640, 340])
        for (const [name, html] of items) {
          const page = `<!doctype html><html lang="en" data-theme="${theme}"><head><meta charset="utf-8"><title>${name}</title><style>${css}</style></head><body><div class="frame" style="--w:${width}px">${html}</div></body></html>`;
          writeFileSync(path.join(dir, `${name}-${theme}-${width}.html`), page);
        }
  });
});

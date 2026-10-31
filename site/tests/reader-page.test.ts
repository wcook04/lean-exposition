import { afterEach, describe, expect, it, vi } from "vitest";
import type { PaperStructure, Stage } from "../src/api/types";
import { prepareDocument, type PreparedDocument } from "../src/reader/engine";
import { sanitizeHtml } from "../src/reader/sanitize";
import {
  authoredRoutes,
  chainOf,
  companionAnchor,
  estimateHeight,
  firstPassageFor,
  idleOrder,
  outlineOf,
  parsePassageRef,
  passagesBetween,
  placeName,
  recordTally,
  relationWord,
  resolveAnchor,
  resolveBeside,
  sameTopic,
  sectionNumber,
  sectionTitleIn,
  selectionSpan,
  statusWords,
  withoutIds,
  type Structures,
} from "../src/reader/page/model";
import { documentFixture, graphFixture, structureFixture } from "./fixtures";

const PATHS: Record<Stage, string> = {
  long: "long/reasoning-record.md",
  short: "short/paper.md",
  expository: "expository/main.md",
};

const structures: Structures = {
  expository: structureFixture("expository"),
  short: structureFixture("short"),
  long: structureFixture("long"),
};

afterEach(() => vi.unstubAllEnvs());

const docs = new Map<Stage, PreparedDocument>();
function doc(stage: Stage): PreparedDocument {
  let d = docs.get(stage);
  if (!d) {
    const structure = structures[stage] as PaperStructure;
    const anchors = new Map(structure.paper.passages.map((p) => [p.ref, p.anchor]));
    d = prepareDocument({
      stage,
      bytes: documentFixture(stage),
      parts: structure.paper.document_parts.map((p) => ({
        kind: p.kind,
        span: p.span,
        passageAnchor: p.passage_ref ? anchors.get(p.passage_ref) : undefined,
      })),
      documentPath: PATHS[stage],
      documentPaths: PATHS,
    });
    docs.set(stage, d);
  }
  return d;
}

describe("passage references", () => {
  it("reads the account and anchor from a passage ref", () => {
    const ref = structures.long!.paper.passages[0].ref;
    expect(parsePassageRef(ref)).toEqual({ stage: "long", anchor: structures.long!.paper.passages[0].anchor });
    expect(parsePassageRef("sha256:x/nodes/support.regularity")).toBeNull();
  });
});

describe("naming places", () => {
  it("names a passage by the heading a reader lands on, with the account when it is another", () => {
    const title = sectionTitleIn(structures.long, "curvature");
    expect(title).toMatch(/^4\.1 /);
    expect(placeName(structures, "expository", "long", "curvature")).toBe(`Long record, §4.1 ${title!.replace(/^4\.1 /, "")}`);
    expect(placeName(structures, "long", "long", "curvature")).toMatch(/^§4\.1 /);
  });

  it("never names a passage by the document title", () => {
    for (const stage of ["long", "short", "expository"] as Stage[]) {
      const h1 = structures[stage]!.paper.sections.find((s) => s.level === 1)!.title;
      for (const p of structures[stage]!.paper.passages) expect(sectionTitleIn(structures[stage], p.anchor)).not.toBe(h1);
    }
  });

  it("puts the edition status in words", () => {
    expect(statusWords("draft", "needs_revision")).toBe("Draft. Review recorded as needing revision.");
    expect(statusWords(undefined, undefined)).toBe("");
  });

  it("tallies a passage's records by kind for its control", () => {
    const graph = graphFixture();
    const claim = [...graph.nodes.values()].find((n) => n.kind === "claim")!.id;
    const assumption = [...graph.nodes.values()].find((n) => n.kind === "assumption")!.id;
    expect(recordTally([claim], graph)).toBe("1 claim");
    expect(recordTally([claim, claim, assumption, assumption], graph)).toBe("2 claims and 2 assumptions");
    expect(recordTally([assumption], graph)).toBe("1 assumption");
  });
});

describe("routes between accounts", () => {
  it("collects incoming and outgoing authored links from every account's mapping", () => {
    const routes = authoredRoutes(structures, "expository", "curvature-transfer");
    // The long record's curvature and fixed-time-coercivity passages expand it.
    expect(routes.filter((r) => r.relation === "incoming" && r.kind === "expands").map((r) => `${r.stage}:${r.anchor}`).sort()).toEqual([
      "long:curvature",
      "long:fixed-time-coercivity",
    ]);
    const outgoing = authoredRoutes(structures, "long", "curvature").filter((r) => r.relation === "outgoing");
    expect(outgoing.map((r) => `${r.stage}:${r.anchor}`)).toContain("expository:curvature-transfer");
    expect(routes.every((r) => r.rationale.length > 0)).toBe(true);
  });

  it("words each relation from the reader's side, in its recorded direction", () => {
    // `expands` is stored from the fuller treatment to the shorter one.
    expect(relationWord({ kind: "expands", relation: "incoming" })).toBe("Expanded by");
    expect(relationWord({ kind: "expands", relation: "outgoing" })).toBe("Expands");
    expect(relationWord({ kind: "illustrates", relation: "outgoing" })).toBe("Illustrates");
    expect(relationWord({ kind: "illustrates", relation: "incoming" })).toBe("Illustrated by");
    expect(relationWord({ kind: "answers", relation: "incoming" })).toBe("Answered by");
    const example = authoredRoutes(structures, "expository", "zero-candidate")[0];
    expect(relationWord(example)).toBe("Illustrates");
  });
});

describe("same topic in…", () => {
  const here = { stage: "short" as Stage, anchor: "density-consequence" };

  it("offers the long record's fuller treatments of short §4, not its overview", () => {
    const groups = sameTopic(structures, here);
    const long = groups.find((g) => g.stage === "long")!;
    expect(long.authored.map((d) => `${d.relation}:${d.anchor}`).sort()).toEqual(["Expanded by:density", "Expanded by:fixed-time-coercivity"]);
    expect(long.authored.every((d) => d.rationale.length > 0)).toBe(true);
    // Positivity is found through the claim both passages map, and the claim is named.
    const viaDensity = long.shared.find((s) => s.places.some((p) => p.anchor === "density-positive"))!;
    expect(viaDensity.record).toBe("scalar.smooth_positive_density");
    // The overview maps the same claim, but a more specific passage comes first and no authored link names it.
    const anchors = long.shared.flatMap((s) => s.places.map((p) => p.anchor));
    expect(anchors.indexOf("density-positive")).toBeLessThan(anchors.indexOf("overview"));
    expect(long.authored.some((d) => d.anchor === "overview")).toBe(false);
    // The exposition is expanded by this passage: the direction is kept.
    const expo = groups.find((g) => g.stage === "expository")!;
    expect(expo.authored.map((d) => `${d.relation}:${d.anchor}`)).toEqual(["Expands:density-and-approximation"]);
    // An authored destination is not repeated as a shared one.
    expect(expo.shared.flatMap((s) => s.places).some((p) => p.anchor === "density-and-approximation")).toBe(false);
  });

  it("names the record that produced each shared match", () => {
    for (const g of sameTopic(structures, here)) {
      for (const s of g.shared) {
        for (const p of s.places) expect(structures[p.stage]!.paper.passages.find((x) => x.anchor === p.anchor)!.claim_ids).toContain(s.record);
      }
    }
  });

  it("keeps a genuine no-match", () => {
    const groups = sameTopic(structures, { stage: "long", anchor: "qaoa-depth-one" });
    const expo = groups.find((g) => g.stage === "expository")!;
    expect(expo.ready).toBe(true);
    expect(expo.authored).toEqual([]);
    expect(expo.shared).toEqual([]);
  });

  it("says when an account's structure has not arrived", () => {
    const groups = sameTopic({ short: structures.short }, here);
    expect(groups.find((g) => g.stage === "long")).toMatchObject({ ready: false, authored: [], shared: [] });
  });

  it("lists authored links inside the same account after the other accounts", () => {
    const synthetic: Structures = {
      expository: {
        ...structures.expository!,
        reading_links: [{ from_anchor: "b", to_stage: "expository", to_anchor: "a", kind: "answers", rationale: "Answers it.", from_text_sha256: "", to_text_sha256: "" }],
      },
    };
    const groups = sameTopic(synthetic, { stage: "expository", anchor: "a" });
    expect(groups[groups.length - 1]).toMatchObject({ stage: "expository", authored: [{ anchor: "b", relation: "Answered by", rationale: "Answers it." }] });
    expect(sameTopic(synthetic, { stage: "expository", anchor: "b" }).at(-1)!.authored[0]).toMatchObject({ anchor: "a", relation: "Answers" });
  });
});

describe("anchors", () => {
  it("resolves a heading id first and a passage anchor second", () => {
    const short = doc("short");
    // The short paper has both a passage "contact" and an explicit <a id="contact">.
    const hit = resolveAnchor(short, "contact")!;
    expect(hit.id).toBe("contact");
    const passage = resolveAnchor(doc("expository"), "contact-and-gap")!;
    expect(passage.id).toBeUndefined();
    const plain = structures.short!.paper.passages.map((p) => p.anchor).find((a) => !short.anchorIndex.has(a))!;
    expect(short.parts[resolveAnchor(short, plain)!.part].anchor).toBe(plain);
    expect(resolveAnchor(short, "no-such-place")).toBeNull();
  });

  it("opens a fragment beside as the passage holding it, keeping the fragment to scroll to", () => {
    const long = doc("long");
    const hit = resolveBeside(long, structures.long!, "curvature-algebra")!;
    expect(hit.passage).toBe(long.parts[hit.part].anchor);
    expect(hit.fragment).toBe("curvature-algebra");
    expect(resolveBeside(long, structures.long!, "curvature")).toMatchObject({ passage: "curvature" });
  });

  it("opens the near-ground section's substantive passage from its preceding bookmark", () => {
    const long = doc("long");
    const hit = resolveBeside(long, structures.long!, "near-ground-overlaps")!;
    expect(hit.passage).toBe("overlap-pairs");
    expect(sectionTitleIn(structures.long!, hit.passage!)).toBe("9.3 Near-ground configurations at a prescribed overlap");
    // This is the same prepared part and copy transformation the Visit pane renders.
    const body = document.createElement("div");
    body.innerHTML = withoutIds(long.render(hit.part).html);
    const text = body.textContent!.replace(/\s+/g, " ");
    expect(text).toContain("Choose one minimizer supplied by the attained Parisi formula");
    expect(text).toContain("The pointwise result also gives a simultaneous statement");
    expect(text).toContain("neither exact arbitrary real overlaps at finite");
    expect(text).not.toContain("The scalar Gaussian construction is not itself an algorithm");
    expect(body.querySelectorAll("p").length).toBeGreaterThan(1);
    expect(body.querySelectorAll(".katex-display").length).toBeGreaterThan(1);
    expect(resolveBeside(long, structures.long!, "exact-finite-maximizers")).toMatchObject({
      passage: "overlap-pairs", fragment: "exact-finite-maximizers",
    });
  });

  it("associates only a directly preceding bookmark with a heading without duplicating its ID", () => {
    for (const between of ["", "This bookmark names prose before the section.\n\n"]) {
      const prepared = prepareDocument({
        stage: "long", bytes: new TextEncoder().encode(`<a id="bookmark"></a>\n\n${between}## Section\n\nSection body.\n`),
        documentPath: PATHS.long, documentPaths: PATHS,
      });
      expect(prepared.parts[0].headings[0].aliases.includes("bookmark")).toBe(between === "");
      const body = document.createElement("div");
      body.innerHTML = prepared.render(0).html;
      expect(body.querySelectorAll('[id="bookmark"]').length).toBe(1);
    }
  });

  it("opens companion links without fragments at a real passage in every account", () => {
    for (const stage of ["long", "short", "expository"] as Stage[]) {
      const anchor = companionAnchor(structures[stage], "");
      expect(resolveBeside(doc(stage), structures[stage]!, anchor)).toMatchObject({ passage: anchor });
      expect(companionAnchor(structures[stage], undefined)).toBe(anchor);
    }
  });

  it("retains explicit companion fragments, including missing ones", () => {
    const anchor = companionAnchor(structures.long, "curvature-algebra");
    expect(resolveBeside(doc("long"), structures.long!, anchor)).toMatchObject({ fragment: "curvature-algebra" });
    const missing = companionAnchor(structures.long, "no-such-place");
    expect(missing).toBe("no-such-place");
    expect(resolveBeside(doc("long"), structures.long!, missing)).toBeNull();
  });

  it("finds the first passage in another account discussing a claim", () => {
    const claim = structures.expository!.paper.passages.find((p) => p.anchor === "curvature-transfer")!.claim_ids[0];
    const anchor = firstPassageFor(structures.long, [claim]);
    expect(structures.long!.paper.passages.find((p) => p.anchor === anchor)!.claim_ids).toContain(claim);
    expect(firstPassageFor(structures.long, [])).toBeNull();
  });
});

describe("native links under a deployment prefix", () => {
  it.each(["/", "/lean-exposition-site/"])("keeps companion and copied fragment hrefs usable under %s", (base) => {
    vi.stubEnv("BASE_URL", base);
    const prepared = prepareDocument({
      stage: "expository",
      bytes: new TextEncoder().encode("[§9.3 Near-ground configurations](../long/reasoning-record.md#near-ground-overlaps)"),
      documentPath: PATHS.expository, documentPaths: PATHS,
    });
    const body = document.createElement("div");
    body.innerHTML = prepared.render(0).html;
    const companion = body.querySelector<HTMLAnchorElement>("a[data-companion]")!;
    const expected = `${base}read/long#near-ground-overlaps`;
    expect(companion.getAttribute("href")).toBe(expected);
    expect(new URL(companion.getAttribute("href")!, "https://example.org").pathname).toBe(`${base}read/long`);
    expect(companion.dataset.fragment).toBe("near-ground-overlaps");
    body.innerHTML = withoutIds('<a href="#near-ground-overlaps" data-in="long">§9.3</a>');
    expect(body.querySelector("a")!.getAttribute("href")).toBe(expected);
    expect(body.querySelector("a")!.getAttribute("data-fragment")).toBe("near-ground-overlaps");
    body.innerHTML = sanitizeHtml([
      `<a href="${expected}">reader</a>`, '<a href="/elsewhere/read/long">outside</a>',
      '<a href="javascript:alert(1)">unsafe</a>', '<a href="https://example.org">external</a>',
      '<a href="#near-ground-overlaps">fragment</a>',
    ].join(""));
    expect([...body.querySelectorAll("a[href]")].map((a) => a.getAttribute("href"))).toEqual([
      expected, "https://example.org", "#near-ground-overlaps",
    ]);
  });
});

describe("outline", () => {
  it("lists sections of levels 2 to 4 without the subtitle", () => {
    const outline = outlineOf(doc("expository"));
    expect(outline[0].title).toBe("1. The finite optimisation problem");
    expect(outline.every((e) => e.level >= 2 && e.level <= 4)).toBe(true);
    expect(outline.some((e) => e.title.startsWith("A variational argument"))).toBe(false);
    expect(outlineOf(doc("long")).some((e) => e.title === "A long reasoning record")).toBe(false);
  });

  it("reaches long §8.1.1 and names its parents as a document breadcrumb", () => {
    const outline = outlineOf(doc("long"));
    const deep = outline.find((e) => e.level === 4 && /^8\.1\.1\b/.test(e.title))!;
    expect(deep).toBeTruthy();
    expect(chainOf(outline, deep.id).map((e) => sectionNumber(e.title))).toEqual(["§8", "§8.1", "§8.1.1"]);
    expect(chainOf(outline, null)).toEqual([]);
  });
});

describe("rendering helpers", () => {
  it("estimates a placeholder height that grows with the part", () => {
    const parts = doc("long").parts.filter((p) => !p.blank);
    const sorted = [...parts].sort((a, b) => a.span.end - a.span.start - (b.span.end - b.span.start));
    expect(estimateHeight(sorted[sorted.length - 1])).toBeGreaterThan(estimateHeight(sorted[0]));
    expect(estimateHeight({ ...sorted[0], blank: true })).toBe(0);
  });

  it("orders idle rendering nearest the reader first and covers every part once", () => {
    const order = idleOrder(10, 4);
    expect(order.slice(0, 3)).toEqual([4, 5, 3]);
    expect([...order].sort((a, b) => a - b)).toEqual([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  });

  it("takes the byte span of the whole parts a selection touches", () => {
    const parts = doc("expository").parts;
    expect(selectionSpan(parts, 7, 5)).toEqual({ start: parts[5].span.start, end: parts[7].span.end });
  });

  it("counts the mapped passages a selection touches", () => {
    const parts = doc("short").parts;
    const i = parts.findIndex((p) => p.kind === "passage");
    expect(passagesBetween(parts, i, i)).toBe(1);
    expect(passagesBetween(parts, 0, parts.length - 1)).toBe(parts.filter((p) => p.kind === "passage").length);
  });

  it("makes a copy's own fragment links open the reader in their account", () => {
    const long = doc("long");
    const index = long.parts.findIndex((p) => /href="#/.test(long.render(p.index).html));
    const primary = long.render(index).html;
    expect(primary).toMatch(/<a href="#[^"]+" data-in="long"/);
    const copy = withoutIds(primary);
    expect(copy).not.toMatch(/href="#/);
    expect(copy).toMatch(/href="\/read\/long#[^"]+" data-fragment="[^"]+"/);
  });

  it("strips fragment ids from a second copy of a part", () => {
    const long = doc("long");
    const hit = resolveBeside(long, structures.long!, "curvature-algebra")!;
    const html = withoutIds(long.render(hit.part).html);
    expect(html).not.toMatch(/\sid="/);
    expect(html).toContain('data-id="curvature-algebra"');
  });
});

describe("searching a paper", () => {
  it("holds every block's words, formulas as their source, on its own line", () => {
    const d = doc("short");
    const blocks = d.textBlocks();
    expect(blocks.length).toBeGreaterThan(40);
    const hit = blocks.find((b) => b.text.includes("Stieltjes"))!;
    expect(hit.line).toBeGreaterThan(1);
    expect(hit.text).not.toMatch(/[\uE000-\uF8FF]/);
    expect(d.textBlocks()).toBe(blocks);
  });
});

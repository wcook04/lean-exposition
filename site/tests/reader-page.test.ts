import { describe, expect, it } from "vitest";
import type { PaperStructure, ReadingItem, Stage } from "../src/api/types";
import { prepareDocument, type PreparedDocument } from "../src/reader/engine";
import {
  authoredRoutes,
  describeRecords,
  estimateHeight,
  firstPassageFor,
  idleOrder,
  outlineOf,
  parsePassageRef,
  placeName,
  resolveAnchor,
  resolveBeside,
  routeLead,
  routeTarget,
  sectionTitleIn,
  selectionSpan,
  sharedPlaces,
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
    expect(placeName(structures, "expository", "long", "curvature")).toBe(`Long record §4.1 ${title!.replace(/^4\.1 /, "")}`);
    expect(placeName(structures, "long", "long", "curvature")).toMatch(/^§4\.1 /);
  });

  it("never names a passage by the document title", () => {
    for (const stage of ["long", "short", "expository"] as Stage[]) {
      const h1 = structures[stage]!.paper.sections.find((s) => s.level === 1)!.title;
      for (const p of structures[stage]!.paper.passages) expect(sectionTitleIn(structures[stage], p.anchor)).not.toBe(h1);
    }
  });

  it("puts the edition status in words", () => {
    expect(statusWords("draft", "needs_revision")).toBe("Draft; review needs revision.");
    expect(statusWords(undefined, undefined)).toBe("");
  });

  it("counts claims and assumptions by kind", () => {
    const graph = graphFixture();
    const claim = [...graph.nodes.values()].find((n) => n.kind === "claim")!.id;
    const assumption = [...graph.nodes.values()].find((n) => n.kind === "assumption")!.id;
    expect(describeRecords([claim], graph)).toBe("claim");
    expect(describeRecords([claim, claim, assumption], graph)).toBe("2 claims and 1 assumption");
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

  it("words each route from the reader's side", () => {
    const here = { stage: "expository" as Stage, anchor: "curvature-transfer" };
    const [incoming] = authoredRoutes(structures, "expository", "curvature-transfer");
    expect(routeLead(incoming, here, structures)).toBe("A fuller treatment");
    const answer = authoredRoutes(structures, "expository", "changed-cases").find((r) => r.kind === "answers")!;
    expect(routeLead(answer, { stage: "expository", anchor: "changed-cases" }, structures)).toBe("Answered below");
    expect(routeTarget(answer, { stage: "expository", anchor: "changed-cases" }, structures)).toBe("see the answer");
    const question = authoredRoutes(structures, "expository", "changed-case-answer")[0];
    expect(routeTarget(question, { stage: "expository", anchor: "changed-case-answer" }, structures)).toBe("the question above");
    const example = authoredRoutes(structures, "expository", "zero-candidate")[0];
    expect(routeLead(example, { stage: "expository", anchor: "zero-candidate" }, structures)).toBe("This is an example of");
  });

  it("keeps derived shared-claim passages apart from authored ones and deduplicates them", () => {
    const self = structures.expository!.paper.passages.find((p) => p.anchor === "curvature-transfer")!.ref;
    const other = (stage: Stage, anchor: string) => structures[stage]!.paper.passages.find((p) => p.anchor === anchor)!.ref;
    const items: ReadingItem[] = [
      { kind: "expands", derived: false, annotation_basis: "", from: other("long", "curvature"), to: self, selection_relation: "incoming" },
      { kind: "shared_claim", derived: true, annotation_basis: "", from: self, to: other("long", "curvature"), selection_relation: "outgoing", shared_claim_refs: ["a"] },
      { kind: "shared_claim", derived: true, annotation_basis: "", from: self, to: other("short", "curvature"), selection_relation: "outgoing", shared_claim_refs: ["a", "b"] },
      { kind: "shared_claim", derived: true, annotation_basis: "", from: other("short", "curvature"), to: self, selection_relation: "incoming", shared_claim_refs: ["a"] },
    ];
    const places = sharedPlaces(items, { stage: "expository", anchor: "curvature-transfer" }, new Set(["long:curvature"]));
    expect(places).toEqual([{ stage: "short", anchor: "curvature", shared: 2 }]);
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

  it("finds the first passage in another account discussing a claim", () => {
    const claim = structures.expository!.paper.passages.find((p) => p.anchor === "curvature-transfer")!.claim_ids[0];
    const anchor = firstPassageFor(structures.long, [claim]);
    expect(structures.long!.paper.passages.find((p) => p.anchor === anchor)!.claim_ids).toContain(claim);
    expect(firstPassageFor(structures.long, [])).toBeNull();
  });
});

describe("outline", () => {
  it("lists sections of levels 2 and 3 without the subtitle", () => {
    const outline = outlineOf(doc("expository"));
    expect(outline[0].title).toBe("1. The finite optimisation problem");
    expect(outline.every((e) => e.level === 2 || e.level === 3)).toBe(true);
    expect(outline.some((e) => e.title.startsWith("A variational argument"))).toBe(false);
    expect(outlineOf(doc("long")).some((e) => e.title === "A long reasoning record")).toBe(false);
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

  it("strips fragment ids from a second copy of a part", () => {
    const long = doc("long");
    const hit = resolveBeside(long, structures.long!, "curvature-algebra")!;
    const html = withoutIds(long.render(hit.part).html);
    expect(html).not.toMatch(/\sid="/);
    expect(html).toContain('data-id="curvature-algebra"');
  });
});

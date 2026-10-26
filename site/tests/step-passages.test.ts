import { describe, expect, it } from "vitest";
import type { AlignedPassage, Stage } from "../src/api/types";
import { STAGE_ORDER } from "../src/app/papers";
import { stepPassages } from "../src/panels/model";
import { documentFixture, graphFixture, structureFixture } from "./fixtures";

/** Reconstruct only the API's direct node mappings from the captured edition. */
function alignedFor(id: string): AlignedPassage[] {
  return STAGE_ORDER.flatMap((stage) => {
    const bytes = documentFixture(stage);
    return structureFixture(stage).paper.passages.flatMap((p) => {
      const mappingField = p.claim_ids.includes(id) ? "claim_ids" : p.assumption_ids.includes(id) ? "assumption_ids" : null;
      if (!mappingField) return [];
      return [{
        stage,
        anchor: p.anchor,
        mapping_field: mappingField,
        passage_ref: p.ref,
        span: p.content_span,
        text: new TextDecoder().decode(bytes.slice(p.content_span.start_byte, p.content_span.end_byte)),
        query_href: "",
        reading_href: "",
        paper_href: "",
      }];
    });
  });
}

const anchors = (p: readonly AlignedPassage[]) => p.map((x) => x.anchor);

describe("step reading from recorded endpoint mappings", () => {
  it("keeps the Long record fallback when only the Exposition has a shared passage", () => {
    const consumer = alignedFor("support.first_variation");
    const prerequisite = alignedFor("support.regularity");
    const result = stepPassages(consumer, prerequisite);
    expect(anchors(result.grouped.get("expository")!)).toEqual(["zero-candidate"]);
    expect(result.basis.get("expository")).toBe("both");
    expect(anchors(result.grouped.get("long")!)).toEqual(["contact"]);
    expect(result.basis.get("long")).toBe("consumer");
    expect(anchors(result.grouped.get("short")!)).toEqual(["contact"]);
    expect(result.basis.get("short")).toBe("consumer");
  });

  it("returns no consumer fallback when only the prerequisite is mapped", () => {
    const result = stepPassages(alignedFor("support.near_ground_pairs"), alignedFor("support.full_relative_support"));
    expect(result.grouped.get("short")).toEqual([]);
    expect(result.basis.get("short")).toBe("none");
  });

  it("does not confuse identical anchors from different accounts", () => {
    const p = (stage: Stage, anchor: string) => ({ stage, anchor }) as AlignedPassage;
    const result = stepPassages([p("long", "contact")], [p("short", "contact")]);
    expect(result.basis.get("long")).toBe("consumer");
  });

  it("recovers all 62 account fallbacks suppressed by cross-account matching in this edition", () => {
    const graph = graphFixture();
    let recovered = 0;
    for (const edge of graph.edges.filter((e) => e.kind === "supports" || e.kind === "formalizes")) {
      const consumer = alignedFor(edge.from);
      const prerequisite = alignedFor(edge.to);
      const keys = new Set(prerequisite.map((p) => `${p.stage}:${p.anchor}`));
      const shared = consumer.filter((p) => keys.has(`${p.stage}:${p.anchor}`));
      if (!shared.length) continue;
      const result = stepPassages(consumer, prerequisite);
      for (const stage of STAGE_ORDER) {
        const own = consumer.filter((p) => p.stage === stage);
        if (!own.length || shared.some((p) => p.stage === stage)) continue;
        recovered += 1;
        expect(result.basis.get(stage)).toBe("consumer");
        expect(result.grouped.get(stage)).toEqual(own);
      }
    }
    expect(recovered).toBe(62);
  });
});

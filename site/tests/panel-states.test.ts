import { describe, expect, it } from "vitest";
import {
  NO_REMAINING,
  accountState,
  accountStateLine,
  applicationView,
  excerptLength,
  outcomeParts,
  routeView,
  sharedObjects,
  stepBasisLabel,
  type ExcerptBlock,
} from "../src/panels/model";

describe("account state table", () => {
  it("never reports an absence before the mapping request succeeds", () => {
    expect(accountState("loading", 0, [])).toEqual({ kind: "loading" });
    expect(accountState("error", 0, undefined)).toEqual({ kind: "error" });
    expect(accountStateLine(accountState("loading", 0, []))).toBe("Loading passages…");
    expect(accountStateLine(accountState("error", 0, []))).toBe("The linked passages could not be loaded.");
  });

  it("distinguishes direct links, use without a link and outside the selection", () => {
    expect(accountStateLine(accountState("ready", 2, ["mapped_claim"]))).toBe("2 passages are linked directly to this step");
    expect(accountStateLine(accountState("ready", 1, ["mapped_claim"]))).toBe("1 passage is linked directly to this step");
    expect(accountStateLine(accountState("ready", 0, ["recorded_prerequisite"]))).toBe(
      "No passage is linked directly to this step. These passages are linked to results that use it.",
    );
    expect(accountStateLine(accountState("ready", 0, []))).toBe("No passage in this paper is linked to this step, and the recorded argument for the paper’s main results does not use it.");
    for (const s of [accountState("ready", 0, []), accountState("ready", 0, ["recorded_prerequisite"])]) {
      expect(accountStateLine(s)).not.toMatch(/proves|does not discuss|uses it\.$/);
    }
  });

  it("labels step passages per account", () => {
    expect(stepBasisLabel("both")).toBe("Both steps linked");
    expect(stepBasisLabel("consumer")).toBe("Linked to the conclusion only");
    expect(stepBasisLabel("none")).toBeNull();
  });
});

describe("applied theorem view", () => {
  const stored = {
    premise_bindings: [
      { assumption_id: "assumptions.value_diffusion", binding_names: ["W", "gamma", "X"], rationale: "r", supplier_id: "scalar.source_diffusion_exists" },
    ],
    rationale: "MainConclusions applies the conditional identity.",
    remaining_assumption_ids: ["assumptions.value_minimizer"],
    shared_bindings: { W: "the caller's BrownianSpace W", X: "diffusionProcess W gamma", gamma: "the caller's OrderParameter gamma" },
    source_span: { source_id: "s", start_line: 21, end_line: 27 },
    status: "authored",
  };

  it("keeps the shared objects, the supplier and the remaining premise", () => {
    const v = applicationView(stored)!;
    expect(v.status).toBe("No program has tested this authored application of the theorem");
    expect(v.shared.map((s) => s.name)).toEqual(["W", "X", "gamma"]);
    expect(v.premises).toEqual([{ premise: "assumptions.value_diffusion", names: ["W", "gamma", "X"], rationale: "r", supplier: "scalar.source_diffusion_exists" }]);
    expect(v.remaining).toEqual(["assumptions.value_minimizer"]);
    expect(v.span).toEqual({ sourceId: "s", startLine: 21, endLine: 27 });
  });

  it("prefers the site model and falls back to the stored record", () => {
    const site = {
      rationale: null,
      bindings: [{ assumption: "a", names: ["gamma"], rationale: "", supplier: "b" }],
      remaining: [],
      shared: { gamma: "one attained gamma_0" },
      status: "authored",
      sourceSpan: null,
    };
    const v = applicationView(site, stored)!;
    expect(v.premises[0].supplier).toBe("b");
    expect(v.remaining).toEqual([]);
    expect(v.shared).toEqual([{ name: "gamma", value: "one attained gamma_0" }]);
    expect(v.rationale).toBe(stored.rationale);
    expect(NO_REMAINING).toBe("No remaining assumption is listed for this application");
  });

  it("never upgrades the recorded status", () => {
    expect(applicationView({ status: null })!.status).toBe("No program has tested this authored application of the theorem");
    expect(applicationView({ status: "authored" })!.status).not.toMatch(/checked$|verified|proved/i);
    expect(sharedObjects([{ name: "x", value: "y" }])).toEqual([{ name: "x", value: "y" }]);
    expect(applicationView()).toBeNull();
  });
});

describe("route and outcomes", () => {
  it("opens the middle of a long route only on request", () => {
    expect(routeView(["g", "a", "b", "c", "x"], false)).toEqual({ items: ["g", "c", "x"], hidden: 2, hiddenAt: 1 });
    expect(routeView(["g", "a", "b", "c", "x"], true).items).toHaveLength(5);
    expect(routeView(["g", "x"], false).hidden).toBe(0);
  });

  it("keeps every outcome apart, in a fixed order", () => {
    expect(outcomeParts({ not_run: 2, failed: 1, unavailable: 2 }).map((p) => `${p.n} ${p.word}`)).toEqual(["1 failed", "2 unavailable", "2 not run"]);
  });
});

describe("excerpt in complete blocks", () => {
  const p = (height: number, extra: Partial<ExcerptBlock> = {}): ExcerptBlock => ({ role: "p", height, ...extra });
  it("shows at least one whole block, however tall", () => {
    expect(excerptLength([p(600), p(40)])).toBe(1);
  });
  it("stops at the budget without cutting a block", () => {
    expect(excerptLength([p(120), p(120), p(120)], 300)).toBe(2);
  });
  it("keeps a formula with its introducing sentence and its qualifying clause", () => {
    const blocks = [p(200, { leads: true }), { role: "math", height: 60 }, p(40, { continues: true }), p(100)];
    expect(excerptLength(blocks, 220)).toBe(3);
  });
  it("never ends on a heading", () => {
    expect(excerptLength([{ role: "heading", height: 30 }, p(400)], 100)).toBe(2);
  });
});

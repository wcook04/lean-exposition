import { describe, expect, it } from "vitest";
import { repFor } from "../src/map/canvas/representation";
import { beyond, chipText, panToward } from "../src/map/canvas/chips";
import { firstSentence, traceTiming } from "../src/map/canvas/trace";
import { boxInView, frameBox, revealBox } from "../src/map/engine/camera";

const vp = { width: 1000, height: 600, insets: { top: 20, right: 20, bottom: 20, left: 20 } };

describe("representation by screen scale", () => {
  it("is a card from 0.8 and a tile below it", () => {
    expect(repFor(1)).toBe("card");
    expect(repFor(0.8)).toBe("card");
    expect(repFor(0.79)).toBe("compact");
    expect(repFor(0.5)).toBe("compact");
    expect(repFor(0.1)).toBe("compact");
  });
});

describe("edge chips", () => {
  const boxes = new Map([
    ["in", { x: 100, y: 100, w: 100, h: 50 }],
    ["right", { x: 1100, y: 100, w: 100, h: 50 }],
    ["cut", { x: 940, y: 100, w: 100, h: 50 }],
    ["left", { x: -300, y: 100, w: 100, h: 50 }],
    ["below", { x: 400, y: 800, w: 100, h: 50 }],
  ]);
  const view = { x: 0, y: 0, k: 1 };
  it("counts each card beyond the view toward the side it runs furthest past", () => {
    const b = beyond(boxes, view, vp);
    expect(b.right.sort()).toEqual(["cut", "right"]);
    expect(b.left).toEqual(["left"]);
    expect(b.down).toEqual(["below"]);
    expect(b.up).toEqual([]);
  });
  it("pans just far enough, never pushing the counted cards out the other side", () => {
    const v = panToward("right", ["cut", "right"], boxes, view, vp);
    expect(v.k).toBe(1);
    expect(boxInView({ x0: 940, y0: 100, x1: 1200, y1: 150 }, vp, v)).toBe(true);
  });
  it("words the count", () => {
    expect(chipText("right", 3)).toBe("3 records ▸");
    expect(chipText("left", 1)).toBe("◂ 1 record");
  });
});

describe("camera policy", () => {
  it("frames at a fixed reading scale and keeps the anchor centred when the box is wider than the view", () => {
    const b = { x0: 0, y0: 0, x1: 3000, y1: 400 };
    const anchor = { x0: 1400, y0: 0, x1: 1600, y1: 100 };
    const v = frameBox(b, vp, { min: 1, max: 1, anchor, top: true });
    expect(v.k).toBe(1);
    expect(1500 * v.k + v.x).toBeCloseTo(500, 5);
    expect(v.y).toBe(20);
  });
  it("reveals by panning when the box fits, and never zooms below the floor", () => {
    const view = { x: 0, y: 0, k: 1 };
    expect(revealBox({ x0: 100, y0: 100, x1: 300, y1: 200 }, vp, view, 0.85)).toBeNull();
    const pan = revealBox({ x0: 1100, y0: 100, x1: 1300, y1: 200 }, vp, view, 0.85)!;
    expect(pan.k).toBe(1);
    const wide = revealBox({ x0: 0, y0: 0, x1: 5000, y1: 200 }, vp, view, 0.85)!;
    expect(wide.k).toBeGreaterThanOrEqual(0.85);
  });
});

describe("lighting a route", () => {
  const rank = new Map([
    ["goal", 0],
    ["a", 1],
    ["b", 2],
    ["c", 3],
  ]);
  const edges = [
    { key: "a-b", from: "a", to: "b" },
    { key: "b-c", from: "b", to: "c" },
  ];
  it("spreads rank by rank from the selection and finishes within --t-trace", () => {
    const t = traceTiming(edges, rank, "a", "rests");
    expect(t.get("a-b")!.delay).toBe(0);
    expect(t.get("b-c")!.delay).toBeGreaterThan(0);
    for (const r of t.values()) expect(r.delay + r.dur).toBeLessThanOrEqual(520);
    expect(t.get("a-b")!.from).toBe("end");
    const up = traceTiming(edges, rank, "c", "uses");
    expect(up.get("b-c")!.delay).toBe(0);
    expect(up.get("a-b")!.delay).toBeGreaterThan(0);
    expect(up.get("a-b")!.from).toBe("start");
  });
  it("takes the first sentence of a warrant", () => {
    expect(firstSentence("This supplies the bound. Then the rest follows.")).toBe("This supplies the bound.");
  });
});

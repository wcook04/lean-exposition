import { describe, expect, it } from "vitest";
import { CLAMP_SLACK, clampView } from "../src/map/engine/camera";

const vp = { width: 1000, height: 600, insets: { top: 20, right: 20, bottom: 20, left: 20 } };
const wide = { x0: 0, y0: 0, x1: 3000, y1: 2000 };
const small = { x0: 0, y0: 0, x1: 400, y1: 200 };

describe("the camera keeps the drawing on the canvas", () => {
  it("leaves a view that is already inside alone", () => {
    const v = { x: -500, y: -300, k: 1 };
    expect(clampView(v, wide, vp)).toEqual(v);
  });

  it("stops a drawing wider than the view before it leaves", () => {
    const right = clampView({ x: 5000, y: 0, k: 1 }, wide, vp);
    expect(right.x).toBeCloseTo(20 + 960 * CLAMP_SLACK);
    const left = clampView({ x: -5000, y: 0, k: 1 }, wide, vp);
    // The drawing's right edge still has most of the view to its left.
    expect(3000 + left.x).toBeCloseTo(980 - 960 * CLAMP_SLACK);
  });

  it("keeps a drawing that fits wholly inside the view", () => {
    const v = clampView({ x: 9000, y: -9000, k: 1 }, small, vp);
    expect(v.x + 400).toBeLessThanOrEqual(980);
    expect(v.y).toBeGreaterThanOrEqual(20);
  });

  it("holds at every scale", () => {
    for (const k of [0.5, 1, 1.8]) {
      const v = clampView({ x: -1e6, y: -1e6, k }, wide, vp);
      expect(wide.x1 * k + v.x).toBeGreaterThan(20);
      expect(wide.y1 * k + v.y).toBeGreaterThan(20);
    }
  });
});

// Camera arithmetic: fit a box into the view, or pan (and zoom out only if it
// must) just enough to bring a box into view.
//
// fitBounds is adapted from xyflow (https://github.com/xyflow/xyflow),
// Copyright (c) 2019-2025 webkid GmbH, MIT licence:
// packages/system/src/utils/general.ts, getViewportForBounds. Changed: insets
// in place of paddings, optional top alignment. ensureVisible follows markmap
// (https://github.com/markmap/markmap), Copyright (c) 2020 Gerald, MIT licence:
// packages/markmap-view/src/view.ts, ensureVisible (pan the minimum, and not
// at all when the box is already inside). Changed: falls back to a fit with a
// zoom floor when the box is larger than the view.

export interface View {
  x: number;
  y: number;
  k: number;
}

export interface Bounds {
  x0: number;
  y0: number;
  x1: number;
  y1: number;
}

export interface Viewport {
  width: number;
  height: number;
  insets: { top: number; right: number; bottom: number; left: number };
}

export function fitBounds(b: Bounds, vp: Viewport, opts: { min?: number; max?: number; top?: boolean } = {}): View {
  const { insets } = vp;
  const availW = Math.max(60, vp.width - insets.left - insets.right);
  const availH = Math.max(60, vp.height - insets.top - insets.bottom);
  const k = Math.max(opts.min ?? 0.2, Math.min(opts.max ?? 1, availW / Math.max(1, b.x1 - b.x0), availH / Math.max(1, b.y1 - b.y0)));
  const x = insets.left + availW / 2 - ((b.x0 + b.x1) / 2) * k;
  const fitsH = (b.y1 - b.y0) * k <= availH;
  const y = opts.top || !fitsH ? insets.top - b.y0 * k : insets.top + availH / 2 - ((b.y0 + b.y1) / 2) * k;
  return { x, y, k };
}

/** The view after the smallest pan that brings `b` inside; null when it already is. */
export function ensureVisible(b: Bounds, vp: Viewport, view: View, minScale: number): View | null {
  const { insets } = vp;
  const v = { x0: insets.left, y0: insets.top, x1: vp.width - insets.right, y1: vp.height - insets.bottom };
  const s = { x0: b.x0 * view.k + view.x, x1: b.x1 * view.k + view.x, y0: b.y0 * view.k + view.y, y1: b.y1 * view.k + view.y };
  if (s.x0 >= v.x0 - 0.5 && s.x1 <= v.x1 + 0.5 && s.y0 >= v.y0 - 0.5 && s.y1 <= v.y1 + 0.5) return null;
  const fits = s.x1 - s.x0 <= v.x1 - v.x0 && s.y1 - s.y0 <= v.y1 - v.y0;
  if (fits) {
    let dx = 0;
    let dy = 0;
    if (s.x0 < v.x0) dx = v.x0 - s.x0;
    else if (s.x1 > v.x1) dx = v.x1 - s.x1;
    if (s.y0 < v.y0) dy = v.y0 - s.y0;
    else if (s.y1 > v.y1) dy = v.y1 - s.y1;
    return { x: view.x + dx, y: view.y + dy, k: view.k };
  }
  const fit = fitBounds(b, vp, { max: view.k, min: minScale, top: true });
  // At the floor the box may still not fit: keep its top-left corner in view.
  return fit;
}

/** Interpolate views through their centres and log-scale, so zooms feel even. */
export function lerpView(a: View, b: View, t: number, vp: Viewport): View {
  const cx = vp.width / 2;
  const cy = vp.height / 2;
  const ca = { x: (cx - a.x) / a.k, y: (cy - a.y) / a.k };
  const cb = { x: (cx - b.x) / b.k, y: (cy - b.y) / b.k };
  const k = Math.exp(Math.log(a.k) + (Math.log(b.k) - Math.log(a.k)) * t);
  const c = { x: ca.x + (cb.x - ca.x) * t, y: ca.y + (cb.y - ca.y) * t };
  return { x: cx - c.x * k, y: cy - c.y * k, k };
}

/**
 * Frame `b` at the largest scale in [min, max] that fits it. When it cannot
 * fit even at `min`, the anchor (the card the reader is working from) is
 * centred across and the box's top is kept in view, so the reader keeps the
 * card they opened and the edge chips say what lies beyond.
 */
export function frameBox(b: Bounds, vp: Viewport, opts: { min: number; max: number; anchor?: Bounds | null; top?: boolean }): View {
  const { insets } = vp;
  const availW = Math.max(60, vp.width - insets.left - insets.right);
  const availH = Math.max(60, vp.height - insets.top - insets.bottom);
  const bw = Math.max(1, b.x1 - b.x0);
  const bh = Math.max(1, b.y1 - b.y0);
  const k = Math.max(opts.min, Math.min(opts.max, availW / bw, availH / bh));
  let x: number;
  if (bw * k <= availW + 0.5 || !opts.anchor) x = insets.left + availW / 2 - ((b.x0 + b.x1) / 2) * k;
  else {
    const a = opts.anchor;
    x = insets.left + availW / 2 - ((a.x0 + a.x1) / 2) * k;
    // No empty margin on a side while the box still runs past the other.
    x = Math.min(x, insets.left - b.x0 * k);
    x = Math.max(x, insets.left + availW - b.x1 * k);
  }
  const fitsH = bh * k <= availH + 0.5;
  let y = opts.top || !fitsH ? insets.top - b.y0 * k : insets.top + availH / 2 - ((b.y0 + b.y1) / 2) * k;
  if (!fitsH && opts.anchor) {
    // Keep the anchor itself on screen.
    const a = opts.anchor;
    const bottom = insets.top + availH;
    if (a.y1 * k + y > bottom) y = bottom - a.y1 * k;
  }
  return { x, y, k };
}

/**
 * Bring `b` into view moving as little as possible: pan only when it fits at
 * the current scale, zoom out no further than `minK` when it does not, and
 * past that keep the anchor in view.
 */
export function revealBox(b: Bounds, vp: Viewport, view: View, minK: number, anchor?: Bounds | null): View | null {
  if (boxInView(b, vp, view)) return null;
  const { insets } = vp;
  const fitsAtK = (b.x1 - b.x0) * view.k <= vp.width - insets.left - insets.right + 0.5 && (b.y1 - b.y0) * view.k <= vp.height - insets.top - insets.bottom + 0.5;
  if (fitsAtK) return ensureVisible(b, vp, view, view.k);
  return frameBox(b, vp, { min: Math.min(view.k, minK), max: view.k, anchor, top: true });
}

/** Whether a box lies wholly inside the view. */
export function boxInView(b: Bounds, vp: Viewport, view: View, slack = 0.5): boolean {
  const { insets } = vp;
  return (
    b.x0 * view.k + view.x >= insets.left - slack &&
    b.x1 * view.k + view.x <= vp.width - insets.right + slack &&
    b.y0 * view.k + view.y >= insets.top - slack &&
    b.y1 * view.k + view.y <= vp.height - insets.bottom + slack
  );
}

// Orthogonal connectors with rounded corners, in two steps:
//
// plan(layout), once per layout: which side and port of each card each
// connector uses (as a fraction of the card's width, so it moves with the
// card), which connectors join a parent's fan-in bus, and which horizontal
// track each connector takes in each gap between ranks.
//
// route(plan, frame), every animation frame: the actual points from the
// current (interpolated) card rectangles. Corners use min(r, leg / 2), so a
// horizontal run that shrinks to nothing becomes a straight line smoothly.
//
// Arrows follow the blueprint convention: a connector runs from a
// prerequisite up into the result it helps prove. All `supports` connectors
// into one result join a single bus in the gap below it: each rises from its
// own port, turns onto the bus's track and the bus rises as one stem into the
// result, ending in one arrowhead. `assumes` and `formalizes` connectors run
// on their own.
//
// The track order follows MSAGL's order-then-assign split for nudging
// parallel segments (https://github.com/microsoft/msagljs, Copyright (c)
// Microsoft Corporation, MIT licence: routing/nudging/CombinatorialNudger.ts,
// Nudger.ts), reduced here to a pairwise crossing preference with a left-edge
// fallback; no code is copied. The rounded corner is adapted from xyflow
// (https://github.com/xyflow/xyflow, Copyright (c) 2019-2025 webkid GmbH, MIT
// licence): packages/system/src/utils/edges/smoothstep-edge.ts, getBend and the
// collinear-point drop in getPoints. Changed: any number of points, corners
// sized by both legs, numbers rounded for the DOM. The arrowhead triangle
// follows getArrowheadPoints in msagljs modules/renderer-svg/src/svgCreator.ts,
// with a wider angle.

import { spacedWithin } from "./pav";
import type { Layout, Metrics, Rect } from "./types";

export interface PlanEdge {
  key: string;
  kind: "supports" | "assumes" | "formalizes";
  from: string;
  to: string;
  /** Joins the consumer's fan-in bus. */
  bus: boolean;
  arrow: boolean;
  /** Port on the prerequisite's top edge, as a fraction of its width. */
  childPort: number;
  /** Port on the consumer's bottom edge (the bus stem for bus edges). */
  parentPort: number;
  rankFrom: number;
  rankTo: number;
  chain: string[];
  /** Track per gap, indexed by gap - rankFrom; null runs straight. */
  tracks: (number | null)[];
}

export interface PlanBus {
  parent: string;
  edges: string[];
  stem: number;
  rank: number;
  track: number | null;
}

export interface Plan {
  metrics: Metrics;
  edges: Map<string, PlanEdge>;
  buses: Map<string, PlanBus>;
  rank: Map<string, number>;
  /** Card ids per rank. */
  rows: string[][];
  trackCount: number[];
}

const EPS = 0.75;

interface Obj {
  id: string;
  top: number[];
  bottom: number[];
  l: number;
  r: number;
  track: number;
}

function median(xs: number[]): number {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

export function plan(layout: Layout): Plan {
  const m = layout.metrics;
  const { boxes, dummies, rank } = layout;
  const dx = (key: string) => dummies.get(key)!.x;
  const edges = new Map<string, PlanEdge>();
  const buses = new Map<string, PlanBus>();

  for (const e of layout.edges) {
    const bus = e.kind === "supports";
    edges.set(e.key, {
      key: e.key,
      kind: e.kind,
      from: e.from,
      to: e.to,
      bus,
      arrow: e.kind !== "formalizes",
      childPort: 0.5,
      parentPort: 0.5,
      rankFrom: rank.get(e.from)!,
      rankTo: rank.get(e.to)!,
      chain: layout.chains.get(e.key) ?? [],
      tracks: [],
    });
    if (bus) {
      if (!buses.has(e.from)) buses.set(e.from, { parent: e.from, edges: [], stem: 0.5, rank: rank.get(e.from)!, track: null });
      buses.get(e.from)!.edges.push(e.key);
    }
  }

  // ---- Ports -------------------------------------------------------------------------
  const cx = (id: string) => boxes.get(id)!.x + boxes.get(id)!.w / 2;
  const topX = new Map<string, number>(); // edge key -> x on the prerequisite's top
  const botX = new Map<string, number>(); // edge key (non-bus) or "bus:" + parent -> x on the consumer's bottom
  for (const pe of edges.values()) {
    topX.set(pe.key, cx(pe.to));
    if (!pe.bus) botX.set(pe.key, cx(pe.from));
  }
  for (const b of buses.values()) botX.set(`bus:${b.parent}`, cx(b.parent));

  const tops = new Map<string, string[]>();
  const bottoms = new Map<string, string[]>();
  for (const pe of edges.values()) {
    if (!tops.has(pe.to)) tops.set(pe.to, []);
    tops.get(pe.to)!.push(pe.key);
    const bk = pe.bus ? `bus:${pe.from}` : pe.key;
    if (!bottoms.has(pe.from)) bottoms.set(pe.from, []);
    if (!bottoms.get(pe.from)!.includes(bk)) bottoms.get(pe.from)!.push(bk);
  }
  const upX = (pe: PlanEdge) => (pe.chain.length ? dx(pe.chain[pe.chain.length - 1]) : botX.get(pe.bus ? `bus:${pe.from}` : pe.key)!);
  const downX = (pe: PlanEdge) => (pe.chain.length ? dx(pe.chain[0]) : topX.get(pe.key)!);
  const resolve = (card: string, keys: string[], desired: (k: string) => number, into: Map<string, number>) => {
    const box = boxes.get(card)!;
    const list = keys.map((k) => ({ k, x: desired(k) })).sort((a, b) => a.x - b.x || (a.k < b.k ? -1 : 1));
    const xs = spacedWithin(
      list.map((p) => p.x),
      m.portSp,
      box.x + m.inset,
      box.x + box.w - m.inset,
    );
    list.forEach((p, i) => into.set(p.k, xs[i]));
  };
  for (let round = 0; round < 3; round++) {
    for (const [card, keys] of bottoms) {
      resolve(
        card,
        keys,
        (k) => {
          if (k.startsWith("bus:")) return median(buses.get(card)!.edges.map((ek) => downX(edges.get(ek)!)));
          return downX(edges.get(k)!);
        },
        botX,
      );
    }
    for (const [card, keys] of tops) resolve(card, keys, (k) => upX(edges.get(k)!), topX);
  }
  for (const pe of edges.values()) {
    const child = boxes.get(pe.to)!;
    const parent = boxes.get(pe.from)!;
    pe.childPort = (topX.get(pe.key)! - child.x) / child.w;
    pe.parentPort = ((pe.bus ? botX.get(`bus:${pe.from}`)! : botX.get(pe.key)!) - parent.x) / parent.w;
  }
  for (const b of buses.values()) {
    const parent = boxes.get(b.parent)!;
    b.stem = (botX.get(`bus:${b.parent}`)! - parent.x) / parent.w;
  }

  // ---- Tracks ------------------------------------------------------------------------
  const depth = layout.layers.length;
  const perGap: Obj[][] = Array.from({ length: Math.max(0, depth - 1) }, () => []);
  const busObj = new Map<string, Obj>();
  const pieceObj = new Map<string, Obj>();
  for (const pe of edges.values()) {
    pe.tracks = new Array(pe.rankTo - pe.rankFrom).fill(null);
    let xb = topX.get(pe.key)!;
    for (let g = pe.rankTo - 1; g >= pe.rankFrom; g--) {
      const atParent = g === pe.rankFrom;
      const xt = atParent ? botX.get(pe.bus ? `bus:${pe.from}` : pe.key)! : dx(pe.chain[g - pe.rankFrom - 1]);
      if (atParent && pe.bus) {
        let o = busObj.get(pe.from);
        if (!o) {
          o = { id: `bus:${pe.from}`, top: [xt], bottom: [], l: xt, r: xt, track: -1 };
          busObj.set(pe.from, o);
        }
        o.bottom.push(xb);
        o.l = Math.min(o.l, xb);
        o.r = Math.max(o.r, xb);
      } else if (Math.abs(xt - xb) > EPS) {
        const o: Obj = { id: `${pe.key}@${g}`, top: [xt], bottom: [xb], l: Math.min(xt, xb), r: Math.max(xt, xb), track: -1 };
        pieceObj.set(o.id, o);
        perGap[g].push(o);
      }
      xb = xt;
    }
  }
  for (const [parent, o] of busObj) if (o.r - o.l > EPS) perGap[rank.get(parent)!].push(o);

  const trackCount = new Array(depth).fill(0);
  const pad = m.radius + 2;
  const inside = (x: number, o: Obj) => x > o.l + EPS && x < o.r - EPS;
  const cost = (a: Obj, b: Obj) => {
    // a's track above b's: a's lower legs cross b's run, b's upper legs cross a's run.
    let c = 0;
    for (const x of a.bottom) if (inside(x, b)) c++;
    for (const x of b.top) if (inside(x, a)) c++;
    return c;
  };
  perGap.forEach((objs, g) => {
    if (!objs.length) return;
    const n = objs.length;
    const overlap = (a: Obj, b: Obj) => a.l - pad < b.r + pad && b.l - pad < a.r + pad;
    const before: Set<number>[] = objs.map(() => new Set());
    for (let i = 0; i < n; i++)
      for (let j = i + 1; j < n; j++) {
        if (!overlap(objs[i], objs[j])) continue;
        const ij = cost(objs[i], objs[j]);
        const ji = cost(objs[j], objs[i]);
        if (ij < ji) before[j].add(i);
        else if (ji < ij) before[i].add(j);
      }
    const placed: number[] = [];
    const done = new Set<number>();
    while (placed.length < n) {
      let pick = -1;
      for (let i = 0; i < n; i++) {
        if (done.has(i)) continue;
        const ready = [...before[i]].every((j) => done.has(j));
        if (ready && (pick < 0 || objs[i].l < objs[pick].l)) pick = i;
      }
      if (pick < 0) for (let i = 0; i < n; i++) if (!done.has(i) && (pick < 0 || objs[i].l < objs[pick].l)) pick = i;
      done.add(pick);
      placed.push(pick);
    }
    const order: Obj[] = [];
    for (const i of placed) {
      const o = objs[i];
      let t = 0;
      for (const p of order) if (overlap(p, o)) t = Math.max(t, p.track + 1);
      o.track = t;
      order.push(o);
    }
    trackCount[g] = Math.max(...objs.map((o) => o.track)) + 1;
  });
  for (const [parent, o] of busObj) buses.get(parent)!.track = o.track >= 0 ? o.track : null;
  for (const pe of edges.values()) {
    for (let g = pe.rankFrom; g < pe.rankTo; g++) {
      if (g === pe.rankFrom && pe.bus) pe.tracks[0] = buses.get(pe.from)!.track;
      else {
        const o = pieceObj.get(`${pe.key}@${g}`);
        pe.tracks[g - pe.rankFrom] = o ? o.track : null;
      }
    }
  }

  const rows: string[][] = layout.layers.map((layer) => layer.filter((id) => !id.startsWith("§")));
  return { metrics: m, edges, buses, rank, rows, trackCount };
}

// ---- Per frame ------------------------------------------------------------------------

export interface Pt {
  x: number;
  y: number;
}

export interface Frame {
  boxes: Map<string, Rect>;
  dummyX(key: string): number;
  /** Cards left out of the row extents (for example, cards still entering). */
  ignoreRows?: ReadonlySet<string>;
}

export interface RoutedEdge {
  key: string;
  points: Pt[];
  /** Where the connector meets its consumer's bus (or its midpoint in the last gap). */
  junction: Pt;
  /** The part that belongs to this edge alone (without a shared stem). */
  own: Pt[];
}

export interface RoutedBus {
  parent: string;
  stem: Pt[];
  head: Pt[];
}

export interface Routed {
  edges: Map<string, RoutedEdge>;
  buses: Map<string, RoutedBus>;
  /** Arrowheads of connectors that run on their own (assumes). */
  heads: Map<string, Pt[]>;
}

export function arrowHead(tip: Pt, length: number, angleDeg = 40): Pt[] {
  const s = length * Math.tan(((angleDeg / 2) * Math.PI) / 180);
  const base = { x: tip.x, y: tip.y + length };
  return [{ x: base.x - s, y: base.y }, tip, { x: base.x + s, y: base.y }];
}

export function route(p: Plan, frame: Frame): Routed {
  const m = p.metrics;
  const { boxes } = frame;
  const depth = p.rows.length;
  const rowTop = new Array<number>(depth);
  const rowBottom = new Array<number>(depth);
  for (let r = 0; r < depth; r++) {
    let top = Infinity;
    let bottom = -Infinity;
    let any = false;
    for (const id of p.rows[r]) {
      if (frame.ignoreRows?.has(id)) continue;
      const b = boxes.get(id);
      if (!b) continue;
      any = true;
      top = Math.min(top, b.y);
      bottom = Math.max(bottom, b.y + b.h);
    }
    if (!any)
      for (const id of p.rows[r]) {
        const b = boxes.get(id);
        if (!b) continue;
        top = Math.min(top, b.y);
        bottom = Math.max(bottom, b.y + b.h);
      }
    rowTop[r] = top;
    rowBottom[r] = bottom;
  }
  const bandMid = (g: number) => {
    const lo = rowBottom[g] + m.padTop;
    const hi = rowTop[g + 1] - m.padBottom;
    return hi >= lo ? (lo + hi) / 2 : (rowBottom[g] + rowTop[g + 1]) / 2;
  };
  const trackY = (g: number, t: number | null): number => {
    const lo = rowBottom[g] + m.padTop;
    const hi = rowTop[g + 1] - m.padBottom;
    const mid = bandMid(g);
    const T = p.trackCount[g] || 1;
    if (t === null || T <= 1) return mid;
    const sp = hi > lo ? Math.min(m.trackSp, (hi - lo) / (T - 1)) : 0;
    return mid - (sp * (T - 1)) / 2 + t * sp;
  };

  const edges = new Map<string, RoutedEdge>();
  const heads = new Map<string, Pt[]>();
  for (const pe of p.edges.values()) {
    const child = boxes.get(pe.to);
    const parent = boxes.get(pe.from);
    if (!child || !parent) continue;
    const pts: Pt[] = [{ x: child.x + pe.childPort * child.w, y: child.y }];
    let junction: Pt = pts[0];
    let ownEnd = 1;
    for (let g = pe.rankTo - 1; g >= pe.rankFrom; g--) {
      const at = pts[pts.length - 1];
      const atParent = g === pe.rankFrom;
      const want = atParent ? parent.x + pe.parentPort * parent.w : frame.dummyX(pe.chain[g - pe.rankFrom - 1]);
      const t = pe.tracks[g - pe.rankFrom];
      const turn = Math.abs(want - at.x) > 0.01;
      const xt = turn ? want : at.x;
      const ty = trackY(g, t);
      if (turn) pts.push({ x: at.x, y: ty }, { x: xt, y: ty });
      if (atParent) {
        junction = { x: at.x, y: ty };
        ownEnd = turn ? pts.length - 1 : pts.length;
        pts.push({ x: xt, y: parent.y + parent.h + (pe.arrow ? m.arrow : 0) });
      } else pts.push({ x: xt, y: rowTop[g] });
    }
    const own = pe.bus ? [...pts.slice(0, ownEnd), junction] : pts;
    edges.set(pe.key, { key: pe.key, points: pts, junction, own });
    if (!pe.bus && pe.arrow) heads.set(pe.key, arrowHead({ x: pts[pts.length - 1].x, y: parent.y + parent.h - 0.5 }, m.arrow));
  }

  const buses = new Map<string, RoutedBus>();
  for (const b of p.buses.values()) {
    const parent = boxes.get(b.parent);
    if (!parent) continue;
    const x = parent.x + b.stem * parent.w;
    const ty = b.rank + 1 < depth ? trackY(b.rank, b.track) : parent.y + parent.h + m.padTop;
    const stem = [
      { x, y: ty },
      { x, y: parent.y + parent.h + m.arrow },
    ];
    buses.set(b.parent, { parent: b.parent, stem, head: arrowHead({ x, y: parent.y + parent.h - 0.5 }, m.arrow) });
  }
  return { edges, buses, heads };
}

// ---- Path strings -----------------------------------------------------------------------

const f = (v: number) => (Math.round(v * 10) / 10).toString();

/** An orthogonal polyline with rounded corners: radius min(r, leg / 2) at each corner. */
export function roundedPath(points: readonly Pt[], r: number): string {
  const pts: Pt[] = [];
  for (const q of points) {
    const last = pts[pts.length - 1];
    if (last && Math.abs(last.x - q.x) < 0.01 && Math.abs(last.y - q.y) < 0.01) continue;
    // Drop a point the path runs straight through; it would shrink the next corner.
    const prev = pts[pts.length - 2];
    if (prev && last && ((Math.abs(prev.x - last.x) < 0.01 && Math.abs(last.x - q.x) < 0.01 && (last.y - prev.y) * (q.y - last.y) >= 0) || (Math.abs(prev.y - last.y) < 0.01 && Math.abs(last.y - q.y) < 0.01 && (last.x - prev.x) * (q.x - last.x) >= 0)))
      pts.pop();
    pts.push(q);
  }
  if (pts.length < 2) return pts.length ? `M${f(pts[0].x)},${f(pts[0].y)}` : "";
  let d = `M${f(pts[0].x)},${f(pts[0].y)}`;
  for (let i = 1; i < pts.length - 1; i++) {
    const a = pts[i - 1];
    const b = pts[i];
    const c = pts[i + 1];
    const ab = Math.hypot(b.x - a.x, b.y - a.y);
    const bc = Math.hypot(c.x - b.x, c.y - b.y);
    const rho = Math.min(r, ab / 2, bc / 2);
    if (rho < 0.05) {
      d += `L${f(b.x)},${f(b.y)}`;
      continue;
    }
    const p1 = { x: b.x + ((a.x - b.x) / ab) * rho, y: b.y + ((a.y - b.y) / ab) * rho };
    const p2 = { x: b.x + ((c.x - b.x) / bc) * rho, y: b.y + ((c.y - b.y) / bc) * rho };
    d += `L${f(p1.x)},${f(p1.y)}Q${f(b.x)},${f(b.y)} ${f(p2.x)},${f(p2.y)}`;
  }
  const z = pts[pts.length - 1];
  return d + `L${f(z.x)},${f(z.y)}`;
}

export function polygonPath(points: readonly Pt[]): string {
  return points.map((q, i) => `${i ? "L" : "M"}${f(q.x)},${f(q.y)}`).join("") + "Z";
}

/** Sample a rounded path's polyline (corners cut by their chords) every `step` px, for tests. */
export function samplePolyline(points: readonly Pt[], step = 4): Pt[] {
  const out: Pt[] = [];
  for (let i = 0; i + 1 < points.length; i++) {
    const a = points[i];
    const b = points[i + 1];
    const len = Math.hypot(b.x - a.x, b.y - a.y);
    const n = Math.max(1, Math.ceil(len / step));
    for (let k = 0; k < n; k++) out.push({ x: a.x + ((b.x - a.x) * k) / n, y: a.y + ((b.y - a.y) * k) / n });
  }
  if (points.length) out.push(points[points.length - 1]);
  return out;
}

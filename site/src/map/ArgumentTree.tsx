// The argument as a tree you unfold. The goal sits at the top as the theorem
// itself; beneath it are the results it uses, each a card with its name in
// words. Unfold a card (its "Uses" control, a double-click, or Space) to see
// what that result uses, down to the starting points the record takes from its
// sources. Each arrow runs from a result up into the result it helps prove.
// The underlying graph is not a tree: a result used several times is drawn
// once, and only the transitive reduction of what is on screen is drawn (a use
// that a longer chain on screen already shows is left out; the card's foot
// still counts it).
//
// Layout, connectors and motion are this project's own engine (./engine):
// a layered layout, an orthogonal connector router planned once per layout and
// routed every frame, and one animation clock for cards, connectors and camera.
// Camera input: d3-zoom.

import { forwardRef, useCallback, useEffect, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import { select } from "d3-selection";
import { zoom as d3zoom, zoomIdentity, type ZoomBehavior, type ZoomTransform } from "d3-zoom";
import type { Stage } from "../api/types";
import { closure, lensRole, type ArgEdge, type ArgGraph, type ArgNode } from "../model/graph";
import type { Trace } from "../app/router";
import { prefersReducedMotion } from "../app/theme";
import { kindName } from "./labels";
import { expandTo, pathFromGoal, reach, routeTo, usesOf, visibleEdges, visibleSet } from "./treeModel";
import { transitiveReduction } from "./engine/skeleton";
import { layoutBounds, layoutTree } from "./engine/layout";
import { arrowHead, polygonPath, roundedPath, route, type Plan, type Pt, type Routed } from "./engine/router";
import { ensureVisible, fitBounds, lerpView, type Bounds, type View, type Viewport } from "./engine/camera";
import { MOVE_MS, easeMove, lerp } from "./engine/motion";
import { METRICS, METRICS_COMPACT, type EngineEdge, type Layout, type Rect, type Size } from "./engine/types";
import "./tree.css";

export interface Insets {
  top: number;
  right: number;
  bottom: number;
  left: number;
}

export interface MapViewHandle {
  fitAll(animate?: boolean): void;
  fitNodes(ids: Iterable<string>, animate?: boolean): void;
  zoomBy(factor: number): void;
  focusNode(id: string): void;
  expandAll(): void;
  collapseAll(): void;
}

export interface TreeProps {
  graph: ArgGraph;
  /** The result at the top. Defaults to the first part's goal (the main theorem). */
  goal?: string;
  /** Accepted for compatibility with the earlier map view; ignored. */
  layout?: unknown;
  region?: string;
  onRegion?(id: string | null): void;
  selected?: string;
  trace?: Trace;
  lens?: Stage;
  /** Nodes lit from elsewhere (a passage or ribbon under the pointer). */
  echo?: ReadonlySet<string> | null;
  insets: Insets;
  intro?: boolean;
  compact?: boolean;
  /** The body of the goal's card: the theorem as a paper states it, and its checks. */
  rootContent?: ReactNode;
  onSelect(id: string | null): void;
  onTrace(id: string): void;
  onHover?(id: string | null): void;
  /** The selected edge, as an ArgEdge.key (`${from}→${to}→${kind}`). */
  selectedEdge?: string;
  onEdgeSelect?(key: string | null): void;
  /** A per-account view: when set, the tree only shows records in this set (the root always). */
  within?: ReadonlySet<string>;
}

const STORE = "lx-tree-expanded:";

function widthOf(node: ArgNode, isRoot: boolean, compact: boolean, rootW = 940): number {
  if (isRoot) return compact ? 260 : rootW;
  if (compact) return 184;
  if (node.kind === "declaration") return 264;
  return 244;
}

function guessHeight(node: ArgNode, isRoot: boolean, compact: boolean): number {
  if (isRoot) return compact ? 76 : 240;
  if (compact) return 62;
  return node.kind === "claim" ? 92 : 108;
}

function hashSet(set: ReadonlySet<string>): string {
  let h = 0;
  for (const id of [...set].sort()) for (let i = 0; i < id.length; i++) h = (Math.imul(h, 31) + id.charCodeAt(i)) | 0;
  return (h >>> 0).toString(36);
}

interface CardState {
  rect: Rect;
  op: number;
  sc: number;
}

interface Motion {
  start: number;
  dur: number;
  from: Map<string, CardState>;
  to: Map<string, CardState>;
  dummyFrom: Map<string, number>;
  entering: Set<string>;
  view?: { from: View; to: View };
}

interface Built {
  layout: Layout;
  plan: Plan;
  skeleton: EngineEdge[];
  implied: Set<string>;
  provisional: boolean;
  pin: string | null;
}

export const ArgumentTree = forwardRef<MapViewHandle, TreeProps>(function ArgumentTree(props, ref) {
  const { graph, selected, trace, lens, echo, insets, intro, compact = false, rootContent, onSelect, onTrace, onHover, selectedEdge, onEdgeSelect, within } = props;
  const goal = props.goal && graph.nodes.has(props.goal) ? props.goal : (graph.regions[0]?.goal ?? graph.goals[0]);
  const metrics = compact ? METRICS_COMPACT : METRICS;
  const wrapRef = useRef<HTMLDivElement>(null);
  const worldRef = useRef<HTMLDivElement>(null);
  const zoomRef = useRef<ZoomBehavior<HTMLDivElement, unknown> | null>(null);
  const viewRef = useRef<View>({ x: 0, y: 0, k: 1 });
  const sizeRef = useRef({ width: 1, height: 1 });
  const insetsRef = useRef(insets);
  insetsRef.current = insets;
  const [ready, setReady] = useState(false);
  // The theorem card narrows on a small screen so it can be read whole at a readable zoom.
  const [paneW, setPaneW] = useState(0);
  const rootW = paneW > 0 && paneW < 860 ? Math.max(340, Math.min(940, Math.floor((paneW - 24) / 0.82 / 20) * 20)) : 940;
  const [hover, setHover] = useState<string | null>(null);
  const [focusId, setFocusId] = useState<string | null>(null);
  const [moving, setMoving] = useState(false);
  const [tip, setTip] = useState<{ key: string; x: number; y: number } | null>(null);
  const [hoverEdge, setHoverEdge] = useState<string | null>(null);
  const reduced = useMemo(() => prefersReducedMotion(), []);

  // ---- What is unfolded -------------------------------------------------------------

  const storeKey = STORE + goal + (within ? `|${hashSet(within)}` : "");
  const derived = !!(within && echo && echo.size);
  const readStore = (key: string) => {
    try {
      const raw = sessionStorage.getItem(key);
      if (raw) return new Set(JSON.parse(raw) as string[]);
    } catch {
      /* storage unavailable */
    }
    return new Set<string>();
  };
  const [expandedState, setExpanded] = useState<Set<string>>(() => readStore(storeKey));
  const keyRef = useRef(storeKey);
  useEffect(() => {
    if (keyRef.current === storeKey) return;
    keyRef.current = storeKey;
    setExpanded(readStore(storeKey));
  }, [storeKey]);
  useEffect(() => {
    if (derived) return;
    try {
      sessionStorage.setItem(storeKey, JSON.stringify([...expandedState]));
    } catch {
      /* storage unavailable */
    }
  }, [expandedState, storeKey, derived]);

  // In a passage view (within + echo), the route to the lit records is open; the lit
  // records' own uses stay folded. Toggles there flip that default until the passage changes.
  const [flips, setFlips] = useState<{ echo: ReadonlySet<string> | null | undefined; ids: Set<string> }>({ echo, ids: new Set() });
  const routeSet = useMemo(() => (derived ? routeTo(graph, goal, echo!, within) : null), [derived, graph, goal, echo, within]);
  const expanded = useMemo(() => {
    if (!derived || !routeSet) return expandedState;
    const open = new Set<string>();
    for (const id of routeSet) if (id !== goal && usesOf(graph, id, within).some((e) => routeSet.has(e.to))) open.add(id);
    if (flips.echo === echo) for (const id of flips.ids) open.has(id) ? open.delete(id) : open.add(id);
    return open;
  }, [derived, routeSet, expandedState, graph, goal, within, flips, echo]);

  const goalReach = useMemo(() => reach(graph, goal, within), [graph, goal, within]);

  const traced = useMemo(() => {
    if (!selected || !trace || !graph.nodes.has(selected)) return null;
    const all = closure(graph, selected, trace === "rests" ? "prerequisites" : "consumers");
    return new Set([...all].filter((id) => goalReach.has(id)));
  }, [graph, selected, trace, goalReach]);

  const edgeObj = useMemo(() => (selectedEdge ? graph.edges.find((e) => e.key === selectedEdge) ?? null : null), [graph, selectedEdge]);

  // Whatever is selected, traced or lit from elsewhere is unfolded into view.
  useEffect(() => {
    if (derived) return;
    const targets = new Set<string>();
    if (selected && goalReach.has(selected)) targets.add(selected);
    if (traced) traced.forEach((id) => targets.add(id));
    if (echo) echo.forEach((id) => goalReach.has(id) && targets.add(id));
    if (edgeObj) [edgeObj.from, edgeObj.to].forEach((id) => goalReach.has(id) && targets.add(id));
    if (!targets.size) return;
    setExpanded((prev) => {
      const next = new Set(prev);
      let changed = expandTo(graph, goal, targets, next, within);
      if (edgeObj && goalReach.has(edgeObj.from) && edgeObj.from !== goal && !next.has(edgeObj.from)) {
        next.add(edgeObj.from);
        changed = true;
      }
      if (traced && trace === "rests") {
        for (const id of traced) {
          if (id !== goal && usesOf(graph, id, within).length && !next.has(id)) {
            next.add(id);
            changed = true;
          }
        }
      }
      return changed ? next : prev;
    });
  }, [derived, selected, traced, trace, echo, edgeObj, graph, goal, goalReach, within]);

  const visible = useMemo(() => visibleSet(graph, goal, expanded, within), [graph, goal, expanded, within]);
  const shownEdges = useMemo(() => visibleEdges(graph, goal, visible, expanded, within), [graph, goal, visible, expanded, within]);
  const skel = useMemo(() => transitiveReduction(visible, shownEdges), [visible, shownEdges]);

  // ---- Sizes and layout -------------------------------------------------------------

  const [heights, setHeights] = useState<Map<string, number>>(() => new Map());
  const committed = useRef<Built | null>(null);
  const committedGoal = useRef<string | null>(null);
  const pinRef = useRef<string | null>(null);

  const built: Built = useMemo(() => {
    const prev = committedGoal.current === `${goal}|${compact}` ? committed.current : null;
    let provisional = false;
    const size = (id: string): Size => {
      const node = graph.nodes.get(id)!;
      const isRoot = id === goal;
      const h = heights.get(id);
      if (h === undefined) provisional = true;
      return { w: widthOf(node, isRoot, compact, rootW), h: h ?? guessHeight(node, isRoot, compact) };
    };
    const pin = pinRef.current && visible.has(pinRef.current) ? pinRef.current : null;
    const nodes = [...visible];
    const { layout, plan } = layoutTree({ root: goal, nodes, edges: skel.edges, size, metrics, prev: prev?.layout ?? null, pin });
    return { layout, plan, skeleton: skel.edges, implied: skel.implied, provisional, pin };
  }, [graph, goal, visible, skel, heights, compact, metrics, rootW]);
  const layout = built.layout;

  // Cards that left: kept mounted while they move into their parent and fade.
  const renderedRef = useRef<Set<string>>(new Set());
  const exiting = useMemo(() => {
    const out = new Set<string>();
    for (const id of renderedRef.current) if (!layout.boxes.has(id) && graph.nodes.has(id)) out.add(id);
    return out;
  }, [layout, graph]);
  const [exitCleared, setExitCleared] = useState<Set<string> | null>(null);
  const exitShown = exitCleared === exiting ? new Set<string>() : exiting;

  // Edges that stop being drawn (now implied, or an end left) fade out; new ones fade in.
  const ghostsAndFresh = useMemo(() => {
    const prev = committed.current;
    const now = new Set(built.skeleton.map((e) => e.key));
    const ghosts: EngineEdge[] = [];
    const fresh = new Set<string>();
    if (prev && committedGoal.current === `${goal}|${compact}`) {
      const before = new Set(prev.skeleton.map((e) => e.key));
      for (const e of prev.skeleton) if (!now.has(e.key)) ghosts.push(e);
      for (const e of built.skeleton) if (!before.has(e.key)) fresh.add(e.key);
    }
    return { ghosts, fresh };
  }, [built, goal, compact]);

  // ---- Element registries (positions and paths are written per frame, not by React) ----

  const cardEls = useRef(new Map<string, HTMLElement>());
  const pathEls = useRef(new Map<string, SVGPathElement>());
  const cardRef = useCallback((id: string) => (el: HTMLElement | null) => {
    if (el) cardEls.current.set(id, el);
    else cardEls.current.delete(id);
  }, []);
  const refCache = useRef(new Map<string, (el: SVGPathElement | null) => void>());
  const pathRef = (key: string) => {
    let fn = refCache.current.get(key);
    if (!fn) {
      fn = (el: SVGPathElement | null) => {
        if (el) pathEls.current.set(key, el);
        else pathEls.current.delete(key);
      };
      refCache.current.set(key, fn);
    }
    return fn;
  };

  // ---- The clock -------------------------------------------------------------------

  const motion = useRef<Motion | null>(null);
  const shown = useRef(new Map<string, CardState>());
  const shownDummy = useRef(new Map<string, number>());
  const lastRouted = useRef<Routed | null>(null);
  const raf = useRef(0);
  const builtRef = useRef(built);
  builtRef.current = built;
  const ghostsRef = useRef(ghostsAndFresh);
  ghostsRef.current = ghostsAndFresh;
  const exitingRef = useRef(exiting);
  exitingRef.current = exiting;

  const applyView = useCallback((v: View) => {
    const wrap = wrapRef.current;
    const zoom = zoomRef.current;
    if (!wrap || !zoom) return;
    select(wrap).call(zoom.transform, zoomIdentity.translate(v.x, v.y).scale(v.k));
  }, []);

  const draw = useCallback(
    (now: number) => {
      const b = builtRef.current;
      const m = motion.current;
      const raw = m && m.dur > 0 ? Math.min(1, Math.max(0, (now - m.start) / m.dur)) : 1;
      const e = easeMove(raw);
      // Cards.
      const boxes = new Map<string, Rect>();
      const all = new Map<string, Rect>();
      const states = m ? m.to : new Map([...b.layout.boxes].map(([id, rect]) => [id, { rect, op: 1, sc: 1 }]));
      for (const [id, to] of states) {
        const from = m?.from.get(id) ?? to;
        const s: CardState = {
          rect: { x: lerp(from.rect.x, to.rect.x, e), y: lerp(from.rect.y, to.rect.y, e), w: to.rect.w, h: to.rect.h },
          op: lerp(from.op, to.op, e),
          sc: lerp(from.sc, to.sc, e),
        };
        shown.current.set(id, s);
        all.set(id, s.rect);
        if (b.layout.boxes.has(id)) boxes.set(id, s.rect);
        const el = cardEls.current.get(id);
        if (el) {
          el.style.transform = `translate(${s.rect.x}px, ${s.rect.y}px)${s.sc !== 1 ? ` scale(${s.sc})` : ""}`;
          el.style.opacity = s.op < 1 ? String(s.op) : "";
          // Entering cards grow out from behind the card that opened them.
          el.style.zIndex = m && raw < 1 && (m.entering.has(id) || s.op < 1) ? "0" : "";
        }
      }
      const dummyX = (key: string) => {
        const to = b.layout.dummies.get(key)!.x;
        const from = m?.dummyFrom.get(key) ?? to;
        const x = lerp(from, to, e);
        shownDummy.current.set(key, x);
        return x;
      };
      const routed = route(b.plan, { boxes, dummyX, ignoreRows: m && raw < 1 ? m.entering : undefined });
      lastRouted.current = routed;
      writePaths(routed, all, e);
      // Camera on the same clock.
      if (m?.view) {
        const vp = viewport();
        applyView(raw >= 1 ? m.view.to : lerpView(m.view.from, m.view.to, e, vp));
      }
      if (m && raw < 1) raf.current = requestAnimationFrame(draw);
      else if (m) {
        motion.current = null;
        raf.current = 0;
        setMoving(false);
        setExitCleared(exitingRef.current);
      }
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [],
  );

  function writePaths(routed: Routed, all: Map<string, Rect>, e: number) {
    const els = pathEls.current;
    const r = metrics.radius;
    const b = builtRef.current;
    const { fresh, ghosts } = ghostsRef.current;
    const busD = new Map<string, string>();
    const busF = new Map<string, string>();
    for (const pe of b.plan.edges.values()) {
      const re = routed.edges.get(pe.key);
      if (!re) continue;
      const d = roundedPath(re.points, r);
      const isFresh = fresh.has(pe.key);
      if (pe.bus) {
        const map = isFresh ? busF : busD;
        map.set(pe.from, (map.get(pe.from) ?? "") + d);
      }
      set(els, `edge:${pe.key}`, d, isFresh ? e : 1);
      set(els, `ov:${pe.key}`, d);
      set(els, `lit:${pe.key}`, d);
      set(els, `sel:${pe.key}`, d);
      set(els, `hit:${pe.key}`, roundedPath(re.own, r));
      if (pe.arrow) {
        const head = pe.bus ? routed.buses.get(pe.from)?.head : routed.heads.get(pe.key);
        if (head) {
          const hd = polygonPath(head);
          set(els, `ahead:${pe.key}`, hd, isFresh ? e : 1);
          set(els, `lithead:${pe.key}`, hd);
          set(els, `selhead:${pe.key}`, hd);
          set(els, `ovhead:${pe.key}`, hd);
        }
      }
      const j = re.junction;
      const rr = compact ? 2.5 : 3.25;
      set(els, `ring:${pe.key}`, `M${(j.x - rr).toFixed(1)},${j.y.toFixed(1)}a${rr},${rr} 0 1,0 ${2 * rr},0a${rr},${rr} 0 1,0 ${-2 * rr},0`, isFresh ? e : 1);
    }
    for (const [parent, rb] of routed.buses) {
      set(els, `bus:${parent}`, busD.get(parent) ?? "");
      set(els, `busf:${parent}`, busF.get(parent) ?? "", e);
      set(els, `head:${parent}`, polygonPath(rb.head), busD.has(parent) ? 1 : e);
      set(els, `hitstem:${parent}`, roundedPath(rb.stem, r));
      set(els, `ovstem:${parent}`, roundedPath(rb.stem, r));
    }
    for (const g of ghosts) {
      const c = all.get(g.to);
      const p = all.get(g.from);
      const el = els.get(`ghost:${g.key}`);
      if (!el) continue;
      if (!c || !p) {
        el.setAttribute("d", "");
        continue;
      }
      const cx = c.x + c.w / 2;
      const px = p.x + p.w / 2;
      const mid = (c.y + p.y + p.h) / 2;
      const pts: Pt[] = [
        { x: cx, y: c.y },
        { x: cx, y: mid },
        { x: px, y: mid },
        { x: px, y: p.y + p.h },
      ];
      el.setAttribute("d", roundedPath(pts, r));
      el.style.opacity = String(1 - e);
    }
  }

  function set(els: Map<string, SVGPathElement>, key: string, d: string, opacity?: number) {
    const el = els.get(key);
    if (!el) return;
    if (el.getAttribute("d") !== d) el.setAttribute("d", d);
    if (opacity !== undefined) el.style.opacity = opacity < 1 ? String(Math.max(0, opacity)) : "";
  }

  const viewport = (): Viewport => ({ width: sizeRef.current.width, height: sizeRef.current.height, insets: insetsRef.current });

  /** Move the camera on the shared clock: with a card motion that starts now, else on its own leg of the same curve. */
  const moveCamera = useCallback(
    (to: View, animate = true) => {
      const m = motion.current;
      if (!animate || reduced) {
        if (m) m.view = undefined;
        cameraOnly.current = null;
        applyView(to);
        return;
      }
      const now = performance.now();
      if (m && m.dur > 0 && now - m.start < 34) {
        m.view = { from: viewRef.current, to };
        cameraOnly.current = null;
        return;
      }
      if (m) m.view = undefined;
      cameraOnly.current = { start: now, from: viewRef.current, to };
      if (!cameraRaf.current) cameraRaf.current = requestAnimationFrame(cameraTick);
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [applyView, reduced],
  );
  const cameraOnly = useRef<{ start: number; from: View; to: View } | null>(null);
  const cameraRaf = useRef(0);
  const cameraTick = (now: number) => {
    const c = cameraOnly.current;
    if (!c) {
      cameraRaf.current = 0;
      return;
    }
    const raw = Math.min(1, (now - c.start) / MOVE_MS);
    applyView(raw >= 1 ? c.to : lerpView(c.from, c.to, easeMove(raw), viewport()));
    if (raw < 1) cameraRaf.current = requestAnimationFrame(cameraTick);
    else {
      cameraOnly.current = null;
      cameraRaf.current = 0;
    }
  };

  // Start a motion whenever the layout changes.
  const pendingCamera = useRef<null | ((l: Layout) => View | null)>(null);
  useLayoutEffect(() => {
    const now = performance.now();
    const prev = committed.current;
    const sameScene = !!prev && committedGoal.current === `${goal}|${compact}`;
    const from = new Map<string, CardState>();
    const to = new Map<string, CardState>();
    const entering = new Set<string>();
    const opener = (id: string): string | null => {
      if (built.pin && shown.current.has(built.pin)) return built.pin;
      // The nearest card above it that was already on screen.
      const seen = new Set([id]);
      const queue = [id];
      while (queue.length) {
        const at = queue.shift()!;
        for (const e of graph.in.get(at) ?? []) {
          if (seen.has(e.from)) continue;
          seen.add(e.from);
          if (shown.current.has(e.from) && !exitingRef.current.has(e.from)) return e.from;
          queue.push(e.from);
        }
      }
      return shown.current.has(goal) ? goal : null;
    };
    for (const [id, rect] of layout.boxes) {
      to.set(id, { rect, op: 1, sc: 1 });
      const cur = sameScene ? shown.current.get(id) : undefined;
      if (cur) {
        from.set(id, cur);
        if (motion.current?.entering.has(id) && cur.op < 1) entering.add(id);
      } else if (sameScene) {
        const o = opener(id);
        const or = o ? shown.current.get(o)?.rect : undefined;
        entering.add(id);
        if (or) from.set(id, { rect: { x: or.x + or.w / 2 - rect.w / 2, y: or.y + or.h / 2 - rect.h / 2, w: rect.w, h: rect.h }, op: 0, sc: 0.96 });
        else from.set(id, { rect, op: 0, sc: 0.96 });
      } else from.set(id, { rect, op: 1, sc: 1 });
    }
    for (const id of exiting) {
      const cur = shown.current.get(id);
      if (!cur) continue;
      // Into the parent's new rectangle.
      let target: Rect | undefined;
      if (built.pin && layout.boxes.has(built.pin)) target = layout.boxes.get(built.pin);
      if (!target) for (const e of graph.in.get(id) ?? []) if (layout.boxes.has(e.from)) target = layout.boxes.get(e.from);
      target ??= layout.boxes.get(goal)!;
      from.set(id, cur);
      to.set(id, { rect: { x: target.x + target.w / 2 - cur.rect.w / 2, y: target.y + target.h / 2 - cur.rect.h / 2, w: cur.rect.w, h: cur.rect.h }, op: 0, sc: 0.96 });
    }
    for (const id of [...shown.current.keys()]) if (!to.has(id)) shown.current.delete(id);
    const dummyFrom = new Map<string, number>();
    for (const [key, d] of layout.dummies) {
      const known = sameScene ? shownDummy.current.get(key) : undefined;
      if (known !== undefined) dummyFrom.set(key, known);
      else {
        // Between where its two ends start.
        const pe = built.plan.edges.get(d.edge)!;
        const a = from.get(pe.from)?.rect;
        const c = from.get(pe.to)?.rect;
        if (a && c) {
          const t = (d.rank - pe.rankFrom) / (pe.rankTo - pe.rankFrom);
          dummyFrom.set(key, lerp(a.x + a.w / 2, c.x + c.w / 2, t));
        }
      }
    }
    for (const key of [...shownDummy.current.keys()]) if (!layout.dummies.has(key)) shownDummy.current.delete(key);
    const animate = sameScene && !reduced;
    const before = motion.current;
    cancelAnimationFrame(raf.current);
    motion.current = { start: now, dur: animate ? MOVE_MS : 0, from, to, dummyFrom, entering };
    let camera: View | null = null;
    if (pendingCamera.current && ready) {
      camera = pendingCamera.current(layout);
      if (!built.provisional) pendingCamera.current = null;
    }
    if (camera) motion.current.view = { from: viewRef.current, to: camera };
    // A camera move that joined the previous (provisional) pass carries over.
    else if (before?.view && now - before.start < 60) motion.current.view = { from: before.view.from, to: before.view.to };
    if (animate) setMoving(true);
    draw(now);
    if (animate) raf.current = requestAnimationFrame(draw);
    renderedRef.current = new Set([...layout.boxes.keys(), ...exiting]);
    if (!built.provisional) {
      committed.current = built;
      committedGoal.current = `${goal}|${compact}`;
      pinRef.current = null;
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [built]);

  useEffect(() => () => cancelAnimationFrame(raf.current), []);

  // Redraw paths after any render (new overlay elements need their geometry now).
  useLayoutEffect(() => {
    if (!motion.current && lastRouted.current) {
      const all = new Map<string, Rect>();
      for (const [id, s] of shown.current) all.set(id, s.rect);
      writePaths(lastRouted.current, all, 1);
    }
  });

  // Measure every card before (re)layout settles: sizes come from the DOM.
  useLayoutEffect(() => {
    const next = new Map(heights);
    let changed = false;
    for (const id of layout.boxes.keys()) {
      const el = cardEls.current.get(id);
      if (!el) continue;
      const h = Math.ceil(el.offsetHeight);
      if (h > 0 && Math.abs((next.get(id) ?? -99) - h) > 1) {
        next.set(id, h);
        changed = true;
      }
    }
    if (changed) setHeights(next);
  });
  useLayoutEffect(() => {
    const observer = new ResizeObserver((entries) => {
      let changed = false;
      const updates = new Map<string, number>();
      for (const entry of entries) {
        const id = (entry.target as HTMLElement).dataset.card;
        if (!id) continue;
        const h = Math.ceil((entry.target as HTMLElement).offsetHeight);
        if (h > 0) updates.set(id, h);
      }
      setHeights((prev) => {
        const next = new Map(prev);
        for (const [id, h] of updates)
          if (Math.abs((prev.get(id) ?? -99) - h) > 1) {
            next.set(id, h);
            changed = true;
          }
        return changed ? next : prev;
      });
    });
    for (const el of cardEls.current.values()) observer.observe(el);
    return () => observer.disconnect();
  }, [layout]);

  // ---- Camera -----------------------------------------------------------------------

  const boundsOf = useCallback((l: Layout, ids: Iterable<string>, pad = 36): Bounds | null => {
    const b = { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity };
    for (const id of ids) {
      const box = l.boxes.get(id);
      if (!box) continue;
      b.x0 = Math.min(b.x0, box.x - pad);
      b.x1 = Math.max(b.x1, box.x + box.w + pad);
      b.y0 = Math.min(b.y0, box.y - pad);
      b.y1 = Math.max(b.y1, box.y + box.h + pad);
    }
    return Number.isFinite(b.x0) ? b : null;
  }, []);

  const floor = compact ? 0.75 : 0.6;
  const startView = useCallback(
    (l: Layout): View | null => {
      if (compact && echo?.size) {
        const b = boundsOf(l, [...echo].filter((id) => l.boxes.has(id)), 24);
        if (b) return fitBounds(b, viewport(), { min: 0.75, max: 1 });
      }
      const ids = [goal, ...usesOf(graph, goal, within).map((e) => e.to)];
      const b = boundsOf(l, ids, 40);
      if (!b) return null;
      const vp = viewport();
      const v = fitBounds(b, vp, { max: 1, min: compact ? 0.75 : 0.72, top: true });
      const availW = vp.width - vp.insets.left - vp.insets.right;
      const root = l.boxes.get(goal);
      // Wider than the screen at a readable zoom: keep the theorem itself centred.
      if (root && (b.x1 - b.x0) * v.k > availW) v.x = vp.insets.left + availW / 2 - (root.x + root.w / 2) * v.k;
      return v;
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [graph, goal, within, compact, echo, boundsOf],
  );

  /** Ask for a camera move computed on the next settled layout (or now, if nothing is pending). */
  const askCamera = useCallback(
    (fn: (l: Layout) => View | null, waitForLayout: boolean) => {
      if (waitForLayout) {
        pendingCamera.current = fn;
        return;
      }
      const v = fn(builtRef.current.layout);
      if (v) moveCamera(v);
    },
    [moveCamera],
  );

  const revealIds = useCallback(
    (ids: Iterable<string>, min = floor, pad = 28) =>
      (l: Layout) => {
        const b = boundsOf(l, ids, pad);
        return b ? ensureVisible(b, viewport(), viewRef.current, Math.min(viewRef.current.k, min)) : null;
      },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [boundsOf, floor],
  );

  useImperativeHandle(
    ref,
    () => ({
      fitAll: (animate = true) => {
        const b = layoutBounds(builtRef.current.layout);
        moveCamera(fitBounds({ x0: b.x0 - 40, y0: b.y0 - 40, x1: b.x1 + 40, y1: b.y1 + 40 }, viewport(), { max: 1, min: 0.2 }), animate);
      },
      fitNodes: (ids, animate = true) => {
        const list = [...ids];
        const fn = (l: Layout) => {
          const b = boundsOf(l, list, compact ? 24 : 40);
          return b ? fitBounds(b, viewport(), { max: 1, min: compact ? 0.75 : 0.35 }) : null;
        };
        if (list.every((id) => builtRef.current.layout.boxes.has(id))) {
          const v = fn(builtRef.current.layout);
          if (v) moveCamera(v, animate);
        } else pendingCamera.current = fn;
      },
      zoomBy: (factor) => {
        const v = viewRef.current;
        const vp = viewport();
        const px = vp.insets.left + (vp.width - vp.insets.left - vp.insets.right) / 2;
        const py = vp.insets.top + (vp.height - vp.insets.top - vp.insets.bottom) / 2;
        const k = Math.max(0.15, Math.min(1.8, v.k * factor));
        moveCamera({ k, x: px - ((px - v.x) / v.k) * k, y: py - ((py - v.y) / v.k) * k });
      },
      focusNode: (id) => cardEls.current.get(id)?.focus({ preventScroll: true }),
      expandAll: () => {
        pinRef.current = null;
        pendingCamera.current = (l) => {
          const b = layoutBounds(l);
          return fitBounds({ x0: b.x0 - 40, y0: b.y0 - 40, x1: b.x1 + 40, y1: b.y1 + 40 }, viewport(), { max: 1, min: 0.35 });
        };
        const all = new Set([...goalReach].filter((id) => id !== goal && usesOf(graph, id, within).length));
        if (derived) setFlips({ echo, ids: new Set([...all].filter((id) => !expanded.has(id))) });
        else setExpanded(all);
      },
      collapseAll: () => {
        pinRef.current = null;
        pendingCamera.current = startView;
        if (derived) setFlips({ echo, ids: new Set() });
        else setExpanded(new Set());
      },
    }),
    [boundsOf, moveCamera, goalReach, goal, graph, within, derived, echo, expanded, startView, compact],
  );

  useLayoutEffect(() => {
    const wrap = wrapRef.current!;
    const world = worldRef.current!;
    const behaviour = d3zoom<HTMLDivElement, unknown>()
      .scaleExtent([0.15, 1.8])
      .filter((event: Event) => {
        if (event.type === "dblclick" || event.type === "wheel") return false;
        const target = event.target as Element;
        if (target.closest?.("button, a, .card__body")) return false;
        return !(event as MouseEvent).button && !(event as MouseEvent).ctrlKey;
      })
      .on("zoom", (event: { transform: ZoomTransform; sourceEvent?: Event | null }) => {
        if (event.sourceEvent) {
          userMoved.current = true;
          if (motion.current) motion.current.view = undefined;
          cameraOnly.current = null;
          pendingCamera.current = null;
        }
        const t = event.transform;
        viewRef.current = { x: t.x, y: t.y, k: t.k };
        world.style.transform = `translate(${t.x}px, ${t.y}px) scale(${t.k})`;
        wrap.style.setProperty("--k", String(t.k));
      });
    zoomRef.current = behaviour;
    const s = select(wrap);
    s.call(behaviour);
    const onWheel = (event: WheelEvent) => {
      event.preventDefault();
      const t = viewRef.current;
      const looksLikeWheel = event.deltaMode === 1 || (Math.abs(event.deltaY) >= 40 && event.deltaX === 0 && Number.isInteger(event.deltaY));
      if (event.ctrlKey || (looksLikeWheel && !compact)) {
        const rect = wrap.getBoundingClientRect();
        const point: [number, number] = [event.clientX - rect.left, event.clientY - rect.top];
        s.call(behaviour.scaleBy, Math.pow(2, -event.deltaY * (event.deltaMode === 1 ? 0.05 : 0.0022) * (event.ctrlKey ? 3.2 : 1)), point);
      } else {
        // In the side pane a wheel scrolls the route rather than shrinking it.
        const unit = event.deltaMode === 1 ? 16 : 1;
        s.call(behaviour.translateBy, (-event.deltaX * unit) / t.k, (-event.deltaY * unit) / t.k);
      }
    };
    wrap.addEventListener("wheel", onWheel, { passive: false });
    const observer = new ResizeObserver(([entry]) => {
      const { width, height } = entry.contentRect;
      sizeRef.current = { width, height };
      setPaneW(Math.round(width));
      if (width > 10 && height > 10) setReady(true);
    });
    observer.observe(wrap);
    return () => {
      observer.disconnect();
      wrap.removeEventListener("wheel", onWheel);
      s.on(".zoom", null);
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // First frame and goal changes: the theorem and what it uses, top-aligned.
  const fittedGoal = useRef<string | null>(null);
  const userMoved = useRef(false);
  const rootH = layout.boxes.get(goal)?.h ?? 0;
  useEffect(() => {
    if (!ready) return;
    if (fittedGoal.current !== goal) {
      const first = fittedGoal.current === null;
      fittedGoal.current = goal;
      userMoved.current = false;
      const v = startView(layout);
      if (v) moveCamera(v, !first);
    } else if (!userMoved.current && !selected && !moving && !(compact && echo?.size)) {
      const v = startView(layout);
      if (v) moveCamera(v, false);
    }
    // Refit while the goal card settles its height.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [ready, goal, rootH]);

  // In the side pane, a new passage frames its lit cards.
  const echoKey = echo ? [...echo].sort().join("|") : "";
  const lastEcho = useRef<string | null>(null);
  useLayoutEffect(() => {
    if (!compact || !ready || !echo?.size) return;
    if (lastEcho.current === echoKey) return;
    if (![...echo].some((id) => layout.boxes.has(id))) return;
    lastEcho.current = echoKey;
    const frame = (l: Layout) => {
      const b = boundsOf(l, [...echo].filter((id) => l.boxes.has(id)), 24);
      return b ? fitBounds(b, viewport(), { min: 0.75, max: 1 }) : null;
    };
    if (built.provisional) {
      pendingCamera.current = frame;
      return;
    }
    const v = frame(layout);
    if (v) moveCamera(v);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [compact, ready, echoKey, layout]);

  // Keep what you asked for on screen: never recentre what is already visible.
  const lastAsk = useRef("");
  const askedIds = (): { ids: string[]; min: number } => {
    if (edgeObj) return { ids: [edgeObj.from, edgeObj.to], min: floor };
    if (traced && selected) return { ids: [...traced], min: 0.45 };
    return { ids: selected ? [selected] : [], min: floor };
  };
  useEffect(() => {
    if (!ready) return;
    const key = `${selected ?? ""}|${trace ?? ""}|${selectedEdge ?? ""}|${insets.right}|${insets.bottom}`;
    if (key === lastAsk.current) return;
    const { ids, min } = askedIds();
    if (!ids.length) {
      lastAsk.current = key;
      return;
    }
    if (!ids.every((id) => layout.boxes.has(id)) || built.provisional) return;
    lastAsk.current = key;
    const v = revealIds(ids, min)(layout);
    if (!v) return;
    moveCamera(v);
  }, [ready, selected, trace, traced, selectedEdge, edgeObj, layout, built.provisional, insets.right, insets.bottom, revealIds, moveCamera, floor]);

  // A layout motion that starts while the camera is heading somewhere replaces
  // it; once everything has settled, make sure the request is still met.
  useEffect(() => {
    if (!ready || moving || built.provisional) return;
    const { ids, min } = askedIds();
    if (!ids.length || !ids.every((id) => layout.boxes.has(id))) return;
    const v = revealIds(ids, min)(layout);
    if (v) moveCamera(v);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [moving, ready, built.provisional]);

  // ---- Interaction ------------------------------------------------------------------

  const toggle = useCallback(
    (id: string) => {
      if (id === goal || usesOf(graph, id, within).length === 0) return;
      pinRef.current = id;
      const opening = !expanded.has(id);
      if (opening) {
        askCamera((l) => {
          const fresh = [...l.boxes.keys()].filter((x) => !committed.current?.layout.boxes.has(x));
          return revealIds([id, ...fresh], 0.6)(l);
        }, true);
      } else pendingCamera.current = null;
      if (derived) {
        setFlips((prev) => {
          const ids = new Set(prev.echo === echo ? prev.ids : []);
          ids.has(id) ? ids.delete(id) : ids.add(id);
          return { echo, ids };
        });
        return;
      }
      setExpanded((prev) => {
        const next = new Set(prev);
        if (next.has(id)) next.delete(id);
        else next.add(id);
        return next;
      });
    },
    [goal, graph, within, expanded, derived, echo, askCamera, revealIds],
  );

  const neighbours = (id: string) => {
    const ups: string[] = [];
    const downs: string[] = [];
    for (const e of built.skeleton) {
      if (e.to === id) ups.push(e.from);
      if (e.from === id) downs.push(e.to);
    }
    return { ups, downs };
  };

  const moveFocus = (from: string, key: string) => {
    const box = layout.boxes.get(from);
    if (!box) return;
    const { ups, downs } = neighbours(from);
    const centre = (b: Rect) => ({ x: b.x + b.w / 2, y: b.y + b.h / 2 });
    const c0 = centre(box);
    let candidates: string[] = [];
    if (key === "ArrowDown") candidates = downs;
    else if (key === "ArrowUp") candidates = ups;
    else {
      const r = layout.rank.get(from);
      candidates = [...layout.boxes.keys()].filter((id) => layout.rank.get(id) === r && (key === "ArrowLeft" ? centre(layout.boxes.get(id)!).x < c0.x : centre(layout.boxes.get(id)!).x > c0.x));
    }
    if (!candidates.length) return;
    candidates.sort((a, b) => {
      const A = centre(layout.boxes.get(a)!);
      const B = centre(layout.boxes.get(b)!);
      return Math.hypot(A.x - c0.x, A.y - c0.y) - Math.hypot(B.x - c0.x, B.y - c0.y);
    });
    const next = candidates[0];
    setFocusId(next);
    requestAnimationFrame(() => cardEls.current.get(next)?.focus({ preventScroll: true }));
    const v = revealIds([next])(layout);
    if (v) moveCamera(v);
  };

  const onCardKey = (id: string, event: React.KeyboardEvent) => {
    if (event.target !== event.currentTarget) return;
    if (event.key.startsWith("Arrow")) {
      event.preventDefault();
      moveFocus(id, event.key);
    } else if (event.key === "Enter") {
      event.preventDefault();
      onSelect(id);
    } else if (event.key === " ") {
      event.preventDefault();
      toggle(id);
    } else if (event.key.toLowerCase() === "t") {
      event.preventDefault();
      onTrace(id);
    }
  };

  const setHovered = (id: string | null) => {
    setHover(id);
    onHover?.(id);
  };

  // Edge hover: a short delay in, immediate out, never during motion.
  const tipTimer = useRef(0);
  const pointerAt = (event: React.PointerEvent) => {
    const rect = wrapRef.current!.getBoundingClientRect();
    return { x: event.clientX - rect.left, y: event.clientY - rect.top };
  };
  const enterEdge = (key: string, event: React.PointerEvent) => {
    setHoverEdge(key);
    const at = pointerAt(event);
    window.clearTimeout(tipTimer.current);
    tipTimer.current = window.setTimeout(() => setTip({ key, ...at }), 120);
  };
  const moveEdge = (key: string, event: React.PointerEvent) => {
    const at = pointerAt(event);
    setTip((t) => (t && t.key === key ? { key, ...at } : t));
    window.clearTimeout(tipTimer.current);
    tipTimer.current = window.setTimeout(() => setTip({ key, ...at }), 120);
  };
  const leaveEdge = () => {
    window.clearTimeout(tipTimer.current);
    setTip(null);
    setHoverEdge(null);
  };
  useEffect(() => () => window.clearTimeout(tipTimer.current), []);

  // ---- Light ------------------------------------------------------------------------

  const edgeByKey = useMemo(() => new Map(graph.edges.map((e) => [e.key, e])), [graph]);

  const hoverTouch = useMemo(() => {
    if (!hoverEdge) return null;
    if (hoverEdge.startsWith("bus:")) {
      const parent = hoverEdge.slice(4);
      const ids = new Set([parent]);
      const keys = new Set<string>();
      for (const e of built.skeleton) if (e.from === parent && e.kind === "supports") {
        ids.add(e.to);
        keys.add(e.key);
      }
      return { ids, keys };
    }
    const e = edgeByKey.get(hoverEdge);
    return e ? { ids: new Set([e.from, e.to]), keys: new Set([e.key]) } : null;
  }, [hoverEdge, built, edgeByKey]);

  const near = useMemo(() => {
    const id = selected;
    if (!id || !layout.boxes.has(id)) return null;
    const set = new Set([id]);
    for (const e of built.skeleton) {
      if (e.from === id) set.add(e.to);
      if (e.to === id) set.add(e.from);
    }
    return set;
  }, [selected, built, layout]);

  const litKeys = useMemo(() => {
    if (!traced) return new Set<string>();
    return new Set(built.skeleton.filter((e) => traced.has(e.from) && traced.has(e.to)).map((e) => e.key));
  }, [traced, built]);

  // Draw-on timing: rank by rank, from the deepest up to the selection ("rests"),
  // or from the selection up to the goal ("uses"); at most about 900 ms in all.
  const drawTiming = useMemo(() => {
    const t = new Map<string, { delay: number; dur: number }>();
    if (!litKeys.size || !selected) return t;
    const ranks = [...litKeys].map((k) => layout.rank.get(built.plan.edges.get(k)!.to)!);
    const lo = Math.min(...ranks);
    const hi = Math.max(...ranks);
    const levels = hi - lo + 1;
    const dur = 300;
    const stagger = levels > 1 ? Math.min(140, (900 - dur) / (levels - 1)) : 0;
    for (const k of litKeys) {
      const r = layout.rank.get(built.plan.edges.get(k)!.to)!;
      // Deepest first for "rests"; for "uses" the selection is the deepest lit card.
      t.set(k, { delay: (hi - r) * stagger, dur });
    }
    return t;
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [litKeys, trace, selected]);

  const traceKey = `${selected ?? ""}|${trace ?? ""}|${goal}`;
  // The draw-on waits until the cards the trace unfolds have settled: one action, then the next.
  const [litShown, setLitShown] = useState<string | null>(null);
  const traceReady = !!traced && [...traced].every((id) => layout.boxes.has(id)) && !moving && !built.provisional;
  useEffect(() => {
    if (!traced) setLitShown(null);
    else if (traceReady) setLitShown(traceKey);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [traced, traceReady]);
  const litOn = !!traced && litShown === traceKey;

  const echoOn = (echo?.size ?? 0) > 0;
  const cardClass = (id: string, node: ArgNode, leaf: boolean): string => {
    const parts = ["card", `card--${node.kind}`, `role-${lensRole(node, lens ?? null)}`];
    if (id === goal) parts.push("card--root");
    if (leaf && id !== goal) parts.push("card--leaf");
    if (id === selected) parts.push("is-selected");
    if (id === hover || hoverTouch?.ids.has(id)) parts.push("is-hover");
    if (edgeObj && (edgeObj.from === id || edgeObj.to === id)) parts.push("is-edge-end");
    if (traced && litOn) parts.push(traced.has(id) ? "is-traced" : "is-dim");
    else if (near && id !== selected && near.has(id)) parts.push("is-near");
    else if (near && !near.has(id) && !edgeObj) parts.push("is-quiet");
    if (echoOn) parts.push(echo!.has(id) ? "is-echo" : compact && within ? "" : "is-quiet");
    if (node.status === "open") parts.push("is-open");
    if (exitShown.has(id)) parts.push("is-exiting");
    return parts.filter(Boolean).join(" ");
  };

  const baseDim = litOn || !!edgeObj || (echoOn && !(compact && within));
  const emphasised = useMemo(() => {
    const keys = new Set<string>();
    const touch = (id: string | null | undefined) => {
      if (!id) return;
      for (const e of built.skeleton) if (e.from === id || e.to === id) keys.add(e.key);
    };
    if (!traced) touch(selected);
    touch(hover);
    hoverTouch?.keys.forEach((k) => keys.add(k));
    return keys;
  }, [built, selected, hover, hoverTouch, traced]);

  const roving = focusId && layout.boxes.has(focusId) ? focusId : selected && layout.boxes.has(selected) ? selected : goal;
  const bounds = layoutBounds(layout);

  const cardIds = [...layout.boxes.keys(), ...[...exitShown].filter((id) => !layout.boxes.has(id))];
  const tipEdge = tip && !moving ? tip : null;

  return (
    <div
      ref={wrapRef}
      className={`tree${compact ? " tree--compact" : ""}${rootW < 700 ? " tree--narrow" : ""}${moving ? " tree--moving" : ""}${traced ? " tree--traced" : ""}${intro ? " tree--intro" : ""}${baseDim ? " tree--dim" : ""}`}
      onClick={(event) => {
        if ((event.target as Element).closest?.(".card, button, a, .hit")) return;
        if (selected) onSelect(null);
        if (selectedEdge) onEdgeSelect?.(null);
      }}
    >
      <div ref={worldRef} className="tree__world" style={{ width: Math.max(1, bounds.x1), height: Math.max(1, bounds.y1) }}>
        <svg className="tree__links" width={1} height={1} aria-hidden="true">
          <g className="links">
            {[...built.plan.buses.keys()].map((parent) => (
              <g key={parent}>
                <path ref={pathRef(`bus:${parent}`)} className="link link--supports" />
                <path ref={pathRef(`busf:${parent}`)} className="link link--supports" />
              </g>
            ))}
            {[...built.plan.edges.values()]
              .filter((pe) => !pe.bus)
              .map((pe) => (
                <path key={pe.key} ref={pathRef(`edge:${pe.key}`)} className={`link link--${pe.kind}`} />
              ))}
            {ghostsAndFresh.ghosts.map((g) => (
              <path key={g.key} ref={pathRef(`ghost:${g.key}`)} className={`link link--${g.kind} link--ghost`} />
            ))}
          </g>
          <g className="links-over">
            {[...emphasised].filter((k) => built.plan.edges.has(k) && !litKeys.has(k)).map((k) => (
              <path key={k} ref={pathRef(`ov:${k}`)} className={`link link--${built.plan.edges.get(k)!.kind} link--near`} />
            ))}
          </g>
          <g className="links-lit" key={traceKey}>
            {[...(litOn ? litKeys : [])].map((k) => {
              const t = drawTiming.get(k) ?? { delay: 0, dur: 300 };
              return (
                <path
                  key={k}
                  ref={pathRef(`lit:${k}`)}
                  pathLength={1}
                  className={`link link--${built.plan.edges.get(k)!.kind} link--lit`}
                  style={{ ["--d" as string]: `${t.delay}ms`, ["--dur" as string]: `${t.dur}ms` }}
                />
              );
            })}
          </g>
          {edgeObj && built.plan.edges.has(edgeObj.key) && (
            <g className="links-sel">
              <path ref={pathRef(`sel:${edgeObj.key}`)} className={`link link--${edgeObj.kind} link--selected`} />
            </g>
          )}
          <g className="hits">
            {[...built.plan.edges.values()]
              .sort((a, b) => Number(a.bus) - Number(b.bus))
              .map((pe) => (
                <path
                  key={pe.key}
                  ref={pathRef(`hit:${pe.key}`)}
                  className="hit"
                  onPointerEnter={(event) => enterEdge(pe.key, event)}
                  onPointerMove={(event) => moveEdge(pe.key, event)}
                  onPointerLeave={leaveEdge}
                  onClick={(event) => {
                    event.stopPropagation();
                    onEdgeSelect?.(pe.key);
                  }}
                />
              ))}
            {[...built.plan.buses.keys()].map((parent) => (
              <path
                key={parent}
                ref={pathRef(`hitstem:${parent}`)}
                className="hit"
                onPointerEnter={(event) => enterEdge(`bus:${parent}`, event)}
                onPointerMove={(event) => moveEdge(`bus:${parent}`, event)}
                onPointerLeave={leaveEdge}
                onClick={(event) => {
                  event.stopPropagation();
                  onSelect(parent);
                }}
              />
            ))}
          </g>
        </svg>
        {cardIds.map((id) => {
          const node = graph.nodes.get(id)!;
          const all = usesOf(graph, id);
          const uses = usesOf(graph, id, within);
          const outside = all.length - uses.length;
          const shownUses = uses.filter((e) => layout.boxes.has(e.to)).length;
          const isRoot = id === goal;
          const open = expanded.has(id);
          const leaf = uses.length === 0;
          return (
            <div
              key={id}
              ref={cardRef(id)}
              data-card={id}
              data-region={node.region}
              data-slot={node.origin.slot}
              data-kind={node.kind}
              className={cardClass(id, node, leaf)}
              style={{ width: widthOf(node, isRoot, compact, rootW), ["--rank" as string]: layout.rank.get(id) ?? 0 }}
              role="button"
              tabIndex={id === roving ? 0 : -1}
              aria-pressed={id === selected}
              aria-expanded={!isRoot && uses.length ? open : undefined}
              aria-label={`${node.label}. ${kindName(node.kind)}.${all.length ? ` Uses ${all.length}.` : " Taken from its source."}`}
              onClick={(event) => {
                if ((event.target as Element).closest?.("button, a")) return;
                if (event.detail >= 2) toggle(id);
                else onSelect(id);
              }}
              onKeyDown={(event) => onCardKey(id, event)}
              onFocus={() => setFocusId(id)}
              onPointerEnter={() => setHovered(id)}
              onPointerLeave={() => setHovered(null)}
            >
              {isRoot && !compact ? (
                <div className="card__root">
                  <p className="card__kind">
                    <span className="region-dot" aria-hidden="true" />
                    {kindName(node.kind)}
                  </p>
                  <p className="card__title">{node.label}</p>
                  {rootContent && <div className="card__theorem card__body">{rootContent}</div>}
                </div>
              ) : (
                <>
                  {node.kind !== "claim" && (
                    <p className="card__kind">
                      <span className="region-dot" aria-hidden="true" />
                      {kindName(node.kind)}
                    </p>
                  )}
                  <p className={`card__label${node.kind === "declaration" ? " lean" : ""}`}>
                    {node.kind === "declaration" ? <LeanName name={node.label} /> : node.label}
                  </p>
                  <div className="card__foot">
                    {uses.length > 0 && !isRoot ? (
                      <button
                        type="button"
                        className={`card__unfold${open ? " is-open" : ""}`}
                        aria-expanded={open}
                        tabIndex={-1}
                        onClick={(event) => {
                          event.stopPropagation();
                          toggle(id);
                        }}
                      >
                        <svg viewBox="0 0 10 10" width="9" height="9" aria-hidden="true">
                          <path d={open ? "M2 6.5 L5 3.5 L8 6.5" : "M2 3.5 L5 6.5 L8 3.5"} fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
                        </svg>
                        {open ? "Fold" : `Uses ${uses.length}`}
                        {!open && outside > 0 && <span className="card__shown"> · {outside} outside</span>}
                        {!open && !outside && shownUses > 0 && shownUses < uses.length && <span className="card__shown"> ({shownUses} shown)</span>}
                      </button>
                    ) : !isRoot ? (
                      <span className="card__leaf">{outside > 0 ? `Uses ${outside} outside` : node.kind === "assumption" ? "Assumed" : "Starting point"}</span>
                    ) : null}
                    <span className="card__source" title={`${node.origin.label}${node.origin.locator ? `: ${node.origin.locator}` : ""}`}>
                      <span className="card__swatch" aria-hidden="true" />
                      {node.origin.place ?? node.origin.label}
                    </span>
                  </div>
                </>
              )}
            </div>
          );
        })}
        <svg className="tree__heads" width={1} height={1} aria-hidden="true">
          <g className="heads">
            {[...built.plan.buses.keys()].map((parent) => (
              <path key={parent} ref={pathRef(`head:${parent}`)} className="head" />
            ))}
            {[...built.plan.edges.values()]
              .filter((pe) => !pe.bus && pe.arrow)
              .map((pe) => (
                <path key={pe.key} ref={pathRef(`ahead:${pe.key}`)} className={`head head--${pe.kind}`} />
              ))}
            {[...built.plan.edges.values()]
              .filter((pe) => pe.bus && edgeByKey.get(pe.key)?.application)
              .map((pe) => (
                <path key={pe.key} ref={pathRef(`ring:${pe.key}`)} className="ring" />
              ))}
          </g>
          <g className="heads-over">
            {[...emphasised].filter((k) => built.plan.edges.get(k)?.arrow && !litKeys.has(k)).map((k) => (
              <path key={k} ref={pathRef(`ovhead:${k}`)} className="head head--near" />
            ))}
          </g>
          <g className="heads-lit" key={traceKey}>
            {[...(litOn ? litKeys : [])].filter((k) => built.plan.edges.get(k)!.arrow).map((k) => {
              const t = drawTiming.get(k) ?? { delay: 0, dur: 300 };
              return <path key={k} ref={pathRef(`lithead:${k}`)} className="head head--lit" style={{ ["--d" as string]: `${t.delay + t.dur - 40}ms` }} />;
            })}
          </g>
          {edgeObj && built.plan.edges.get(edgeObj.key)?.arrow && <path ref={pathRef(`selhead:${edgeObj.key}`)} className="head head--lit" />}
        </svg>
      </div>
      {tipEdge && <EdgeTip tip={tipEdge} graph={graph} edgeByKey={edgeByKey} skeleton={built.skeleton} wrap={wrapRef.current} compact={compact} />}
    </div>
  );
});

// ---- Edge tooltip -------------------------------------------------------------------------

function relationLine(graph: ArgGraph, e: ArgEdge): string {
  const label = (id: string) => graph.nodes.get(id)?.label ?? id;
  if (e.kind === "assumes") return `${label(e.from)} assumes ${label(e.to)}`;
  if (e.kind === "formalizes") {
    const decl = graph.nodes.get(e.to)?.kind === "declaration" ? e.to : e.from;
    const claim = decl === e.to ? e.from : e.to;
    return `${label(decl)} states ${label(claim)} in Lean`;
  }
  return `${label(e.to)} helps prove ${label(e.from)}`;
}

function statusLine(status: string | undefined, shared: boolean | undefined): string | null {
  if (!status) return null;
  const base =
    status === "not_run"
      ? "Recorded from the sources; not independently reviewed"
      : status === "passed"
        ? "Recorded from the sources; the review passed"
        : status === "failed"
          ? "Recorded from the sources; the review failed"
          : `Recorded from the sources; review ${status.replace(/_/g, " ")}`;
  return shared ? `${base}. Shared with other steps.` : `${base}.`;
}

function EdgeTip({ tip, graph, edgeByKey, skeleton, wrap, compact }: { tip: { key: string; x: number; y: number }; graph: ArgGraph; edgeByKey: Map<string, ArgEdge>; skeleton: EngineEdge[]; wrap: HTMLDivElement | null; compact: boolean }) {
  const ref = useRef<HTMLDivElement>(null);
  const [pos, setPos] = useState<{ left: number; top: number } | null>(null);
  useLayoutEffect(() => {
    const el = ref.current;
    if (!el || !wrap) return;
    const W = wrap.clientWidth;
    const H = wrap.clientHeight;
    const w = el.offsetWidth;
    const h = el.offsetHeight;
    // Beside the pointer, away from the (mostly vertical) edge; flipped to stay inside.
    let left = tip.x + 18;
    let top = tip.y - h / 2;
    if (left + w > W - 8) left = tip.x - 18 - w;
    left = Math.max(8, Math.min(W - w - 8, left));
    top = Math.max(8, Math.min(H - h - 8, top));
    setPos({ left, top });
  }, [tip, wrap]);
  let body: ReactNode;
  if (tip.key.startsWith("bus:")) {
    const parent = tip.key.slice(4);
    const n = skeleton.filter((e) => e.from === parent && e.kind === "supports").length;
    body = <p className="edge-tip__rel">{`${n === 1 ? "One result helps" : `${n} results help`} prove ${graph.nodes.get(parent)?.label ?? parent}`}</p>;
  } else {
    const e = edgeByKey.get(tip.key);
    if (!e) return null;
    body = (
      <>
        <p className="edge-tip__rel">{relationLine(graph, e)}</p>
        {e.warrant?.text && <p className="edge-tip__warrant">{e.warrant.text}</p>}
        {e.application && <p className="edge-tip__app">Applies a conditional result; this step supplies some of its premises.</p>}
        {statusLine(e.warrant?.status, e.warrant?.shared) && <p className="edge-tip__status">{statusLine(e.warrant?.status, e.warrant?.shared)}</p>}
      </>
    );
  }
  return (
    <div ref={ref} className={`edge-tip${compact ? " edge-tip--compact" : ""}`} role="tooltip" style={pos ? { left: pos.left, top: pos.top } : { left: -9999, top: 0 }}>
      {body}
    </div>
  );
}

/** Region membership used for colour; re-exported for the page key. */
export { goalFor } from "./treeModel";
export { pathFromGoal };
// Kept for callers that draw a single arrowhead elsewhere.
export { arrowHead };

/** A Lean name may break after its dots and underscores, never mid-word; copying it stays exact. */
function LeanName({ name }: { name: string }) {
  const parts = name.split(/(?<=[._])/);
  return (
    <>
      {parts.map((part, i) => (
        <span key={i}>
          {part}
          {i < parts.length - 1 && <wbr />}
        </span>
      ))}
    </>
  );
}

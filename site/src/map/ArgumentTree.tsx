// The argument as a map you unfold. The goal sits at the top as a plate with
// the theorem itself; beneath it are the results it uses, each a card with its
// name in words. Open a card's inputs (its "Inputs" button, a double-click, or
// Space) to see what that result uses, down to the records with no recorded
// inputs. Each line runs from a result up into the result it helps establish,
// typed by colour and pattern: recorded support, explicit assumption, recorded
// Lean correspondence. The underlying graph is not a tree: a result used
// several times is drawn once. The drawing is simplified only where a longer
// chain of recorded support already joins two records, and says so.
//
// Two scales, three representations (DESIGN.md): the camera never shrinks a
// card's prose below reading size. Past k = 0.8 a card shows its title alone at
// a constant 13px on screen; past k = 0.5 it becomes a mark in its source
// colour, and screen-space labels name the goal, the selection and the record
// under the pointer. "Steps" opens at k = 1; "Overview" fits the whole goal.
//
// Layout, connectors and motion are this project's own engine (./engine): a
// layered layout, an orthogonal connector router planned once per layout and
// routed every frame, and one animation clock for cards, connectors and camera.
// Camera input: d3-zoom. Screen-space parts (edge chips, labels, notes) live
// in ./canvas.

import { forwardRef, useCallback, useEffect, useId, useImperativeHandle, useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import { select } from "d3-selection";
import { zoom as d3zoom, zoomIdentity, type ZoomBehavior, type ZoomTransform } from "d3-zoom";
import type { Stage } from "../api/types";
import { argumentProjection, closure, lensRole, type ArgEdge, type ArgGraph, type ArgNode } from "../model/graph";
import type { Trace } from "../app/router";
import { kindName } from "./labels";
import { TREE_KINDS, expandTo, pathFromGoal, reach, routeTo, usesOf, visibleEdges, visibleSet } from "./treeModel";
import { transitiveReduction } from "./engine/skeleton";
import { consumerOf, edgeKeyOf, layoutScope, recordOf, splitSharedLeaves } from "./engine/occurrences";
import { layoutBounds, layoutTree } from "./engine/layout";
import { arrowHead, polygonPath, roundedPath, route, type Plan, type Pt, type Routed } from "./engine/router";
import { fitBounds, frameBox, lerpView, revealBox, type Bounds, type View, type Viewport } from "./engine/camera";
import { CAMERA_MS, MOVE_MS, easeMove, lerp } from "./engine/motion";
import { METRICS, METRICS_COMPACT, type EngineEdge, type Layout, type Rect, type Size } from "./engine/types";
import { COMPACT_FLOOR, MAX_K, MIN_K, STEPS_FLOOR, STEPS_K, repFor, type MapMode, type Rep } from "./canvas/representation";
import type { MapScene } from "./canvas/scene";
import { useReducedMotion } from "./canvas/useReducedMotion";
import { SIDES, beyond, chipAt, chipText, freeSpot, panToward, sameBeyond, screenRects, type Beyond, type Side } from "./canvas/chips";
import { traceTiming } from "./canvas/trace";
import { EdgeTip, type TipState } from "./canvas/EdgeTip";
import { SimplifiedMap } from "./canvas/SimplifiedMap";
import "./tree.css";

export type { MapScene } from "./canvas/scene";
export type { MapMode } from "./canvas/representation";

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
  getScene(): MapScene;
  /** Apply a remembered scene at once, before any automatic framing. */
  restoreScene(scene: MapScene): void;
  /** Commit the unfolding that shows these records, then frame them. */
  revealIds(ids: readonly string[]): void;
  /** Move keyboard focus to a drawn card; false when it is not drawn. */
  focusCard(id: string): boolean;
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
  /**
   * In the side pane (compact): the records of the passage being read; the
   * tree opens the route to them. On the map page: a transient preview, as
   * `previewIds` (kept until every caller passes previewIds).
   */
  echo?: ReadonlySet<string> | null;
  /** Records lit from elsewhere (a passage or ribbon under the pointer). Tints only; never unfolds or moves. */
  previewIds?: ReadonlySet<string> | null;
  insets: Insets;
  intro?: boolean;
  compact?: boolean;
  /** "steps" reads at k = 1; "overview" fits the whole goal. Uncontrolled when omitted. */
  mode?: MapMode;
  onModeChange?(mode: MapMode): void;
  /** After layout and camera settle (including the end of a pan or zoom). */
  onSceneSettled?(scene: MapScene): void;
  /** The body of the goal's plate: the theorem as a paper states it, and its checks. */
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

/** World widths. Narrow enough that a goal's first row usually reads at k = 1 on a laptop. */
function widthOf(node: ArgNode, isRoot: boolean, compact: boolean, rootW: number): number {
  if (isRoot) return compact ? 260 : rootW;
  if (compact) return 184;
  if (node.kind === "declaration") return 196;
  return 176;
}

/** Layout ids of each record, per layout. */
const lidCache = new WeakMap<Layout, Map<string, string[]>>();
function lidsOf(l: Layout, record: string): string[] {
  let m = lidCache.get(l);
  if (!m) {
    m = new Map();
    for (const lid of l.boxes.keys()) {
      const r = recordOf(lid);
      if (!m.has(r)) m.set(r, []);
      m.get(r)!.push(lid);
    }
    lidCache.set(l, m);
  }
  return m.get(record) ?? [];
}

function guessHeight(node: ArgNode, isRoot: boolean, compact: boolean): number {
  if (isRoot) return compact ? 76 : 300;
  if (compact) return 62;
  return node.kind === "declaration" ? 112 : 124;
}

function hashSet(set: ReadonlySet<string>): string {
  let h = 0;
  for (const id of [...set].sort()) for (let i = 0; i < id.length; i++) h = (Math.imul(h, 31) + id.charCodeAt(i)) | 0;
  return (h >>> 0).toString(36);
}

/** The graph with only the edges live in the goal's scoped argument (a premise an application supplies is not drawn back in). */
function scopedGraph(graph: ArgGraph, goal: string): ArgGraph {
  let live: Set<string>;
  try {
    live = argumentProjection(graph, [goal]).edges;
  } catch {
    return graph;
  }
  const keep = (e: ArgEdge) => !TREE_KINDS.has(e.kind) || live.has(e.key);
  if (graph.edges.every(keep)) return graph;
  const filter = (m: Map<string, ArgEdge[]>) => new Map([...m].map(([k, list]) => [k, list.filter(keep)]));
  return { ...graph, edges: graph.edges.filter(keep), out: filter(graph.out), in: filter(graph.in) };
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
  /** Drawn edges between layout ids (records, or occurrences of shared leaves); keys are drawn keys. */
  skeleton: EngineEdge[];
  /** Records drawn as several occurrences, with their number of drawn consumers. */
  shared: Map<string, number>;
  implied: Set<string>;
  provisional: boolean;
  pin: string | null;
}

export const ArgumentTree = forwardRef<MapViewHandle, TreeProps>(function ArgumentTree(props, ref) {
  const { graph: fullGraph, selected, trace, lens, echo, insets, intro, compact = false, rootContent, onSelect, onTrace, onHover, selectedEdge, onEdgeSelect, within } = props;
  const goal = props.goal && fullGraph.nodes.has(props.goal) ? props.goal : (fullGraph.regions[0]?.goal ?? fullGraph.goals[0]);
  const graph = useMemo(() => scopedGraph(fullGraph, goal), [fullGraph, goal]);
  const metrics = compact ? METRICS_COMPACT : METRICS;
  const uid = useId().replace(/[^a-zA-Z0-9_-]/g, "");
  const wrapRef = useRef<HTMLDivElement>(null);
  const worldRef = useRef<HTMLDivElement>(null);
  const zoomRef = useRef<ZoomBehavior<HTMLDivElement, unknown> | null>(null);
  const viewRef = useRef<View>({ x: 0, y: 0, k: 1 });
  const sizeRef = useRef({ width: 1, height: 1 });
  const insetsRef = useRef(insets);
  insetsRef.current = insets;
  const [ready, setReady] = useState(false);
  const readyRef = useRef(false);
  readyRef.current = ready;
  // The plate narrows on a small screen so it reads whole at k = 1.
  const [paneW, setPaneW] = useState(0);
  const [paneH, setPaneH] = useState(0);
  const rootW = paneW > 0 && paneW < 860 ? Math.max(300, Math.min(800, Math.floor(paneW - 32))) : 800;
  const [hover, setHover] = useState<string | null>(null);
  const [focusId, setFocusId] = useState<string | null>(null);
  const [moving, setMoving] = useState(false);
  const [tip, setTip] = useState<TipState | null>(null);
  const [hoverEdge, setHoverEdge] = useState<string | null>(null);
  const reduced = useReducedMotion();
  const reducedRef = useRef(reduced);
  reducedRef.current = reduced;
  const [rep, setRep] = useState<Rep>("card");
  const repRef = useRef<Rep>("card");
  const onSettledRef = useRef(props.onSceneSettled);
  onSettledRef.current = props.onSceneSettled;

  // ---- Mode -------------------------------------------------------------------------

  const [modeState, setModeState] = useState<MapMode>("steps");
  const mode: MapMode = compact ? "steps" : (props.mode ?? modeState);
  const modeRef = useRef(mode);
  modeRef.current = mode;
  const onModeChangeRef = useRef(props.onModeChange);
  onModeChangeRef.current = props.onModeChange;
  const controlled = props.mode !== undefined;
  const requestMode = useCallback(
    (m: MapMode) => {
      if (!controlled) setModeState(m);
      onModeChangeRef.current?.(m);
    },
    [controlled],
  );

  // On the map page, the echo channel is a transient preview; in the side pane it is the passage.
  const preview = compact ? null : (props.previewIds ?? echo ?? null);

  // ---- What is unfolded -------------------------------------------------------------

  const storeKey = STORE + goal + (within ? `|${hashSet(within)}` : "");
  const derived = !!(compact && within && echo && echo.size);
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

  // In a passage view (side pane), the route to the passage's records is open; their
  // own uses stay folded. Toggles there flip that default until the passage changes.
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
  /** What a card unfolds: its recorded supports and Lean correspondences. */
  const inputsOf = (id: string) => usesOf(graph, id, within).filter((e) => e.kind !== "assumes");
  /** Its explicit assumptions, drawn on the card as premise tags. */
  const tagsOf = (id: string) => usesOf(graph, id, within).filter((e) => e.kind === "assumes");

  const traced = useMemo(() => {
    if (!selected || !trace || !graph.nodes.has(selected)) return null;
    const all = closure(fullGraph, selected, trace === "rests" ? "prerequisites" : "consumers");
    return new Set([...all].filter((id) => goalReach.has(id)));
  }, [fullGraph, graph, selected, trace, goalReach]);

  const edgeObj = useMemo(() => (selectedEdge ? fullGraph.edges.find((e) => e.key === selectedEdge) ?? null : null), [fullGraph, selectedEdge]);

  // Whatever is selected or traced is unfolded into view: a deliberate act. A preview never is.
  useEffect(() => {
    if (derived) return;
    const targets = new Set<string>();
    if (selected && goalReach.has(selected)) targets.add(selected);
    if (traced) traced.forEach((id) => targets.add(id));
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
  }, [derived, selected, traced, trace, edgeObj, graph, goal, goalReach, within]);

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
    // Assumptions are premise tags on their consumers, not nodes; a shared record
    // with nothing drawn below it is drawn under each of its consumers (a clone).
    const scope = layoutScope(goal, visible, skel.edges, (id) => graph.nodes.get(id)?.kind === "assumption");
    const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
    const size = (lid: string): Size => {
      const id = recordOf(lid);
      const node = graph.nodes.get(id) ?? fullGraph.nodes.get(id)!;
      const isRoot = lid === goal;
      const h = heights.get(lid);
      if (h === undefined) provisional = true;
      if (lid !== id) return { w: compact ? 184 : 176, h: h ?? (compact ? 54 : 96) };
      return { w: widthOf(node, isRoot, compact, rootW), h: h ?? guessHeight(node, isRoot, compact) };
    };
    const nodeSet = new Set(split.nodes);
    let prevLayout = prev?.layout ?? null;
    let pin = pinRef.current;
    if (pin && !nodeSet.has(pin)) {
      // An occurrence opened: the record becomes one card where that occurrence was.
      const r = recordOf(pin);
      if (nodeSet.has(r) && prevLayout?.boxes.has(pin)) {
        prevLayout = { ...prevLayout, boxes: new Map(prevLayout.boxes).set(r, prevLayout.boxes.get(pin)!) };
        pin = r;
      } else pin = null;
    }
    const { layout, plan } = layoutTree({ root: goal, nodes: split.nodes, edges: split.edges, size, metrics, prev: prevLayout, pin });
    return { layout, plan, skeleton: split.edges, shared: split.shared, implied: skel.implied, provisional, pin };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [graph, goal, visible, skel, heights, compact, metrics, rootW]);
  const layout = built.layout;
  /** For each assumption, the drawn cards that carry it as a tag. */
  const tagHolders = useMemo(() => {
    const m = new Map<string, string[]>();
    for (const lid of layout.boxes.keys())
      for (const e of usesOf(graph, recordOf(lid), within))
        if (e.kind === "assumes") {
          if (!m.has(e.to)) m.set(e.to, []);
          m.get(e.to)!.push(lid);
        }
    return m;
  }, [layout, graph, within]);

  // Cards that left: kept mounted while they move into their parent and fade.
  const renderedRef = useRef<Set<string>>(new Set());
  const exiting = useMemo(() => {
    const out = new Set<string>();
    for (const id of renderedRef.current) if (!layout.boxes.has(id) && graph.nodes.has(recordOf(id))) out.add(id);
    return out;
  }, [layout, graph]);
  const [exitCleared, setExitCleared] = useState<Set<string> | null>(null);
  const exitShown = exitCleared === exiting ? new Set<string>() : exiting;

  // Edges that stop being drawn fade out; new ones fade in.
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
  const labelEls = useRef(new Map<string, HTMLElement>());
  const cardRefCache = useRef(new Map<string, (el: HTMLElement | null) => void>());
  const cardRef = (id: string) => {
    let fn = cardRefCache.current.get(id);
    if (!fn) {
      fn = (el: HTMLElement | null) => {
        if (el) cardEls.current.set(id, el);
        else cardEls.current.delete(id);
      };
      cardRefCache.current.set(id, fn);
    }
    return fn;
  };
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
  const labelRefCache = useRef(new Map<string, (el: HTMLElement | null) => void>());
  const labelRef = (id: string) => {
    let fn = labelRefCache.current.get(id);
    if (!fn) {
      fn = (el: HTMLElement | null) => {
        if (el) labelEls.current.set(id, el);
        else labelEls.current.delete(id);
      };
      labelRefCache.current.set(id, fn);
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

  /** Screen-space labels follow their cards every frame. */
  const placeLabels = useCallback(() => {
    const v = viewRef.current;
    const W = sizeRef.current.width;
    for (const [id, el] of labelEls.current) {
      const r = shown.current.get(id)?.rect ?? builtRef.current.layout.boxes.get(id);
      if (!r) continue;
      const cx = (r.x + r.w / 2) * v.k + v.x;
      const top = r.y * v.k + v.y;
      const w = el.offsetWidth;
      const left = Math.max(8, Math.min(W - w - 8, cx - w / 2));
      el.style.transform = `translate(${left.toFixed(1)}px, ${(top - el.offsetHeight - 6).toFixed(1)}px)`;
    }
  }, []);

  // Edge chips: counted from the layout against the current view, re-rendered only when counts change.
  const [chips, setChips] = useState<{ ids: Beyond; at: Record<Side, number | null>; notes: { x: number; top: boolean } | null }>({
    ids: { left: [], right: [], up: [], down: [] },
    at: { left: null, right: null, up: null, down: null },
    notes: null,
  });
  const notesRef = useRef<HTMLDivElement>(null);
  const chipsRaf = useRef(0);
  const refreshChips = useCallback(() => {
    if (chipsRaf.current) return;
    chipsRaf.current = requestAnimationFrame(() => {
      chipsRaf.current = 0;
      const boxes = builtRef.current.layout.boxes;
      const vp = viewport();
      const v = viewRef.current;
      const ids = beyond(boxes, v, vp);
      // Screen-space controls never sit over a card: each slides along its edge to a free place, or hides.
      const rects = screenRects(boxes.values(), v);
      const { insets } = vp;
      // The notes sit at the bottom-left; when cards fill the bottom edge they move along it, else to the top edge.
      const ne = notesRef.current;
      let notes: { x: number; top: boolean } | null = null;
      if (ne) {
        const w = ne.offsetWidth;
        const h = ne.offsetHeight;
        const bottom = freeSpot("x", vp.height - insets.bottom - h, insets.left + w / 2, w, h, insets.left, vp.width - insets.right, rects, 24);
        const top = bottom === null ? freeSpot("x", insets.top, insets.left + w / 2, w, h, insets.left, vp.width - insets.right, rects, 24) : null;
        notes = bottom !== null ? { x: bottom - w / 2, top: false } : top !== null ? { x: top - w / 2, top: true } : null;
      }
      // Chips keep clear of the notes too.
      if (ne && notes) {
        const w = ne.offsetWidth;
        const h = ne.offsetHeight;
        const y0 = notes.top ? insets.top : vp.height - insets.bottom - h;
        rects.push({ x0: notes.x - 6, x1: notes.x + w + 6, y0: y0 - 6, y1: y0 + h + 6 });
      }
      // And off the lines where a gap between them exists: horizontal runs for chips that slide
      // up and down an edge, vertical runs for chips that slide along the top or bottom.
      const hLines: typeof rects = [];
      const vLines: typeof rects = [];
      const routedNow = lastRouted.current;
      if (routedNow) {
        const add = (a: Pt, b: Pt) => {
          const x0 = Math.min(a.x, b.x) * v.k + v.x;
          const x1 = Math.max(a.x, b.x) * v.k + v.x;
          const y0 = Math.min(a.y, b.y) * v.k + v.y;
          const y1 = Math.max(a.y, b.y) * v.k + v.y;
          if (Math.abs(a.y - b.y) < 0.5) hLines.push({ x0, x1, y0: y0 - 5, y1: y1 + 5 });
          else if (Math.abs(a.x - b.x) < 0.5) vLines.push({ x0: x0 - 5, x1: x1 + 5, y0, y1 });
        };
        for (const re of routedNow.edges.values()) for (let i = 1; i < re.points.length; i++) add(re.points[i - 1], re.points[i]);
        for (const rb of routedNow.buses.values()) add(rb.stem[0], rb.stem[1]);
      }
      const place = (axis: "x" | "y", fixed: number, want: number, w: number, h: number, lo: number, hi: number) =>
        freeSpot(axis, fixed, want, w, h, lo, hi, [...rects, ...(axis === "y" ? hLines : vLines)]) ?? freeSpot(axis, fixed, want, w, h, lo, hi, rects);
      const at = {} as Record<Side, number | null>;
      for (const side of SIDES) {
        if (!ids[side].length) {
          at[side] = null;
          continue;
        }
        const want = chipAt(side, ids[side], boxes, v, vp);
        const w = 118;
        const h = 30;
        if (side === "left") at[side] = place("y", Math.max(4, insets.left - 12), want, w, h, insets.top, vp.height - insets.bottom);
        else if (side === "right") at[side] = place("y", vp.width - Math.max(4, insets.right - 12) - w, want, w, h, insets.top, vp.height - insets.bottom);
        else if (side === "up") at[side] = place("x", Math.max(4, insets.top - 12), want, w, h, insets.left, vp.width - insets.right);
        else at[side] = place("x", vp.height - insets.bottom - 4 - h, want, w, h, insets.left, vp.width - insets.right);
        // Cards cut by the bottom or top edge leave no free place there; the chip still says
        // what lies beyond, sitting on the cut-off edge of the row rather than over its titles.
        if (at[side] === null && (side === "down" || side === "up")) at[side] = Math.round(want);
      }
      setChips((prev) =>
        sameBeyond(prev.ids, ids) && SIDES.every((side) => prev.at[side] === at[side] || (prev.at[side] !== null && at[side] !== null && Math.abs(prev.at[side]! - at[side]!) < 2)) && prev.notes?.x === notes?.x && prev.notes?.top === notes?.top
          ? prev
          : { ids, at, notes },
      );
    });
    // eslint-disable-next-line react-hooks/exhaustive-deps
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
      placeLabels();
      if (m && raw < 1) raf.current = requestAnimationFrame(draw);
      else if (m) {
        motion.current = null;
        raf.current = 0;
        setMoving(false);
        setExitCleared(exitingRef.current);
        scheduleSettle();
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
      set(els, `case:${pe.key}`, d, isFresh ? e : 1);
      set(els, `ov:${pe.key}`, d);
      set(els, `lit:${pe.key}`, d);
      set(els, `litcase:${pe.key}`, d);
      set(els, `mask:${pe.key}`, d);
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
      const stem = roundedPath(rb.stem, r);
      set(els, `bus:${parent}`, (busD.get(parent) ?? "") + stem);
      set(els, `buscase:${parent}`, (busD.get(parent) ?? "") + stem);
      set(els, `busf:${parent}`, busF.get(parent) ?? "", e);
      set(els, `head:${parent}`, polygonPath(rb.head), busD.has(parent) ? 1 : e);
      set(els, `hitstem:${parent}`, stem);
      set(els, `ovstem:${parent}`, stem);
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

  /** Where the camera is heading (or is). Reveals are judged against this, so they never fight a move in flight. */
  const targetView = (): View => cameraOnly.current?.to ?? motion.current?.view?.to ?? viewRef.current;

  /** Move the camera on the shared clock: with a card motion that starts now, else on its own leg of the same curve. */
  const moveCamera = useCallback(
    (to: View, animate = true, dur = MOVE_MS) => {
      const m = motion.current;
      if (!animate || reducedRef.current) {
        if (m) m.view = undefined;
        cameraOnly.current = null;
        applyView(to);
        scheduleSettle();
        return;
      }
      const now = performance.now();
      if (m && m.dur > 0 && now - m.start < 34) {
        m.view = { from: viewRef.current, to };
        cameraOnly.current = null;
        return;
      }
      if (m) m.view = undefined;
      cameraOnly.current = { start: now, from: viewRef.current, to, dur };
      if (!cameraRaf.current) cameraRaf.current = requestAnimationFrame(cameraTick);
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [applyView],
  );
  const cameraOnly = useRef<{ start: number; from: View; to: View; dur: number } | null>(null);
  const cameraRaf = useRef(0);
  const cameraTick = (now: number) => {
    const c = cameraOnly.current;
    if (!c) {
      cameraRaf.current = 0;
      return;
    }
    const raw = Math.min(1, (now - c.start) / c.dur);
    applyView(raw >= 1 ? c.to : lerpView(c.from, c.to, easeMove(raw), viewport()));
    if (raw < 1) cameraRaf.current = requestAnimationFrame(cameraTick);
    else {
      cameraOnly.current = null;
      cameraRaf.current = 0;
      scheduleSettle();
    }
  };

  // ---- Settling ---------------------------------------------------------------------
  // Once nothing moves, the request (selection, trace, step) must be met — under
  // reduced motion and after a sheet changes the insets too — and the page hears
  // about the scene it can remember.

  const restoreRef = useRef<MapScene | null>(null);
  const framedRef = useRef(false);
  const enteringRef = useRef(false);
  const userMovedSinceAsk = useRef(false);
  const settleTimer = useRef(0);
  const lastSettled = useRef("");
  const askViewRef = useRef<() => View | null>(() => null);
  const getSceneRef = useRef<() => MapScene>(() => ({ camera: { ...viewRef.current }, expanded: [], mode: "steps" }));
  const scheduleSettle = useCallback(() => {
    window.clearTimeout(settleTimer.current);
    settleTimer.current = window.setTimeout(() => {
      if (motion.current || cameraOnly.current || builtRef.current.provisional || !readyRef.current) return;
      refreshChips();
      if (restoreRef.current) restoreRef.current = null;
      else if (!userMovedSinceAsk.current) {
        const v = askViewRef.current();
        if (v) {
          moveCamera(v, true, CAMERA_MS);
          return;
        }
      }
      const scene = getSceneRef.current();
      // Keyed by the entry too: the same scene still has to be written into a new history entry.
      const key = `${window.location.href}|${JSON.stringify(scene)}`;
      if (key === lastSettled.current) return;
      lastSettled.current = key;
      onSettledRef.current?.(scene);
    }, 40);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);
  useEffect(() => () => window.clearTimeout(settleTimer.current), []);

  // Start a motion whenever the layout changes.
  const pendingCamera = useRef<null | ((l: Layout) => View | null)>(null);
  useLayoutEffect(() => {
    const now = performance.now();
    const prev = committed.current;
    const sameScene = !!prev && committedGoal.current === `${goal}|${compact}`;
    const from = new Map<string, CardState>();
    const to = new Map<string, CardState>();
    const entering = new Set<string>();
    const opener = (lid: string): string | null => {
      if (built.pin && shown.current.has(built.pin)) return built.pin;
      const c = consumerOf(lid);
      if (c && shown.current.has(c)) return c;
      const id = recordOf(lid);
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
        // New cards grow out of the card that opened them: in place, from behind it.
        const o = opener(id);
        const or = o ? shown.current.get(o)?.rect : undefined;
        entering.add(id);
        if (or) {
          const cx = or.x + or.w / 2;
          const cy = or.y + or.h / 2;
          // Start just below the opener, a short way toward the final place.
          const sx = lerp(cx - rect.w / 2, rect.x, 0.35);
          const sy = lerp(cy - rect.h / 2, rect.y, 0.35);
          from.set(id, { rect: { x: sx, y: sy, w: rect.w, h: rect.h }, op: 0, sc: 0.96 });
        } else from.set(id, { rect, op: 0, sc: 0.96 });
      } else from.set(id, { rect, op: 1, sc: 1 });
    }
    for (const id of exiting) {
      const cur = shown.current.get(id);
      if (!cur) continue;
      // Into the parent's new rectangle.
      let target: Rect | undefined;
      if (built.pin && layout.boxes.has(built.pin)) target = layout.boxes.get(built.pin);
      const c = consumerOf(id);
      if (!target && c && layout.boxes.has(c)) target = layout.boxes.get(c);
      if (!target) for (const e of graph.in.get(recordOf(id)) ?? []) if (layout.boxes.has(e.from)) target = layout.boxes.get(e.from);
      target ??= layout.boxes.get(goal)!;
      from.set(id, cur);
      to.set(id, { rect: { x: lerp(cur.rect.x, target.x + target.w / 2 - cur.rect.w / 2, 0.65), y: lerp(cur.rect.y, target.y + target.h / 2 - cur.rect.h / 2, 0.65), w: cur.rect.w, h: cur.rect.h }, op: 0, sc: 0.96 });
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
    // Until the first framing (and during the entrance) the layout settles in place: nothing slides into view.
    const animate = sameScene && !reducedRef.current && !restoreRef.current && framedRef.current && !enteringRef.current;
    const before = motion.current;
    cancelAnimationFrame(raf.current);
    motion.current = { start: now, dur: animate ? MOVE_MS : 0, from, to, dummyFrom, entering };
    let camera: View | null = null;
    if (pendingCamera.current && ready && !restoreRef.current) {
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
    // A remembered scene: put the anchor card back exactly where it was.
    const restore = restoreRef.current;
    if (restore) applyView(restoredView(restore, layout));
    refreshChips();
    if (!animate) scheduleSettle();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [built]);

  useEffect(
    () => () => {
      // Reset as well as cancel: a remount (StrictMode) must be able to schedule again.
      cancelAnimationFrame(raf.current);
      cancelAnimationFrame(cameraRaf.current);
      cancelAnimationFrame(chipsRaf.current);
      raf.current = 0;
      cameraRaf.current = 0;
      chipsRaf.current = 0;
      cameraOnly.current = null;
    },
    [],
  );

  // Redraw paths after any render (new overlay elements need their geometry now).
  useLayoutEffect(() => {
    if (!motion.current && lastRouted.current) {
      const all = new Map<string, Rect>();
      for (const [id, s] of shown.current) all.set(id, s.rect);
      writePaths(lastRouted.current, all, 1);
    }
    placeLabels();
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

  /** The card that stands for a record: the record itself, else its occurrence nearest the view. */
  const pick = (l: Layout, id: string): string | null => {
    if (l.boxes.has(id)) return id;
    const lids = lidsOf(l, id);
    if (lids.length <= 1) return lids[0] ?? null;
    const v = targetView();
    const vp = viewport();
    const cx = (vp.width / 2 - v.x) / v.k;
    const cy = (vp.height / 2 - v.y) / v.k;
    let best = lids[0];
    let d0 = Infinity;
    for (const lid of lids) {
      const r = l.boxes.get(lid)!;
      const d = Math.hypot(r.x + r.w / 2 - cx, r.y + r.h / 2 - cy);
      if (d < d0) [d0, best] = [d, lid];
    }
    return best;
  };
  const hasRec = (l: Layout, id: string) => l.boxes.has(id) || lidsOf(l, id).length > 0;

  const boundsOf = useCallback((l: Layout, ids: Iterable<string>, pad = 36): Bounds | null => {
    const b = { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity };
    for (const id of ids) {
      const lid = pick(l, id);
      const box = lid ? l.boxes.get(lid) : undefined;
      if (!box) continue;
      b.x0 = Math.min(b.x0, box.x - pad);
      b.x1 = Math.max(b.x1, box.x + box.w + pad);
      b.y0 = Math.min(b.y0, box.y - pad);
      b.y1 = Math.max(b.y1, box.y + box.h + pad);
    }
    return Number.isFinite(b.x0) ? b : null;
  }, []);
  const boxOf = (l: Layout, id: string, pad = 0): Bounds | null => boundsOf(l, [id], pad);

  const floor = compact ? COMPACT_FLOOR : STEPS_FLOOR;

  /** Reading scale for a box: k = 1, or down to the floor if that fits the box across; never lower. */
  const readingK = (b: Bounds, max = STEPS_K) => {
    const vp = viewport();
    const availW = vp.width - vp.insets.left - vp.insets.right;
    const k = availW / Math.max(1, b.x1 - b.x0);
    return k >= max ? max : k >= floor ? k : max;
  };

  /** Steps: the goal and its direct inputs at reading size, top-aligned; what does not fit is counted by the edge chips. */
  const startView = useCallback(
    (l: Layout): View | null => {
      const vp = viewport();
      if (compact && echo?.size) {
        const b = boundsOf(l, [...echo].filter((id) => hasRec(l, id)), 24);
        if (b) return fitBounds(b, vp, { min: COMPACT_FLOOR, max: 1 });
      }
      const ids = [goal, ...builtRef.current.skeleton.filter((e) => e.from === goal).map((e) => e.to)];
      const b = boundsOf(l, ids, compact ? 24 : 14);
      if (!b) return null;
      if (compact) return fitBounds(b, vp, { max: 1, min: COMPACT_FLOOR, top: true });
      // The plate and its whole first row inside the visible canvas: k = 1 if that fits,
      // else the largest k down to the floor that fits, else the floor with the plate on top.
      const availW = vp.width - vp.insets.left - vp.insets.right;
      const availH = vp.height - vp.insets.top - vp.insets.bottom;
      const fit = Math.min(availW / Math.max(1, b.x1 - b.x0), availH / Math.max(1, b.y1 - b.y0));
      const k = fit >= STEPS_K ? STEPS_K : Math.max(floor, fit);
      return frameBox(b, vp, { min: k, max: k, anchor: boxOf(l, goal), top: true });
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [graph, goal, within, compact, echo, boundsOf, floor],
  );

  const overviewView = useCallback(
    (l: Layout): View => {
      const b = layoutBounds(l);
      // Room above the goal for its screen label.
      const vp = viewport();
      return fitBounds({ x0: b.x0 - 24, y0: b.y0 - 24, x1: b.x1 + 24, y1: b.y1 + 24 }, { ...vp, insets: { ...vp.insets, top: vp.insets.top + 34 } }, { max: 1, min: MIN_K });
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [],
  );

  /** Steps around one record: it and its drawn inputs at reading size, the record itself kept in view. */
  const aroundView = useCallback(
    (l: Layout, id: string): View | null => {
      const lid = pick(l, id);
      if (!lid) return null;
      const inputs = builtRef.current.skeleton.filter((e) => e.from === lid).map((e) => e.to);
      const b = boundsOf(l, [lid, ...inputs], 32);
      if (!b) return null;
      const k = readingK(b);
      return frameBox(b, viewport(), { min: k, max: k, anchor: boxOf(l, lid, 24), top: true });
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [boundsOf, floor],
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

  /** The smallest move that brings `ids` into view; never below the reading floor in Steps. */
  const revealFn = useCallback(
    (ids: Iterable<string>, anchor?: string | null, pad = 28) =>
      (l: Layout) => {
        const b = boundsOf(l, ids, pad);
        if (!b) return null;
        const cur = targetView();
        const a = anchor ? boxOf(l, anchor, pad) : null;
        if (modeRef.current === "overview") return revealBox(b, viewport(), cur, cur.k, a);
        // Steps never chooses a scale below the reading floor; what does not fit is counted by the edge chips.
        if (cur.k < floor - 1e-3) return frameBox(b, viewport(), { min: floor, max: floor, anchor: a, top: true });
        return revealBox(b, viewport(), cur, floor, a);
      },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [boundsOf, floor],
  );

  // ---- Scenes -----------------------------------------------------------------------

  const expandedRef = useRef(expandedState);
  expandedRef.current = expandedState;
  const selectedRef = useRef(selected);
  selectedRef.current = selected;

  /** The camera is remembered relative to the goal's plate, which a rebuilt layout keeps as its origin. */
  const getScene = useCallback((): MapScene => {
    const v = viewRef.current;
    const l = builtRef.current.layout;
    const root = l.boxes.get(goal);
    const camera = root ? { x: v.x + root.x * v.k, y: v.y + root.y * v.k, k: v.k } : { ...v };
    // The anchor: the selection if drawn, else the card nearest the middle of the view.
    let anchorId = selectedRef.current ? pick(l, selectedRef.current) : null;
    if (!anchorId) {
      const vp = viewport();
      const mx = (vp.width / 2 - v.x) / v.k;
      const my = (vp.height / 2 - v.y) / v.k;
      let best = Infinity;
      for (const [id, r] of l.boxes) {
        const d = Math.hypot(r.x + r.w / 2 - mx, r.y + r.h / 2 - my);
        if (d < best) [best, anchorId] = [d, id];
      }
    }
    const a = anchorId ? l.boxes.get(anchorId)! : null;
    return {
      camera,
      expanded: [...expandedRef.current].sort(),
      mode: modeRef.current,
      ...(a && anchorId ? { anchor: { id: anchorId, x: a.x * v.k + v.x, y: a.y * v.k + v.y } } : {}),
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [goal]);
  getSceneRef.current = getScene;

  function restoredView(scene: MapScene, l: Layout): View {
    const k = scene.camera.k;
    const aid = scene.anchor ? (l.boxes.has(scene.anchor.id) ? scene.anchor.id : pick(l, recordOf(scene.anchor.id))) : null;
    const a = aid ? l.boxes.get(aid) : undefined;
    if (a && scene.anchor) return { k, x: scene.anchor.x - a.x * k, y: scene.anchor.y - a.y * k };
    const root = l.boxes.get(goal);
    return root ? { k, x: scene.camera.x - root.x * k, y: scene.camera.y - root.y * k } : { ...scene.camera };
  }

  // ---- Handle -----------------------------------------------------------------------

  const fittedGoal = useRef<string | null>(null);
  const userMoved = useRef(false);
  const skipModeFrame = useRef(false);
  const lastAsk = useRef("");
  const askKeyOf = () => `${selected ?? ""}|${trace ?? ""}|${selectedEdge ?? ""}|${insets.right}|${insets.bottom}|${mode}`;

  const doRevealIds = useCallback(
    (ids: readonly string[]) => {
      const list = ids.filter((id) => goalReach.has(id));
      if (!list.length) return;
      pinRef.current = null;
      userMovedSinceAsk.current = true;
      const frame = revealFn(list, list[0]);
      if (list.every((id) => hasRec(builtRef.current.layout, id))) {
        const v = frame(builtRef.current.layout);
        if (v) moveCamera(v);
        return;
      }
      pendingCamera.current = frame;
      if (derived) {
        setFlips((prev) => {
          const next = new Set(prev.echo === echo ? prev.ids : []);
          for (const id of list) for (const p of pathFromGoal(graph, goal, id, within)?.slice(1, -1) ?? []) if (!expanded.has(p)) next.add(p);
          return { echo, ids: next };
        });
      } else
        setExpanded((prev) => {
          const next = new Set(prev);
          return expandTo(graph, goal, list, next, within) ? next : prev;
        });
    },
    [goalReach, revealFn, moveCamera, derived, echo, graph, goal, within, expanded],
  );

  useImperativeHandle(
    ref,
    () => ({
      fitAll: (animate = true) => {
        const l = builtRef.current.layout;
        if (mode === "overview" || compact) {
          moveCamera(overviewView(l), animate);
          return;
        }
        // Steps: the drawn branch at reading size, anchored on the selection (else the goal).
        const b = layoutBounds(l);
        const box = { x0: b.x0 - 32, y0: b.y0 - 32, x1: b.x1 + 32, y1: b.y1 + 32 };
        const k = readingK(box);
        const anchor = (selected && pick(l, selected)) || goal;
        moveCamera(frameBox(box, viewport(), { min: k, max: k, anchor: boxOf(l, anchor, 24), top: true }), animate);
      },
      fitNodes: (ids, animate = true) => {
        const list = [...ids];
        const fn = (l: Layout) => {
          const b = boundsOf(l, list, compact ? 24 : 40);
          return b ? fitBounds(b, viewport(), { max: 1, min: compact ? COMPACT_FLOOR : floor }) : null;
        };
        if (list.every((id) => hasRec(builtRef.current.layout, id))) {
          const v = fn(builtRef.current.layout);
          if (v) moveCamera(v, animate);
        } else pendingCamera.current = fn;
      },
      zoomBy: (factor) => {
        const v = viewRef.current;
        const vp = viewport();
        const px = vp.insets.left + (vp.width - vp.insets.left - vp.insets.right) / 2;
        const py = vp.insets.top + (vp.height - vp.insets.top - vp.insets.bottom) / 2;
        const k = Math.max(MIN_K, Math.min(MAX_K, v.k * factor));
        userMovedSinceAsk.current = true;
        moveCamera({ k, x: px - ((px - v.x) / v.k) * k, y: py - ((py - v.y) / v.k) * k }, true, CAMERA_MS);
      },
      focusNode: (id) => {
        const lid = pick(builtRef.current.layout, id);
        if (lid) cardEls.current.get(lid)?.querySelector<HTMLElement>(".card__open")?.focus({ preventScroll: true });
      },
      expandAll: () => {
        pinRef.current = null;
        userMovedSinceAsk.current = false;
        pendingCamera.current = overviewView;
        const all = new Set([...goalReach].filter((id) => id !== goal && usesOf(graph, id, within).length));
        if (derived) setFlips({ echo, ids: new Set([...all].filter((id) => !expanded.has(id))) });
        else setExpanded(all);
        if (!compact && mode !== "overview") {
          skipModeFrame.current = true;
          requestMode("overview");
        }
      },
      collapseAll: () => {
        pinRef.current = null;
        userMovedSinceAsk.current = false;
        pendingCamera.current = startView;
        if (derived) setFlips({ echo, ids: new Set() });
        else setExpanded(new Set());
        if (!compact && mode !== "steps") {
          skipModeFrame.current = true;
          requestMode("steps");
        }
      },
      getScene,
      restoreScene: (scene) => {
        restoreRef.current = scene;
        fittedGoal.current = goal;
        userMoved.current = true;
        userMovedSinceAsk.current = true;
        pendingCamera.current = null;
        cameraOnly.current = null;
        if (motion.current) motion.current.view = undefined;
        lastAsk.current = askKeyOf();
        if (scene.mode !== modeRef.current) skipModeFrame.current = true;
        if (!controlled && !compact) setModeState(scene.mode);
        if (!derived) {
          const next = new Set(scene.expanded.filter((id) => graph.nodes.has(id)));
          setExpanded((prev) => (prev.size === next.size && [...next].every((id) => prev.has(id)) ? prev : next));
        }
        applyView(restoredView(scene, builtRef.current.layout));
        scheduleSettle();
      },
      revealIds: doRevealIds,
      focusCard: (id) => {
        const lid = pick(builtRef.current.layout, id);
        const el = lid ? cardEls.current.get(lid)?.querySelector<HTMLElement>(".card__open") : null;
        if (!el || !lid) return false;
        setFocusId(lid);
        el.focus({ preventScroll: true });
        const v = revealFn([lid])(builtRef.current.layout);
        if (v) moveCamera(v, true, CAMERA_MS);
        return true;
      },
    }),
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [boundsOf, moveCamera, goalReach, goal, graph, within, derived, echo, expanded, startView, compact, mode, selected, getScene, doRevealIds, revealFn, controlled, requestMode, overviewView, floor],
  );

  // ---- Camera input -----------------------------------------------------------------

  useLayoutEffect(() => {
    const wrap = wrapRef.current!;
    const world = worldRef.current!;
    const behaviour = d3zoom<HTMLDivElement, unknown>()
      .scaleExtent([MIN_K, MAX_K])
      .filter((event: Event) => {
        if (event.type === "dblclick" || event.type === "wheel") return false;
        const target = event.target as Element;
        if (target.closest?.("button, a, .card__body, .tree__ui")) return false;
        return !(event as MouseEvent).button && !(event as MouseEvent).ctrlKey;
      })
      .on("zoom", (event: { transform: ZoomTransform; sourceEvent?: Event | null }) => {
        if (event.sourceEvent) {
          userMoved.current = true;
          userMovedSinceAsk.current = true;
          if (motion.current) motion.current.view = undefined;
          cameraOnly.current = null;
          pendingCamera.current = null;
        }
        const t = event.transform;
        viewRef.current = { x: t.x, y: t.y, k: t.k };
        world.style.transform = `translate(${t.x}px, ${t.y}px) scale(${t.k})`;
        wrap.style.setProperty("--k", String(t.k));
        // The dot grid lives in world space: it moves and scales with the map.
        wrap.style.backgroundPosition = `${t.x}px ${t.y}px`;
        wrap.style.backgroundSize = `${22 * t.k}px ${22 * t.k}px`;
        const r = repFor(t.k);
        if (r !== repRef.current) {
          repRef.current = r;
          wrap.dataset.rep = r;
          setRep(r);
        }
        placeLabels();
        refreshChips();
      })
      .on("end", (event: { sourceEvent?: Event | null }) => {
        if (event.sourceEvent) scheduleSettle();
      });
    zoomRef.current = behaviour;
    const s = select(wrap);
    s.call(behaviour);
    wrap.dataset.rep = repRef.current;
    let wheelEnd = 0;
    const onWheel = (event: WheelEvent) => {
      if ((event.target as Element).closest?.(".tree__ui")) return;
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
      userMoved.current = true;
      userMovedSinceAsk.current = true;
      pendingCamera.current = null;
      cameraOnly.current = null;
      window.clearTimeout(wheelEnd);
      wheelEnd = window.setTimeout(scheduleSettle, 160);
    };
    wrap.addEventListener("wheel", onWheel, { passive: false });
    const observer = new ResizeObserver(([entry]) => {
      const { width, height } = entry.contentRect;
      sizeRef.current = { width, height };
      setPaneW(Math.round(width));
      setPaneH(Math.round(height));
      if (width > 10 && height > 10) setReady(true);
      refreshChips();
    });
    observer.observe(wrap);
    return () => {
      observer.disconnect();
      wrap.removeEventListener("wheel", onWheel);
      window.clearTimeout(wheelEnd);
      s.on(".zoom", null);
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // First frame and goal changes: the plate and its first row, framed once the plate's
  // statement has rendered (or after 1.2 s), so the camera does not jump as the theorem
  // is typeset. Later size changes re-frame only until the reader pans, zooms, unfolds or selects.
  const rootH = layout.boxes.get(goal)?.h ?? 0;
  const firstRowKey = useMemo(() => {
    const ids = built.skeleton.filter((e) => e.from === goal).map((e) => e.to);
    let bottom = 0;
    for (const id of ids) {
      const r = layout.boxes.get(id);
      if (r) bottom = Math.max(bottom, Math.round(r.y + r.h));
    }
    return `${ids.length}|${bottom}`;
  }, [built, layout, goal]);
  const [framed, setFramed] = useState(false);
  framedRef.current = framed || compact;
  const [holdOver, setHoldOver] = useState(false);
  useEffect(() => {
    const t = window.setTimeout(() => setHoldOver(true), 1200);
    return () => window.clearTimeout(t);
  }, []);
  const statementIn = () => !!cardEls.current.get(goal)?.querySelector(".plate__statement, .plate__recorded");
  if (selected && !compact) userMoved.current = true;
  useEffect(() => {
    if (!ready || restoreRef.current) {
      if (restoreRef.current && !framed) setFramed(true);
      return;
    }
    if (fittedGoal.current !== goal) {
      const first = fittedGoal.current === null;
      const wait = first && !compact && !selected && mode === "steps" && !holdOver && (built.provisional || !statementIn());
      if (wait) return;
      fittedGoal.current = goal;
      if (!selected) userMoved.current = false;
      const v = mode === "overview" ? overviewView(layout) : startView(layout);
      if (v) moveCamera(v, !first);
      setFramed(true);
    } else if (!userMoved.current && !selected && !moving && mode === "steps" && !(compact && echo?.size) && !built.provisional) {
      const v = startView(layout);
      if (v) moveCamera(v, false);
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [ready, goal, rootH, rootW, paneH, insets.bottom, insets.top, firstRowKey, holdOver, built.provisional]);

  // The entrance: first visit per session, never under reduced motion, never moving the camera.
  const [entering, setEntering] = useState(false);
  enteringRef.current = entering;
  const enteredRef = useRef(false);
  useEffect(() => {
    if (!framed || enteredRef.current) return;
    enteredRef.current = true;
    if (!intro || reduced || compact || selected) return;
    setEntering(true);
    const t = window.setTimeout(() => setEntering(false), 900);
    return () => window.clearTimeout(t);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [framed]);
  // Acting during the entrance jumps to its end.
  useEffect(() => {
    if (!entering) return;
    const wrap = wrapRef.current!;
    const stop = () => setEntering(false);
    wrap.addEventListener("pointerdown", stop, true);
    wrap.addEventListener("wheel", stop, true);
    window.addEventListener("keydown", stop, true);
    return () => {
      wrap.removeEventListener("pointerdown", stop, true);
      wrap.removeEventListener("wheel", stop, true);
      window.removeEventListener("keydown", stop, true);
    };
  }, [entering]);

  // A change of mode frames for the new task.
  const lastMode = useRef(mode);
  useEffect(() => {
    if (lastMode.current === mode) return;
    lastMode.current = mode;
    if (skipModeFrame.current) {
      skipModeFrame.current = false;
      return;
    }
    if (!ready || restoreRef.current) return;
    userMovedSinceAsk.current = false;
    if (mode === "overview") moveCamera(overviewView(layout));
    else {
      const v = selected && hasRec(layout, selected) ? aroundView(layout, selected) : startView(layout);
      if (v) moveCamera(v);
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [mode]);

  // In the side pane, a new passage frames its lit cards.
  const echoKey = echo ? [...echo].sort().join("|") : "";
  const lastEcho = useRef<string | null>(null);
  useLayoutEffect(() => {
    if (!compact || !ready || !echo?.size) return;
    if (lastEcho.current === echoKey) return;
    if (![...echo].some((id) => hasRec(layout, id))) return;
    lastEcho.current = echoKey;
    const frame = (l: Layout) => {
      const b = boundsOf(l, [...echo].filter((id) => hasRec(l, id)), 24);
      return b ? fitBounds(b, viewport(), { min: COMPACT_FLOOR, max: 1 }) : null;
    };
    if (built.provisional) {
      pendingCamera.current = frame;
      return;
    }
    const v = frame(layout);
    if (v) moveCamera(v);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [compact, ready, echoKey, layout]);

  // Keep what was asked for on screen: never recentre what is already visible.
  const askedIds = (): { ids: string[]; anchor: string | null } => {
    const l = builtRef.current.layout;
    if (edgeObj) {
      const ends = [edgeObj.from, edgeObj.to].filter((id) => hasRec(l, id));
      return { ids: ends, anchor: ends.includes(edgeObj.to) ? edgeObj.to : edgeObj.from };
    }
    if (traced && selected) return { ids: [...traced].filter((id) => hasRec(l, id)), anchor: hasRec(l, selected) ? selected : null };
    // An assumption is drawn as tags on the records that assume it: frame those.
    if (selected && !hasRec(l, selected) && tagHolders.has(selected)) return { ids: tagHolders.get(selected)!, anchor: tagHolders.get(selected)![0] };
    return { ids: selected ? [selected] : [], anchor: selected ?? null };
  };
  askViewRef.current = () => {
    const { ids, anchor } = askedIds();
    const l = builtRef.current.layout;
    // Overview keeps the whole goal fitted until the reader moves the camera.
    if (modeRef.current === "overview" && !compact && !ids.length) {
      const v = overviewView(l);
      const cur = viewRef.current;
      return Math.abs(v.k - cur.k) > 0.002 || Math.abs(v.x - cur.x) > 2 || Math.abs(v.y - cur.y) > 2 ? v : null;
    }
    if (!ids.length || !ids.every((id) => hasRec(l, id))) return null;
    // Of a trace, the selection itself must be in view; the rest as far as the floor allows.
    const v = revealFn(ids, anchor)(l);
    if (!v) return null;
    return v;
  };
  useEffect(() => {
    if (!ready) return;
    const key = askKeyOf();
    if (key === lastAsk.current) return;
    if (restoreRef.current) {
      lastAsk.current = key;
      return;
    }
    const { ids } = askedIds();
    if (!ids.length) {
      lastAsk.current = key;
      return;
    }
    if (!ids.every((id) => hasRec(layout, id)) || built.provisional) return;
    lastAsk.current = key;
    userMovedSinceAsk.current = false;
    const v = askViewRef.current();
    if (v) moveCamera(v);
    else scheduleSettle();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [ready, selected, trace, traced, selectedEdge, edgeObj, layout, built.provisional, insets.right, insets.bottom, mode]);

  // A new history entry (a selection, a step, a trace) hears about the scene it shows, even when nothing moved.
  useEffect(() => {
    if (ready) scheduleSettle();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [selected, selectedEdge, trace, mode, expandedState]);

  // ---- Interaction ------------------------------------------------------------------

  const toggle = useCallback(
    (id: string, lid: string = id) => {
      if (id === goal || inputsOf(id).length === 0) return;
      userMoved.current = true;
      pinRef.current = lid;
      const opening = !expanded.has(id);
      if (opening) {
        askCamera((l) => {
          const fresh = [...l.boxes.keys()].filter((x) => !committed.current?.layout.boxes.has(x));
          const at = l.boxes.has(lid) ? lid : id;
          return revealFn([at, ...fresh], at)(l);
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
    [goal, graph, within, expanded, derived, echo, askCamera, revealFn],
  );

  /** Opening a mark: select it and read it in Steps, at k = 1 with its inputs in view. */
  const openMark = (id: string, lid: string) => {
    onSelect(id);
    if (!compact && mode !== "steps") {
      skipModeFrame.current = true;
      requestMode("steps");
    }
    lastAsk.current = `${id}||${""}|${insets.right}|${insets.bottom}|steps`;
    userMovedSinceAsk.current = false;
    const v = aroundView(layout, lid);
    if (v) moveCamera(v);
  };

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
    requestAnimationFrame(() => cardEls.current.get(next)?.querySelector<HTMLElement>(".card__open")?.focus({ preventScroll: true }));
    const v = revealFn([next], next)(layout);
    if (v) moveCamera(v, true, CAMERA_MS);
  };

  const onCardKey = (lid: string, event: React.KeyboardEvent) => {
    const id = recordOf(lid);
    const onOpen = (event.target as Element).classList?.contains("card__open");
    if (!onOpen) return;
    if (event.key.startsWith("Arrow")) {
      event.preventDefault();
      moveFocus(lid, event.key);
    } else if (event.key === " ") {
      // Space opens the inputs; Enter (the button's own click) opens the record.
      event.preventDefault();
      toggle(id, lid);
    } else if (event.key.toLowerCase() === "t" && !event.metaKey && !event.ctrlKey && !event.altKey) {
      event.preventDefault();
      onTrace(id);
    }
  };

  const setHovered = (lid: string | null) => {
    setHover(lid);
    onHover?.(lid ? recordOf(lid) : null);
  };
  const hoverRec = hover ? recordOf(hover) : null;

  // Edge hover: a short delay in; leaving waits a moment so the pointer can reach the tooltip.
  const tipTimer = useRef(0);
  const tipLeave = useRef(0);
  const pointerAt = (event: React.PointerEvent) => {
    const rect = wrapRef.current!.getBoundingClientRect();
    return { x: event.clientX - rect.left, y: event.clientY - rect.top };
  };
  const enterEdge = (key: string, event: React.PointerEvent) => {
    window.clearTimeout(tipLeave.current);
    setHoverEdge(key);
    const at = pointerAt(event);
    window.clearTimeout(tipTimer.current);
    tipTimer.current = window.setTimeout(() => setTip((t) => (t && t.key === key ? t : { key, ...at })), 120);
  };
  const leaveEdge = () => {
    window.clearTimeout(tipTimer.current);
    window.clearTimeout(tipLeave.current);
    tipLeave.current = window.setTimeout(() => {
      setTip(null);
      setHoverEdge(null);
    }, 220);
  };
  useEffect(
    () => () => {
      window.clearTimeout(tipTimer.current);
      window.clearTimeout(tipLeave.current);
    },
    [],
  );
  // Premise tags: pointing at one names the relation and tints every tag of the same assumption.
  const [hoverTag, setHoverTag] = useState<string | null>(null);
  const enterTag = (e: ArgEdge, el: HTMLElement, delay = 120) => {
    window.clearTimeout(tipLeave.current);
    window.clearTimeout(tipTimer.current);
    setHoverTag(e.to);
    const wrap = wrapRef.current!.getBoundingClientRect();
    const r = el.getBoundingClientRect();
    const at = { key: e.key, x: r.right - wrap.left, y: r.top + r.height / 2 - wrap.top };
    tipTimer.current = window.setTimeout(() => setTip(at), delay);
  };
  const leaveTag = () => {
    setHoverTag(null);
    leaveEdge();
  };
  const tagClass = (e: ArgEdge) => {
    const parts = ["tag"];
    if (hoverTag === e.to) parts.push("is-hover");
    if (selected === e.to || selectedEdge === e.key) parts.push("is-selected");
    if (litOn && traced?.has(e.from) && traced.has(e.to)) parts.push("is-lit");
    return parts.join(" ");
  };

  // Escape closes the tooltip before anything else on the page.
  useEffect(() => {
    if (!tip) return;
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape") return;
      event.preventDefault();
      event.stopPropagation();
      setTip(null);
      setHoverEdge(null);
    };
    window.addEventListener("keydown", onKey, true);
    return () => window.removeEventListener("keydown", onKey, true);
  }, [tip]);

  // ---- Light ------------------------------------------------------------------------

  const edgeByKey = useMemo(() => new Map(fullGraph.edges.map((e) => [e.key, e])), [fullGraph]);

  const hoverTouch = useMemo(() => {
    if (!hoverEdge) return null;
    if (hoverEdge.startsWith("bus:")) {
      const parent = hoverEdge.slice(4);
      const ids = new Set([parent]);
      const keys = new Set<string>();
      for (const e of built.skeleton)
        if (e.from === parent && e.kind === "supports") {
          ids.add(e.to);
          keys.add(e.key);
        }
      return { ids, keys };
    }
    const e = built.skeleton.find((x) => x.key === hoverEdge);
    return e ? { ids: new Set([e.from, e.to]), keys: new Set([e.key]) } : null;
  }, [hoverEdge, built, edgeByKey]);

  const near = useMemo(() => {
    const id = selected;
    if (!id || !hasRec(layout, id)) return null;
    const mine = new Set(lidsOf(layout, id));
    const set = new Set(mine);
    for (const e of built.skeleton) {
      if (mine.has(e.from)) set.add(e.to);
      if (mine.has(e.to)) set.add(e.from);
    }
    return set;
  }, [selected, built, layout]);

  const litKeys = useMemo(() => {
    if (!traced) return new Set<string>();
    return new Set(built.skeleton.filter((e) => traced.has(recordOf(e.from)) && traced.has(recordOf(e.to))).map((e) => e.key));
  }, [traced, built]);

  const drawTiming = useMemo(() => {
    if (!litKeys.size || !selected || !trace) return new Map<string, { delay: number; dur: number; from: "start" | "end" }>();
    return traceTiming(
      built.skeleton.filter((e) => litKeys.has(e.key)),
      layout.rank,
      pick(layout, selected) ?? selected,
      trace,
    );
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [litKeys, trace, selected]);

  const traceKey = `${selected ?? ""}|${trace ?? ""}|${goal}`;
  // The route lights once the cards the trace unfolds have settled: one action, then the next.
  const [litShown, setLitShown] = useState<string | null>(null);
  const traceReady = !!traced && [...traced].every((id) => hasRec(layout, id) || graph.nodes.get(id)?.kind === "assumption") && !moving && !built.provisional;
  useEffect(() => {
    if (!traced) setLitShown(null);
    else if (traceReady) setLitShown(traceKey);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [traced, traceReady]);
  const litOn = !!traced && litShown === traceKey;

  const echoOn = compact && (echo?.size ?? 0) > 0;
  const previewOn = !!preview && preview.size > 0;
  const previewFolded = useMemo(
    () => (preview ? [...preview].filter((id) => goalReach.has(id) && !hasRec(layout, id) && !tagHolders.has(id)) : []),
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [preview, goalReach, layout],
  );

  const cardClass = (lid: string, node: ArgNode, leaf: boolean): string => {
    const id = recordOf(lid);
    const parts = ["card", `card--${node.kind}`];
    if (lid === goal) parts.push("card--root");
    if (lid !== id) parts.push("card--clone");
    if (leaf && lid !== goal) parts.push("card--leaf");
    if (id === selected) parts.push("is-selected");
    if (id === hoverRec || hoverTouch?.ids.has(lid)) parts.push("is-hover");
    const holdsTag = (rec: string) => !!tagsOf(rec).length && (tagsOf(rec).some((e) => e.to === selected) || (!!edgeObj && edgeObj.kind === "assumes" && edgeObj.from === rec));
    if (edgeObj && (edgeObj.from === id || edgeObj.to === id)) parts.push("is-edge-end");
    if (traced && litOn) parts.push(traced.has(id) ? "is-lit" : "is-quiet");
    else if (edgeObj) parts.push(edgeObj.from === id || edgeObj.to === id ? "" : "is-quiet");
    else if (near && id !== selected) parts.push(near.has(lid) ? "is-near" : "is-quiet");
    else if (selected && !near && tagHolders.has(selected)) parts.push(holdsTag(id) ? "is-near" : "is-quiet");
    if (echoOn) parts.push(echo!.has(id) ? "is-echo" : within ? "" : "is-quiet");
    if (previewOn && preview!.has(id)) parts.push("is-preview");
    if (exitShown.has(lid)) parts.push("is-exiting");
    return parts.filter(Boolean).join(" ");
  };

  const baseDim = litOn || !!edgeObj || (echoOn && !within);
  const emphasised = useMemo(() => {
    const keys = new Set<string>();
    const touch = (id: string | null | undefined) => {
      if (!id) return;
      for (const e of built.skeleton) if (e.from === id || e.to === id) keys.add(e.key);
    };
    if (!traced && selected) for (const lid of lidsOf(layout, selected)) touch(lid);
    touch(hover);
    hoverTouch?.keys.forEach((k) => keys.add(k));
    return keys;
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [built, selected, hover, hoverTouch, traced]);

  const roving = focusId && layout.boxes.has(focusId) ? focusId : (selected && pick(layout, selected)) || goal;
  const bounds = layoutBounds(layout);

  const cardIds = [...layout.boxes.keys(), ...[...exitShown].filter((id) => !layout.boxes.has(id))];
  const tipEdge = tip && !moving ? tip : null;

  // Relations in the drawn scope that the simplified drawing leaves out.
  const hiddenEdges = useMemo(() => [...built.implied].map((k) => edgeByKey.get(k)).filter((e): e is ArgEdge => !!e), [built.implied, edgeByKey]);

  // Screen-space labels: in compact and mark form, the goal, the selection and the record under the pointer or focus.
  const labelled = useMemo(() => {
    if (rep === "card") return [] as string[];
    const ids: string[] = [];
    // In compact form the plate keeps its own title, so the goal is labelled only as a mark.
    for (const id of [rep === "mark" ? goal : null, selected ? pick(layout, selected) : null, hover, focusId]) if (id && layout.boxes.has(id) && !ids.includes(id)) ids.push(id);
    return ids;
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [rep, goal, selected, hover, focusId, layout]);

  const showChips = !compact && mode === "steps" && rep !== "mark";
  const chipClick = (side: Side) => {
    const ids = chips.ids[side];
    if (!ids.length) return;
    userMovedSinceAsk.current = true;
    moveCamera(panToward(side, ids, builtRef.current.layout.boxes, viewRef.current, viewport()), true, CAMERA_MS);
  };

  const kindOf = (key: string) => built.plan.edges.get(key)?.kind ?? "supports";

  // The entrance: the first row left to right, and the band its lines draw through.
  const enterOrder = useMemo(() => {
    const ids = built.skeleton.filter((e) => e.from === goal).map((e) => e.to).filter((id) => layout.boxes.has(id));
    ids.sort((a, b) => layout.boxes.get(a)!.x - layout.boxes.get(b)!.x);
    return new Map(ids.map((id, i) => [id, i]));
  }, [built, layout, goal]);
  const enterMask = useMemo(() => {
    const root = layout.boxes.get(goal);
    if (!root || !enterOrder.size) return null;
    let bottom = root.y + root.h;
    for (const id of enterOrder.keys()) bottom = Math.max(bottom, layout.boxes.get(id)!.y);
    const b = layoutBounds(layout);
    return { x0: b.x0 - 50, x1: b.x1 + 50, y0: root.y + root.h - 2, y1: bottom + 2 };
  }, [layout, goal, enterOrder]);

  return (
    <div
      ref={wrapRef}
      className={`tree${compact ? " tree--compact" : ""}${rootW < 700 ? " tree--narrow" : ""}${moving ? " tree--moving" : ""}${traced ? " tree--traced" : ""}${entering ? " tree--entering" : ""}${!framed && !compact ? " tree--unframed" : ""}${baseDim ? " tree--dim" : ""}${reduced ? " tree--reduced" : ""}`}
      data-mode={mode}
      onClick={(event) => {
        if ((event.target as Element).closest?.(".card, button, a, .hit, .tree__ui")) return;
        if (selected) onSelect(null);
        if (selectedEdge) onEdgeSelect?.(null);
      }}
    >
      <div ref={worldRef} className="tree__world" style={{ width: Math.max(1, bounds.x1), height: Math.max(1, bounds.y1) }}>
        <svg className="tree__links" width={1} height={1} aria-hidden="true">
          {entering && enterMask && (
            <defs>
              <mask id={`${uid}-enter`} maskUnits="userSpaceOnUse" x={-100000} y={-100000} width={200000} height={200000}>
                <rect x={-100000} y={-100000} width={200000} height={200000} fill="#fff" />
                {/* The first row's lines draw upward into the plate: this cover shrinks toward the row. */}
                <rect className="enter-cover" x={enterMask.x0} y={enterMask.y0} width={enterMask.x1 - enterMask.x0} height={enterMask.y1 - enterMask.y0} fill="#000" />
              </mask>
            </defs>
          )}
          <g className="links" mask={entering && enterMask ? `url(#${uid}-enter)` : undefined}>
            {[...built.plan.buses.keys()].map((parent) => (
              <g key={parent}>
                <path ref={pathRef(`buscase:${parent}`)} className="casing" />
                <path ref={pathRef(`bus:${parent}`)} className="link link--supports" />
                <path ref={pathRef(`busf:${parent}`)} className="link link--supports" />
              </g>
            ))}
            {[...built.plan.edges.values()]
              .filter((pe) => !pe.bus)
              .map((pe) => (
                <g key={pe.key}>
                  <path ref={pathRef(`case:${pe.key}`)} className="casing" />
                  <path ref={pathRef(`edge:${pe.key}`)} className={`link link--${pe.kind}`} />
                </g>
              ))}
            {ghostsAndFresh.ghosts.map((g) => (
              <path key={g.key} ref={pathRef(`ghost:${g.key}`)} className={`link link--${g.kind} link--ghost`} />
            ))}
          </g>
          <g className="links-over">
            {[...emphasised]
              .filter((k) => built.plan.edges.has(k) && !(litOn && litKeys.has(k)))
              .map((k) => (
                <path key={k} ref={pathRef(`ov:${k}`)} className={`link link--${kindOf(k)} link--near`} />
              ))}
          </g>
          <g className="links-lit" key={traceKey}>
            {litOn && !reduced && (
              <defs>
                {[...litKeys].map((k, i) => {
                  const t = drawTiming.get(k) ?? { delay: 0, dur: 240, from: "start" as const };
                  return (
                    <mask key={k} id={`${uid}-m${i}`} maskUnits="userSpaceOnUse" x={-100000} y={-100000} width={200000} height={200000}>
                      <path
                        ref={pathRef(`mask:${k}`)}
                        pathLength={1}
                        className={`lit-mask lit-mask--${t.from}`}
                        style={{ ["--d" as string]: `${t.delay}ms`, ["--dur" as string]: `${t.dur}ms` }}
                      />
                    </mask>
                  );
                })}
              </defs>
            )}
            {[...(litOn ? litKeys : [])].map((k, i) => (
              <g key={k} mask={reduced ? undefined : `url(#${uid}-m${i})`}>
                <path ref={pathRef(`litcase:${k}`)} className="casing casing--lit" />
                <path ref={pathRef(`lit:${k}`)} className={`link link--${kindOf(k)} link--lit`} />
              </g>
            ))}
          </g>
          {edgeObj && built.plan.edges.has(edgeObj.key) && (
            <g className="links-sel">
              <path ref={pathRef(`sel:${edgeObj.key}`)} className={`link link--${edgeObj.kind} link--lit link--selected`} />
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
                  onPointerLeave={leaveEdge}
                  onClick={(event) => {
                    event.stopPropagation();
                    if (onEdgeSelect) onEdgeSelect(edgeKeyOf(pe.key));
                    else onSelect(recordOf(pe.from));
                  }}
                />
              ))}
            {[...built.plan.buses.keys()].map((parent) => (
              <path
                key={parent}
                ref={pathRef(`hitstem:${parent}`)}
                className="hit"
                onPointerEnter={(event) => enterEdge(`bus:${parent}`, event)}
                onPointerLeave={leaveEdge}
                onClick={(event) => {
                  event.stopPropagation();
                  onSelect(recordOf(parent));
                }}
              />
            ))}
          </g>
        </svg>
        {cardIds.map((lid) => {
          const id = recordOf(lid);
          const node = graph.nodes.get(id) ?? fullGraph.nodes.get(id)!;
          const all = usesOf(graph, id).filter((e) => e.kind !== "assumes");
          const uses = inputsOf(id);
          const outside = all.length - uses.length;
          const tags = tagsOf(id);
          const isRoot = lid === goal;
          const clone = lid !== id;
          const open = expanded.has(id);
          const leaf = uses.length === 0;
          const role = lens ? lensRole(node, lens) : "all";
          const tab = lid === roving ? 0 : -1;
          const source = isRoot && !compact && node.origin.place ? `${node.origin.label} · ${node.origin.place}` : (node.origin.place ?? node.origin.label);
          const sourceTitle = `${node.origin.label}${node.origin.locator ? `: ${node.origin.locator}` : ""}`;
          const usedBy = built.shared.get(id) ?? 0;
          return (
            <div
              key={lid}
              ref={cardRef(lid)}
              data-card={lid}
              data-record={id}
              data-region={node.region}
              data-slot={node.origin.slot}
              data-kind={node.kind}
              className={cardClass(lid, node, leaf)}
              style={{ width: clone ? (compact ? 184 : 176) : widthOf(node, isRoot, compact, rootW), ["--rank" as string]: layout.rank.get(lid) ?? 0, ["--enter-i" as string]: enterOrder.get(lid) ?? 0 }}
              role="group"
              aria-label={`${node.label}, ${kindName(node.kind)}${clone ? `, drawn once under each of the ${usedBy} records that use it` : ""}`}
              title={clone ? node.label : undefined}
              onClick={(event) => {
                if ((event.target as Element).closest?.(".card__inputs, .card__usedby, .tag, a, .card__body")) return;
                if (repRef.current === "mark") openMark(id, lid);
                else if (event.detail >= 2) toggle(id, lid);
                else onSelect(id);
              }}
              onKeyDown={(event) => onCardKey(lid, event)}
              onFocus={() => setFocusId(lid)}
              onPointerEnter={() => setHovered(lid)}
              onPointerLeave={() => setHovered(null)}
            >
              <div className="card__full">
                <p className="card__head">
                  <span className="caps card__kind">{kindName(node.kind)}</span>
                  <span className="card__src" title={sourceTitle}>
                    <span className="src-sq" aria-hidden="true" />
                    <span className="card__srcname">{source}</span>
                  </span>
                </p>
                <button
                  type="button"
                  className={`card__open${isRoot ? " plate__title" : ""}`}
                  tabIndex={tab}
                  aria-pressed={id === selected}
                  aria-label={`Open ${node.label}`}
                >
                  <span className={`card__title${node.kind === "declaration" ? " lean" : ""}`}>{node.kind === "declaration" ? <LeanName name={node.label} /> : node.label}</span>
                  {node.status === "open" && <span className="card__status"> · open</span>}
                </button>
                {tags.length > 0 && (
                  <div className="card__tags">
                    <span className="caps card__tagword">Assumes</span>
                    {tags.map((e) => (
                      <button
                        key={e.key}
                        type="button"
                        className={tagClass(e)}
                        tabIndex={tab}
                        aria-label={`Explicit assumption: ${node.label} assumes ${graph.nodes.get(e.to)?.label ?? e.to}. Open the step.`}
                        onClick={(event) => {
                          event.stopPropagation();
                          if (onEdgeSelect) onEdgeSelect(e.key);
                          else onSelect(e.to);
                        }}
                        title={graph.nodes.get(e.to)?.label ?? e.to}
                        onPointerEnter={(event) => enterTag(e, event.currentTarget)}
                        onPointerLeave={leaveTag}
                        onFocus={(event) => enterTag(e, event.currentTarget, 0)}
                        onBlur={leaveTag}
                      >
                        {tagTitle(tags, e, (x) => graph.nodes.get(x)?.label ?? x)}
                      </button>
                    ))}
                  </div>
                )}
                {isRoot && !compact ? (
                  rootContent && <div className="card__theorem card__body">{rootContent}</div>
                ) : (
                  <div className="card__foot">
                    {uses.length > 0 && !isRoot ? (
                      <button
                        type="button"
                        className={`card__inputs${open ? " is-open" : ""}`}
                        aria-expanded={open}
                        aria-label={`${open ? "Hide" : "Show"} the ${uses.length} recorded ${uses.length === 1 ? "input" : "inputs"} of ${node.label}`}
                        tabIndex={tab}
                        onClick={(event) => {
                          event.stopPropagation();
                          toggle(id, lid);
                        }}
                      >
                        <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true">
                          <path d="M2.5 3.5 L5 6.2 L7.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
                        </svg>
                        Inputs · {uses.length}
                        {outside > 0 && <span className="card__outside"> · {outside} outside</span>}
                      </button>
                    ) : !isRoot && !clone && !tags.length ? (
                      <span className="card__none">{outside > 0 ? `${outside} ${outside === 1 ? "input" : "inputs"} outside this account` : "No recorded inputs"}</span>
                    ) : null}
                    {clone && (
                      <button
                        type="button"
                        className="card__usedby"
                        tabIndex={tab}
                        aria-label={`Used by ${usedBy} records on this map. Open ${node.label}`}
                        onClick={(event) => {
                          event.stopPropagation();
                          onSelect(id);
                        }}
                      >
                        Used by {usedBy}
                      </button>
                    )}
                    {role !== "all" && !isRoot && !clone && (
                      <span className="card__cov">
                        <span className={`cov-mark${role === "support" ? " cov-mark--relied" : role === "outside" ? " cov-mark--outside" : ""}`} aria-hidden="true" />
                        {role === "direct" ? "with a passage" : role === "support" ? "used without a passage" : "not used"}
                      </span>
                    )}
                  </div>
                )}
              </div>
              <div className="card__compact" aria-hidden="true">
                <span className="src-sq" />
                <span className="card__ctitle">{node.label}</span>
              </div>
              {tags.length > 0 && (
                <span className="card__notches" aria-hidden="true">
                  {tags.map((e) => (
                    <i key={e.key} className={tagClass(e)} />
                  ))}
                </span>
              )}
            </div>
          );
        })}
        <svg className="tree__heads" width={1} height={1} aria-hidden="true">
          <g className="heads">
            {[...built.plan.buses.keys()].map((parent) => (
              <path key={parent} ref={pathRef(`head:${parent}`)} className="head head--supports" />
            ))}
            {[...built.plan.edges.values()]
              .filter((pe) => !pe.bus && pe.arrow)
              .map((pe) => (
                <path key={pe.key} ref={pathRef(`ahead:${pe.key}`)} className={`head head--${pe.kind}`} />
              ))}
            {[...built.plan.edges.values()]
              .filter((pe) => pe.bus && edgeByKey.get(edgeKeyOf(pe.key))?.application)
              .map((pe) => (
                <path key={pe.key} ref={pathRef(`ring:${pe.key}`)} className="ring" />
              ))}
          </g>
          <g className="heads-over">
            {[...emphasised]
              .filter((k) => built.plan.edges.get(k)?.arrow && !(litOn && litKeys.has(k)))
              .map((k) => (
                <path key={k} ref={pathRef(`ovhead:${k}`)} className={`head head--${kindOf(k)} head--near`} />
              ))}
          </g>
          <g className="heads-lit" key={traceKey}>
            {[...(litOn ? litKeys : [])]
              .filter((k) => built.plan.edges.get(k)!.arrow)
              .map((k) => {
                const t = drawTiming.get(k) ?? { delay: 0, dur: 240, from: "start" as const };
                // The head appears when its line arrives (at its consumer end).
                const at = t.from === "start" ? t.delay + t.dur - 40 : t.delay;
                return <path key={k} ref={pathRef(`lithead:${k}`)} className={`head head--${kindOf(k)} head--lit`} style={{ ["--d" as string]: `${Math.max(0, at)}ms` }} />;
              })}
          </g>
          {edgeObj && built.plan.edges.get(edgeObj.key)?.arrow && <path ref={pathRef(`selhead:${edgeObj.key}`)} className={`head head--${edgeObj.kind} head--lit`} />}
        </svg>
      </div>

      {/* Screen-space layer: never scales with the map. */}
      <div className="tree__labels" aria-hidden="true">
        {labelled.map((id) => (
          <span key={id} ref={labelRef(id)} className={`tree__label${id === selected ? " is-selected" : ""}${id === goal ? " is-goal" : ""}`}>
            {graph.nodes.get(recordOf(id))?.label ?? id}
          </span>
        ))}
      </div>
      {showChips &&
        SIDES.map((side) =>
          chips.ids[side].length && chips.at[side] !== null ? (
            <button
              key={side}
              type="button"
              className={`tree__ui tree__chip tree__chip--${side}`}
              style={chipStyle(side, insets, chips.at[side]!)}
              onClick={() => chipClick(side)}
              aria-label={`Show ${uniqueCount(chips.ids[side])} more ${uniqueCount(chips.ids[side]) === 1 ? "record" : "records"} ${side === "up" ? "above" : side === "down" ? "below" : `to the ${side}`}`}
            >
              {chipText(side, uniqueCount(chips.ids[side]))}
            </button>
          ) : null,
        )}
      {!compact && (previewFolded.length > 0 || hiddenEdges.length > 0) && (
        <div
          ref={notesRef}
          className={`tree__ui tree__notes${chips.notes?.top ? " tree__notes--top" : ""}`}
          style={chips.notes?.top ? { left: chips.notes.x, top: insets.top } : { left: chips.notes?.x ?? insets.left, bottom: insets.bottom }}
          onClick={(event) => event.stopPropagation()}
        >
          {previewFolded.length > 0 && (
            <p className="tree__note" role="status">
              {previewFolded.length === 1 ? "1 linked record is in a collapsed branch" : `${previewFolded.length} linked records are in collapsed branches`}
              <button type="button" className="tree__note-action" onClick={() => doRevealIds(previewFolded)}>
                {previewFolded.length === 1 ? "Show it" : "Show them"}
              </button>
            </p>
          )}
          <SimplifiedMap graph={fullGraph} hidden={hiddenEdges} onChoose={(key) => (onEdgeSelect ? onEdgeSelect(key) : onSelect(edgeByKey.get(key)?.from ?? null))} />
        </div>
      )}
      {tipEdge && (
        <EdgeTip
          tip={tipEdge}
          graph={fullGraph}
          edge={tipEdge.key.startsWith("bus:") ? null : (edgeByKey.get(edgeKeyOf(tipEdge.key)) ?? null)}
          bus={tipEdge.key.startsWith("bus:") ? { parent: recordOf(tipEdge.key.slice(4)), count: built.skeleton.filter((e) => e.from === tipEdge.key.slice(4) && e.kind === "supports").length } : null}
          wrap={wrapRef.current}
          compact={compact}
          onEnter={() => window.clearTimeout(tipLeave.current)}
          onLeave={leaveEdge}
        />
      )}
    </div>
  );
});

const uniqueCount = (lids: readonly string[]) => new Set(lids.map(recordOf)).size;

/** A tag shows a short title; the full one is its accessible name and tooltip. */
function shortTitle(label: string): string {
  const t = label.split(/[:;]/)[0].trim();
  return t.length > 40 ? `${t.slice(0, 38).replace(/\s+\S*$/, "")}…` : t;
}

/** Short titles on one card, unless two would read the same: then the full titles (clipped by width). */
function tagTitle(tags: readonly ArgEdge[], e: ArgEdge, label: (id: string) => string): string {
  const short = tags.map((t) => shortTitle(label(t.to)));
  if (new Set(short).size === short.length) return shortTitle(label(e.to));
  // "Scalar-value interface: Brownian space…" twice on one card: the part after the colon tells them apart.
  const full = label(e.to);
  const rest = full.includes(":") ? full.slice(full.indexOf(":") + 1).trim() : full;
  return rest.charAt(0).toUpperCase() + rest.slice(1);
}

function chipStyle(side: Side, insets: Insets, at: number): React.CSSProperties {
  if (side === "left") return { left: Math.max(4, insets.left - 12), top: at };
  if (side === "right") return { right: Math.max(4, insets.right - 12), top: at };
  if (side === "up") return { top: Math.max(4, insets.top - 12), left: at };
  return { bottom: insets.bottom + 4, left: at };
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

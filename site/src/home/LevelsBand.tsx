// One argument at each level. The rail lists the levels from the Lean down to the film;
// beside it the main theorem's real argument, laid out by the map's own engine, closes up
// to the records the chosen level uses. Each paper is a narrower part of one graph, and
// this band shows that as the graph narrowing. Every tile opens that step side by side.
// The drawing is plain DOM and CSS transitions over the engine's boxes, so it adds no
// work to the page beyond its layouts, which are computed once.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { prefersReducedMotion } from "../app/theme";
import { routeHref } from "../app/router";
import { PAPER_NAMES } from "../app/papers";
import { lensRole, type ArgGraph } from "../model/graph";
import { recordLine, shortTitle } from "../compare/useAlignment";
import { levelCounts } from "../map/levels";
import { reach, scopedGraph, usesOf, visibleEdges, visibleSet } from "../map/treeModel";
import { transitiveReduction } from "../map/engine/skeleton";
import { layoutScope, recordOf, splitSharedLeaves } from "../map/engine/occurrences";
import { layoutBounds, layoutTree } from "../map/engine/layout";
import { roundedPath, route } from "../map/engine/router";
import { METRICS_COMPACT, type EngineEdge, type Size } from "../map/engine/types";

type LevelId = "lean" | Stage;

const TILE: Size = { w: 136, h: 40 };
const ROOT: Size = { w: 248, h: 42 };
/** The map's compact spacing with no arrowheads, drawn tight enough to read as one figure. */
const SPACING = { ...METRICS_COMPACT, arrow: 0, gapMin: 24, trackSp: 5, padTop: 10, padBottom: 6 };

interface Tile {
  id: string;
  lid: string;
  x: number;
  y: number;
  w: number;
  h: number;
  root: boolean;
  assumption: boolean;
}

interface Drawing {
  tiles: Map<string, Tile>;
  lines: string[];
  x: number;
  y: number;
  w: number;
  h: number;
}

/**
 * The argument restricted to the records a level discusses. A paper can skip a step, so
 * two kept records stay joined when a chain of skipped records connects them: the drawing
 * shows the paper's own narrower graph, with the step it skipped closed up.
 */
function contract(visible: ReadonlySet<string>, edges: readonly EngineEdge[], keep: ReadonlySet<string>, assumption: (id: string) => boolean): { visible: Set<string>; edges: EngineEdge[] } {
  const out = new Map<string, string[]>();
  for (const e of edges) out.set(e.from, [...(out.get(e.from) ?? []), e.to]);
  const kept = new Set([...visible].filter((id) => keep.has(id) && !assumption(id)));
  const joined: EngineEdge[] = [];
  for (const from of kept) {
    const seen = new Set<string>();
    const stack = [...(out.get(from) ?? [])];
    while (stack.length) {
      const id = stack.pop()!;
      if (seen.has(id)) continue;
      seen.add(id);
      if (kept.has(id)) joined.push({ key: `${from}→${id}→supports`, from, to: id, kind: "supports" });
      else stack.push(...(out.get(id) ?? []));
    }
  }
  return { visible: kept, edges: joined };
}

function drawingOf(full: ArgGraph, goal: string, keep: ReadonlySet<string> | null): Drawing {
  const graph = scopedGraph(full, goal);
  const all = new Set([...reach(graph, goal)].filter((id) => id !== goal && usesOf(graph, id).length));
  const whole = visibleSet(graph, goal, all);
  const wholeEdges = visibleEdges(graph, goal, whole, all);
  const isAssumption = (id: string) => graph.nodes.get(id)?.kind === "assumption";
  const { visible, edges } = keep ? contract(whole, wholeEdges, keep, isAssumption) : { visible: whole, edges: wholeEdges };
  const skeleton = transitiveReduction(visible, edges);
  const scope = layoutScope(goal, visible, skeleton.edges, (id) => graph.nodes.get(id)?.kind === "assumption");
  const split = splitSharedLeaves(goal, scope.nodes, scope.edges);
  const { layout, plan } = layoutTree({
    root: goal,
    nodes: split.nodes,
    edges: split.edges,
    size: (lid) => (lid === goal ? ROOT : TILE),
    metrics: SPACING,
  });
  const routed = route(plan, { boxes: layout.boxes, dummyX: (key) => layout.dummies.get(key)!.x });
  const radius = SPACING.radius;
  const lines: string[] = [];
  for (const edge of plan.edges.values()) {
    const line = routed.edges.get(edge.key);
    if (line) lines.push(roundedPath(line.points, radius));
  }
  for (const [, bus] of routed.buses) lines.push(roundedPath(bus.stem, radius));
  const tiles = new Map<string, Tile>();
  for (const [lid, box] of layout.boxes) {
    const id = recordOf(lid);
    tiles.set(lid, { id, lid, x: box.x, y: box.y, w: box.w, h: box.h, root: lid === goal, assumption: graph.nodes.get(id)?.kind === "assumption" });
  }
  const b = layoutBounds(layout);
  return { tiles, lines, x: b.x0, y: b.y0, w: b.x1 - b.x0, h: b.y1 - b.y0 };
}

const plural = (n: number, one: string, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;
const base = import.meta.env.BASE_URL;

/** The levels of the funnel, widest first. */
const STAGES: Stage[] = ["long", "short", "expository"];

export function LevelsBand({ id, leanModules }: { id: string; leanModules: number }) {
  const edition = useEdition();
  const { graph } = edition;
  const goal = edition.graph.goals.find((g) => g === "full_support") ?? edition.graph.goals[0];
  const version = edition.context;
  const [level, setLevel] = useState<LevelId>("long");

  const nodes = useMemo(() => [...graph.nodes.values()], [graph]);
  const total = nodes.length;
  const counts = useMemo(() => {
    const out = {} as Record<LevelId, number>;
    for (const stage of STAGES) out[stage] = nodes.filter((n) => lensRole(n, stage) === "direct").length;
    out.lean = nodes.filter((n) => (recordLine(n.id)?.lean ?? 0) > 0).length;
    return out;
  }, [nodes]);

  const drawings = useMemo(() => {
    const within = (stage: Stage) => new Set(nodes.filter((n) => n.id === goal || lensRole(n, stage) === "direct").map((n) => n.id));
    const whole = drawingOf(graph, goal, null);
    return {
      lean: whole,
      long: drawingOf(graph, goal, within("long")),
      short: drawingOf(graph, goal, within("short")),
      expository: drawingOf(graph, goal, within("expository")),
    } satisfies Record<LevelId, Drawing>;
    // The stored edges attach to the same graph object as they arrive.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [graph, goal, version, nodes]);

  const widest = drawings.lean;
  const current = drawings[level];
  const everyTile = useMemo(() => {
    const seen = new Map<string, Tile>();
    for (const d of Object.values(drawings)) for (const [lid, t] of d.tiles) if (!seen.has(lid)) seen.set(lid, t);
    return [...seen.values()];
  }, [drawings]);

  const stageRef = useRef<HTMLDivElement>(null);
  const [scale, setScale] = useState(1);
  // The page's one orchestrated moment: on first sight the argument closes up from the
  // long record to the exposition, once. A reader's own choice ends it at once.
  const chose = useRef(false);
  const choose = (next: LevelId) => {
    chose.current = true;
    setLevel(next);
  };
  useEffect(() => {
    const el = stageRef.current;
    if (!el || typeof IntersectionObserver === "undefined" || prefersReducedMotion()) return;
    const timers: number[] = [];
    const observer = new IntersectionObserver(([entry]) => {
      if (!entry.isIntersecting) return;
      observer.disconnect();
      const step = (next: LevelId, after: number) => timers.push(window.setTimeout(() => chose.current || setLevel(next), after));
      step("short", 1500);
      step("expository", 3000);
    }, { threshold: 0.5 });
    observer.observe(el);
    return () => {
      observer.disconnect();
      timers.forEach((timer) => window.clearTimeout(timer));
    };
  }, []);
  useLayoutEffect(() => {
    const el = stageRef.current;
    if (!el) return;
    const measure = () => setScale(Math.min(1, el.clientWidth / widest.w));
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, [widest.w]);

  const argumentSize = useMemo(() => levelCounts(graph, reach(scopedGraph(graph, goal), goal)), [graph, goal]);
  const leftover = (widest.w - current.w) / 2;
  const offset = (t: Tile, d: Drawing) => ({ x: t.x - d.x + (d === widest ? 0 : leftover), y: t.y - d.y });

  const rows: { id: LevelId; name: string; who: string; count: string; read?: string; readWord?: string; stage?: Stage }[] = [
    {
      id: "lean",
      name: "The Lean proof",
      who: "OpenAI’s statements and proofs, written for a computer to check.",
      count: `${plural(leanModules, "source file")}, linked to ${counts.lean} of the ${total} records`,
      read: routeHref({ view: "lean" }),
      readWord: "Browse the Lean",
    },
    ...STAGES.map((stage) => ({
      id: stage,
      stage,
      name: PAPER_NAMES[stage].short,
      who: PAPER_NAMES[stage].reader,
      count: `${counts[stage]} of the ${total} records`,
      read: routeHref({ view: "read", stage }),
      readWord: "Read it here",
    })),
  ];

  return (
    <section className="front__band levels" id={id} aria-labelledby="front-levels">
      <h2 id="front-levels" className="front__bandtitle">
        One argument at four levels
      </h2>
      <p className="front__text">
        The argument is one graph of {total} records: claims, assumptions and Lean declarations, joined by what uses what. Each
        paper keeps a narrower part of that graph for a wider reader. Choose a level to see what it keeps, and open any step
        to compare it across the levels.
      </p>
      <div className="levels__body">
        <ol className="levels__rail">
          {rows.map((row) => {
            const share = row.id === "lean" ? counts.lean / total : counts[row.id] / total;
            const pdf = row.stage ? PAPER_PDFS[row.stage] : null;
            const page = pdf?.firstPage;
            return (
              <li
                key={row.id}
                className={`levels__row${level === row.id ? " is-chosen" : ""}`}
                onPointerEnter={(event) => {
                  if (event.pointerType === "mouse") choose(row.id);
                }}
                onFocusCapture={() => choose(row.id)}
                onClick={() => choose(row.id)}
              >
                <div className="levels__sheet" aria-hidden="true">
                  {page ? (
                    <img
                      src={`${base}${page.src}`}
                      srcSet={page.srcSet.split(", ").map((entry) => `${base}${entry}`).join(", ")}
                      sizes="60px"
                      alt=""
                      width={page.width}
                      height={page.height}
                      loading="lazy"
                      decoding="async"
                    />
                  ) : (
                    <span className="levels__code">
                      theorem full_support (W) (γ) (hmin) : FullSupportConclusion W γ := by have hμ := parameterMeasure_isStieltjes γ
                    </span>
                  )}
                </div>
                <div className="levels__text">
                  <h3 className="levels__name">{row.name}</h3>
                  <p className="levels__who">{row.who}</p>
                  <p className="levels__count">
                    <span className="levels__bar" aria-hidden="true">
                      <span style={{ width: `${Math.round(share * 100)}%` }} />
                    </span>
                    {row.count}
                  </p>
                  <p className="levels__links">
                    <a href={row.read}>
                      {row.readWord}
                      <span className="sr-only">: {row.name}</span>
                    </a>
                    {pdf ? (
                      <a href={`${base}${pdf.path}`} target="_blank" rel="noopener">
                        PDF, {plural(pdf.pages, "page")}
                        <span className="sr-only">: {row.name}</span>
                      </a>
                    ) : null}
                  </p>
                </div>
              </li>
            );
          })}
        </ol>

        <figure className="levels__figure">
          <figcaption className="levels__cap">
            {level === "lean" ? (
              <>The argument for the main theorem. Marked steps are linked to Lean declarations.</>
            ) : (
              <>
                {PAPER_NAMES[level].short}: {argumentSize[level]} of the {argumentSize.all} records in the argument for the main theorem.
              </>
            )}
          </figcaption>
          <div ref={stageRef} className="levels__stage" style={{ height: widest.h * scale }}>
            <div className="levels__world" style={{ width: widest.w, height: widest.h, transform: `scale(${scale})` }}>
              <svg className="levels__lines" width={widest.w} height={widest.h} aria-hidden="true">
                {(Object.entries(drawings) as [LevelId, Drawing][])
                  .filter(([key]) => key !== "lean")
                  .map(([key, d]) => (
                    <g
                      key={key}
                      className={level === key || (level === "lean" && key === "long") ? "is-shown" : undefined}
                      transform={`translate(${-d.x + (d === widest ? 0 : (widest.w - d.w) / 2)} ${-d.y})`}
                    >
                      {d.lines.map((path, i) => (
                        <path key={i} d={path} />
                      ))}
                    </g>
                  ))}
              </svg>
              {everyTile.map((tile) => {
                const here = current.tiles.get(tile.lid);
                const at = here ? offset(here, current) : offset(tile, widest.tiles.has(tile.lid) ? widest : current);
                const title = shortTitle(tile.id, graph.nodes.get(tile.id)?.label ?? tile.id);
                const hasLean = (recordLine(tile.id)?.lean ?? 0) > 0;
                return (
                  <a
                    key={tile.lid}
                    href={routeHref({ view: "compare", node: tile.id })}
                    className={`levels__tile${tile.root ? " levels__tile--root" : ""}${tile.assumption ? " levels__tile--assumption" : ""}${here ? "" : " is-gone"}${level === "lean" && hasLean ? " is-lean" : ""}`}
                    style={{ width: here?.w ?? tile.w, height: here?.h ?? tile.h, transform: `translate(${at.x}px, ${at.y}px)` }}
                    tabIndex={here ? undefined : -1}
                    aria-hidden={here ? undefined : true}
                    title={graph.nodes.get(tile.id)?.label}
                  >
                    {title}
                  </a>
                );
              })}
            </div>
          </div>
        </figure>
      </div>
    </section>
  );
}

// One argument at each level. The rail lists the levels from the Lean down to the film;
// beside it the main theorem's real argument, laid out by the map's own engine, closes up
// to the records the chosen level uses. Each paper is a narrower part of one graph, and
// this band shows that as the graph narrowing. Every tile opens that step side by side.
// The drawing is plain DOM and CSS transitions over the engine's boxes, so it adds no
// work to the page beyond its layouts, which are computed once.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import site from "@instance/site";
import { SITE_FACTS } from "virtual:site-facts";
import type { Account as Stage } from "../api/types";
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
import { countKinds, kindsInWords } from "./recordKinds";

type LevelId = "lean" | Stage;

/**
 * Where each level draws its own goal (#257), the drawing is a handful of records wide, so its
 * cards are sized for a whole short title on up to three lines and the drawing may grow past its
 * natural size to fill the column (wide.css sets the type in pixels to match). The SK site keeps
 * its compact cards.
 */
const ROOMY = Boolean(site.levelGoals);
const TILE: Size = ROOMY ? { w: 132, h: 54 } : { w: 136, h: 40 };
const ROOT: Size = ROOMY ? { w: 264, h: 46 } : { w: 248, h: 42 };
/** The map's compact spacing with no arrowheads, drawn tight enough to read as one figure. */
const SPACING = { ...METRICS_COMPACT, arrow: 0, gapMin: ROOMY ? 12 : 24, trackSp: 5, padTop: 10, padBottom: 6 };
/** How far the drawing may grow past its natural size. */
const MAX_SCALE = ROOMY ? 1.4 : 1;
/** A level whose own drawing is no more than its goal and one record draws the short paper's tree instead. */
const OWN_TREE_MIN = 3;

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

/**
 * The level a reader last chose, kept while the page's scripts stay loaded, so that Back from
 * a record opened from the tree returns to the same tree (#257; the SK band replays its opening).
 */
let lastChosen: LevelId | null = null;

/** The levels of the funnel, widest first. */
const STAGES: Stage[] = ["long", "short", "expository"];

export function LevelsBand({ id, leanModules }: { id: string; leanModules: number | null }) {
  const edition = useEdition();
  const { graph } = edition;
  const goal = edition.graph.goals.find((g) => g === site.mainGoal) ?? edition.graph.goals[0];
  const version = edition.context;
  // Where a level draws its own goal (#257), the long record records no steps between its
  // results, so the band opens on the short paper and the Lean level draws the whole argument.
  const [level, setLevel] = useState<LevelId>(site.levelGoals ? (lastChosen ?? "short") : "long");

  const nodes = useMemo(() => [...graph.nodes.values()], [graph]);
  const total = nodes.length;
  const counts = useMemo(() => {
    const out = {} as Record<LevelId, number>;
    for (const stage of STAGES) out[stage] = nodes.filter((n) => lensRole(n, stage) === "direct").length;
    out.lean = nodes.filter((n) => (recordLine(n.id)?.lean ?? 0) > 0).length;
    return out;
  }, [nodes]);

  // The goal each level draws: the main theorem, or that paper's own record of it (site.levelGoals).
  const goalOf = (stage: Stage) => {
    const own = site.levelGoals?.[stage];
    return own && graph.nodes.has(own) ? own : goal;
  };
  const drawings = useMemo(() => {
    const within = (stage: Stage) => new Set(nodes.filter((n) => n.id === goalOf(stage) || lensRole(n, stage) === "direct").map((n) => n.id));
    // The Lean level draws the same steps as the long record, so it shares that drawing:
    // its cards stay where they are and only their marks change.
    const long = drawingOf(graph, goalOf("long"), within("long"));
    const short = drawingOf(graph, goalOf("short"), within("short"));
    if (!site.levelGoals) return { lean: long, long, short, expository: drawingOf(graph, goalOf("expository"), within("expository")) } satisfies Record<LevelId, Drawing>;
    // Where a level draws its own goal, the Lean's own tree is of declarations, not of these
    // records, and a paper may state too few of the argument's records to make a tree. Those
    // levels draw the short paper's tree with their own records marked (borrowed, below).
    const own = (d: Drawing) => (d.tiles.size >= OWN_TREE_MIN ? d : short);
    return {
      lean: short,
      long: own(long),
      short,
      expository: own(drawingOf(graph, goalOf("expository"), within("expository"))),
    } satisfies Record<LevelId, Drawing>;
    // The stored edges attach to the same graph object as they arrive.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [graph, goal, version, nodes]);

  // The SK site draws one argument, widest at the long record; where a level draws its own
  // goal, the stage is as wide and as tall as the largest drawing.
  const unique = useMemo(() => [...new Set(Object.values(drawings))], [drawings]);
  const widest = useMemo<Drawing>(() => {
    if (!site.levelGoals) return drawings.lean;
    const all = Object.values(drawings);
    const wide = all.reduce((a, b) => (b.w > a.w ? b : a));
    return { ...wide, h: Math.max(...all.map((d) => d.h)) };
  }, [drawings]);
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
    if (site.levelGoals) lastChosen = next;
    setLevel(next);
  };
  useEffect(() => {
    const el = stageRef.current;
    // Where a level draws its own goal (#257), the band stays on the short paper, the main
    // theorem's level, until the reader chooses another.
    if (site.levelGoals) return;
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
    const measure = () => setScale(Math.min(MAX_SCALE, el.clientWidth / widest.w));
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, [widest.w]);

  const levelGoal = level === "lean" ? goal : goalOf(level);
  // eslint-disable-next-line react-hooks/exhaustive-deps
  const argumentSize = useMemo(() => levelCounts(graph, reach(scopedGraph(graph, levelGoal), levelGoal)), [graph, levelGoal]);
  const argumentName = levelGoal === goal ? "the main theorem" : (graph.nodes.get(levelGoal)?.label ?? levelGoal);
  const leftover = (widest.w - current.w) / 2;
  // A level drawn on the short paper's tree marks its own records there.
  const borrowed = Boolean(site.levelGoals) && level !== "short" && current === drawings.short;
  const marks = (id: string) => {
    if (!borrowed) return false;
    if (level === "lean") return (recordLine(id)?.lean ?? 0) > 0;
    const node = graph.nodes.get(id);
    return !!node && lensRole(node, level) === "direct";
  };
  const drawn = [...new Set([...current.tiles.values()].map((t) => t.id))];
  const marked = drawn.filter(marks).length;
  const offset = (t: Tile, d: Drawing) => ({ x: t.x - d.x + (d.tiles === widest.tiles ? 0 : leftover), y: t.y - d.y });

  // An instance that sorts its records (#257) says what they are; the SK site calls each a step.
  const kindOf = site.recordKind;
  const kinds = useMemo(() => (kindOf ? countKinds(nodes, kindOf) : null), [nodes, kindOf]);
  const levelKinds = (stage: Stage) => (kindOf ? kindsInWords(countKinds(nodes.filter((n) => lensRole(n, stage) === "direct"), kindOf), true) : "");
  const noun = kindOf ? "records" : "steps";

  const rows: { id: LevelId; name: string; who: string; count: string; read?: string; readWord?: string; stage?: Stage }[] = [
    {
      id: "lean",
      name: "The Lean proof",
      who: site.leanLevelWho,
      count: `${leanModules === null ? "" : `${plural(leanModules, "source file")}, `}linked to ${counts.lean} of the ${total} ${noun} on this site`,
      read: routeHref({ view: "lean" }),
      readWord: "Open the Lean index",
    },
    ...STAGES.map((stage) => ({
      id: stage,
      stage,
      name: PAPER_NAMES[stage].short,
      who: PAPER_NAMES[stage].reader,
      count: `${kindOf ? levelKinds(stage) : `${counts[stage]} of the ${total} steps on this site`}${SITE_FACTS.ties ? `${kindOf ? ";" : ","} ${SITE_FACTS.ties.papers[stage].statements} marked statements, ${SITE_FACTS.ties.papers[stage].withLean} with Lean` : ""}`,
      read: routeHref({ view: "read", stage }),
      readWord: "Read it here",
    })),
  ];

  return (
    <section className="front__band levels" id={id} aria-labelledby="front-levels">
      <h2 id="front-levels" className="front__bandtitle">
        One argument at four levels
      </h2>
      {kinds ? (
        <p className="front__text">
          The site holds {total.toLocaleString("en-GB")} records joined by what uses what: {kindsInWords(kinds)}. Each paper below the Lean states fewer of them than the one above it, for a wider readership. Choose a level to see which records it states, and open any record to compare it across the levels.
        </p>
      ) : (
        <p className="front__text">
          The argument is one graph of {total} steps: claims, assumptions and Lean declarations, joined by what uses what. Each paper below the Lean covers fewer of those steps than the one above it, for a wider readership. Choose a level to see which steps it covers, and open any step to compare it across the levels.
        </p>
      )}
      <div className="levels__body">
        <ol className="levels__rail">
          {rows.map((row) => {
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
                  ) : site.levelsLeanSnippet ? (
                    <span className="levels__code">{site.levelsLeanSnippet}</span>
                  ) : null}
                </div>
                <div className="levels__text">
                  <h3 className="levels__name">{row.name}</h3>
                  <p className="levels__who">{row.who}</p>
                  <p className="levels__count">{row.count}</p>
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
            {borrowed && level === "lean" ? (
              <>The Lean proof has no tree of these records of its own, so this is the short paper’s tree for {argumentName}: the {marked} of its {drawn.length} records linked to Lean declarations are marked.</>
            ) : borrowed && level !== "lean" ? (
              marked === 0 ? (
                <>{PAPER_NAMES[level].short}: none of the {argumentSize.all} {noun} in the argument for {argumentName}, so it has no tree of its own. This is the short paper’s tree.</>
              ) : (
                <>{PAPER_NAMES[level].short} has no tree of its own for {argumentName}, so this is the short paper’s tree: the {marked} of its {drawn.length} records {PAPER_NAMES[level].short.toLowerCase()} states are marked.</>
              )
            ) : level === "lean" ? (
              <>The argument for the main theorem. Marked steps are linked to Lean declarations.</>
            ) : (
              <>
                {argumentSize[level] === 0
                  ? `${PAPER_NAMES[level].short}: none of the ${argumentSize.all} ${noun} in the argument for ${argumentName}.`
                  : `${PAPER_NAMES[level].short}: ${argumentSize[level]} of the ${argumentSize.all} ${noun} in the argument for ${argumentName}.`}
              </>
            )}
          </figcaption>
          <div ref={stageRef} className="levels__stage" style={{ height: widest.h * scale }}>
            <div className="levels__world" style={{ width: widest.w, height: widest.h, transform: `scale(${scale})` }}>
              <svg className="levels__lines" width={widest.w} height={widest.h} aria-hidden="true">
                {unique.map((d, key) => (
                  <g
                    key={key}
                    className={d === current ? "is-shown" : undefined}
                    transform={`translate(${-d.x + (d.tiles === widest.tiles ? 0 : (widest.w - d.w) / 2)} ${-d.y})`}
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
                    className={`levels__tile${tile.root ? " levels__tile--root" : ""}${tile.assumption ? " levels__tile--assumption" : ""}${here ? "" : " is-gone"}${level === "lean" && hasLean ? " is-lean" : ""}${here && level !== "lean" && marks(tile.id) ? " is-marked" : ""}`}
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

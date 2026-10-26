// The checks at a glance: the argument for the main result with each record shaded by
// the checks recorded about it, and every check record as one square, grouped by kind.
// Both use the same shading, so a reader sees where checks were run and where they were
// not before reading any table. Only a recorded failure is coloured (DESIGN.md).

import { useLayoutEffect, useMemo, useRef, useState } from "react";
import { useEdition } from "../app/data";
import { routeHref } from "../app/router";
import { mainGoal } from "../map/TheoremPlate";
import { recordOf } from "../map/engine/occurrences";
import { METRICS } from "../map/engine/types";
import { useArgumentDrawing } from "../home/ArgumentFigure";
import { CHECK_KINDS, CHECK_ORDER, groupByKind, type EvidenceCard } from "./summary";
import "../map/tree.css";

/** What the checks recorded about one record add up to. */
type Standing = "failed" | "passed" | "partly" | "unrun" | "none";

const STANDING_WORDS: Record<Standing, string> = {
  failed: "a check failed",
  passed: "every check passed",
  partly: "some checks passed",
  unrun: "checks recorded, none passed",
  none: "no check recorded",
};

const OUTCOME_ORDER = ["failed", "passed", "unavailable", "not_run"] as const;
/** Checks that test a statement or its proof. Source-file checks compare a file's bytes, so they do not shade a record. */
const SHADING_KINDS = new Set(["lean_build", "comparator", "extraction", "semantic_review"]);
const OUTCOME_WORDS: Record<string, string> = { passed: "passed", failed: "failed", unavailable: "unavailable", not_run: "not run" };

function standingOf(statuses: string[]): Standing {
  if (!statuses.length) return "none";
  if (statuses.includes("failed")) return "failed";
  const passed = statuses.filter((s) => s === "passed").length;
  if (passed === statuses.length) return "passed";
  return passed ? "partly" : "unrun";
}

export function CheckMap() {
  const edition = useEdition();
  const { graph, map } = edition;
  const goal = mainGoal(edition);
  const drawing = useArgumentDrawing(graph, goal, edition.context);
  const cards = map.records.evidence as EvidenceCard[];
  const groups = useMemo(() => groupByKind(cards).filter((g) => g.cards.length), [cards]);

  // Each record's checks: the full records name their subjects; a record's own citations add the rest.
  const checksOf = useMemo(() => {
    const status = new Map(cards.map((c) => [c.id, c]));
    const by = new Map<string, Set<string>>();
    const add = (record: string, check: string) => {
      if (!by.has(record)) by.set(record, new Set());
      by.get(record)!.add(check);
    };
    for (const e of edition.evidence ?? []) for (const s of e.subject_ids) add(s, e.id);
    for (const [id, node] of graph.nodes) for (const e of node.evidenceIds ?? []) add(id, e);
    const out = new Map<string, EvidenceCard[]>();
    for (const [id, set] of by) out.set(id, [...set].map((e) => status.get(e)).filter((c): c is EvidenceCard => !!c));
    return out;
  }, [edition.evidence, graph, cards]);

  const tiles = drawing.tiles.map((t) => {
    const id = recordOf(t.lid);
    const checks = checksOf.get(id) ?? [];
    const node = graph.nodes.get(id);
    const parts = CHECK_ORDER.map((kind) => {
      const of = checks.filter((c) => c.kind === kind);
      if (!of.length) return "";
      const counts = OUTCOME_ORDER.map((o) => [o, of.filter((c) => c.status === o).length] as const).filter(([, n]) => n);
      return `${CHECK_KINDS[kind]?.title ?? kind}: ${counts.map(([o, n]) => `${n} ${OUTCOME_WORDS[o]}`).join(", ")}`;
    }).filter(Boolean);
    const standing = standingOf(checks.filter((c) => SHADING_KINDS.has(c.kind)).map((c) => c.status));
    return { ...t, id, label: node?.label ?? id, standing, parts };
  });
  const shown = new Map<string, Standing>();
  for (const t of tiles) shown.set(t.id, t.standing);
  const tally = (s: Standing) => [...shown.values()].filter((x) => x === s).length;
  const outcomeTally = (o: string) => cards.filter((c) => c.status === o).length;
  const goalLabel = graph.nodes.get(goal)?.label ?? goal;
  const { x, y, w, h } = drawing.view;
  // The drawing's scale on screen, so its lines keep the map's width ("meet" uses the tighter side).
  const svgRef = useRef<SVGSVGElement>(null);
  const [k, setK] = useState(0.3);
  useLayoutEffect(() => {
    const el = svgRef.current;
    if (!el) return;
    const measure = () => {
      const r = el.getBoundingClientRect();
      if (r.width > 0 && r.height > 0) setK(Math.min(r.width / w, r.height / h));
    };
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, [w, h]);

  return (
    <section className="checks__band checkmap" aria-labelledby="checkmap-title">
      <h2 id="checkmap-title">What has been checked, at a glance</h2>
      <div className="checkmap__pair">
        <figure className="checkmap__fig checkmap__fig--argument">
          <svg ref={svgRef} className="argfig checkmap__argument" viewBox={`${x} ${y} ${w} ${h}`} preserveAspectRatio="xMidYMin meet" role="group" aria-label={`The argument for ${goalLabel}, each record shaded by its recorded checks`} style={{ ["--k" as string]: k }}>
            <defs>
              <pattern id="ck-half" width="10" height="10" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
                <rect width="5" height="10" className="ck-half__ink" />
              </pattern>
            </defs>
            <g className="argfig__links">
              {drawing.buses.map((d, i) => (
                <path key={`bus${i}`} className="link link--supports" d={d} />
              ))}
              {drawing.lines.map((l) => (
                <path key={l.key} className={`link link--${l.kind}`} d={l.d} />
              ))}
            </g>
            {tiles.map((t) => (
              <a key={t.lid} href={routeHref({ view: "checks", node: t.id })} className={`checkmap__tile ck--${t.standing}${t.root ? " is-root" : ""}`}>
                <title>{`${t.label}: ${STANDING_WORDS[t.standing]}${t.parts.length ? `. ${t.parts.join("; ")}.` : "."}`}</title>
                <rect x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx={METRICS.radius} />
                {t.standing === "partly" && <rect className="ck-half" x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx={METRICS.radius} />}
              </a>
            ))}
          </svg>
          <figcaption>
            The argument for <a href={routeHref({ view: "map", goal })}>{goalLabel}</a>, every branch open, each record shaded by
            the checks recorded about its statement or proof (source-file checks compare file bytes, so they are left out).
            Point at a record for its checks; select it to list them.
          </figcaption>
          <ul className="checkmap__key" aria-label="Shading of the records">
            {(["failed", "passed", "partly", "unrun", "none"] as Standing[]).filter((s) => tally(s) > 0).map((s) => (
              <li key={s}>
                <span className={`checkmap__swatch ck--${s}`} aria-hidden="true" />
                {STANDING_WORDS[s]} <span className="num">{tally(s)}</span>
              </li>
            ))}
          </ul>
        </figure>

        <figure className="checkmap__fig checkmap__fig--records">
          <div className="checkmap__kinds">
            {groups.map((g) => (
              <div key={g.kind} className="checkmap__kind">
                <p className="checkmap__kindname">
                  <a href={`#kind-${g.kind}`}>{g.title}</a> <span className="num">{g.cards.length}</span>
                </p>
                <div className="checkmap__squares" aria-hidden="true">
                  {[...g.cards]
                    .sort((a, b) => OUTCOME_ORDER.indexOf(a.status as never) - OUTCOME_ORDER.indexOf(b.status as never))
                    .map((c) => (
                      <a key={c.id} tabIndex={-1} href={routeHref({ view: "checks", node: c.id })} className={`checkmap__square ck--${c.status}`} title={`${c.label}: ${OUTCOME_WORDS[c.status] ?? c.status}`} />
                    ))}
                </div>
              </div>
            ))}
          </div>
          <figcaption>
            Every check record on this site, one square each, by kind of check. Select a square to open that check’s record.
          </figcaption>
          <ul className="checkmap__key" aria-label="Outcomes">
            {OUTCOME_ORDER.map((o) => (
              <li key={o}>
                <span className={`checkmap__swatch checkmap__swatch--square ck--${o}`} aria-hidden="true" />
                {OUTCOME_WORDS[o]} <span className="num">{outcomeTally(o)}</span>
              </li>
            ))}
          </ul>
        </figure>
      </div>
    </section>
  );
}

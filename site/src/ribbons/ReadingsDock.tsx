// The three accounts laid side by side in reading order. Each strip is one
// paper from its first line to its last; each mark is a passage mapped to the
// argument, tinted by the part of the argument it discusses. Threads join a
// passage to the fuller treatment, example or answer its authors linked it to.
// Choosing a paper lights its selection on the map above.

import { useEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition, useRecord } from "../app/data";
import { navigate, routeHref } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { sectionLabel } from "../map/TheoremPlate";
import { useReadings, type StripPassage, type Thread } from "./useReadings";
import "./dock.css";

interface Props {
  lens?: Stage;
  /** The record selected on the map: passages that discuss it light up. */
  selected?: string;
  onLens(stage: Stage | undefined): void;
  onEcho(ids: ReadonlySet<string> | null): void;
}

const ROW_H = 22;
const ROW_GAP = 10;
const KIND_WORDS: Record<string, string> = {
  expands: "fuller treatment",
  illustrates: "example",
  answers: "answer",
  shared_claim: "same claim",
};

export function ReadingsDock({ lens, selected, onLens, onEcho }: Props) {
  const edition = useEdition();
  const readings = useReadings();
  const selectedNode = selected ? edition.graph.nodes.get(selected) : undefined;
  const record = useRecord(selectedNode?.ref ?? null);
  // Passages that discuss the selection: mapped to it in the strips, or aligned to it by the record.
  const lit = useMemo(() => {
    const keys = new Set<string>();
    if (!selected || readings.status !== "ready") return keys;
    for (const p of readings.value.byKey.values()) if (p.claims.includes(selected)) keys.add(p.key);
    if (record.status === "ready" && record.value.record.id === selected)
      for (const a of record.value.aligned_passages ?? []) if (readings.value.byKey.has(`${a.stage}:${a.anchor}`)) keys.add(`${a.stage}:${a.anchor}`);
    return keys;
  }, [selected, readings, record]);
  const litCount = (stage: Stage) => [...lit].filter((k) => k.startsWith(`${stage}:`)).length;
  const areaRef = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(800);
  const [active, setActive] = useState<string | null>(null);
  const [collapsed, setCollapsed] = useState(false);

  useEffect(() => {
    const el = areaRef.current;
    if (!el) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(200, entry.contentRect.width)));
    observer.observe(el);
    return () => observer.disconnect();
  }, [collapsed]);

  const strips = readings.status === "ready" ? readings.value.strips : [];
  const rowOf = (stage: Stage) => STAGE_ORDER.indexOf(stage);
  const xOf = (p: StripPassage) => {
    const strip = strips.find((s) => s.stage === p.stage)!;
    return ((p.start + p.end) / 2 / strip.length) * width;
  };

  const threads = readings.status === "ready" ? readings.value.threads : [];
  const authored = useMemo(() => threads.filter((t) => !t.derived), [threads]);
  const activeThreads = useMemo(
    () => (active ? threads.filter((t) => t.from === active || t.to === active) : []),
    [threads, active],
  );

  const hover = (p: StripPassage | null) => {
    setActive(p?.key ?? null);
    onEcho(p ? new Set(p.claims) : null);
  };

  const threadPath = (t: Thread) => {
    if (readings.status !== "ready") return "";
    const a = readings.value.byKey.get(t.from);
    const b = readings.value.byKey.get(t.to);
    if (!a || !b) return "";
    const ya = rowOf(a.stage) * (ROW_H + ROW_GAP) + ROW_H / 2;
    const yb = rowOf(b.stage) * (ROW_H + ROW_GAP) + ROW_H / 2;
    const xa = xOf(a);
    const xb = xOf(b);
    if (a.stage === b.stage) {
      const lift = Math.min(ROW_GAP + 6, 8 + Math.abs(xb - xa) * 0.08);
      return `M${xa},${ya - 7}C${xa},${ya - 7 - lift} ${xb},${yb - 7 - lift} ${xb},${yb - 7}`;
    }
    const down = yb > ya;
    const y1 = ya + (down ? 7 : -7);
    const y2 = yb + (down ? -7 : 7);
    const mid = (y1 + y2) / 2;
    return `M${xa},${y1}C${xa},${mid} ${xb},${mid} ${xb},${y2}`;
  };

  const activePassage = active && readings.status === "ready" ? readings.value.byKey.get(active) : null;
  const height = STAGE_ORDER.length * ROW_H + (STAGE_ORDER.length - 1) * ROW_GAP;

  return (
    <section className={`dock${collapsed ? " dock--collapsed" : ""}`} aria-label="The three accounts">
      <header className="dock__head">
        <h2 className="dock__title">Three accounts of the same argument</h2>
        <p className="dock__hint">
          {selectedNode
            ? lit.size
              ? `Lit: the passages that discuss ${selectedNode.label} (${STAGE_ORDER.map((s) => `${litCount(s)} in ${PAPER_NAMES[s].short.toLowerCase()}`).join(", ")}).`
              : `No passage discusses ${selectedNode.label} directly.`
            : lens
            ? `The map shows what the ${PAPER_NAMES[lens].short.toLowerCase()} discusses (filled) and relies on (open).`
            : "Choose an account to light its selection on the map. Point at a passage to see what it discusses."}
        </p>
        <button type="button" className="control control--plain dock__toggle" aria-expanded={!collapsed} onClick={() => setCollapsed((c) => !c)}>
          {collapsed ? "Show" : "Hide"}
        </button>
      </header>
      {!collapsed && (
        <div className="dock__body">
          <div className="dock__labels" style={{ gap: ROW_GAP }}>
            {STAGE_ORDER.map((stage) => {
              const strip = strips.find((s) => s.stage === stage);
              return (
                <button
                  key={stage}
                  type="button"
                  className="dock__label"
                  style={{ height: ROW_H }}
                  aria-pressed={lens === stage}
                  onClick={() => onLens(lens === stage ? undefined : stage)}
                >
                  <span className="dock__label-name">{PAPER_NAMES[stage].short}</span>
                  {strip &&
                    (selectedNode ? (
                      <span className={`dock__label-meta num${litCount(stage) ? " dock__label-meta--lit" : ""}`}>
                        {litCount(stage)} of {strip.passages.length}
                      </span>
                    ) : (
                      <span className="dock__label-meta num">{strip.passages.length} passages</span>
                    ))}
                </button>
              );
            })}
          </div>
          <div className="dock__area" ref={areaRef} onPointerLeave={() => hover(null)}>
            <svg className="dock__svg" width={width} height={height} role="presentation">
              <g className="dock__threads">
                {authored.map((t) => (
                  <path key={`${t.from}|${t.to}|${t.kind}`} d={threadPath(t)} className={`thread thread--${t.kind} thread--rest`} />
                ))}
                {activeThreads.map((t) => (
                  <path key={`a|${t.from}|${t.to}|${t.kind}`} d={threadPath(t)} className={`thread thread--${t.kind} thread--active`} />
                ))}
              </g>
              {strips.map((strip) => {
                const y = rowOf(strip.stage) * (ROW_H + ROW_GAP);
                const dimmed = lens && lens !== strip.stage;
                return (
                  <g
                    key={strip.stage}
                    transform={`translate(0,${y})`}
                    className={`strip${dimmed ? " strip--dimmed" : ""}${lit.size ? " strip--selecting" : ""}`}
                  >
                    <line x1={0} x2={width} y1={ROW_H / 2} y2={ROW_H / 2} className="strip__line" />
                    {strip.sections
                      .filter((s) => s.level === 2)
                      .map((s) => (
                        <line
                          key={s.ref}
                          x1={(s.span.start_byte / strip.length) * width}
                          x2={(s.span.start_byte / strip.length) * width}
                          y1={3}
                          y2={ROW_H - 3}
                          className="strip__tick"
                        />
                      ))}
                    {strip.passages.map((p) => {
                      const x = (p.start / strip.length) * width;
                      const w = Math.max(3, ((p.end - p.start) / strip.length) * width - 1);
                      const related =
                        active && activeThreads.some((t) => (t.from === active && t.to === p.key) || (t.to === active && t.from === p.key));
                      return (
                        <a
                          key={p.key}
                          href={routeHref({ view: "read", stage: p.stage, anchor: p.anchor })}
                          className={`seg${p.key === active ? " seg--active" : ""}${related ? " seg--related" : ""}${p.region ? "" : " seg--example"}${lit.has(p.key) ? " seg--lit" : ""}`}
                          data-region={p.region ?? undefined}
                          aria-label={`${PAPER_NAMES[p.stage].short}: ${p.section ? sectionLabel(p.section) : p.anchor}`}
                          onPointerEnter={() => hover(p)}
                          onFocus={() => hover(p)}
                          onBlur={() => hover(null)}
                          onClick={(event) => {
                            event.preventDefault();
                            navigate(routeHref({ view: "read", stage: p.stage, anchor: p.anchor }));
                          }}
                        >
                          <rect x={x} y={5} width={w} height={ROW_H - 10} rx={2} className="seg__mark" />
                          {lit.has(p.key) && (
                            <g key={`lit:${selected}`} className="seg__lit">
                              <path d={`M${x + w / 2 - 4},0.5h8l-4,4z`} className="seg__pin" />
                              <rect x={x - 1} y={4} width={w + 2} height={ROW_H - 8} rx={2.5} className="seg__halo" />
                            </g>
                          )}
                          <rect x={x - 1} y={0} width={w + 2} height={ROW_H} className="seg__hit" />
                        </a>
                      );
                    })}
                  </g>
                );
              })}
            </svg>
            {activePassage && (
              <DockTip passage={activePassage} x={xOf(activePassage)} width={width} threads={activeThreads} regionTitle={edition.graph.regions.find((r) => r.id === activePassage.region)?.title} />
            )}
          </div>
        </div>
      )}
    </section>
  );
}

function DockTip({
  passage,
  x,
  width,
  threads,
  regionTitle,
}: {
  passage: StripPassage;
  x: number;
  width: number;
  threads: Thread[];
  regionTitle?: string;
}) {
  const authored = threads.filter((t) => !t.derived);
  const shared = threads.filter((t) => t.derived).length;
  const left = Math.min(Math.max(x - 150, 0), width - 300);
  return (
    <div className="dock-tip" style={{ left }} role="status">
      <p className="dock-tip__title">{passage.section ? sectionLabel(passage.section) : passage.anchor}</p>
      <p className="dock-tip__meta">
        {passage.claims.length === 0
          ? "No claim mapped: a worked example or exercise."
          : `${passage.claims.length} ${passage.claims.length === 1 ? "claim" : "claims"}${regionTitle ? `, mostly ${regionTitle.toLowerCase()}` : ""}.`}
        {authored.length > 0 && ` Linked to ${authored.map((t) => KIND_WORDS[t.kind] ?? t.kind).join(", ")}.`}
        {shared > 0 && ` ${shared} ${shared === 1 ? "passage" : "passages"} elsewhere share a claim.`}
      </p>
    </div>
  );
}

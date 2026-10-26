// The three accounts laid side by side in reading order, on demand. Collapsed,
// the dock is one bar under the canvas with a miniature of the three strips;
// opened, each strip is one paper from its first line to its last, and each
// mark is a passage mapped to the argument, in the source colour of what it
// discusses. Threads join a passage to the fuller treatment, example or answer
// its authors linked it to. Choosing a paper scopes the map to its records.
//
// Pointing at or focusing a passage previews its records on the map; it never
// unfolds, moves or saves anything. Each strip is one tab stop: arrow keys move
// between its passages, Home and End jump to its ends, Tab leaves.

import { useEffect, useMemo, useRef, useState, type KeyboardEvent, type MouseEvent } from "react";
import type { Stage } from "../api/types";
import { useEdition, useRecord } from "../app/data";
import { navigate, routeHref } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { sectionLabel } from "../map/TheoremPlate";
import { useReadings, type Strip, type StripPassage, type Thread } from "./useReadings";
import { StripMarks } from "./StripMarks";
import "./dock.css";

interface Props {
  lens?: Stage;
  /** The record selected on the map: passages that discuss it light up. */
  selected?: string;
  /** The step being inspected, if any: the dock then stays collapsed unless the reader opens it. */
  step?: string;
  onLens(stage: Stage | undefined): void;
  /** Transient preview of the records a passage discusses; null when attention leaves. */
  onPreview(ids: ReadonlySet<string> | null): void;
}

const ROW_H = 26;
const ROW_GAP = 8;
const OPEN_KEY = "lx-dock-open";
const KIND_WORDS: Record<string, string> = {
  expands: "a fuller treatment",
  illustrates: "an example",
  answers: "an answer",
  shared_claim: "a passage linked to the same record",
};

const plural = (n: number, one: string, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;

export function passageName(p: StripPassage): string {
  const place = p.section ? sectionLabel(p.section) : p.anchor;
  const what = p.claims.length ? `linked to ${plural(p.claims.length, "record")}` : "linked to no record";
  return `${PAPER_NAMES[p.stage].short} ${place}, ${what}`;
}

/** Only a plain primary click stays in the page; modified and middle clicks keep the browser's meaning. */
export function isPlainClick(event: Pick<MouseEvent, "button" | "metaKey" | "ctrlKey" | "shiftKey" | "altKey">): boolean {
  return event.button === 0 && !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey;
}

function readOpen(): boolean {
  try {
    return sessionStorage.getItem(OPEN_KEY) === "1";
  } catch {
    return false;
  }
}

export function ReadingsDock({ lens, selected, step, onLens, onPreview }: Props) {
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

  // Collapsed by default; the reader's choice holds for the session. While a step is
  // inspected the dock stays down unless the reader opens it during that step.
  const [open, setOpen] = useState(readOpen);
  const [stepOpened, setStepOpened] = useState(false);
  useEffect(() => setStepOpened(false), [step]);
  const expanded = step ? stepOpened : open;
  const setExpanded = (value: boolean) => {
    setOpen(value);
    if (step) setStepOpened(value);
    try {
      sessionStorage.setItem(OPEN_KEY, value ? "1" : "0");
    } catch {
      /* storage unavailable */
    }
    if (!value) hover(null);
  };

  const areaRef = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(800);
  const [active, setActive] = useState<string | null>(null);

  useEffect(() => {
    const el = areaRef.current;
    if (!el) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(200, entry.contentRect.width)));
    observer.observe(el);
    return () => observer.disconnect();
  }, [expanded]);

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

  function hover(p: StripPassage | null) {
    setActive(p?.key ?? null);
    onPreview(p && p.claims.length ? new Set(p.claims) : null);
  }
  // Leaving the map clears any preview this dock started.
  useEffect(() => () => onPreview(null), [onPreview]);

  // Roving focus: one tab stop per strip, on its first lit passage or its first passage.
  const [cursor, setCursor] = useState<Partial<Record<Stage, string>>>({});
  const segRefs = useRef(new Map<string, HTMLAnchorElement>());
  const tabStop = (strip: Strip) => {
    const own = cursor[strip.stage];
    if (own && strip.passages.some((p) => p.key === own)) return own;
    return strip.passages.find((p) => lit.has(p.key))?.key ?? strip.passages[0]?.key;
  };
  const onSegKey = (strip: Strip, index: number, event: KeyboardEvent<HTMLAnchorElement>) => {
    const last = strip.passages.length - 1;
    let j = -1;
    if (event.key === "ArrowRight" || event.key === "ArrowDown") j = Math.min(last, index + 1);
    else if (event.key === "ArrowLeft" || event.key === "ArrowUp") j = Math.max(0, index - 1);
    else if (event.key === "Home") j = 0;
    else if (event.key === "End") j = last;
    if (j < 0) return;
    event.preventDefault();
    const key = strip.passages[j].key;
    setCursor((c) => ({ ...c, [strip.stage]: key }));
    segRefs.current.get(key)?.focus();
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

  if (!expanded) {
    return (
      <section className="dock dock--collapsed" aria-label="The three accounts">
        <button type="button" className="dockbar" aria-expanded={false} onClick={() => setExpanded(true)}>
          <span className="dockbar__title">Compare the three accounts</span>
          <span className="dockbar__strips" aria-hidden="true">
            {STAGE_ORDER.map((stage) => {
              const strip = strips.find((s) => s.stage === stage);
              return (
                <span key={stage} className="dockbar__strip">
                  <span className="dockbar__name">{PAPER_NAMES[stage].short}</span>
                  <StripMarks strip={strip} lit={lit} />
                </span>
              );
            })}
          </span>
          {selectedNode && lit.size > 0 && <span className="dockbar__lit num">{plural(lit.size, "passage")} linked to this record</span>}
          <span className="dockbar__open">
            Show
            <svg viewBox="0 0 10 10" width="9" height="9" aria-hidden="true">
              <path d="M2 6.5 L5 3.5 L8 6.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
            </svg>
          </span>
        </button>
      </section>
    );
  }

  return (
    <section className="dock" aria-labelledby="dock-title">
      <header className="dock__head">
        <h2 className="dock__title" id="dock-title">
          Compare the three accounts
        </h2>
        <p className="dock__hint">
          {selectedNode
            ? lit.size
              ? `${lit.size === 1 ? "The passage" : `The ${lit.size} passages`} linked directly to ${selectedNode.label} ${lit.size === 1 ? "is" : "are"} highlighted.`
              : `No passage is linked directly to ${selectedNode.label}.`
            : lens
            ? `Only the records the ${PAPER_NAMES[lens].short.toLowerCase()} uses are drawn on the map. Select its name again to draw all records.`
            : "Each mark on a strip is one passage, in reading order. Pointing at a mark highlights that passage’s records on the map, and selecting an account’s name draws only the records it uses."}
        </p>
        <button type="button" className="dock__toggle" aria-expanded={true} onClick={() => setExpanded(false)}>
          Hide
          <svg viewBox="0 0 10 10" width="9" height="9" aria-hidden="true">
            <path d="M2 3.5 L5 6.5 L8 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
          </svg>
        </button>
      </header>
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
                aria-label={`Draw only the records the ${PAPER_NAMES[stage].short.toLowerCase()} uses`}
                onClick={() => onLens(lens === stage ? undefined : stage)}
              >
                <span className="dock__label-name">{PAPER_NAMES[stage].short}</span>
                {strip &&
                  (selectedNode ? (
                    <span className={`dock__label-meta num${litCount(stage) ? " dock__label-meta--lit" : ""}`}>
                      {litCount(stage)} of {plural(strip.passages.length, "passage")}
                    </span>
                  ) : (
                    <span className="dock__label-meta num">{plural(strip.passages.length, "passage")}</span>
                  ))}
              </button>
            );
          })}
        </div>
        <div className="dock__area" ref={areaRef} onPointerLeave={() => hover(null)}>
          <svg className="dock__svg" width={width} height={height}>
            <g className="dock__threads" aria-hidden="true">
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
              const stop = tabStop(strip);
              return (
                <g
                  key={strip.stage}
                  transform={`translate(0,${y})`}
                  className={`strip${dimmed ? " strip--dimmed" : ""}${lit.size ? " strip--selecting" : ""}`}
                  role="group"
                  aria-label={`${PAPER_NAMES[strip.stage].short}: ${plural(strip.passages.length, "passage")} in reading order. Arrow keys move between them.`}
                >
                  <line x1={0} x2={width} y1={ROW_H / 2} y2={ROW_H / 2} className="strip__line" />
                  {strip.sections
                    .filter((s) => s.level === 2)
                    .map((s) => (
                      <line
                        key={s.ref}
                        x1={(s.span.start_byte / strip.length) * width}
                        x2={(s.span.start_byte / strip.length) * width}
                        y1={4}
                        y2={ROW_H - 4}
                        className="strip__tick"
                      />
                    ))}
                  {strip.passages.map((p, index) => {
                    const x = (p.start / strip.length) * width;
                    const w = Math.max(3, ((p.end - p.start) / strip.length) * width - 1);
                    const related =
                      active && activeThreads.some((t) => (t.from === active && t.to === p.key) || (t.to === active && t.from === p.key));
                    const href = routeHref({ view: "read", stage: p.stage, anchor: p.anchor });
                    return (
                      <a
                        key={p.key}
                        ref={(el) => {
                          if (el) segRefs.current.set(p.key, el);
                          else segRefs.current.delete(p.key);
                        }}
                        href={href}
                        tabIndex={p.key === stop ? 0 : -1}
                        className={`seg${p.key === active ? " seg--active" : ""}${related ? " seg--related" : ""}${p.claims.length ? "" : " seg--example"}${lit.has(p.key) ? " seg--lit" : ""}`}
                        data-slot={p.slot}
                        aria-label={passageName(p)}
                        onPointerEnter={() => hover(p)}
                        onFocus={() => {
                          setCursor((c) => ({ ...c, [strip.stage]: p.key }));
                          hover(p);
                        }}
                        onBlur={() => hover(null)}
                        onKeyDown={(event) => onSegKey(strip, index, event)}
                        onClick={(event) => {
                          if (!isPlainClick(event)) return;
                          event.preventDefault();
                          navigate(href);
                        }}
                      >
                        <rect x={x} y={7} width={w} height={ROW_H - 14} rx={2} className="seg__mark" />
                        {lit.has(p.key) && (
                          <g key={`lit:${selected}`} className="seg__lit">
                            <path d={`M${x + w / 2 - 4},0.5h8l-4,4z`} className="seg__pin" />
                            <rect x={x - 1} y={6} width={w + 2} height={ROW_H - 12} rx={2.5} className="seg__halo" />
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
    <div className="dock-tip" style={{ left }} aria-hidden="true">
      <p className="dock-tip__title">{passage.section ? sectionLabel(passage.section) : passage.anchor}</p>
      <p className="dock-tip__meta">
        {passage.claims.length === 0
          ? "No record is linked to this passage."
          : `Linked to ${plural(passage.claims.length, "record")}${regionTitle ? `, mostly on ${regionTitle.toLowerCase()}` : ""}.`}
        {authored.length > 0 && ` Recorded as linked to ${authored.map((t) => KIND_WORDS[t.kind] ?? t.kind).join(", ")} in another passage.`}
        {shared > 0 && ` ${shared === 1 ? "1 other passage is" : `${shared} other passages are`} linked to at least one of the same records.`}
      </p>
    </div>
  );
}

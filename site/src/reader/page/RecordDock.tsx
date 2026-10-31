// The expanded Lean. The graph is what stands on the right page while reading; a click on a
// statement or a highlighted card opens that step here, rising from its card over the graph,
// which keeps its place underneath. It is headed by the step's plain title with the raw name
// small beside it, then where each paper states the step, then the raw Lean with its exact
// lines lit. A step with no Lean says so and offers the papers. Back or Escape closes it.

import { useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { Alignment, RecordAlignment, StatementLean } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref, type Trace } from "../../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { shortTitle } from "../../compare/useAlignment";
import { LazyLeanBlock } from "../../lean/lazy";
import type { LeanWalk } from "../../lean/walk";
import { statementHref } from "../links";
import { RecordPanel } from "../../panels/RecordPanel";
import { ROLE_WORDS, sameWords, statementFor, type TieModel } from "../ties";
import { bestSlice, sectionNumber } from "./model";

/** What is open: a step, its statement here when it has one, or a declaration walked to. */
export interface LeanOpen {
  record: string | null;
  tie: number | null;
  /** A declaration reached by a name in the Lean or from search. */
  decl: string | null;
}

interface Props {
  open: LeanOpen;
  ties: TieModel;
  stage: Stage;
  alignment: Alignment | null;
  /** Stands in for the Lean: a theorem or citation preview, or the passage inspector. */
  slot?: ReactNode;
  onRelease(): void;
  onPick(id: string): void;
  onPoint(tie: number | null, record?: string): void;
  onName?(walk: LeanWalk): void;
  /** Where the opening rises from. */
  from?: HTMLElement | null;
  passageHref(stage: Stage, anchor: string): string;
}

/** The Lean a statement means, or the record's own rows where it names none, without repeats. */
function leanRows(alignment: Alignment | null, record: string | null, at: string | null): StatementLean[] {
  const row = record ? alignment?.records[record] : undefined;
  if (!row) return [];
  const statement = at ? row.statements.find((s) => s.at === at) : undefined;
  const rows: StatementLean[] = statement?.lean?.length ? statement.lean : row.lean;
  const seen = new Set<string>();
  return rows.filter((item) => {
    const key = `${item.module}:${item.name}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

/** The record a declaration belongs to, if the alignment links one. */
export function recordOfDecl(alignment: Alignment | null, name: string): string | null {
  for (const [id, row] of Object.entries(alignment?.records ?? {})) if (row.lean.some((lean) => lean.name === name)) return id;
  return null;
}

const lastName = (name: string) => name.slice(name.lastIndexOf(".") + 1);

/** A declaration's name in words: the authored one, else its record's title, else its last part with spaces. */
export function plainName(alignment: Alignment | null, name: string): string {
  const authored = (alignment as { names?: Record<string, string | { title?: string; plain?: string }> } | null)?.names?.[name];
  if (typeof authored === "string") return authored;
  if (authored?.title || authored?.plain) return (authored.title ?? authored.plain)!;
  const record = recordOfDecl(alignment, name);
  if (record) return shortTitle(record, alignment!.records[record].short || record);
  return lastName(name).replace(/_/g, " ");
}

/** Short paper §2, Long record §5.3, Exposition §4, Compare: where each paper states this, each a link. */
export function PaperCrumbs({ record, row, stage, alignment }: { record: string; row: RecordAlignment | undefined; stage: Stage; alignment: Alignment | null }) {
  const order = [stage, ...STAGE_ORDER.filter((s) => s !== stage)];
  const places = order.flatMap((paper) => {
    const slice = bestSlice(alignment, paper, record);
    return slice ? [{ paper, slice }] : [];
  });
  return (
    <nav className="lean-crumbs" aria-label="Where the papers state this">
      {places.map(({ paper, slice }) => (
        <a key={paper} href={statementHref(slice)} title={slice.section || undefined}>
          {PAPER_NAMES[paper].short}
          {slice.section ? ` ${sectionNumber(slice.section)}` : ""}
        </a>
      ))}
      {row && <a href={routeHref({ view: "compare", node: record })}>Compare</a>}
    </nav>
  );
}

/** Other steps tied to the same words. Pointing lights them, choosing opens them. */
function AlsoHere({ tie, ties, onPick, onPoint }: { tie: number; ties: TieModel; onPick(id: string): void; onPoint(tie: number | null, record?: string): void }) {
  const { graph } = useEdition();
  const others = [...new Set(sameWords(ties, tie).map((t) => ties.index.ties[t].record))].filter((id) => id !== ties.index.ties[tie].record && graph.nodes.has(id));
  if (!others.length) return null;
  return (
    <p className="lean-page__also">
      <span>The same words also tie to</span>
      {others.slice(0, 4).map((id) => (
        <button key={id} type="button" onClick={() => onPick(id)} onPointerEnter={() => onPoint(statementFor(ties, id), id)} onPointerLeave={() => onPoint(null)}>
          {shortTitle(id, graph.nodes.get(id)!.label)}
        </button>
      ))}
      {others.length > 4 && <span>and {others.length - 4} more</span>}
    </p>
  );
}

export function LeanDock({ open, ties, stage, alignment, slot, onRelease, onPick, onPoint, onName, from, passageHref }: Props) {
  const { graph } = useEdition();
  const page = useRef<HTMLDivElement>(null);
  const [full, setFull] = useState(false);
  const [chosen, setChosen] = useState(0);
  const tie = open.tie !== null ? ties.index.ties[open.tie] : null;
  const at = tie?.at ?? null;
  const record = open.record;
  const rows = useMemo(() => {
    const list = leanRows(alignment, record, at);
    if (list.length || !tie?.name || !tie.module) return list;
    // Before the alignment arrives the statement's own index row names its first declaration.
    return [{ name: tie.name, module: tie.module, line: tie.lines?.[0] ?? 0, end_line: tie.lines?.[1] ?? 0, relation: null, note: "", lines: tie.lines ?? [0, 0] } as StatementLean];
  }, [alignment, record, at, tie]);
  const key = open.decl ?? `${record}|${at}`;
  const [shown, setShown] = useState(key);
  if (shown !== key) {
    setShown(key);
    setChosen(0);
    setFull(false);
  }
  const row = open.decl ? null : rows[Math.min(chosen, rows.length - 1)];
  const name = open.decl ?? row?.name ?? null;
  const plain = record ? shortTitle(record, graph.nodes.get(record)?.label ?? alignment?.records[record]?.short ?? record) : name ? plainName(alignment, name) : "";

  // The Lean rises out of the card: it opens from the card's box to its own.
  const opening = useRef(true);
  useLayoutEffect(() => {
    const el = page.current;
    if (!opening.current || !el) return;
    opening.current = false;
    if (window.matchMedia?.("(prefers-reduced-motion: reduce)").matches || !from?.isConnected || !el.animate) return;
    const box = el.getBoundingClientRect();
    const card = from.getBoundingClientRect();
    const inset = [card.top - box.top, box.right - card.right, box.bottom - card.bottom, card.left - box.left].map((v) => `${Math.max(0, Math.round(v))}px`).join(" ");
    el.animate([{ clipPath: `inset(${inset} round 7px)`, opacity: 0.5 }, { clipPath: "inset(0px round 0px)", opacity: 1 }], { duration: 240, easing: "cubic-bezier(0.2, 0.7, 0.2, 1)" });
  }, [from]);

  return (
    <div className="lean-page" ref={page} role="region" aria-label={plain ? `The Lean of ${plain}` : "The Lean"}>
      <header className="lean-page__head">
        <div className="lean-page__names">
          <h3 className="lean-page__title">{plain}</h3>
          {name && !slot && <code className="lean-page__raw" title={name}>{lastName(name)}</code>}
        </div>
        {!!record && !slot && graph.nodes.has(record) && (
          <button type="button" className="lean-page__action" aria-pressed={full} onClick={() => setFull(!full)}>
            Whole record
          </button>
        )}
        <button type="button" className="lean-page__action" aria-keyshortcuts="Escape" onClick={onRelease}>
          Close
        </button>
      </header>
      {slot ? (
        <div className="lean-page__body lean-page__body--read" data-keep>
          {slot}
        </div>
      ) : (
        <>
          {record && <PaperCrumbs record={record} row={alignment?.records[record]} stage={stage} alignment={alignment} />}
          {tie && open.tie !== null && (
            <div className="lean-page__lead">
              <span className="lean-page__role">{ROLE_WORDS[tie.role]} here</span>
              <AlsoHere tie={open.tie} ties={ties} onPick={onPick} onPoint={onPoint} />
            </div>
          )}
          {!open.decl && rows.length > 1 && !full && (
            <ul className="lean-page__rows" aria-label="Lean declarations of this step">
              {rows.map((item, i) => (
                <li key={`${item.module}:${item.name}`}>
                  <button type="button" aria-pressed={i === Math.min(chosen, rows.length - 1)} title={item.name} onClick={() => setChosen(i)}>
                    {plainName(alignment, item.name) === plain ? lastName(item.name) : plainName(alignment, item.name)}
                  </button>
                </li>
              ))}
            </ul>
          )}
          <div className={`lean-page__body${full || !name ? " lean-page__body--read" : ""}`} data-keep>
            {full && record ? (
              <RecordPanel
                key={record}
                nodeId={record}
                compact
                onClose={() => setFull(false)}
                onSelect={onPick}
                onTrace={(trace: Trace | undefined) => navigate({ view: "map", node: record, trace })}
                passageHref={passageHref}
              />
            ) : name ? (
              <LazyLeanBlock
                key={`${row?.module ?? ""}:${name}`}
                name={name}
                module={row?.module}
                relation={row?.relation ?? undefined}
                note={row?.note}
                clause={row?.clause}
                lines={row?.lines}
                compact
                fill
                onName={onName}
              />
            ) : alignment ? (
              <p className="lean-page__plain">No Lean declaration is linked to this step. The papers above state it.</p>
            ) : null}
          </div>
        </>
      )}
    </div>
  );
}

// ---- How far the Lean rises ---------------------------------------------------------------

const SHARE_KEY = "lx-reader-lean";
export const DOCK_MIN = 0.4;
export const DOCK_MAX = 0.88;

export function clampDock(share: number): number {
  return Math.min(DOCK_MAX, Math.max(DOCK_MIN, share));
}

/** The remembered height, or most of the page; side by side, a little over half of its width. */
export function readDockShare(side = false): number {
  const fallback = side ? 0.54 : 0.75;
  try {
    const value = Number(localStorage.getItem(`${SHARE_KEY}${side ? "-side" : ""}`));
    return value ? clampDock(value) : fallback;
  } catch {
    return fallback;
  }
}

export function saveDockShare(share: number, side = false) {
  try {
    localStorage.setItem(`${SHARE_KEY}${side ? "-side" : ""}`, String(share));
  } catch {
    /* storage unavailable: the height lasts until the page closes */
  }
}

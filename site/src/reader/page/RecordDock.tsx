// The Lean page: the lower half of the right page, or its left half where the page is wide
// enough. It is not something a reader opens. It always shows the Lean of what is being
// read, what is being pointed at, or what is pinned, and says which in one quiet line. A
// statement with no Lean says so and offers the papers; so does a stretch of paper with no
// ties at all. A pinned record can open its whole record panel here.

import { useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { AlignedStatement, Alignment, StatementLean } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref, type Trace } from "../../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { shortTitle } from "../../compare/useAlignment";
import { LazyLeanBlock } from "../../lean/lazy";
import { statementHref } from "../links";
import { sectionLabel } from "../../map/TheoremPlate";
import { RecordPanel } from "../../panels/RecordPanel";
import { ROLE_WORDS, sameWords, statementFor, type TieModel } from "../ties";

/** What the Lean page is showing and why. */
export type LeanView =
  | { via: "follow" | "point" | "pin"; kind: "statement"; tie: number; record: string }
  | { via: "point" | "pin"; kind: "record"; record: string }
  | { via: "follow"; kind: "passage"; anchor: string; records: readonly string[] }
  | { via: "follow"; kind: "nothing" };

interface Props {
  view: LeanView;
  ties: TieModel;
  stage: Stage;
  alignment: Alignment | null;
  /** The passage of an untied paragraph under the pointer: named on one line, nothing moves. */
  caption?: string | null;
  captionRecords?: readonly string[];
  /** Stands in for the view: a theorem or citation preview, or the passage inspector. */
  slot?: ReactNode;
  onRelease(): void;
  onPick(id: string): void;
  onPoint(tie: number | null, record?: string): void;
  onClose?(): void;
  passageHref(stage: Stage, anchor: string): string;
}

/** The Lean a statement means, or the record's own rows where it names none. */
function leanRows(alignment: Alignment | null, record: string, at: string | null): StatementLean[] {
  const row = alignment?.records[record];
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

function placeOf(statement: AlignedStatement): string {
  const name = PAPER_NAMES[statement.paper].short;
  return statement.section ? `${name}, ${sectionLabel(statement.section)}` : name;
}

/** Where else the step is stated, nearest paper first. */
function Elsewhere({ stage, record, at, alignment, none }: { stage: Stage; record: string; at: string | null; alignment: Alignment | null; none?: string }) {
  const rows = (alignment?.records[record]?.statements ?? []).filter((s) => s.at !== at && s.role !== "mention");
  const order = [stage, ...STAGE_ORDER.filter((s) => s !== stage)];
  const seen = new Set<string>();
  const shown = order.flatMap((paper) => rows.filter((s) => s.paper === paper).slice(0, 2)).filter((s) => {
    const key = `${s.paper}${s.at}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
  if (!shown.length) return none ? <p className="lean-page__note">{none}</p> : null;
  return (
    <div className="lean-page__places">
      <h4 className="lean-page__label">Also stated in</h4>
      <ul>
        {shown.map((s) => (
          <li key={`${s.paper}${s.at}`}>
            <a href={statementHref(s)}>{placeOf(s)}</a>
          </li>
        ))}
      </ul>
    </div>
  );
}

function Declaration({ row }: { row: StatementLean }) {
  // Exact lines and the fill-the-page layout come from the Lean lane's block.
  const extra = { lines: row.lines, compact: true } as object;
  return <LazyLeanBlock key={`${row.module}:${row.name}`} name={row.name} module={row.module} relation={row.relation ?? undefined} note={row.note} clause={row.clause} {...extra} />;
}

/** A declaration's last name, or as much of its namespace as tells two apart. */
function shortName(name: string, all: readonly { name: string }[]): string {
  const parts = name.split(".");
  for (let keep = 1; keep < parts.length; keep++) {
    const tail = parts.slice(-keep).join(".");
    if (all.filter((row) => row.name === name || row.name.endsWith(`.${tail}`)).length === all.filter((row) => row.name === name).length) return tail;
  }
  return name;
}

/** Other steps tied to the same words. Pointing lights them, choosing pins them. */
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

function Statement({ view, ties, stage, alignment, full, onPick, onPoint }: { view: Extract<LeanView, { kind: "statement" | "record" }>; ties: TieModel; stage: Stage; alignment: Alignment | null; full: ReactNode; onPick(id: string): void; onPoint(tie: number | null, record?: string): void }) {
  const { graph } = useEdition();
  const tie = view.kind === "statement" ? ties.index.ties[view.tie] : null;
  const at = tie?.at ?? null;
  const rows = useMemo(() => leanRows(alignment, view.record, at), [alignment, view.record, at]);
  // Before the alignment arrives the statement's own index row names its first declaration.
  const fallback: StatementLean | null =
    tie?.lean && tie.name && tie.module ? { name: tie.name, module: tie.module, line: tie.lines?.[0] ?? 0, end_line: tie.lines?.[1] ?? 0, relation: null, note: "", lines: tie.lines ?? [0, 0] } : null;
  const list = rows.length ? rows : fallback ? [fallback] : [];
  const [chosen, setChosen] = useState(0);
  useEffect(() => setChosen(0), [view.record, at]);
  const row = list[Math.min(chosen, list.length - 1)];
  const label = graph.nodes.get(view.record)?.label ?? alignment?.records[view.record]?.short ?? view.record;
  if (full) return <>{full}</>;
  return (
    <>
      <h3 className="lean-page__title">{label}</h3>
      {tie && <p className="lean-page__role">{ROLE_WORDS[tie.role]} here</p>}
      {view.kind === "statement" && <AlsoHere tie={view.tie} ties={ties} onPick={onPick} onPoint={onPoint} />}
      {!tie && <p className="lean-page__note">This paper has no statement of this step.</p>}
      {list.length > 1 && (
        <ul className="lean-page__rows" aria-label="Lean declarations of this step">
          {list.map((item, i) => (
            <li key={`${item.module}:${item.name}`}>
              <button type="button" aria-pressed={i === Math.min(chosen, list.length - 1)} title={item.name} onClick={() => setChosen(i)}>
                <code>{shortName(item.name, list)}</code>
              </button>
            </li>
          ))}
        </ul>
      )}
      {row ? (
        <Declaration row={row} />
      ) : alignment ? (
        <p className="lean-page__plain">No Lean declaration is linked to this step.</p>
      ) : null}
      <Elsewhere stage={stage} record={view.record} at={at} alignment={alignment} none={row ? undefined : "No paper states it apart from here."} />
    </>
  );
}

function Passage({ records, ties, alignment, onPick, onPoint }: { records: readonly string[]; ties: TieModel; alignment: Alignment | null; onPick(id: string): void; onPoint(tie: number | null, record?: string): void }) {
  const { graph } = useEdition();
  const shown = records.filter((id) => graph.nodes.has(id));
  return (
    <>
      <p className="lean-page__plain">No sentence at the reading line is tied to the Lean. This passage discusses:</p>
      <ul className="lean-page__topics">
        {shown.map((id) => {
          const hasLean = !!alignment?.records[id]?.lean.length;
          return (
            <li key={id}>
              <button
                type="button"
                onClick={() => onPick(id)}
                onPointerEnter={() => onPoint(statementFor(ties, id), id)}
                onPointerLeave={() => onPoint(null)}
                onFocus={() => onPoint(statementFor(ties, id), id)}
                onBlur={() => onPoint(null)}
              >
                <span>{shortTitle(id, graph.nodes.get(id)!.label)}</span>
                <span className="lean-page__has">{hasLean ? "Lean" : "no Lean"}</span>
              </button>
            </li>
          );
        })}
      </ul>
    </>
  );
}

function stateWords(view: LeanView, label: string, topics: string[] | undefined): ReactNode {
  if (topics?.length) return <>No exact tie in this paragraph. Its passage discusses {topics.join(", ")}.</>;
  if (view.via === "pin") return <>Pinned: <strong>{label}</strong></>;
  if (view.via === "point") return <>Pointing at: <strong>{label}</strong></>;
  if (view.kind === "statement") return <>Following the text: <strong>{label}</strong></>;
  if (view.kind === "passage") return <>Following the text: no exact statement here</>;
  return <>Following the text</>;
}

export function LeanDock({ view, ties, stage, alignment, caption, captionRecords, slot, onRelease, onPick, onPoint, onClose, passageHref }: Props) {
  const { graph } = useEdition();
  const body = useRef<HTMLDivElement>(null);
  const [fullFor, setFullFor] = useState<string | null>(null);
  const record = view.kind === "statement" || view.kind === "record" ? view.record : null;
  const label = record ? shortTitle(record, graph.nodes.get(record)?.label ?? record) : "";
  const full = view.via === "pin" && record !== null && fullFor === record;
  // A new thing to read starts at its top, in this page's own scroller.
  const key = view.kind === "statement" ? `s${view.tie}` : record ?? view.kind;
  useEffect(() => {
    if (body.current) body.current.scrollTop = 0;
  }, [key]);
  const topics = caption ? captionRecords?.filter((id) => graph.nodes.has(id)).slice(0, 3).map((id) => shortTitle(id, graph.nodes.get(id)!.label)) : undefined;

  return (
    <div className="lean-page" role="region" aria-label="The Lean of this statement">
      <header className="lean-page__head">
        <p className="lean-page__state" data-via={view.via} role="status">
          <span className="lean-page__dot" aria-hidden="true" />
          <span className="lean-page__words">{stateWords(view, label, topics)}</span>
        </p>
        {view.via === "pin" && (
          <>
            {record && graph.nodes.has(record) && (
              <button type="button" className="lean-page__action" aria-pressed={full} onClick={() => setFullFor(full ? null : record)}>
                Whole record
              </button>
            )}
            <button type="button" className="lean-page__action" onClick={onRelease}>
              Follow the text
            </button>
          </>
        )}
        {onClose && (
          <button type="button" className="lean-page__close" aria-label="Close the Lean" onClick={onClose}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
          </button>
        )}
      </header>
      <div className="lean-page__body" ref={body} tabIndex={-1}>
        {slot ?? (
          <>
            {(view.kind === "statement" || view.kind === "record") && (
              <Statement
                view={view}
                ties={ties}
                stage={stage}
                alignment={alignment}
                onPick={onPick}
                onPoint={onPoint}
                full={
                  full ? (
                    <RecordPanel
                      key={record!}
                      nodeId={record!}
                      compact
                      onClose={() => setFullFor(null)}
                      onSelect={onPick}
                      onTrace={(trace: Trace | undefined) => navigate({ view: "map", node: record!, trace })}
                      passageHref={passageHref}
                    />
                  ) : null
                }
              />
            )}
            {view.kind === "passage" && <Passage records={view.records} ties={ties} alignment={alignment} onPick={onPick} onPoint={onPoint} />}
            {view.kind === "nothing" && (
              <p className="lean-page__plain">
                Nothing in this stretch of the paper is tied to the Lean. Scroll on, or press <kbd>j</kbd> for the next tied statement.
              </p>
            )}
          </>
        )}
        {record && !slot && (
          <a className="lean-page__map" href={routeHref({ view: "map", node: record })}>
            Open in the full map
          </a>
        )}
      </div>
    </div>
  );
}

// ---- The split between the graph and the Lean -------------------------------------------

const SHARE_KEY = "lx-reader-sheet";
const PANES_KEY = "lx-reader-panes";
export const DOCK_MIN = 0.28;
export const DOCK_MAX = 0.8;
/** Below this page height the Lean is what a reader came for, so it starts with more room. */
const SHORT_PAGE = 680;

export function clampDock(share: number): number {
  return Math.min(DOCK_MAX, Math.max(DOCK_MIN, share));
}

/** The remembered split, or by default half, or more for the Lean on a short page. */
export function readDockShare(height = 0): number {
  const fallback = height && height < SHORT_PAGE ? 0.62 : 0.5;
  try {
    const value = Number(localStorage.getItem(SHARE_KEY));
    return value ? clampDock(value) : fallback;
  } catch {
    return fallback;
  }
}

export function saveDockShare(share: number) {
  try {
    localStorage.setItem(SHARE_KEY, String(share));
  } catch {
    /* storage unavailable: the split lasts until the page closes */
  }
}

export interface Panes {
  graph: boolean;
  lean: boolean;
}

export function readPanes(fallback: Panes): Panes {
  try {
    const value = JSON.parse(localStorage.getItem(PANES_KEY) ?? "null") as Panes | null;
    return value && (value.graph || value.lean) ? value : fallback;
  } catch {
    return fallback;
  }
}

export function savePanes(panes: Panes) {
  try {
    localStorage.setItem(PANES_KEY, JSON.stringify(panes));
  } catch {
    /* storage unavailable */
  }
}

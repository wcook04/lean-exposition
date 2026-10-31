// The Lean page. The graph is what stands on the right page while reading; a click on a
// statement or a highlighted card opens that step here, rising from its card over the graph,
// which keeps its place underneath. It is headed by the step's plain title with the raw name
// small beside it, then where each paper states the step, then the raw Lean with its exact
// lines lit. A step with no Lean says so and offers the papers. Back or Escape closes it.
//
// A reader who wants it can keep the page open ("Keep the Lean open", or by dragging its
// handle up). It then follows the text: the Lean of the statement being read, of what is
// pointed at, or, between statements, what the passage discusses. The line at its head says
// which, and the choice is remembered in this browser.

import { useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { Alignment, RecordAlignment, StatementLean } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref, type Trace } from "../../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { shortTitle } from "../../compare/useAlignment";
import { LazyLeanBlock } from "../../lean/lazy";
import type { LeanWalk } from "../../lean/walk";
import { RecordPanel } from "../../panels/RecordPanel";
import { ROLE_WORDS, sameWords, statementFor, type TieModel } from "../ties";
import { paperTarget, sectionNumber } from "./model";
import { leanPage } from "./rightPage";

/** What is open: a step, its statement here when it has one, or a declaration walked to. */
export interface LeanOpen {
  /** Why it is showing: a pin stays; the others go with the reader. */
  via: "pin" | "follow" | "point";
  record: string | null;
  tie: number | null;
  /** A declaration reached by a name in the Lean or from search. */
  decl: string | null;
  declModule?: string;
  /** Kept open between statements: what the passage discusses. */
  topics?: readonly string[];
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
  const authored = alignment?.names?.[name];
  if (authored) return authored;
  const record = recordOfDecl(alignment, name);
  if (record) return shortTitle(record, alignment!.records[record].short || record);
  return lastName(name).replace(/_/g, " ");
}

/** Short paper §2, Long record §5.3, Exposition §4, Compare: where each paper states this, each a link. */
export function PaperCrumbs({ record, row, stage, alignment, decl, at, children }: { record: string; row: RecordAlignment | undefined; stage: Stage; alignment: Alignment | null; decl: string | null; at: string | null; children?: ReactNode }) {
  const order = [stage, ...STAGE_ORDER.filter((s) => s !== stage)];
  const places = order.flatMap((paper) => {
    // In this paper the open statement is itself the place.
    const here = paper === stage && at ? row?.statements.find((s) => s.paper === paper && s.at === at) : undefined;
    const target = here ? { record, slice: here, near: false } : paperTarget(alignment, paper, record, decl);
    return target ? [{ paper, ...target }] : [];
  });
  return (
    <nav className="lean-crumbs" aria-label="Where the papers state this">
      {places.map(({ paper, record: id, slice, near }) => (
        <a
          key={paper}
          href={routeHref({ view: "read", stage: paper, anchor: slice.anchor ?? undefined, at: slice.at, node: id })}
          aria-current={paper === stage && slice.at === at ? "location" : undefined}
          title={near ? "This paper states the step. It does not name this declaration at that place." : slice.section || undefined}
        >
          {PAPER_NAMES[paper].short}
          {/* A place with no number (the opening) is the paper itself: its name is enough. */}
          {sectionNumber(slice.section ?? "").startsWith("§") ? ` ${sectionNumber(slice.section)}` : ""}
          {near && <span className="lean-crumbs__near">, same step</span>}
        </a>
      ))}
      {row && <a href={routeHref({ view: "compare", node: record })}>Compare</a>}
      {children}
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

/** Kept open between statements: the records of the passage, each one a way in. */
function Passage({ records, ties, alignment, onPick, onPoint }: { records: readonly string[]; ties: TieModel; alignment: Alignment | null; onPick(id: string): void; onPoint(tie: number | null, record?: string): void }) {
  const { graph } = useEdition();
  const shown = records.filter((id) => graph.nodes.has(id));
  return (
    <>
      <p className="lean-page__plain">No sentence at the reading line is tied to the Lean. This passage discusses:</p>
      <ul className="lean-page__topics">
        {shown.map((id) => (
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
              <span className="lean-page__has">{alignment?.records[id]?.lean.length ? "Lean" : "no Lean"}</span>
            </button>
          </li>
        ))}
      </ul>
    </>
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
  const row = open.decl ? null : (rows[Math.min(chosen, rows.length - 1)] ?? null);
  const name = open.decl ?? row?.name ?? null;
  const plain = record ? shortTitle(record, graph.nodes.get(record)?.label ?? alignment?.records[record]?.short ?? record) : name ? plainName(alignment, name) : "";

  useLayoutEffect(() => {
    const el = page.current;
    leanPage.current = el;
    return () => {
      if (leanPage.current === el) leanPage.current = null;
    };
  }, []);

  // The Lean rises out of the card: it opens from the card's box to its own.
  const opening = useRef(true);
  useLayoutEffect(() => {
    const el = page.current;
    if (!opening.current || !el) return;
    opening.current = false;
    if (open.via !== "pin" || window.matchMedia?.("(prefers-reduced-motion: reduce)").matches || !from?.isConnected || !el.animate) return;
    const box = el.getBoundingClientRect();
    const card = from.getBoundingClientRect();
    const inset = [card.top - box.top, box.right - card.right, box.bottom - card.bottom, card.left - box.left].map((v) => `${Math.max(0, Math.round(v))}px`).join(" ");
    el.animate([{ clipPath: `inset(${inset} round 7px)`, opacity: 0.5 }, { clipPath: "inset(0px round 0px)", opacity: 1 }], { duration: 240, easing: "cubic-bezier(0.2, 0.7, 0.2, 1)" });
    // Runs for the opening only.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [from]);

  const empty = !record && !name;
  return (
    <div className="lean-page" data-via={open.via} ref={page} role="region" aria-label={plain ? `The Lean of ${plain}` : "The Lean"}>
      {!slot && (
        <header className="lean-page__head">
          {open.via !== "pin" && (
            <p className="lean-page__state" role="status">
              <span className="lean-page__dot" aria-hidden="true" />
              {open.via === "point" ? "Pointing at" : "Following the text"}
            </p>
          )}
          <div className="lean-page__names">
            {plain && (
              <h3 className="lean-page__title" tabIndex={-1}>
                {plain}
              </h3>
            )}
            {name && <code className="lean-page__raw" title={name}>{lastName(name)}</code>}
          {tie && <span className="lean-page__role">{ROLE_WORDS[tie.role]} here</span>}
          </div>
          <button type="button" className="lean-page__action" aria-keyshortcuts="Escape" onClick={onRelease}>
            Close
          </button>
        </header>
      )}
      {slot ? (
        <div className="lean-page__body lean-page__body--read" data-keep>
          {slot}
        </div>
      ) : (
        <>
          {record && (
            <PaperCrumbs record={record} row={alignment?.records[record]} stage={stage} alignment={alignment} decl={name} at={at}>
              {open.via === "pin" && graph.nodes.has(record) && (
                <button type="button" aria-pressed={full} onClick={() => setFull(!full)}>
                  {full ? "Back to the Lean" : "Everything on this step"}
                </button>
              )}
            </PaperCrumbs>
          )}
          {!open.decl && rows.length > 1 && !full && (
            <ul className="lean-page__rows" aria-label="Lean declarations of this step">
              {rows.map((item, i) => (
                <li key={`${item.module}:${item.name}`}>
                  <button type="button" aria-pressed={i === Math.min(chosen, rows.length - 1)} title={item.name} onClick={() => setChosen(i)}>
                    {item.plain ?? plainName(alignment, item.name)}
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
            ) : empty ? (
              open.topics?.length ? (
                <Passage records={open.topics} ties={ties} alignment={alignment} onPick={onPick} onPoint={onPoint} />
              ) : (
                <p className="lean-page__plain">
                  Nothing in this stretch of the paper is tied to the Lean. Scroll on, or press <kbd>j</kbd> for the next tied statement.
                </p>
              )
            ) : name ? (
              <LazyLeanBlock
                key={`${row?.module ?? open.declModule ?? ""}:${name}`}
                name={name}
                module={row?.module ?? open.declModule}
                relation={row?.relation ?? undefined}
                note={row?.note}
                clause={row?.clause}
                lines={row?.lines}
                compact
                fill
                onName={onName}
                noPapers
                below={open.tie !== null ? <AlsoHere tie={open.tie} ties={ties} onPick={onPick} onPoint={onPoint} /> : undefined}
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
export const DOCK_MIN = 0.3;
export const DOCK_MAX = 0.92;
/** The band of graph left above the Lean by default, in pixels. */
const BAND = 92;

export function clampDock(share: number): number {
  return Math.min(DOCK_MAX, Math.max(DOCK_MIN, share));
}

const shareKey = (side: boolean, kept: boolean) => `${SHARE_KEY}${side ? "-side" : ""}${kept ? "-kept" : ""}`;

/**
 * The remembered size. A click raises the Lean over all but a slim band of graph, which keeps
 * the place; kept open beside the reading, it takes half, so the graph above it stays useful.
 * Side by side, a little over half of the width.
 */
export function readDockShare(side = false, kept = false, height = 0): number {
  const fallback = side ? 0.54 : kept ? 0.5 : height ? Math.min(DOCK_MAX, Math.max(0.75, 1 - BAND / height)) : 0.75;
  try {
    const value = Number(localStorage.getItem(shareKey(side, kept)));
    return value ? clampDock(value) : fallback;
  } catch {
    return fallback;
  }
}

export function saveDockShare(share: number, side = false, kept = false) {
  try {
    localStorage.setItem(shareKey(side, kept), String(share));
  } catch {
    /* storage unavailable: the height lasts until the page closes */
  }
}

const KEEP_KEY = "lx-reader-keep-lean";

/** Whether this reader keeps the Lean open beside their reading. Closed unless they asked. */
export function readKeepLean(): boolean {
  try {
    return localStorage.getItem(KEEP_KEY) === "open";
  } catch {
    return false;
  }
}

export function saveKeepLean(open: boolean) {
  try {
    if (open) localStorage.setItem(KEEP_KEY, "open");
    else localStorage.removeItem(KEEP_KEY);
  } catch {
    /* storage unavailable: the choice lasts until the page closes */
  }
}

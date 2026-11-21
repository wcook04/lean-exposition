// The Lean page: the dock under the graph and, filling the pane, the Lean view. A click on a
// statement or a card shows that step here. It is headed by the step's plain title with the raw name
// small beside it, then where each paper states the step, then the raw Lean with its exact
// lines lit. A step with no Lean says so and offers the papers. Back or Escape closes it.
//
// With nothing opened it follows the text: the Lean of the statement being read, of what
// is pointed at, or, between statements, what the passage discusses. The line at its head says
// which, and an opened statement has a quiet way back to following.

import { OriginLine } from "../../compare/Fidelity";
import { useEffect, useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { Alignment, PhraseLean, RecordAlignment, StatementLean } from "../../api/lean";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref, type Trace } from "../../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { shortTitle } from "../../compare/useAlignment";
import { useBarLine, useBarLineShown } from "../../lean/barLine";
import { LazyLeanBlock } from "../../lean/lazy";
import type { LeanWalk } from "../../lean/walk";
import { RecordPanel } from "../../panels/RecordPanel";
import { isPhraseRecord, leanTruth, phraseTitle, ROLE_WORDS, sameWords, statementFor, topicOf, type TieModel } from "../ties";
import { declLight, dockDecl, PhraseCard, usePhraseNotes } from "./PhraseCard";
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
  /** Kept for callers of the earlier dock; the subject band now holds these acts. */
  onRelease?(): void;
  onFollowText?(): void;
  onPick(id: string): void;
  onPoint(tie: number | null, record?: string): void;
  onName?(walk: LeanWalk): void;
  /** Where the opening rises from. */
  from?: HTMLElement | null;
  passageHref(stage: Stage, anchor: string): string;
  /** Under the graph on the Graph tab, following the paper: there is nothing to close. */
  noClose?: boolean;
  /** Under the graph: show the same declaration in the Lean view. */
  onOpenLean?(): void;
  /** In the Lean view: show what this uses, and what uses it, in the graph. */
  onOpenGraph?(): void;
  /** Stands where "No Lean is linked to this paragraph" would: where to start, before the paper's first link. */
  emptySlot?: ReactNode;
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
          title={near ? "The step is stated here, and this declaration is not named at that place." : slice.section || undefined}
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
      <span>These words are also tied to</span>
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
      <p className="lean-page__plain">No Lean is linked to this paragraph. Steps of the map in its passage:</p>
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

export function LeanDock({ open, ties, stage, alignment, slot, onPick, onPoint, onName, from, passageHref, onOpenLean, onOpenGraph, emptySlot }: Props) {
  const { graph } = useEdition();
  const page = useRef<HTMLDivElement>(null);
  const scroller = useRef<HTMLDivElement>(null);
  // A pointed name is read in the top bar; where the bar has no room, in a row under the column.
  const barLine = useBarLine();
  const barShown = useBarLineShown();
  const [foot, setFoot] = useState<HTMLElement | null>(null);
  const [full, setFull] = useState(false);
  const [chosen, setChosen] = useState(0);
  const tie = open.tie !== null ? ties.index.ties[open.tie] : null;
  const at = tie?.at ?? null;
  const record = open.record;
  // A phrase brings its own declarations, each with its comparison; its titles and notes load here.
  const phrase = !!tie?.rows && !open.decl;
  const notes = usePhraseNotes(stage, !!tie?.rows);
  const part = notes?.parts[tie?.part ?? 0];
  const rows = useMemo(() => {
    // A statement with no Lean has none, whatever its step has elsewhere.
    if (tie && !tie.lean) return [];
    if (tie?.rows) return tie.rows as unknown as StatementLean[];
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
  // The graph above a phrase's card follows the declaration its card shows.
  useEffect(() => {
    dockDecl.set(phrase && row ? { name: row.name, module: row.module } : null);
  }, [phrase, row]);
  useEffect(() => () => dockDecl.set(null), []);
  const titleOf = (decl: string) => part?.titles[decl] ?? plainName(alignment, decl);
  const plain = phrase && name
    ? titleOf(name)
    : record && !isPhraseRecord(record)
      ? shortTitle(record, graph.nodes.get(record)?.label ?? alignment?.records[record]?.short ?? record)
      : name
        ? plainName(alignment, name)
        : "";
  // The paper's phrases of a declaration light while its card is pointed at, and go out with it.
  useLayoutEffect(() => () => declLight.set(null), []);
  // The phrase's own words, as the paper sets them, for the head of its card.
  const [quote, setQuote] = useState<string | null>(null);
  const segments = phrase && open.tie !== null ? ties.segmentsOf[open.tie] : undefined;
  useEffect(() => {
    if (!segments?.length) return setQuote(null);
    const read = () => {
      const found = open.tie !== null ? quoteOf(ties, open.tie) : null;
      if (found) setQuote(found);
      return found;
    };
    // New words never stand under an old quotation: clear it if these are not on the page yet.
    if (!read()) setQuote(null);
    const later = window.setTimeout(read, 400);
    return () => window.clearTimeout(later);
  }, [segments]);

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

  // The whole column is one scroller, so a new declaration starts at its top.
  const showing = `${row?.module ?? open.declModule ?? ""}:${name}:${full}`;
  useLayoutEffect(() => {
    if (scroller.current) scroller.current.scrollTop = 0;
  }, [showing]);
  // A phrase's card stays at the top; the tied lines are brought into view below it, as the Lean arrives.
  useEffect(() => {
    if (!phrase) return;
    const bring = () => {
      const box = scroller.current;
      const lit = box?.querySelector<HTMLElement>(".lean-line.is-lit");
      if (!box || !lit) return false;
      // As far as the lines need, never past the head of the phrase's card.
      const card = box.querySelector<HTMLElement>(".phrase-card");
      const over = lit.getBoundingClientRect().bottom - box.getBoundingClientRect().bottom + 24;
      const most = card ? card.getBoundingClientRect().top - box.getBoundingClientRect().top + box.scrollTop - 8 : Infinity;
      if (over > 0) box.scrollTo({ top: Math.min(box.scrollTop + over, Math.max(0, most)), behavior: "instant" as ScrollBehavior });
      return true;
    };
    const timers = [60, 250, 600, 1200].map((ms) => window.setTimeout(bring, ms));
    return () => timers.forEach((t) => window.clearTimeout(t));
  }, [showing, phrase]);

  const empty = !record && !name;
  // Where each paper states this step. Under a phrase's card it follows the comparison and the note.
  const crumbs = record && !isPhraseRecord(record) && (
    <PaperCrumbs record={record} row={alignment?.records[record]} stage={stage} alignment={alignment} decl={name} at={at}>
      {open.via === "pin" && graph.nodes.has(record) && (
        <button type="button" aria-pressed={full} onClick={() => setFull(!full)}>
          {full ? "Back to the Lean" : "Everything on this step"}
        </button>
      )}
    </PaperCrumbs>
  );
  const topic = phrase && open.tie !== null ? topicOf(ties, open.tie) : null;
  const names = useMemo(() => rows.map((item) => item.name), [rows]);
  return (
    <div className="lean-page" data-via={open.via} ref={page} role="region" aria-label={plain ? `The Lean of ${plain}` : "The Lean"}>
      {!slot && (
        <header className="lean-page__head">
          <div className="lean-page__names">
            {open.via === "point" && (
              <p className="lean-page__preview" role="status">
                Preview, not selected
              </p>
            )}
            {plain && (
              <h3 className="lean-page__title" tabIndex={-1}>
                {plain}
              </h3>
            )}
            {(tie || name || topic) && (
              <p className="lean-page__meta">
                {tie && <span className="lean-page__role">{ROLE_WORDS[tie.role]} here</span>}
                {name && <code className="lean-page__raw" title={name}>{lastName(name)}</code>}
                {topic && (
                  <span className="lean-page__topic" data-tone={topic.tone} title={topic.description || undefined}>
                    <span className="phrase-card__swatch" aria-hidden="true" />
                    {topic.name}
                  </span>
                )}
              </p>
            )}
          </div>
          {onOpenLean && !empty && (
            <button type="button" className="lean-page__quiet" onClick={onOpenLean}>
              Open its Lean
            </button>
          )}
          {onOpenGraph && !empty && (
            <button type="button" className="lean-page__quiet" onClick={onOpenGraph}>
              See what this uses in the graph
            </button>
          )}
        </header>
      )}
      {slot ? (
        <div className="lean-page__body lean-page__body--read" data-keep>
          {slot}
        </div>
      ) : (
        <div ref={scroller} className="lean-page__scroll" data-keep>
          {!(phrase && row && !full) && crumbs}
          {!open.decl && rows.length > 1 && !full && (
            <ul className="lean-page__rows" aria-label="Lean declarations of this step">
              {rows.map((item, i) => (
                <li key={`${item.module}:${item.name}`}>
                  <button
                    type="button"
                    aria-pressed={i === Math.min(chosen, rows.length - 1)}
                    title={phrase ? `${item.name}. Pointing lights every phrase of this paper it states.` : item.name}
                    onClick={() => setChosen(i)}
                    onPointerEnter={phrase ? () => declLight.set(item.name) : undefined}
                    onPointerLeave={phrase ? () => declLight.set(null) : undefined}
                    onFocus={phrase ? () => declLight.set(item.name) : undefined}
                    onBlur={phrase ? () => declLight.set(null) : undefined}
                  >
                    {phrase ? titleOf(item.name) : (item.plain ?? plainName(alignment, item.name))}
                  </button>
                </li>
              ))}
            </ul>
          )}
          <div className="lean-page__body">
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
              ) : emptySlot ? (
                emptySlot
              ) : (
                <p className="lean-page__plain">
                  No Lean is linked to this paragraph. Scroll on, or press <kbd>j</kbd> for the next linked passage.
                </p>
              )
            ) : name ? (
              <>
              {phrase && row && (
                <PhraseCard
                  row={row as unknown as PhraseLean}
                  note={part?.notes[row.name]}
                  quote={quote}
                  phrase={tie?.phrase}
                  names={names}
                />
              )}
              {phrase && row && crumbs}
              <LazyLeanBlock
                key={`${row?.module ?? open.declModule ?? ""}:${name}`}
                name={name}
                module={row?.module ?? open.declModule}
                relation={row?.relation ?? undefined}
                note={row?.note}
                fidelity={phrase ? undefined : (row ?? undefined)}
                // The phrase's card stays in view above a lit statement; lit proof lines are scrolled to.
                quietLines={phrase && !(row?.proof_lines && row.lines && row.lines[0] >= row.proof_lines[0]) ? true : undefined}
                clause={row?.clause}
                lines={row?.lines}
                compact
                onName={onName}
                noPapers
                previewSlot={barLine && barShown ? barLine : foot}
                below={
                  open.tie !== null ? (
                    ties.index.ties[open.tie]?.origin ? (
                      <>
                        <OriginLine origin={ties.index.ties[open.tie].origin} />
                        <AlsoHere tie={open.tie} ties={ties} onPick={onPick} onPoint={onPoint} />
                      </>
                    ) : (
                      <AlsoHere tie={open.tie} ties={ties} onPick={onPick} onPoint={onPoint} />
                    )
                  ) : undefined
                }
              />
              </>
            ) : alignment ? (
              <>
                <p className="lean-page__plain">{open.tie !== null ? leanTruth(ties, open.tie, alignment).words : "No Lean linked."}</p>
                {open.tie !== null && <OriginLine origin={ties.index.ties[open.tie]?.origin} />}
              </>
            ) : null}
          </div>
        </div>
      )}
      {!slot && <div ref={setFoot} className="lean-slot lean-slot--compact lean-page__foot" />}
    </div>
  );
}

/** The words of one link as the paper sets them: every fragment of it that is on the page, in order. */
export function quoteOf(ties: TieModel, t: number): string | null {
  const segments = ties.segmentsOf[t];
  if (!segments?.length) return null;
  const marks = segments.flatMap((segment) => [...document.querySelectorAll<HTMLElement>(`.paper [data-t="${segment}"]`)]);
  return marks.length ? marks.map((mark) => mark.innerHTML).join(" ") : null;
}

/**
 * A selected paragraph: every link in it, in the order of the text. Each row gives the linked
 * words whole, the plain title of what they are linked to and how many Lean declarations that is;
 * choosing a row selects those words.
 */
export function ParagraphLinks({ ties, list, onOpen, onPoint }: { ties: TieModel; list: readonly number[]; onOpen(t: number): void; onPoint(tie: number | null, record?: string): void }) {
  const [quotes, setQuotes] = useState<(string | null)[]>([]);
  useEffect(() => setQuotes(list.map((t) => quoteOf(ties, t))), [ties, list]);
  return (
    <section className="para-links" aria-label="Links in the selected paragraph">
      <h3 className="lean-page__title" tabIndex={-1}>
        {list.length === 1 ? "One link in this paragraph" : `${list.length} links in this paragraph`}
      </h3>
      <p className="para-links__lead">Each is a passage of the paragraph with the Lean it is linked to. Choose one to read its comparison and its Lean.</p>
      <ol className="para-links__list">
        {list.map((t, i) => {
          const tie = ties.index.ties[t];
          const count = tie.rows?.length ?? (tie.lean ? 1 : 0);
          return (
            <li key={t}>
              <button type="button" onClick={() => onOpen(t)} onPointerEnter={() => onPoint(t, tie.record)} onPointerLeave={() => onPoint(null)} onFocus={() => onPoint(t, tie.record)} onBlur={() => onPoint(null)}>
                <span className="para-links__quote" dangerouslySetInnerHTML={{ __html: quotes[i] ?? "" }} />
                <span className="para-links__to">
                  {phraseTitle(ties, t) || "No Lean linked"}
                  {count > 1 && <span className="para-links__count">, and {count - 1} more Lean {count === 2 ? "declaration" : "declarations"}</span>}
                </span>
              </button>
            </li>
          );
        })}
      </ol>
    </section>
  );
}

export { clampDock, DOCK_MAX, DOCK_MIN, readDockShare, readKeepLean, saveDockShare, saveKeepLean } from "./panePrefs";

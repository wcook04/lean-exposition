// The ledger of every recorded check in the edition. It opens with what a Lean reader asks
// first (Standing.tsx): what compiled, what Comparator did, which axioms, any sorry, and what
// is only read. Then a table by kind of check with the number passed, failed, unavailable
// and not run in columns of their own. Outcomes are never merged across kinds. Only a
// recorded failure is coloured; there is no percentage and no success badge. Every number
// is computed from the edition or read from a record. A page about one record keeps the
// plain paragraph at its head.

import { useEffect, useId, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Route } from "../app/router";
import { routeHref } from "../app/router";
import { describeError, useEdition, useRecord } from "../app/data";
import type { ArgGraph } from "../model/graph";
import { useAlignment } from "../compare/useAlignment";
import { useEvidence, type EvidenceRecord } from "./evidence";
import {
  CHECK_KINDS,
  countsInWords,
  failureLine,
  groupByKind,
  inStatedTimeOrder,
  OUTCOME_MEANINGS,
  OUTCOME_NAMES,
  recordsWord,
  statedDate,
  type EvidenceCard,
  type KindGroup,
} from "./summary";
import { RecordList } from "./RecordTiles";
import { Standing } from "./Standing";
import "./checks.css";

const PAGE = 25;
/** Kinds with more records than this are shown in pages of PAGE. */
const PAGED_OVER = 40;
const STATUS_ORDER = ["failed", "unavailable", "not_run", "passed"];
/** The outcome columns of the table, in the order a reader takes them. */
const COUNT_COLUMNS = ["passed", "failed", "unavailable", "not_run"] as const;
const COLUMN_NAMES: Record<string, string> = { passed: "Passed", failed: "Failed", unavailable: "Unavailable", not_run: "Not run" };

type Target =
  | { type: "none" }
  | { type: "node"; id: string; formal?: string }
  | { type: "evidence"; id: string; kind: string; index: number }
  | { type: "unknown"; id: string };

function resolveTarget(n: string | undefined, graph: ArgGraph, cards: EvidenceCard[]): Target {
  if (!n) return { type: "none" };
  const node = graph.nodes.get(n);
  if (node) {
    const formal = node.kind === "declaration" ? undefined : (graph.out.get(n) ?? []).find((e) => e.kind === "formalizes")?.to;
    return { type: "node", id: n, formal };
  }
  const card = cards.find((c) => c.id === n);
  if (card) {
    const index = cards.filter((c) => c.kind === card.kind).indexOf(card);
    return { type: "evidence", id: n, kind: card.kind, index };
  }
  return { type: "unknown", id: n };
}

/** Outcome counts in a fixed order, failures first so they are never last in a list. */
export function outcomeParts(counts: Record<string, number>): { status: string; n: number }[] {
  const known = STATUS_ORDER.filter((s) => counts[s]).map((status) => ({ status, n: counts[status] }));
  const other = Object.keys(counts)
    .filter((s) => !STATUS_ORDER.includes(s) && counts[s])
    .sort()
    .map((status) => ({ status, n: counts[status] }));
  return [...known, ...other];
}

/**
 * One plain sentence a row adds under its counts, or null. It only restates
 * the counts: a kind with records and no pass has no successful result.
 */
export function rowNote(kind: string, counts: Record<string, number>): string | null {
  const total = Object.values(counts).reduce((s, n) => s + n, 0);
  if (!total || counts.passed) return null;
  if (kind === "comparator") return "No successful Comparator result is recorded.";
  if (kind === "semantic_review" && counts.not_run === total)
    return "All written, none independently run. Each is an authored explanation of one step, with the source lines it rests on.";
  if (counts.failed || counts.unavailable) return "No successful run is recorded.";
  return null;
}

/**
 * The edition-level note, said once. The table gives each kind's counts and what it tests,
 * and the opening paragraph says when no review has passed; this adds the whole, and what
 * an outcome is.
 */
export function editionNote(cards: readonly EvidenceCard[]): string {
  const total = cards.length;
  const notRun = cards.filter((c) => c.status === "not_run").length;
  const reviews = cards.filter((c) => c.kind === "semantic_review");
  const reviewed = reviews.filter((c) => c.status === "passed").length;
  const lead =
    notRun * 2 > total
      ? `Most recorded checks on this site have not been run (${notRun} of ${total}).`
      : `${notRun} of the ${total} recorded checks on this site have not been run.`;
  const review = reviewed
    ? ` ${reviewed} correspondence ${reviewed === 1 ? "review is" : "reviews are"} recorded as passed, and the reviewer is not recorded as independent.`
    : "";
  return `${lead}${review} Each outcome is the result written in one check record, for that check alone, and is not a judgement on whether the mathematics is correct.`;
}

export function ChecksPage({ route }: { route: Extract<Route, { view: "checks" }> }) {
  const { graph, map } = useEdition();
  const cards = map.records.evidence as EvidenceCard[];
  const groups = useMemo(() => groupByKind(cards), [cards]);
  const target = useMemo(() => resolveTarget(route.node, graph, cards), [route.node, graph, cards]);
  const subject = target.type === "node" ? graph.nodes.get(target.id)! : null;
  const supportObservation = cards.some((card) => card.id === "full_support_v2_receipt_binding_20261026");

  const declarations = useMemo(() => {
    const ids = graph.order.filter((id) => graph.nodes.get(id)!.kind === "declaration");
    const formalizesGoal = (id: string) =>
      (graph.in.get(id) ?? []).some((e) => e.kind === "formalizes" && graph.nodes.get(e.from)?.kind === "goal");
    return [...ids.filter(formalizesGoal), ...ids.filter((id) => !formalizesGoal(id))];
  }, [graph]);

  return (
    <div className="checks">
      {subject ? (
        <header className="checks__head">
          <div className="checks__lead">
            <h1>
              Checks recorded for <span className={subject.kind === "declaration" ? "lean" : undefined}>{subject.label}</span>
            </h1>
            <Established cards={cards} />
          </div>
          <OutcomeKey />
        </header>
      ) : (
        <header className="checks__first">
          <h1>What ran on this proof, and what did not</h1>
          <Standing groups={groups} />
        </header>
      )}

      {target.type === "unknown" && (
        <p className="checks__notice" role="status">
          No record on this site has the identifier <code className="lean">{target.id}</code>. All the checks are listed below.
        </p>
      )}

      {target.type === "node" && <SubjectChecks id={target.id} formal={target.formal} />}

      <section className="checks__band" aria-labelledby="by-kind">
        <h2 id="by-kind">{subject ? "All checks on this site, by kind" : "Every check, by kind"}</h2>
        {!subject && <OutcomeKey wide />}
        <CheckTable
          caption="All recorded checks on this site, by kind"
          rows={groups.map((g) => ({ group: g, examined: null }))}
          target={target.type === "evidence" ? target : null}
          paged
          pointers
        />
        <div className="checks__notes">
        <p className="checks__edition">{editionNote(cards)}</p>
        {supportObservation && (
          <p className="checks__edition">
            A separate <a href={`${import.meta.env.BASE_URL}verification/full-support-build-extraction-observation-20261026.json`}>
              Support observation from 26 October 2026
            </a> records a completed build and a scoped dependency extraction. Its graph is partial and is not part of this
            edition, so it does not change the outcomes above or establish Comparator acceptance.
          </p>
        )}
        </div>
      </section>

      {target.type !== "node" && <RecordList />}

      <section className="checks__band" aria-labelledby="formal">
        <h2 id="formal">The main statements in Lean</h2>
        <p className="checks__intro">
          {declarations.length === 1 ? "One Lean declaration" : `${declarations.length} Lean declarations`}, each with the claims
          recorded as corresponding to it.
        </p>
        <div className="formal-list">
          {declarations.map((id) => (
            <FormalStatement
              key={id}
              id={id}
              selected={target.type === "node" && (target.id === id || target.formal === id)}
            />
          ))}
        </div>
      </section>
    </div>
  );
}

/**
 * The opening paragraph: what the one passed build examined, then what has no result.
 * Its facts come from the records' own text, its counts from the edition. While the
 * build's record loads, the counts alone stand in, so nothing is said that is not yet read.
 */
function Established({ cards }: { cards: EvidenceCard[] }) {
  const { graph } = useEdition();
  const groups = useMemo(() => groupByKind(cards), [cards]);
  const of = (kind: string) => groups.find((g) => g.kind === kind);
  const passedBuilds = useMemo(() => cards.filter((c) => c.kind === "lean_build" && c.status === "passed"), [cards]);
  const evidence = useEvidence(useMemo(() => passedBuilds.map((c) => c.ref), [passedBuilds]));
  const record = evidence.status === "ready" && passedBuilds[0] ? evidence.records.get(passedBuilds[0].ref) : undefined;
  const module = /\bOAI(?:\.\w+)+/.exec(record?.details ?? "")?.[0];
  const version = /(\d+\.\d+\.\d+)/.exec(record?.tool ?? "")?.[1];
  const date = statedDate(record?.details);
  const subject = record?.subject_ids?.[0] ? graph.nodes.get(record.subject_ids[0]) : undefined;
  const comparator = of("comparator");
  const reviews = of("semantic_review");
  const hashes = of("source_hash");
  return (
    <p className="checks__lede">
      {record ? (
        <>
          Lean, a language in which a computer checks each step of a proof, compiled{" "}
          {module ? <code className="lean" translate="no">{module}</code> : "the Lean file"}
          {subject ? <>, the module recorded for <span className="lean" translate="no">{subject.label}</span>,</> : null} without an error
          {version ? ` on version ${version}` : ""}
          {date ? `; the record of that build is dated ${date.text}` : ""}.{" "}
        </>
      ) : passedBuilds.length === 0 ? (
        <>No Lean build, the step in which a computer checks each line of a proof, is recorded as passed. </>
      ) : null}
      {hashes && hashes.cards.length > 0 && <>The cited files match their recorded hashes in {countsInWords(hashes.counts)} checks. </>}
      {comparator && comparator.cards.length > 0 && (
        <>
          Comparator, a program that compares a Lean proof with a separately written statement of the theorem, has{" "}
          {comparator.counts.passed ? `${comparator.counts.passed} passed` : "no successful result"}: of its{" "}
          {recordsWord(comparator.cards.length)}, {countsInWords(comparator.counts)}.{" "}
        </>
      )}
      {reviews && reviews.cards.length > 0 && !reviews.counts.passed && (
        <>
          The {reviews.cards.length} correspondence reviews, which compare a recorded step with its source, are written but none
          has been independently run, so no one has confirmed that the papers and the Lean say the same thing.
        </>
      )}
    </p>
  );
}

function OutcomeKey({ wide }: { wide?: boolean }) {
  return (
    <section className={`outcome-key${wide ? " outcome-key--wide" : ""}`} aria-labelledby="outcome-key">
      <h2 id="outcome-key" className={wide ? "visually-hidden" : undefined}>What each outcome means</h2>
      <dl className="outcomes">
        {OUTCOME_MEANINGS.map((o) => (
          <div key={o.status} className="outcomes__row">
            <dt>
              <Outcome status={o.status} />
            </dt>
            <dd>{o.meaning}</dd>
          </div>
        ))}
      </dl>
    </section>
  );
}

// ------------------------------------------------------- the selected subject

function SubjectChecks({ id, formal }: { id: string; formal?: string }) {
  const { graph, map } = useEdition();
  const node = graph.nodes.get(id)!;
  const detail = useRecord(node.ref);
  const record = detail.status === "ready" ? detail.value.record : null;
  const cards = useMemo(() => {
    const byId = new Map((map.records.evidence as EvidenceCard[]).map((c) => [c.id, c]));
    return ((record?.evidence_ids as string[] | undefined) ?? []).map((e) => byId.get(e)).filter((c): c is EvidenceCard => !!c);
  }, [record, map]);
  const groups = useMemo(() => groupByKind(cards).filter((g) => g.cards.length > 0), [cards]);
  // No scroll on arrival: the rows follow the heading and the edition note, which must be read first.
  const formalNode = formal ? graph.nodes.get(formal) : null;

  return (
    <section className="checks__band subject is-selected" aria-labelledby="subject-checks">
      <h2 id="subject-checks">Checks attached to this {node.kind === "declaration" ? "Lean declaration" : node.kind === "goal" ? "result" : node.kind}</h2>
      <p className="checks__intro">
        {detail.status === "loading" && "Loading the record…"}
        {detail.status === "error" && <span className="checks__error">{describeError(detail.error).title}.</span>}
        {record && cards.length === 0 && (
          <>
            No check is recorded for this {node.kind === "assumption" ? "assumption" : "record"} itself. The record’s status is{" "}
            {node.status === "unverified"
              ? "unverified, which means it was stated from the sources and has not been independently checked"
              : node.status.replace(/_/g, " ")}
            .{" "}
          </>
        )}
        {record && cards.length > 0 && <>The counts below refer only to the {recordsWord(cards.length)} attached to it. </>}
        {formalNode && (
          <>
            Its formal statement in Lean is <a className="lean" href={`#${formal}`}>{formalNode.label}</a>.{" "}
          </>
        )}
        <a href={routeHref({ view: "map", node: id })}>Open it on the argument map</a>
      </p>
      {groups.length > 0 && (
        <CheckTable
          caption={`Checks attached to ${node.label}, by kind`}
          rows={groups.map((g) => ({ group: g, examined: null }))}
          target={null}
        />
      )}
    </section>
  );
}

// ------------------------------------------------------------- the table

interface Row {
  group: KindGroup;
  /** A line under the kind's question; null for none. */
  examined: string | null;
}

function CheckTable({
  caption,
  rows,
  target,
  paged,
  pointers,
}: {
  caption: string;
  rows: Row[];
  target: Extract<Target, { type: "evidence" }> | null;
  paged?: boolean;
  /** Add the row for the site's own check of its Lean and paper links. */
  pointers?: boolean;
}) {
  const shown = rows.filter((r) => r.group.cards.length > 0);
  return (
    <table className="checktable">
        <caption className="visually-hidden">{caption}</caption>
        <thead>
          <tr>
            <th scope="col">Check</th>
            <th scope="col">What it tests</th>
            {COUNT_COLUMNS.map((c) => (
              <th key={c} scope="col" className="checktable__n">
                {COLUMN_NAMES[c]}
              </th>
            ))}
            <th scope="col">
              <span className="visually-hidden">Records</span>
            </th>
          </tr>
        </thead>
        {shown.map((row) => (
          <KindRow key={row.group.kind} row={row} target={target && target.kind === row.group.kind ? target : null} paged={!!paged} />
        ))}
        {pointers && <PointerRow />}
    </table>
  );
}

function CountCells({ counts }: { counts: Record<string, number> }) {
  return (
    <>
      {COUNT_COLUMNS.map((c) => {
        const n = counts[c] ?? 0;
        return (
          <td key={c} className={`checktable__n num${n === 0 ? " is-zero" : ""}${c === "failed" && n > 0 ? " is-failed" : ""}`} data-label={COLUMN_NAMES[c]}>
            {n}
          </td>
        );
      })}
    </>
  );
}

/**
 * The links between records, Lean and the papers. They are authored; the export keeps a
 * link only if it lands, so the edition holds no count of failures to report here.
 * This is a row of the site's own, computed from the alignment, not a stored check record.
 */
function PointerRow() {
  const alignment = useAlignment();
  const links = useMemo(() => {
    if (!alignment) return null;
    const rows = Object.values(alignment.records);
    return { lean: rows.reduce((s, r) => s + r.lean.length, 0), papers: rows.reduce((s, r) => s + r.statements.length, 0) };
  }, [alignment]);
  return (
    <tbody className="checkrow checkrow--pointers">
      <tr>
        <th scope="row" className="checkrow__kind">
          Lean and paper links
        </th>
        <td className="checkrow__examined" data-label="What it tests">
          Whether each authored link still lands: every quoted passage is found in its paper and every named declaration
          in its Lean file.
          <span className="checkrow__note">
            {links ? `${links.lean} links to Lean and ${links.papers} to the papers. ` : ""}The site’s own test at each build,
            not a stored check record. No one has reviewed whether the mathematics on the two sides of a link matches.
          </span>
        </td>
        <td className="checktable__n num" data-label="Passed">
          {links ? links.lean + links.papers : ""}
        </td>
        <td colSpan={3} className="checkrow__left-out">
          A link that does not land is left out of the site.
        </td>
        <td className="checkrow__details" />
      </tr>
    </tbody>
  );
}

function FailureNotes({ group }: { group: KindGroup }) {
  const failed = useMemo(() => group.cards.filter((c) => c.status === "failed"), [group]);
  const evidence = useEvidence(useMemo(() => failed.map((c) => c.ref), [failed]));
  return (
    <tr className="checkrow__failures">
      <td colSpan={7}>
        <ul>
          {failed.map((c) => (
            <li key={c.id}>
              <Outcome status="failed" />
              <span>{failureLine(c, evidence.status === "ready" ? evidence.records.get(c.ref) : undefined)}</span>
            </li>
          ))}
        </ul>
        <p>A failed build is not a rejection of the proof. These runs stopped before any comparison, and their records say that no mathematical rejection was observed.</p>
      </td>
    </tr>
  );
}

function KindRow({ row, target, paged: allowPaging }: { row: Row; target: Extract<Target, { type: "evidence" }> | null; paged: boolean }) {
  const { group } = row;
  const uid = useId();
  const total = group.cards.length;
  const paged = allowPaging && total > PAGED_OVER;
  const [open, setOpen] = useState(!!target);
  const [shown, setShown] = useState(paged ? PAGE : total);
  useEffect(() => {
    if (!target) return;
    setOpen(true);
    if (paged) setShown((s) => Math.max(s, Math.ceil((target.index + 1) / PAGE) * PAGE));
  }, [target, paged]);

  const visible = open ? group.cards.slice(0, shown) : [];
  // Only records a reader opens are requested; earlier pages stay cached.
  const evidence = useEvidence(open ? visible.map((c) => c.ref) : null);
  const ordered = useMemo(() => {
    if (evidence.status !== "ready") return null;
    return inStatedTimeOrder(visible.map((card) => ({ card, details: evidence.records.get(card.ref)?.details, record: evidence.records.get(card.ref) })));
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [evidence, shown, open]);
  const historyId = `${uid}-history`;
  const note = rowNote(group.kind, group.counts);

  return (
    <tbody id={`kind-${group.kind}`} className="checkrow">
      <tr>
        <th scope="row" className="checkrow__kind">
          {group.title}
        </th>
        <td className="checkrow__examined" data-label="What it tests">
          {group.question || <span className="faint">Not stated in the check records.</span>}
          {row.examined && <span className="checkrow__subjects">{row.examined}</span>}
          {note && <span className="checkrow__note">{note}</span>}
        </td>
        <CountCells counts={group.counts} />
        <td className="checkrow__details">
          <button type="button" className="control checkrow__toggle" aria-expanded={open} aria-controls={historyId} onClick={() => setOpen((o) => !o)}>
            <Chevron open={open} />
            {open ? "Hide" : total === 1 ? "Open" : `Open all ${total}`}
            <span className="visually-hidden">{` ${group.title} records`}</span>
          </button>
        </td>
      </tr>
      {group.counts.failed > 0 && <FailureNotes group={group} />}
      <tr className="checkrow__history" id={historyId} hidden={!open}>
        <td colSpan={7}>
          {open && (
            <>
              {evidence.status === "error" && <p className="checks__error">{describeError(evidence.error).title}.</p>}
              {evidence.status !== "ready" && evidence.status !== "error" && <p className="faint">Loading the check records…</p>}
              {ordered && (
                <>
                  {ordered.dated.length > 0 && (
                    <ol className="ledger">
                      {ordered.dated.map(({ record: r }) => (
                        <EvidenceRow key={r.card.id} card={r.card} record={r.record} selected={target?.id === r.card.id} />
                      ))}
                    </ol>
                  )}
                  {ordered.undated.length > 0 && (
                    <>
                      {ordered.dated.length > 0 && <p className="ledger__break">Check records with no date, in their stored order</p>}
                      <ol className="ledger">
                        {ordered.undated.map((r) => (
                          <EvidenceRow key={r.card.id} card={r.card} record={r.record} selected={target?.id === r.card.id} />
                        ))}
                      </ol>
                    </>
                  )}
                </>
              )}
              {paged && (
                <p className="kind__more">
                  <span className="faint num">
                    {Math.min(shown, total)} of {total} shown
                  </span>
                  {shown < total && (
                    <button type="button" className="control" onClick={() => setShown((s) => s + PAGE)}>
                      Show {Math.min(PAGE, total - shown)} more
                    </button>
                  )}
                </p>
              )}
            </>
          )}
        </td>
      </tr>
    </tbody>
  );
}

// ----------------------------------------------------------- formal statements

function FormalStatement({ id, selected }: { id: string; selected: boolean }) {
  const { graph } = useEdition();
  const node = graph.nodes.get(id)!;
  const detail = useRecord(node.ref);
  const record = detail.status === "ready" ? detail.value.record : null;
  const claims = (graph.in.get(id) ?? []).filter((e) => e.kind === "formalizes").map((e) => e.from);
  const count = ((record?.evidence_ids as string[] | undefined) ?? []).length;

  return (
    <article id={id} className={`formal${selected ? " is-selected" : ""}`} aria-labelledby={`formal-${id}`}>
      <h3 id={`formal-${id}`} className="formal__name lean" translate="no">
        {node.label}
      </h3>
      <p className="formal__of">
        {claims.length === 0 ? (
          "No claim is recorded as corresponding to this declaration."
        ) : (
          <>
            Recorded as the formal statement of{" "}
            {claims.map((c, i) => (
              <span key={c}>
                {i > 0 && (i === claims.length - 1 ? " and " : ", ")}
                <a href={routeHref({ view: "map", node: c })}>{graph.nodes.get(c)?.label ?? c}</a>
              </span>
            ))}
            .{" "}
            <a href={routeHref({ view: "map", node: id })} className="formal__map">
              Show it on the argument map
            </a>
          </>
        )}
      </p>
      {detail.status === "loading" && <p className="faint">Loading the statement…</p>}
      {detail.status === "error" && <p className="checks__error">{describeError(detail.error).title}.</p>}
      {record?.statement && (
        <pre className="formal__lean">
          <code className="lean" translate="no">
            {String(record.statement)}
          </code>
        </pre>
      )}
      {record?.boundary && (
        <p className="formal__scope">
          <span className="formal__label">Recorded scope.</span> {String(record.boundary)}
        </p>
      )}
      {record && (
        <p className="formal__checks">
          {count === 0 ? (
            "No check is recorded for this declaration on its own."
          ) : selected ? (
            <>Its {recordsWord(count)} are listed at the top of this page.</>
          ) : (
            <a href={routeHref({ view: "checks", node: id })}>Show its {recordsWord(count)}, by kind</a>
          )}
        </p>
      )}
    </article>
  );
}

// ------------------------------------------------------------------ one record

function EvidenceRow({
  card,
  record,
  showKind,
  selected,
  compact,
}: {
  card: EvidenceCard;
  record?: EvidenceRecord;
  showKind?: boolean;
  selected?: boolean;
  /** In a statement's own history: receipt and identifier only when expanded. */
  compact?: boolean;
}) {
  const { graph } = useEdition();
  // A recorded failure shows its whole record: date, inputs and where it stopped.
  const [expanded, setExpanded] = useState(card.status === "failed");
  const [clipped, setClipped] = useState(false);
  const detailsRef = useRef<HTMLParagraphElement>(null);
  const rowRef = useScrollTarget<HTMLLIElement>(!!selected && !!record);

  // The details are clamped only when that hides two lines or more: hiding one line behind
  // a button saves no room. scrollHeight is the whole text's height, clamped or not.
  const clampLines = compact ? 2 : 3;
  useLayoutEffect(() => {
    const el = detailsRef.current;
    if (!el || expanded) return;
    const measure = () => {
      const line = parseFloat(getComputedStyle(el).lineHeight) || 20;
      setClipped(Math.round(el.scrollHeight / line) >= clampLines + 2);
    };
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, [record, expanded, clampLines]);

  const date = statedDate(record?.details);
  const subjects = record?.subject_ids ?? [];
  const SUBJECTS_SHOWN = 4;
  const visibleSubjects = expanded ? subjects : subjects.slice(0, SUBJECTS_SHOWN);
  const hidden = subjects.length - visibleSubjects.length;
  const kindTitle = CHECK_KINDS[card.kind]?.title ?? card.kind.replace(/_/g, " ");
  const canExpand = clipped || hidden > 0 || (record?.command?.length ?? 0) > 0 || (record?.source_ids?.length ?? 0) > 0 || (!!compact && !!record?.receipt_path);

  return (
    <li ref={rowRef} id={`check-${card.id}`} className={`ev${compact ? " ev--compact" : ""}${selected ? " is-selected" : ""}`}>
      <div className="ev__outcome">
        <Outcome status={card.status} />
      </div>
      <div className="ev__body">
        <p className="ev__tool">
          {showKind && <span className="ev__kind">{kindTitle}. </span>}
          {record ? record.tool ?? "No tool is named in the record." : <span className="faint">Loading the record…</span>}
        </p>
        {record && (
          <>
            <p className="ev__meta">
              {date && <span className="ev__date">The date given in the record is {date.text}. </span>}
              {subjects.length === 0 ? (
                "No statement is named as the subject of this check."
              ) : (
                <>
                  It concerns{" "}
                  {visibleSubjects.map((s, i) => {
                    const n = graph.nodes.get(s);
                    return (
                      <span key={s}>
                        {i > 0 && (i === visibleSubjects.length - 1 && hidden === 0 ? " and " : ", ")}
                        {n ? (
                          <a href={routeHref({ view: "map", node: s })} className={n.kind === "declaration" ? "lean" : undefined}>
                            {n.label}
                          </a>
                        ) : (
                          <code className="lean">{s}</code>
                        )}
                      </span>
                    );
                  })}
                  {hidden > 0 && ` and ${hidden} more`}.
                </>
              )}
            </p>
            {record.details && (
              <p ref={detailsRef} className={`ev__details${expanded || !clipped ? "" : compact ? " is-clamped is-short" : " is-clamped"}`}>
                {record.details}
              </p>
            )}
            {expanded && record.command && record.command.length > 0 && (
              <div className="ev__extra">
                <p className="ev__label">Command recorded</p>
                <pre className="ev__command">
                  <code translate="no">{record.command.join(" ")}</code>
                </pre>
              </div>
            )}
            {expanded && record.source_ids && record.source_ids.length > 0 && (
              <p className="ev__extra ev__sources">
                <span className="ev__label">Sources named in the record. </span>
                {record.source_ids.map((s, i) => (
                  <span key={s}>
                    {i > 0 && ", "}
                    <code className="lean" translate="no">
                      {s}
                    </code>
                  </span>
                ))}
              </p>
            )}
            {record.receipt_path && (!compact || expanded) && (
              <p className="ev__receipt">
                The output saved for this check is in the repository file{" "}
                <code className="lean" translate="no">{record.receipt_path}</code>, which this site does not serve.
                {expanded && record.receipt_sha256 && (
                  <>
                    {" "}
                    The SHA-256 hash of that file is <code className="lean ev__hash">{record.receipt_sha256}</code>.
                  </>
                )}
              </p>
            )}
            <p className="ev__foot">
              {(!compact || expanded) && (
                <span className="faint" translate="no">
                  Record {card.id}
                </span>
              )}
              {canExpand && (
                <button type="button" className="ev__more" aria-expanded={expanded} onClick={() => setExpanded((e) => !e)}>
                  {expanded ? "Show less" : "Show the full record"}
                </button>
              )}
            </p>
          </>
        )}
      </div>
    </li>
  );
}

function Outcome({ status }: { status: string }) {
  return (
    <span className={`outcome outcome--${status}`}>
      <span className="outcome__mark" aria-hidden="true" />
      {OUTCOME_NAMES[status] ?? status.replace(/_/g, " ")}
    </span>
  );
}

function Chevron({ open }: { open: boolean }) {
  return (
    <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true" className={`chevron${open ? " is-open" : ""}`}>
      <path d="M3 2l3.5 3L3 8" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  );
}

/** Scroll an element into view once, the first time `when` becomes true. */
function useScrollTarget<T extends HTMLElement>(when: boolean) {
  const ref = useRef<T>(null);
  const done = useRef(false);
  useEffect(() => {
    if (!when || done.current || !ref.current) return;
    done.current = true;
    const el = ref.current;
    requestAnimationFrame(() => el.scrollIntoView({ block: "start" }));
  }, [when]);
  return ref;
}

// The ledger of every recorded check in the edition. Checks are grouped by
// the question each kind answers, never merged across kinds, and a run that
// did not happen or did not finish is shown with the record's own words.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Route } from "../app/router";
import { routeHref } from "../app/router";
import { describeError, useEdition, useRecord } from "../app/data";
import type { ArgGraph } from "../model/graph";
import { useEvidence, type EvidenceRecord } from "./evidence";
import {
  CHECK_KINDS,
  countsInWords,
  groupByKind,
  inStatedTimeOrder,
  OUTCOME_MEANINGS,
  OUTCOME_NAMES,
  recordsWord,
  standingSentence,
  statedDate,
  type EvidenceCard,
  type KindGroup,
} from "./summary";
import "./checks.css";

const PAGE = 25;
/** Kinds with more records than this are shown in pages of PAGE. */
const PAGED_OVER = 40;

type Target =
  | { type: "none" }
  | { type: "formal"; id: string; via?: string }
  | { type: "node"; id: string }
  | { type: "evidence"; id: string; kind: string; index: number }
  | { type: "unknown"; id: string };

function resolveTarget(n: string | undefined, graph: ArgGraph, cards: EvidenceCard[]): Target {
  if (!n) return { type: "none" };
  const node = graph.nodes.get(n);
  if (node) {
    if (node.kind === "declaration") return { type: "formal", id: n };
    const formal = (graph.out.get(n) ?? []).find((e) => e.kind === "formalizes");
    if (formal) return { type: "formal", id: formal.to, via: n };
    return { type: "node", id: n };
  }
  const card = cards.find((c) => c.id === n);
  if (card) {
    const index = cards.filter((c) => c.kind === card.kind).indexOf(card);
    return { type: "evidence", id: n, kind: card.kind, index };
  }
  return { type: "unknown", id: n };
}

export function ChecksPage({ route }: { route: Extract<Route, { view: "checks" }> }) {
  const { graph, map } = useEdition();
  const cards = map.records.evidence as EvidenceCard[];
  const groups = useMemo(() => groupByKind(cards), [cards]);
  const target = useMemo(() => resolveTarget(route.node, graph, cards), [route.node, graph, cards]);

  const declarations = useMemo(() => {
    const ids = graph.order.filter((id) => graph.nodes.get(id)!.kind === "declaration");
    const formalizesGoal = (id: string) =>
      (graph.in.get(id) ?? []).some((e) => e.kind === "formalizes" && graph.nodes.get(e.from)?.kind === "goal");
    return [...ids.filter(formalizesGoal), ...ids.filter((id) => !formalizesGoal(id))];
  }, [graph]);

  useEffect(() => {
    document.title = "Recorded checks";
  }, []);

  return (
    <div className="checks">
      <header className="checks__head">
        <h1>Recorded checks</h1>
        <p className="checks__lede">
          Every check recorded in this edition, grouped by the question each kind of check answers. A check that was
          planned but not run, or that did not finish, is listed as such: it is not a verdict on the mathematics.
        </p>
      </header>

      {target.type === "node" && <NodeChecks id={target.id} />}
      {target.type === "unknown" && (
        <p className="checks__notice" role="status">
          Nothing in this edition is called <code className="lean">{target.id}</code>. The full ledger follows.
        </p>
      )}

      <section className="checks__band" aria-labelledby="standing">
        <h2 id="standing">Where things stand</h2>
        <ul className="standing">
          {groups.map((g) => (
            <li key={g.kind}>
              <a href={`#kind-${g.kind}`} className="standing__kind">
                {g.title}
              </a>
              <span className="standing__text">{standingSentence(g)}</span>
            </li>
          ))}
        </ul>
      </section>

      <section className="checks__band" aria-labelledby="formal">
        <h2 id="formal">Formal statements</h2>
        <p className="checks__intro">
          The edition records {declarations.length === 1 ? "one Lean declaration" : `${declarations.length} Lean declarations`}. Each is
          the formal statement of a claim in the shared record. Below each statement are the checks recorded for it,
          earliest first where the record gives a date.
        </p>
        {declarations.map((id) => (
          <FormalStatement key={id} id={id} selected={target.type === "formal" && target.id === id} via={target.type === "formal" && target.id === id ? target.via : undefined} />
        ))}
      </section>

      <section className="checks__band" aria-labelledby="by-kind">
        <h2 id="by-kind">Every check, by kind</h2>
        <p className="checks__intro">
          {recordsWord(cards.length)} in all. Each record is one check of one kind: what was run or planned, on which
          statements, and what happened. An outcome means:
        </p>
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
        {groups.map((g) => (
          <KindSection key={g.kind} group={g} target={target.type === "evidence" && target.kind === g.kind ? target : null} />
        ))}
      </section>
    </div>
  );
}

// ----------------------------------------------------------- formal statements

function FormalStatement({ id, selected, via }: { id: string; selected: boolean; via?: string }) {
  const { graph, map } = useEdition();
  const node = graph.nodes.get(id)!;
  const detail = useRecord(node.ref);
  const record = detail.status === "ready" ? detail.value.record : null;
  const claims = (graph.in.get(id) ?? []).filter((e) => e.kind === "formalizes").map((e) => e.from);
  const evidenceIds = (record?.evidence_ids as string[] | undefined) ?? [];
  const cards = useMemo(() => {
    const byId = new Map((map.records.evidence as EvidenceCard[]).map((c) => [c.id, c]));
    return evidenceIds.map((e) => byId.get(e)).filter((c): c is EvidenceCard => !!c);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [record, map]);
  const evidence = useEvidence(record ? cards.map((c) => c.ref) : null);
  const ref = useScrollTarget<HTMLElement>(selected && detail.status === "ready");

  const ordered = useMemo(() => {
    if (evidence.status !== "ready") return null;
    const rows = cards.map((card) => ({ card, record: evidence.records.get(card.ref)!, details: evidence.records.get(card.ref)?.details }));
    return inStatedTimeOrder(rows);
  }, [evidence, cards]);

  return (
    <article ref={ref} id={id} className={`formal${selected ? " is-selected" : ""}`} aria-labelledby={`formal-${id}`}>
      <h3 id={`formal-${id}`} className="formal__name lean" translate="no">
        {node.label}
      </h3>
      <p className="formal__of">
        {claims.length === 0 ? (
          "No claim in the record names it as its formal statement."
        ) : (
          <>
            Formal statement of{" "}
            {claims.map((c, i) => (
              <span key={c}>
                {i > 0 && (i === claims.length - 1 ? " and " : ", ")}
                <a href={routeHref({ view: "map", node: c })} className={via === c ? "is-from" : undefined}>
                  {graph.nodes.get(c)?.label ?? c}
                </a>
              </span>
            ))}
            .{" "}
            <a href={routeHref({ view: "map", node: id })} className="formal__map">
              Show it on the map
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
          <span className="formal__label">Scope recorded with it.</span> {String(record.boundary)}
        </p>
      )}
      {record && (
        <div className="formal__checks">
          <h4 className="formal__label">
            {cards.length === 0 ? "No check is recorded for this declaration on its own." : `Checks recorded for it: ${recordsWord(cards.length)}; ${countsInWords(countOf(cards))}`}
          </h4>
          {cards.length > 0 && evidence.status === "loading" && <p className="faint">Loading the records…</p>}
          {evidence.status === "error" && <p className="checks__error">{describeError(evidence.error).title}.</p>}
          {ordered && (
            <>
              {ordered.dated.length > 0 && (
                <ol className="ledger">
                  {ordered.dated.map(({ record: row }) => (
                    <EvidenceRow key={row.card.id} card={row.card} record={row.record} showKind compact />
                  ))}
                </ol>
              )}
              {ordered.undated.length > 0 && (
                <>
                  {ordered.dated.length > 0 && <p className="ledger__break">Records that state no date, in the order the record lists them</p>}
                  <ol className="ledger">
                    {ordered.undated.map((row) => (
                      <EvidenceRow key={row.card.id} card={row.card} record={row.record} showKind compact />
                    ))}
                  </ol>
                </>
              )}
            </>
          )}
        </div>
      )}
    </article>
  );
}

function countOf(cards: EvidenceCard[]): Record<string, number> {
  const counts: Record<string, number> = {};
  for (const c of cards) counts[c.status] = (counts[c.status] ?? 0) + 1;
  return counts;
}

// --------------------------------------------- a node that is not a declaration

function NodeChecks({ id }: { id: string }) {
  const { graph, map } = useEdition();
  const node = graph.nodes.get(id)!;
  const detail = useRecord(node.ref);
  const record = detail.status === "ready" ? detail.value.record : null;
  const cards = useMemo(() => {
    const byId = new Map((map.records.evidence as EvidenceCard[]).map((c) => [c.id, c]));
    return ((record?.evidence_ids as string[] | undefined) ?? []).map((e) => byId.get(e)).filter((c): c is EvidenceCard => !!c);
  }, [record, map]);
  const evidence = useEvidence(record ? cards.map((c) => c.ref) : null);
  const ref = useScrollTarget<HTMLElement>(detail.status === "ready");
  return (
    <section ref={ref} className="checks__band node-checks is-selected" aria-labelledby="node-checks">
      <h2 id="node-checks">
        Checks recorded for <span className={node.kind === "declaration" ? "lean" : undefined}>{node.label}</span>
      </h2>
      {detail.status === "loading" && <p className="faint">Loading…</p>}
      {record && cards.length === 0 && (
        <p className="checks__intro">
          No check is recorded for this {node.kind === "assumption" ? "assumption" : "claim"} itself. Its status in the record:{" "}
          {node.status === "unverified" ? "stated from the sources, not independently checked" : node.status.replace(/_/g, " ")}.{" "}
          <a href={routeHref({ view: "map", node: id })}>Return to it on the map</a>
        </p>
      )}
      {cards.length > 0 && (
        <p className="checks__intro">
          {recordsWord(cards.length)}: {countsInWords(countOf(cards))}. <a href={routeHref({ view: "map", node: id })}>Return to it on the map</a>
        </p>
      )}
      {evidence.status === "ready" && cards.length > 0 && (
        <ol className="ledger">
          {cards.map((card) => (
            <EvidenceRow key={card.id} card={card} record={evidence.records.get(card.ref)} showKind />
          ))}
        </ol>
      )}
    </section>
  );
}

// ------------------------------------------------------------- kinds of check

function KindSection({ group, target }: { group: KindGroup; target: Extract<Target, { type: "evidence" }> | null }) {
  const paged = group.cards.length > PAGED_OVER;
  const [open, setOpen] = useState(!!target);
  const [shown, setShown] = useState(paged ? PAGE : group.cards.length);
  useEffect(() => {
    if (!target) return;
    setOpen(true);
    if (paged) setShown((s) => Math.max(s, Math.ceil((target.index + 1) / PAGE) * PAGE));
  }, [target, paged]);

  const visible = open ? group.cards.slice(0, shown) : [];
  // Only the newest page is requested; earlier pages are already cached.
  const evidence = useEvidence(open ? visible.map((c) => c.ref) : null);
  const total = group.cards.length;
  const info = CHECK_KINDS[group.kind];
  const listId = `kind-${group.kind}-records`;

  return (
    <section id={`kind-${group.kind}`} className="kind" aria-labelledby={`kind-${group.kind}-title`}>
      <h3 id={`kind-${group.kind}-title`} className="kind__title">
        {group.title}
      </h3>
      {info?.question && <p className="kind__question">{info.question}</p>}
      <p className="kind__counts">
        {total === 0 ? "No records of this kind in this edition." : `${recordsWord(total)}: ${countsInWords(group.counts)}.`}
      </p>
      {total > 0 && (
        <button type="button" className="control kind__toggle" aria-expanded={open} aria-controls={listId} onClick={() => setOpen((o) => !o)}>
          <Chevron open={open} />
          {open ? "Hide the records" : paged ? `Show the first ${PAGE} of ${total} records` : total === 1 ? "Show the record" : `Show the ${total} records`}
        </button>
      )}
      {open && (
        <div id={listId}>
          {evidence.status === "error" && <p className="checks__error">{describeError(evidence.error).title}.</p>}
          <ol className="ledger">
            {visible.map((card) => (
              <EvidenceRow
                key={card.id}
                card={card}
                record={evidence.status === "ready" ? evidence.records.get(card.ref) : undefined}
                selected={target?.id === card.id}
              />
            ))}
          </ol>
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
        </div>
      )}
    </section>
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
  const [expanded, setExpanded] = useState(false);
  const [clipped, setClipped] = useState(false);
  const detailsRef = useRef<HTMLParagraphElement>(null);
  const rowRef = useScrollTarget<HTMLLIElement>(!!selected && !!record);

  useLayoutEffect(() => {
    const el = detailsRef.current;
    if (!el || expanded) return;
    const measure = () => setClipped(el.scrollHeight > el.clientHeight + 1);
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(el);
    return () => observer.disconnect();
  }, [record, expanded]);

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
          {record ? record.tool ?? "No tool is named." : <span className="faint">Loading the record…</span>}
        </p>
        {record && (
          <>
            <p className="ev__meta">
              {date && <span className="ev__date">Date given in the record: {date.text}. </span>}
              {subjects.length === 0 ? (
                "It names no statement."
              ) : (
                <>
                  Concerns{" "}
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
              <p ref={detailsRef} className={`ev__details${expanded ? "" : compact ? " is-clamped is-short" : " is-clamped"}`}>
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
                <span className="ev__label">Sources it names. </span>
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
                Receipt file <code className="lean" translate="no">{record.receipt_path}</code>, kept in the repository and not served by this site.
                {expanded && record.receipt_sha256 && (
                  <>
                    {" "}
                    Its SHA-256 is <code className="lean ev__hash">{record.receipt_sha256}</code>.
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

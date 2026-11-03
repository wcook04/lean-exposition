// The goal's plate: the theorem as an account states it, its Lean
// counterpart, one line about its recorded checks, and where to read it.

import { useEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition, useRecord, type Edition } from "../app/data";
import { routeHref } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { partOfPassage, sectionTitleOf, useDocument } from "../reader/documents";
import { goalCheckLine } from "../checks/summary";
import { mountFigures } from "../reader/mount";
import { markWideMaths } from "../reader/page/PaperBody";
import { formatLeanSignature, tokenizeLean } from "../panels/leanTokens";

/** The result every account selects: the site's main theorem. */
export function mainGoal(edition: Edition): string {
  const sets = edition.overview.papers.map((p) => new Set(p.paper_scope.selected_goal_ids));
  const common = [...(sets[0] ?? [])].filter((g) => sets.every((s) => s.has(g)));
  return common[0] ?? edition.graph.regions[0]?.goal ?? edition.graph.goals[0];
}

/** The goals a reader can start from, most foundational first, with the accounts that select each. */
export function startingGoals(edition: Edition): { id: string; title: string; stages: Stage[] }[] {
  const long = edition.overview.papers.find((p) => p.stage === "long");
  const ids = long?.paper_scope.selected_goal_ids ?? [mainGoal(edition)];
  const titles = new Map(edition.graph.regions.map((r) => [r.goal, r.title]));
  return ids
    .filter((id) => edition.graph.nodes.has(id))
    .map((id) => ({
      id,
      title: titles.get(id) ?? edition.graph.nodes.get(id)!.label,
      stages: STAGE_ORDER.filter((s) => edition.overview.papers.find((p) => p.stage === s)?.paper_scope.selected_goal_ids.includes(id)),
    }));
}

/** "4. The full-support theorem" -> "§4 The full-support theorem". */
export function sectionLabel(title: string): string {
  const match = title.match(/^(\d+(?:\.\d+)*)\.?\s+(.*)$/);
  return match ? `§${match[1]} ${match[2]}` : title;
}

interface StatementSource {
  stage: Stage;
  anchor: string;
}

type Doc = ReturnType<typeof useDocument>;

/** A theorem-like run-in lead ("Theorem 1 (…).") opens one of the passage's paragraphs. */
const THEOREM_LEAD = /data-run-in="(theorem|proposition|corollary|lemma)"/;

/**
 * The passage where an account treats the goal: its authored statement, else its
 * first authored treatment, else a passage mapped directly to the goal, preferring
 * one that states a theorem in so many words.
 */
function goalPassage(doc: Doc, goal: string): { stage: Stage; anchor: string; section: string | null; index: number; statement: boolean } | null {
  if (doc.status !== "ready") return null;
  const { paper, doc: prepared } = doc.value;
  const passages = paper.structure.paper.passages;
  const stated = passages.find((p) => (p.treatments ?? []).some((t) => t.claim_id === goal && t.kinds.includes("statement")));
  let passage = stated ?? passages.find((p) => (p.treatments ?? []).some((t) => t.claim_id === goal));
  let statement = !!stated;
  if (!passage) {
    const mapped = passages.filter((p) => p.claim_ids.includes(goal));
    const theorem = mapped.find((p) => {
      const index = partOfPassage(prepared, p.anchor);
      return index >= 0 && THEOREM_LEAD.test(prepared.render(index).html);
    });
    passage = theorem ?? mapped[0];
    statement = !!theorem;
  }
  if (!passage) return null;
  return { stage: paper.stage, anchor: passage.anchor, section: sectionTitleOf(paper, passage.anchor), index: partOfPassage(prepared, passage.anchor), statement };
}

function useStatement(
  goal: string,
  first = false,
): { html: string; partial: boolean; source: StatementSource; section: string | null; readIn: { stage: Stage; anchor: string; section: string | null }[] } | null {
  const exposition = useDocument("expository");
  const short = useDocument("short");
  const long = useDocument("long");
  return useMemo(() => {
    const readIn = [exposition, short, long].map((d) => goalPassage(d, goal)).filter((p): p is NonNullable<typeof p> => !!p);
    for (const doc of [exposition, short, long]) {
      const at = goalPassage(doc, goal);
      if (!at || !at.statement || at.index < 0 || doc.status !== "ready") continue;
      const excerpt = excerptStatement(doc.value.doc.render(at.index).html, first);
      return {
        ...excerpt,
        source: { stage: at.stage, anchor: at.anchor },
        section: at.section,
        readIn,
      };
    }
    return readIn.length
      ? { html: "", partial: false, source: { stage: readIn[0].stage, anchor: readIn[0].anchor }, section: readIn[0].section, readIn }
      : null;
  }, [exposition, short, long, goal, first]);
}

/** "§4 The full-support theorem" -> "§4"; a title without a number stays whole. */
function sectionMark(title: string | null): string {
  if (!title) return "";
  const match = title.match(/^(\d+(?:\.\d+)*)\.?\s/);
  return match ? `§${match[1]}` : "";
}

/**
 * The plate under the goal's title: the statement as an account states it, its Lean counterpart, the checks line and where to read it.
 * The front page shows the statement and its source line alone (`lean` and `foot` off),
 * and only the theorem's first sentence (`first`): its continuation refers to objects
 * defined earlier in the paper, which the front page does not show.
 */
export function TheoremBody({ goal, lean = true, foot = true, first = false }: { goal: string; lean?: boolean; foot?: boolean; first?: boolean }) {
  const edition = useEdition();
  const node = edition.graph.nodes.get(goal);
  const formal = edition.graph.edges.find((e) => e.from === goal && e.kind === "formalizes")?.to;
  const formalNode = formal && lean ? edition.graph.nodes.get(formal) : undefined;
  const formalRecord = useRecord(formalNode?.ref ?? null);
  const goalRecord = useRecord(node?.ref ?? null);
  const statement = useStatement(goal, first);
  const statementRef = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const el = statementRef.current;
    if (!el) return;
    const unmount = mountFigures(el);
    // A display wider than the plate shrinks to fit, then breaks at a relation; it never scrolls here.
    const unmark = markWideMaths(el);
    return () => {
      unmark();
      unmount?.();
    };
  }, [statement]);
  // A long statement is clamped with a soft fade; the source link below stays in view.
  const clampRef = useRef<HTMLDivElement>(null);
  const [clamped, setClamped] = useState(false);
  useEffect(() => {
    const el = clampRef.current;
    if (!el) return;
    const check = () => setClamped(el.scrollHeight > el.clientHeight + 2);
    check();
    const observer = new ResizeObserver(check);
    observer.observe(el);
    if (el.firstElementChild) observer.observe(el.firstElementChild);
    return () => observer.disconnect();
  }, [statement]);

  const checkNode = formalNode?.id ?? goal;
  const checks = goalCheckLine(edition, checkNode, formalRecord.status === "ready" && formalNode ? (formalRecord.value.record.evidence_ids ?? undefined) : undefined);
  const leanStatement = formalRecord.status === "ready" ? (formalRecord.value.record.statement as string | undefined) : undefined;
  const correspondence = formalNode ? edition.graph.edges.find((e) => e.from === goal && e.to === formalNode.id && e.kind === "formalizes") : undefined;

  return (
    <div className={`plate${formalNode ? " plate--two" : ""}`}>
      <div className="plate__body">
                <div className="plate__main">
          
          {statement?.html ? (
            <div ref={clampRef} className={`plate__clamp${clamped ? " is-clamped" : ""}`}>
              <div ref={statementRef} className="prose plate__statement" dangerouslySetInnerHTML={{ __html: statement.html }} />
            </div>
          ) : goalRecord.status === "ready" && goalRecord.value.record.statement ? (
            <p className="plate__recorded">{String(goalRecord.value.record.statement)}</p>
          ) : null}
          {statement?.html && (
            <p className="plate__source">
              <a href={routeHref({ view: "read", stage: statement.source.stage, anchor: statement.source.anchor })}>
                {statement.partial ? "Start of the statement, from the" : "Statement from the"}{" "}
                {PAPER_NAMES[statement.source.stage].short.toLowerCase()}
                {statement.section ? `, ${sectionLabel(statement.section)}` : ""}
              </a>
            </p>
          )}
        </div>
        {formalNode && (
          <div className="plate__lean">
            <p className="caps plate__label">In Lean</p>
            <LeanSignature source={leanStatement ?? formalNode.label} />
            <p className="plate__leanstatus">
              Recorded as the Lean statement of this result.{correspondence?.warrant?.status ? ` ${reviewSentence(correspondence.warrant.status)}` : ""}
            </p>
          </div>
        )}
      </div>
      {foot && (
      <div className="plate__foot">
        <span className="plate__checks">{checks.line}</span>
        {checks.total > 0 && (
          <a href={routeHref({ view: "checks", node: checkNode })}>
            {checks.total === 1 ? "Show the run record" : `Show the ${checks.total} run records`}
          </a>
        )}
        <span className="plate__sep" />
        {statement && statement.readIn.length > 0 && (
          <span className="plate__readin">
            <span className="plate__readlabel">Read the result in</span>
            {statement.readIn.map((r) => (
              <a key={r.stage} href={routeHref({ view: "read", stage: r.stage, anchor: r.anchor })}>
                {PAPER_NAMES[r.stage].short} {sectionMark(r.section)}
              </a>
            ))}
          </span>
        )}
      </div>
      )}
    </div>
  );
}

/**
 * The map's compact plate under the goal's title: one sentence of the theorem and the
 * ways on. The full theorem and its Lean live in the sheet, which the button opens (a
 * click on the plate selects the goal).
 */
export function GoalPlate({ goal }: { goal: string }) {
  const statement = useStatement(goal, true);
  const html = useMemo(() => (statement?.html ? plainExcerpt(statement.html) : ""), [statement]);
  const ref = useRef<HTMLDivElement>(null);
  return (
    <div className="goal-plate">
      {html ? <div ref={ref} className="prose goal-plate__sentence" dangerouslySetInnerHTML={{ __html: html }} /> : null}
      <div className="goal-plate__actions">
        <button type="button" className="goal-plate__primary">
          Full statement and Lean
        </button>
        {statement && statement.readIn.length > 0 && <span>Read it in</span>}
        {statement?.readIn.map((r) => (
          <a key={r.stage} href={routeHref({ view: "read", stage: r.stage, anchor: r.anchor })}>
            {PAPER_NAMES[r.stage].short} {sectionMark(r.section)}
          </a>
        ))}
      </div>
    </div>
  );
}

/**
 * The theorem's first sentence alone, for the plate's compact form on the map. That
 * form takes no pointer or focus, so links become plain text; ids are dropped so they
 * never repeat the full plate's.
 */
export function StatementExcerpt({ goal }: { goal: string }) {
  const statement = useStatement(goal, true);
  const html = useMemo(() => (statement?.html ? plainExcerpt(statement.html) : ""), [statement]);
  if (!html) return null;
  return <div className="prose plate__statement" dangerouslySetInnerHTML={{ __html: html }} />;
}

function plainExcerpt(html: string): string {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, "text/html");
  const root = doc.body.firstElementChild as HTMLElement;
  root.querySelectorAll("a").forEach((a) => a.replaceWith(...Array.from(a.childNodes)));
  root.querySelectorAll("[id]").forEach((el) => el.removeAttribute("id"));
  return root.innerHTML;
}

/** The theorem itself: a run-in statement and its displays, else the opening paragraph and its displays. */
/**
 * The statement's paragraphs: the theorem's lead paragraph, its displays, and up to
 * two following "For …" paragraphs that continue it. With `first`, only the lead
 * paragraph and its displays; `partial` says a continuation was left out.
 */
function excerptStatement(html: string, first = false): { html: string; partial: boolean } {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, "text/html");
  const root = doc.body.firstElementChild as HTMLElement;
  const lead =
    root.querySelector('p.run-in[data-run-in="theorem"], p.run-in[data-run-in="proposition"], p.run-in[data-run-in="corollary"]') ??
    root.querySelector("p.run-in") ??
    root.querySelector("p");
  if (!lead) return { html, partial: false };
  // A theorem written as one paragraph ("…, then $$…$$ For the solution … $$…$$")
  // ends its first sentence at its first display: cut there.
  if (first) {
    const display = [...lead.children].find((c) => c.classList.contains("math-display"));
    let dropped = false;
    for (let n = display?.nextSibling ?? null; n; ) {
      const after: ChildNode | null = n.nextSibling;
      if ((n.textContent ?? "").trim()) dropped = true;
      n.remove();
      n = after;
    }
    if (dropped) return { html: lead.outerHTML, partial: true };
  }
  const kept: Element[] = [lead];
  let next = lead.nextElementSibling;
  const isDisplay = (el: Element | null) => !!el && el.classList.contains("math-display");
  const continues = (el: Element) => el.tagName === "P" && kept.length < 3 && /^For\b/.test(el.textContent ?? "");
  while (next && (isDisplay(next) || (!first && continues(next)))) {
    kept.push(next);
    next = next.nextElementSibling;
  }
  return { html: kept.map((el) => el.outerHTML).join(""), partial: !!next && first && continues(next) };
}

export function useMainGoal(): string {
  return mainGoal(useEdition());
}

/** The Lean statement laid out as Lean code is written, one binder per line, with light colouring. */
function LeanSignature({ source }: { source: string }) {
  const tokens = useMemo(() => tokenizeLean(formatLeanSignature(source)), [source]);
  return (
    <code className="lean plate__code">
      {tokens.map((t, i) =>
        t.kind === "space" || t.kind === "punct" ? (
          t.text
        ) : (
          <span key={i} className={`lk lk--${t.kind}`}>
            {t.text}
          </span>
        ),
      )}
    </code>
  );
}

/** One sentence on the review of a recorded Lean correspondence; a passed record is never called independent. */
function reviewSentence(status: string): string {
  if (status === "passed") return "A review of that match is recorded as passed.";
  if (status === "failed") return "A review of that match is recorded as failed.";
  if (status === "unavailable") return "A review of that match was attempted but gave no outcome.";
  if (status === "not_run") return "No review of that match has been run.";
  return `Review of that match: ${status.replace(/_/g, " ")}.`;
}

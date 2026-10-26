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

function useStatement(goal: string): { html: string; source: StatementSource; section: string | null; readIn: { stage: Stage; anchor: string; section: string | null }[] } | null {
  const exposition = useDocument("expository");
  const short = useDocument("short");
  const long = useDocument("long");
  return useMemo(() => {
    const readIn = [exposition, short, long].map((d) => goalPassage(d, goal)).filter((p): p is NonNullable<typeof p> => !!p);
    for (const doc of [exposition, short, long]) {
      const at = goalPassage(doc, goal);
      if (!at || !at.statement || at.index < 0 || doc.status !== "ready") continue;
      return {
        html: excerptStatement(doc.value.doc.render(at.index).html),
        source: { stage: at.stage, anchor: at.anchor },
        section: at.section,
        readIn,
      };
    }
    return readIn.length ? { html: "", source: { stage: readIn[0].stage, anchor: readIn[0].anchor }, section: readIn[0].section, readIn } : null;
  }, [exposition, short, long, goal]);
}

/** "§4 The full-support theorem" -> "§4"; a title without a number stays whole. */
function sectionMark(title: string | null): string {
  if (!title) return "";
  const match = title.match(/^(\d+(?:\.\d+)*)\.?\s/);
  return match ? `§${match[1]}` : "";
}

/** The plate under the goal's title: the statement as an account states it, its Lean counterpart, the checks line and where to read it. */
export function TheoremBody({ goal }: { goal: string }) {
  const edition = useEdition();
  const node = edition.graph.nodes.get(goal);
  const formal = edition.graph.edges.find((e) => e.from === goal && e.kind === "formalizes")?.to;
  const formalNode = formal ? edition.graph.nodes.get(formal) : undefined;
  const formalRecord = useRecord(formalNode?.ref ?? null);
  const goalRecord = useRecord(node?.ref ?? null);
  const statement = useStatement(goal);
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
                Statement from the {PAPER_NAMES[statement.source.stage].short.toLowerCase()}
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
              Recorded Lean correspondence{correspondence?.warrant?.status ? ` · review ${correspondence.warrant.status.replace(/_/g, " ")}` : ""}
            </p>
          </div>
        )}
      </div>
      <div className="plate__foot">
        <span className="plate__checks">{checks.line}</span>
        {checks.total > 0 && (
          <a href={routeHref({ view: "checks", node: checkNode })}>
            {checks.total === 1 ? "Show the check record" : `Show the ${checks.total} check records`}
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
    </div>
  );
}

/** The theorem itself: a run-in statement and its displays, else the opening paragraph and its displays. */
function excerptStatement(html: string): string {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, "text/html");
  const root = doc.body.firstElementChild as HTMLElement;
  const lead =
    root.querySelector('p.run-in[data-run-in="theorem"], p.run-in[data-run-in="proposition"], p.run-in[data-run-in="corollary"]') ??
    root.querySelector("p.run-in") ??
    root.querySelector("p");
  if (!lead) return html;
  const kept: Element[] = [lead];
  let next = lead.nextElementSibling;
  const isDisplay = (el: Element | null) => !!el && el.classList.contains("math-display");
  while (next && (isDisplay(next) || (next.tagName === "P" && kept.length < 3 && /^For\b/.test(next.textContent ?? "")))) {
    kept.push(next);
    next = next.nextElementSibling;
  }
  return kept.map((el) => el.outerHTML).join("");
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

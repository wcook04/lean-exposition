// The goal's own card: the theorem as a paper states it, its Lean
// counterpart and what has been checked, and where to read it.

import { useEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition, useRecord, type Edition } from "../app/data";
import { routeHref } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { partOfPassage, sectionTitleOf, useDocument } from "../reader/documents";
import { checkSummary } from "../checks/summary";
import { mountFigures } from "../reader/mount";

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

function useStatement(goal: string): { html: string; source: StatementSource; section: string | null } | null {
  const exposition = useDocument("expository");
  const short = useDocument("short");
  return useMemo(() => {
    for (const doc of [exposition, short]) {
      if (doc.status !== "ready") continue;
      const { paper, doc: prepared } = doc.value;
      const passage = paper.structure.paper.passages.find((p) =>
        (p.treatments ?? []).some((t) => t.claim_id === goal && t.kinds.includes("statement")),
      );
      if (!passage) continue;
      const index = partOfPassage(prepared, passage.anchor);
      if (index < 0) continue;
      return {
        html: excerptStatement(prepared.render(index).html),
        source: { stage: paper.stage, anchor: passage.anchor },
        section: sectionTitleOf(paper, passage.anchor),
      };
    }
    return null;
  }, [exposition, short, goal]);
}

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
    if (statementRef.current) return mountFigures(statementRef.current);
  }, [statement]);
  // A long statement is clamped with a soft fade; its source link below stays in view.
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

  const checks = formalRecord.status === "ready" ? checkSummary(edition, formalRecord.value.record.evidence_ids ?? []) : null;
  const leanStatement = formalRecord.status === "ready" ? (formalRecord.value.record.statement as string | undefined) : undefined;

  return (
    <div className={`theorem${formalNode ? " theorem--two" : ""}`}>
      <div className="theorem__main">
      {statement ? (
        <>
          <div ref={clampRef} className={`theorem__clamp${clamped ? " is-clamped" : ""}`}>
            <div ref={statementRef} className="prose prose--theorem" dangerouslySetInnerHTML={{ __html: statement.html }} />
          </div>
          <p className="theorem__source">
            <a href={routeHref({ view: "read", stage: statement.source.stage, anchor: statement.source.anchor })}>
              As the {PAPER_NAMES[statement.source.stage].short.toLowerCase()} states it
              {statement.section ? `, ${sectionLabel(statement.section)}` : ""}
            </a>
          </p>
        </>
      ) : goalRecord.status === "ready" && goalRecord.value.record.statement ? (
        <p className="theorem__recorded">{String(goalRecord.value.record.statement)}</p>
      ) : null}
      </div>

      {formalNode && (
        <div className="theorem__formal">
          <p className="theorem__lean-line">
            <span className="theorem__label">In Lean</span>
            <code className="lean theorem__lean">{leanStatement ?? formalNode.label}</code>
          </p>
          {checks && (
            <p className="theorem__checks">
              {checksSentence(checks)}{" "}
              <a href={routeHref({ view: "checks", node: formalNode.id })}>What each check examined</a>
            </p>
          )}
        </div>
      )}
    </div>
  );
}

/** One sentence for the checks: what passed, and which kinds have no completed run. */
const CHECK_PHRASES: Record<string, string> = {
  lean_build: "Lean build",
  comparator: "Comparator run",
  extraction: "dependency extraction",
  semantic_review: "correspondence review",
  platform: "platform check",
};

export function checksSentence(rows: { kind: string; title: string; counts: Record<string, number> }[]): string {
  const passed = rows
    .filter((r) => (r.counts.passed ?? 0) > 0)
    .map((r) => (r.kind === "source_hash" ? "the cited files match their recorded hashes" : `the ${CHECK_PHRASES[r.kind] ?? r.title} passed`));
  const open = rows.filter((r) => !(r.counts.passed ?? 0)).map((r) => CHECK_PHRASES[r.kind] ?? r.title);
  const join = (xs: string[], word: string) => (xs.length <= 1 ? xs.join("") : `${xs.slice(0, -1).join(", ")} ${word} ${xs[xs.length - 1]}`);
  const parts: string[] = [];
  if (passed.length) parts.push(join(passed, "and"));
  if (open.length) parts.push(`no completed ${join(open, "or")} is recorded`);
  const sentence = parts.join("; ");
  return sentence ? sentence.charAt(0).toUpperCase() + sentence.slice(1) + "." : "";
}

/** The theorem itself: a run-in statement and its displays, else the opening paragraph and its displays. */
function excerptStatement(html: string): string {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, "text/html");
  const root = doc.body.firstElementChild as HTMLElement;
  const lead = root.querySelector("p.run-in") ?? root.querySelector("p");
  if (!lead) return html;
  const kept: Element[] = [lead];
  let next = lead.nextElementSibling;
  const isDisplay = (el: Element | null) => !!el && el.classList.contains("math-display");
  while (next && (isDisplay(next) || (next.tagName === "P" && kept.length < 3 && /^For every/.test(next.textContent ?? "")))) {
    kept.push(next);
    next = next.nextElementSibling;
  }
  return kept.map((el) => el.outerHTML).join("");
}

export function useMainGoal(): string {
  return mainGoal(useEdition());
}

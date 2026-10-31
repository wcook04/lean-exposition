// Every record with what its checks say: one line each, in groups by outcome, so the few
// that differ lead and the long run of records with nothing passed follows in columns.
// A line names its record by short title and states its checks in words; opening it
// compares the record across its levels. Only a recorded failure is coloured (DESIGN.md).

import { useMemo } from "react";
import { useEdition } from "../app/data";
import { routeHref } from "../app/router";
import { shortTitle } from "../compare/useAlignment";
import { countsInWords, type EvidenceCard } from "./summary";

/** What the checks recorded about one record add up to. */
export type Standing = "failed" | "partly" | "passed" | "unrun" | "none";

export const STANDING_ORDER: Standing[] = ["failed", "partly", "passed", "unrun", "none"];

const STANDING_HEADS: Record<Standing, string> = {
  failed: "A run on the step failed",
  partly: "Some runs passed",
  passed: "Every run passed",
  unrun: "Runs planned, none passed",
  none: "No run recorded",
};

/** Checks that test a statement or its proof. Source-file checks compare a file's bytes, so they do not place a record. */
const STATEMENT_KINDS = new Set(["lean_build", "comparator", "extraction", "semantic_review"]);

export function standingOf(statuses: readonly string[]): Standing {
  if (!statuses.length) return "none";
  if (statuses.includes("failed")) return "failed";
  const passed = statuses.filter((s) => s === "passed").length;
  if (passed === statuses.length) return "passed";
  return passed ? "partly" : "unrun";
}

/** A Lean name standing in for a title, such as `scalar_value_target`. */
const RAW_NAME = /^[a-z][a-z0-9]*(_[a-z0-9]+)+$/;

/** The record's plain name: its short title, or for a bare Lean name the record it is linked to. */
export function plainTitle(title: string, linked: string | undefined): { title: string; lean: boolean } {
  if (!RAW_NAME.test(title)) return { title, lean: false };
  return linked ? { title: `Lean linked to ${linked}`, lean: false } : { title, lean: true };
}

/** The outcomes of a record's statement checks, in words: "1 failed, 2 unavailable and 9 not run". */
export function tileWords(statuses: readonly string[]): string {
  const counts: Record<string, number> = {};
  for (const s of statuses) counts[s] = (counts[s] ?? 0) + 1;
  return statuses.length ? countsInWords(counts) : "No run recorded";
}

export function RecordList() {
  const edition = useEdition();
  const { graph, map } = edition;
  const cards = map.records.evidence as EvidenceCard[];

  const groups = useMemo(() => {
    const status = new Map(cards.map((c) => [c.id, c]));
    const by = new Map<string, Set<string>>();
    const add = (record: string, check: string) => {
      if (!by.has(record)) by.set(record, new Set());
      by.get(record)!.add(check);
    };
    for (const e of edition.evidence ?? []) for (const s of e.subject_ids) add(s, e.id);
    for (const [id, node] of graph.nodes) for (const e of node.evidenceIds ?? []) add(id, e);
    const tiles = graph.order.map((id) => {
      const statuses = [...(by.get(id) ?? [])]
        .map((e) => status.get(e))
        .filter((c): c is EvidenceCard => !!c && STATEMENT_KINDS.has(c.kind))
        .map((c) => c.status);
      const node = graph.nodes.get(id)!;
      const short = shortTitle(id, node.label);
      const claim = node.kind === "declaration" ? (graph.in.get(id) ?? []).find((e) => e.kind === "formalizes")?.from : undefined;
      const claimNode = claim ? graph.nodes.get(claim) : undefined;
      const plain = plainTitle(short, claim && claimNode ? shortTitle(claim, claimNode.label) : undefined);
      return { id, ...plain, full: node.label, words: tileWords(statuses), standing: standingOf(statuses) };
    });
    return STANDING_ORDER.map((standing) => ({ standing, tiles: tiles.filter((t) => t.standing === standing) })).filter((g) => g.tiles.length > 0);
  }, [edition.evidence, graph, cards]);

  return (
    <section className="checks__band rlist" aria-labelledby="rlist-title">
      <h2 id="rlist-title">Each step and what ran on it</h2>
      <p className="checks__intro">
        All {graph.order.length} steps, by what ran on their statement or proof. File hash comparisons are left out, because they compare bytes only. Open a step to compare it across the Lean and the papers.
      </p>
      {groups.map((group) => (
        <div key={group.standing} className={`rlist__group${group.tiles.length < 10 && group.standing !== "none" ? " is-few" : ""}${group.standing === "failed" ? " is-failed" : ""}`}>
          <h3>
            {STANDING_HEADS[group.standing]}, <span className="num">{group.tiles.length}</span>{" "}
            {group.tiles.length === 1 ? "step" : "steps"}
          </h3>
          <ul>
            {group.tiles.map((t) => (
              <li key={t.id}>
                <a className="rline" href={routeHref({ view: "compare", node: t.id })} title={t.full === t.title ? undefined : t.full}>
                  <span className={`rline__title${t.lean ? " lean" : ""}`}>{t.title}</span>
                  {group.standing !== "none" && (
                    <span className="rline__words">
                      {t.words.split(/(\d+ failed)/).map((part, i) => (i % 2 ? <span key={i} className="is-failed">{part}</span> : part))}
                    </span>
                  )}
                </a>
              </li>
            ))}
          </ul>
        </div>
      ))}
    </section>
  );
}

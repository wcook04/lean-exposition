// Every record with what its checks say, as labelled tiles grouped by outcome. A tile
// names its record by short title and states its checks in words; opening it compares the
// record across its levels. Only a recorded failure is coloured (DESIGN.md).

import { useMemo } from "react";
import { useEdition } from "../app/data";
import { routeHref } from "../app/router";
import { shortTitle } from "../compare/useAlignment";
import { countsInWords, type EvidenceCard } from "./summary";

/** What the checks recorded about one record add up to. */
export type Standing = "failed" | "partly" | "passed" | "unrun" | "none";

export const STANDING_ORDER: Standing[] = ["failed", "partly", "passed", "unrun", "none"];

const STANDING_HEADS: Record<Standing, string> = {
  failed: "A check on the record failed",
  partly: "Some checks passed",
  passed: "Every check passed",
  unrun: "Checks written, none passed",
  none: "No check recorded",
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

/** The outcomes of a record's statement checks, in words: "1 failed, 2 unavailable and 9 not run". */
export function tileWords(statuses: readonly string[]): string {
  const counts: Record<string, number> = {};
  for (const s of statuses) counts[s] = (counts[s] ?? 0) + 1;
  return statuses.length ? countsInWords(counts) : "No check recorded";
}

export function RecordTiles() {
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
      return { id, title: shortTitle(id, node.label), lean: node.kind === "declaration" && shortTitle(id, node.label) === node.label, words: tileWords(statuses), standing: standingOf(statuses) };
    });
    return STANDING_ORDER.map((standing) => ({ standing, tiles: tiles.filter((t) => t.standing === standing) })).filter((g) => g.tiles.length > 0);
  }, [edition.evidence, graph, cards]);

  return (
    <section className="checks__band rtiles" aria-labelledby="rtiles-title">
      <h2 id="rtiles-title">Each record and its checks</h2>
      <p className="checks__intro">
        All {graph.order.length} records, grouped by the checks on their statement or proof. Each tile names the record and
        gives those outcomes in words; source-file checks compare file bytes and are left out. Open a tile to compare that
        record across the Lean and the papers.
      </p>
      {groups.map((group) => (
        <div key={group.standing} className="rtiles__group">
          <h3>
            {STANDING_HEADS[group.standing]}, <span className="num">{group.tiles.length}</span>{" "}
            {group.tiles.length === 1 ? "record" : "records"}
          </h3>
          <ul>
            {group.tiles.map((t) => (
              <li key={t.id}>
                <a className="rtile" href={routeHref({ view: "compare", node: t.id })}>
                  <span className={`rtile__title${t.lean ? " lean" : ""}`}>{t.title}</span>
                  <span className="rtile__words">
                    {t.words.split(/(\d+ failed)/).map((part, i) => (i % 2 ? <span key={i} className="is-failed">{part}</span> : part))}
                  </span>
                </a>
              </li>
            ))}
          </ul>
        </div>
      ))}
    </section>
  );
}

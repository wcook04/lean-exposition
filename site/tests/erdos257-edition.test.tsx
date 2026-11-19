// @vitest-environment jsdom
// The #257 site over its real data: a capture of the #257 static edition
// (tests/fixtures/erdos257-edition, written by scripts/capture-erdos257-fixture.py), the
// example's own evidence records and receipts, and the papers' reference tables. The SK suite
// has the same checks over the SK edition (first-screen, site-facts, compare-table,
// checks-ledger, references). These read no file under public/edition, so they run for
// either instance.

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { describe, expect, it } from "vitest";
import type { RecordAlignment } from "../src/api/lean";
import { buildRunLedger, type EvidenceInput } from "../src/checks/runLedger";
import { RunTable } from "../src/checks/RunTable";
import { tableRows } from "../src/compare/table";
import { siteFacts } from "../src/home/siteFacts";
import { countKinds, kindsInWords } from "../src/home/recordKinds";
import erdos from "../src/instances/erdos257/site";
import { ELSEWHERE, OVERVIEW_URL } from "../src/instances/erdos257/elsewhereLinks";

const REPO = resolve(__dirname, "../..");
const EDITION = resolve(__dirname, "fixtures/erdos257-edition/edition");
const json = (path: string) => JSON.parse(readFileSync(path, "utf8"));
const index = json(resolve(EDITION, "index.json"));
const route = (name: string) => {
  const body = json(resolve(EDITION, index.responses[name]));
  return body.data ?? body;
};
const facts = siteFacts(REPO, EDITION, erdos);

describe("the #257 edition's facts", () => {
  it("is the #257 edition", () => {
    expect(route("/overview").graph.id).toBe("erdos257-lambert-subseries");
  });

  it("counts every record once, in the papers' terms, and the counts add up", () => {
    const nodes = json(resolve(EDITION, index.summaries_by_table.nodes)) as { id: string; kind: string; status: string }[];
    expect(facts.steps).toBe(nodes.length);
    expect(facts.kinds).toEqual(countKinds(nodes, erdos.recordKind!));
    const k = facts.kinds!;
    expect(k.result + k.step + k.cited + k.open + k.declaration).toBe(facts.steps);
    expect(k.declaration).toBe(nodes.filter((n) => n.kind === "declaration").length);
    // The short paper prints 11 results and the long record 175; two records are shared, and the exposition's Theorem 1 is one more.
    expect(k.result).toBe(11 + 175 - 2 + 1);
    expect(kindsInWords(k)).toMatch(/^\d+ results printed in the papers, \d+ proof steps .* and \d+ Lean declarations$/);
  });

  it("counts the ties from the tie indexes, and says who made every one", () => {
    const ties = (["short", "long", "expository"] as const).map((stage) => route(`/ties/${stage}`) as { ties: { origin?: string }[] });
    expect(facts.ties!.total).toBe(ties.reduce((n, t) => n + t.ties.length, 0));
    expect(facts.origins!.evidenceRecord + facts.origins!.ai).toBe(facts.ties!.total);
    expect(facts.origins!.unmarked).toBe(0);
  });

  it("finds Theorem A.1 in the short paper as the main theorem", () => {
    expect(facts.mainRecord).toBe("short.res-reciprocal-support");
    const statement = (route("/alignment").records as Record<string, RecordAlignment>)["short.res-reciprocal-support"].statements.find((s) => s.paper === "short")!;
    expect(statement.markdown).toMatch(/^\*\*Theorem A\.1\b/);
    expect(facts.theorem1).toEqual({ at: `b${statement.start_byte}-${statement.end_byte}`, anchor: statement.anchor });
  });
});

describe("the #257 first screen", () => {
  const html = erdos.hero("/erdos-257-reader/", facts, (tex) => `<i>${tex}</i>`);

  it("opens Theorem A.1 with its Lean from the clause table", () => {
    expect(html).toContain("Theorem A.1, clause by clause");
    expect(html).toContain(`href="/erdos-257-reader/read/short?l=${facts.theorem1!.at}&n=short.res-reciprocal-support#${facts.theorem1!.anchor}"`);
  });

  it("states the ties once, every number from the edition", () => {
    const { ties, origins } = facts;
    expect(html).toContain(`The three papers have ${ties!.statements} marked statements, ${ties!.withLean} of them with Lean, joined to the records by ${ties!.total} ties: ${origins!.evidenceRecord} copied from the papers’ published evidence mapping and ${origins!.ai} made by an AI agent for this site.`);
    expect(html).not.toContain("Each tie says who made it");
    expect(html).not.toContain("TODO(copy)");
  });

  it("shows the three films with stills, running times and YouTube links", () => {
    const films = [...html.matchAll(/<figure class="film-slot[^"]*">[\s\S]*?<\/figure>/g)].map((m) => m[0]);
    expect(films).toHaveLength(3);
    for (const film of films) {
      expect(film).toMatch(/href="https:\/\/www\.youtube\.com\/watch\?v=[\w-]{11}"/);
      expect(film).toMatch(/src="\/erdos-257-reader\/films\/[\w-]+-640\.webp"/);
      expect(film).toMatch(/class="film-slot__time">\d+:\d\d</);
    }
  });
});

describe("the #257 Compare table", () => {
  const records = route("/alignment").records as Record<string, RecordAlignment>;
  const nodes = json(resolve(EDITION, index.summaries_by_table.nodes)) as { id: string; kind: string }[];
  const declaration = new Set(nodes.filter((n) => n.kind === "declaration").map((n) => n.id));
  const steps = Object.fromEntries(Object.entries(records).filter(([id]) => !declaration.has(id)));

  it("has no step in all of the Lean, the short paper and the exposition, so the page lists every step any column has", () => {
    expect(tableRows(steps, ["lean", "short", "expository"], false, "short.res-reciprocal-support")).toEqual([]);
    const any = tableRows(steps, ["lean", "short", "expository"], true, "short.res-reciprocal-support");
    expect(any.length).toBeGreaterThan(100);
    expect(any[0].id).toBe("short.res-reciprocal-support");
  });

  it("says what each compared Lean statement says against the paper, and who compared it", () => {
    const row = (id: string, name: string) => records[id].lean.find((l) => l.name.endsWith(name))!;
    expect(row("exp.thm-main", "irrational_erdosSupportSeries_of_summable_reciprocal")).toMatchObject({ fidelity: "stronger", fidelity_source: "ai" });
    expect(row("short.res-weighted-support", "divisibilityWeightedClaim")).toMatchObject({ fidelity: "same", fidelity_source: "ai" });
    // mixedSupportClaim is the (V) case only; the positive-weight variant is a second declaration.
    expect(row("short.res-mixed-supports", "mixedSupportClaim")).toMatchObject({ fidelity: "weaker", fidelity_source: "ai" });
    expect(row("short.res-mixed-supports", "arbitraryWeightMixedSupport_allBase_hereditary").fidelity).toBe("same");
  });
});

describe("the #257 table of runs", () => {
  const example = resolve(REPO, "examples/erdos257");
  const evidence = json(resolve(example, "evidence-graph.json")).evidence as EvidenceInput[];
  const read = (path: string) => {
    try {
      return json(resolve(example, path));
    } catch {
      return null;
    }
  };
  const ledger = buildRunLedger(evidence, read);
  const actions = ledger.groups.find((g) => g.type === "github_actions_run")!;

  it("finds every receipt the evidence records name", () => {
    expect(ledger.missing).toEqual([]);
  });

  it("keeps the failed first attempt of replay 35935225572 and the passed second attempt", () => {
    const replay = actions.rows.filter((r) => r.where?.label.includes("run 35935225572"));
    expect(replay.map((r) => [r.where!.label, r.status])).toEqual([
      ["wcook04/plectis-erdos-lean, run 35935225572", "failed"],
      ["wcook04/plectis-erdos-lean, run 35935225572, attempt 2", "passed"],
    ]);
  });

  it("shows no run with a better outcome than its receipt records", () => {
    for (const row of actions.rows) {
      const receipt = read(row.receipt!.replace(/^verification\//, "verification/"));
      const status = receipt.conclusion === "success" ? "passed" : receipt.conclusion === "failure" ? "failed" : "unavailable";
      expect(row.status, row.id).toBe(status);
    }
    const comparator = ledger.groups.find((g) => g.type === "comparator_receipt")!;
    for (const row of comparator.rows) expect(["passed", "failed", "unavailable"]).toContain(row.status);
  });

  it("keeps a failed run in view outside the summary row, with every attempt of the same run", async () => {
    const host = document.createElement("div");
    document.body.append(host);
    const root: Root = createRoot(host);
    await act(async () => root.render(<RunTable ledger={ledger} />));
    const outside = [...host.querySelectorAll("tbody > tr.runs__row:not(.runs__row--summary)")].filter((tr) => !tr.closest("details"));
    expect(outside.some((tr) => tr.classList.contains("runs__row--failed") && tr.textContent!.includes("35935225572"))).toBe(true);
    expect(outside.some((tr) => tr.classList.contains("runs__row--passed") && tr.textContent!.includes("attempt 2"))).toBe(true);
    await act(async () => root.unmount());
    host.remove();
  });
});

describe("the #257 Elsewhere links", () => {
  it("names each address the old problem page offered, the overview in one constant", () => {
    const hrefs = ELSEWHERE.flatMap((row) => row.links.map((link) => link.href));
    expect(hrefs).toContain("https://www.erdosproblems.com/257");
    expect(hrefs).toContain("https://github.com/wcook04/plectis-erdos/tree/main/lean/ErdosProblems/Erdos257");
    expect(hrefs).toContain("https://wcook04.github.io/practical-formal-verification/maths/universe.html#o=problem%3Aerdos_257");
    expect(hrefs.filter((href) => href.endsWith(".pdf"))).toHaveLength(3);
    expect(hrefs.filter((href) => href.endsWith(".tex"))).toHaveLength(3);
    expect(hrefs).toContain(OVERVIEW_URL);
  });
});

// The reference tables: every "Theorem 1.2", "§3", "Appendix" and the like in the paper's prose
// is either a row of its paper's table or inside the paper's own link (the SK suite's check).
const PATHS = { long: "long/reasoning-record.md", short: "short/paper.md", expository: "expository/main.md" } as const;
const NUMBER = String.raw`(?:[A-Z]\.)?\d+(?:\.\d+)*`;
const CANDIDATE = new RegExp(
  String.raw`\b(?:Theorems?|Lemmas?|Propositions?|Corollar(?:y|ies)|Assumptions?|Figures?)[\s~]+${NUMBER}|§§?\s?\d+(?:\.\d+)*|\bSections?[\s~]+\d+(?:\.\d+)*|\b[Aa]ppendix\b`,
  "g",
);
function blank(text: string): string {
  const spaces = (m: string) => m.replace(/[^\n]/g, " ");
  return text
    .replace(/<!--[\s\S]*?-->/g, spaces)
    .replace(/^\[[^\]\n]+\]:.*$/gm, spaces)
    .replace(/^(`{3,})[^\n]*\n[\s\S]*?^\1[ \t]*$/gm, spaces)
    .replace(/\\begin\{figure\*?\}[\s\S]*?\\end\{figure\*?\}/g, spaces)
    .replace(/\$\$[\s\S]*?\$\$/g, spaces)
    .replace(/(?<!\\)\$(?!\s)(?:[^$\\]|\\.)*?(?<![\s\\])\$(?!\d)/g, spaces);
}

describe.each(Object.keys(PATHS) as (keyof typeof PATHS)[])("the #257 reference table of the %s paper", (stage) => {
  const table = json(resolve(REPO, `examples/erdos257/alignment/references-${stage}.json`)) as { references: { start_byte: number; end_byte: number }[] };
  const text = readFileSync(resolve(REPO, "papers/erdos257", PATHS[stage]), "utf8");

  it("leaves no candidate undecided", () => {
    const prose = blank(text);
    const covered = new Set<number>();
    const encoder = new TextEncoder();
    const toChar = new Map<number, number>();
    let byte = 0;
    let char = 0;
    for (const c of text) {
      toChar.set(byte, char);
      byte += encoder.encode(c).length;
      char += c.length;
    }
    toChar.set(byte, char);
    for (const row of table.references) {
      const end = toChar.get(row.end_byte)!;
      for (let i = toChar.get(row.start_byte)!; i < end; i++) covered.add(i);
    }
    // Decided without a row: inside or just before one of the paper's own links ("Theorem [3.1](#…)",
    // "Appendix [A](#…)") or a citation (\[…\]); a result's own bold head; the reference list;
    // the common noun "appendix"; and a place in another work, which names a page or "of" a
    // linked work or the other paper, or is "his", "their", "the authors'" or another author's.
    const spans = [...text.matchAll(/\[[^\]\n]*\]\([^)\s]+\)|\\\[[\s\S]*?\\\]/g)].map((m) => [m.index!, m.index! + m[0].length] as const);
    const inside = (i: number) => spans.some(([a, b]) => a <= i && i < b);
    const references = text.indexOf('<a id="references"></a>');
    const otherWork = (end: number, start: number) =>
      /^[^\n]{0,40}?\bpp?\.\s?\d|^[^.\n]{0,60}?\bof (?:the |their |his )?(?:\[|short paper|long record)/.test(text.slice(end)) ||
      /^[^.\n]{0,20}\bthe authors\b/.test(text.slice(end)) ||
      /(?:\b(?:his|their|the authors[’']?)|[’']s)\s*$/.test(text.slice(Math.max(0, start - 20), start));
    const undecided = [...prose.matchAll(CANDIDATE)].filter((m) => {
      const i = m.index!;
      const end = i + m[0].length;
      if (covered.has(i) || inside(i) || /^[\s~]*\[/.test(text.slice(end, end + 3))) return false;
      if (text.slice(Math.max(0, i - 2), i) === "**" || (references >= 0 && i > references) || m[0] === "appendix") return false;
      return !otherWork(end, i);
    });
    expect(undecided.map((m) => text.slice(Math.max(0, m.index! - 30), m.index! + m[0].length + 10))).toEqual([]);
  });
});

// @vitest-environment jsdom
// The parts the erdos257 instance adds, over the synthetic fixture in
// tests/fixtures/erdos257-synthetic/ (invented data, no claim about #257): the table of runs
// from Actions and Comparator receipts, tie origins and comparisons in the edition's facts,
// the comparison and origin lines, image figures, and the copy slots. These suites run for
// every instance: the code they test is shared.

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, describe, expect, it } from "vitest";
import type { LeanDeclaration, LeanModule, LeanModules } from "../src/api/lean";
import { buildRunLedger, conclusionStatus, SUMMARY_OVER, type EvidenceInput, type RunLedger } from "../src/checks/runLedger";
import { RunTable } from "../src/checks/RunTable";
import { FidelityLine, OriginLine } from "../src/compare/Fidelity";
import { fidelitySentence, originWords, verdictWords } from "../src/compare/fidelityWords";
import { siteFacts } from "../src/home/siteFacts";
import { copyTodos, INSTANCES, selectInstance } from "../src/instances/registry";
import { COPY } from "../src/instances/erdos257/copy";
import { countsLine, heroHtml as erdosHero } from "../src/instances/erdos257/hero";
import erdos from "../src/instances/erdos257/site";
import type { LeanShell } from "../src/lean/data";
import { DeclView } from "../src/lean/LeanBlock";
import { buildIndex } from "../src/lean/resolve";
import { prepareDocument } from "../src/reader/engine";
import { mountFigures } from "../src/reader/mount";
import { siteFilms } from "../src/app/siteFilms";

const FIXTURE = resolve(__dirname, "fixtures/erdos257-synthetic");
const json = (path: string) => JSON.parse(readFileSync(resolve(FIXTURE, path), "utf8"));
const read = (path: string) => {
  try {
    return json(`example/${path}`);
  } catch {
    return null;
  }
};
const evidence = json("example/evidence-graph.json").evidence as EvidenceInput[];
const ledger = (): RunLedger => buildRunLedger(evidence, read);

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
  root = undefined;
});
async function render(node: React.ReactNode): Promise<HTMLDivElement> {
  host = document.createElement("div");
  document.body.append(host);
  root = createRoot(host);
  await act(async () => root!.render(node));
  return host;
}

describe("the table of runs, from evidence records and their receipts", () => {
  it("reads Actions runs, an index of Comparator receipts and a generic one, and leaves out what is not a run", () => {
    const { groups, missing } = ledger();
    expect(groups.map((g) => g.type)).toEqual(["github_actions_run", "comparator_receipt", "evidence"]);
    const [actions, comparator, other] = groups;
    expect(actions.rows.map((r) => [r.id, r.status])).toEqual([
      ["actions_build_failed", "failed"],
      ["actions_build_cancelled", "unavailable"],
      ["actions_build_passed", "passed"],
    ]);
    expect(comparator.rows).toHaveLength(11);
    expect(comparator.counts).toEqual({ passed: 10, failed: 1 });
    // The written review is not a run; the planned extraction and the record whose receipt is gone are.
    expect(other.rows.map((r) => r.id).sort()).toEqual(["extraction_planned", "receipt_missing"]);
    expect(missing).toEqual(["verification/not-there.json"]);
  });

  it("gives each Actions run its place, commit, date, outcome and what it shows", () => {
    const row = ledger().groups[0].rows.find((r) => r.id === "actions_build_passed")!;
    expect(row.what).toBe("Build the Lean");
    expect(row.where).toEqual({ label: "example-owner/example-lean, run 1001", url: "https://github.com/example-owner/example-lean/actions/runs/1001" });
    expect(row.commit?.url).toBe(`https://github.com/example-owner/example-lean/commit/${"a".repeat(40)}`);
    expect(row.date).toBe("1 November 2026");
    expect(row.outcome).toBe("The run succeeded");
    expect(row.shows).toBe("The Lean project compiles at this commit.");
    expect(row.receipt).toBe("verification/actions-success.json");
    const failed = ledger().groups[0].rows.find((r) => r.id === "actions_build_failed")!;
    expect(failed.where?.label).toBe("example-owner/example-lean, run 1002, attempt 2");
    expect(ledger().groups[0].rows.find((r) => r.id === "actions_build_cancelled")!.outcome).toBe("The run was cancelled");
    expect(conclusionStatus("timed_out")).toBe("unavailable");
  });

  it("links the upstream run log and published receipt for an interrupted check", async () => {
    const repository = "https://github.com/example-owner/archive";
    const commit = "c".repeat(40);
    const log = `${repository}/blob/${commit}/verify/results/sample.txt`;
    const path = "verification/archive-sample.json";
    const check: EvidenceInput = {
      id: "archive.sample", kind: "platform_observation", status: "unavailable",
      tool: "Sample runs", receipt_path: path,
    };
    const result = buildRunLedger([check], (file) => file === path ? {
      record_type: "upstream_run_observation", repository, commit, date: "2026-11-22",
      where: "The authors’ archive run", logs: [{ url: log }],
      targets: [{ record: "decl.checked", url: `${log}#L42` },
                { record: "decl.unrelated", url: `${repository}/blob/${commit}/other.txt#L12` }],
      outcome: "The memory limit stopped one check",
      shows: "The other 500 names were accepted.",
      does_not_show: "The interrupted process gave no verdict.",
    } : null);
    expect(result.missing).toEqual([]);
    expect(result.groups[0].rows[0].targetLinks).toEqual({ "decl.checked": `${log}#L42` });
    const page = await render(<RunTable ledger={result} />);
    const links = [...page.querySelectorAll("a")].map((link) => link.getAttribute("href"));
    expect(links).toEqual(expect.arrayContaining([log, `${repository}/commit/${commit}`]));
    expect(links.some((href) => href?.endsWith("/" + path))).toBe(true);
    expect(page.textContent).toContain("The memory limit stopped one check");
    expect(page.textContent).toContain("The interrupted process gave no verdict.");
  });

  it("reads Palomar replay receipts: entry, theorems, kernels, axioms and a failure's stage", () => {
    const rows = ledger().groups[1].rows;
    const failed = rows.find((r) => r.entry === "E257_07")!;
    expect(failed.status).toBe("failed");
    expect(failed.outcome).toContain("Comparator rejected");
    expect(failed.outcome).toContain("refused by Lean’s default kernel and nanoda");
    expect(failed.outcome).toContain("stopped at run comparator");
    const passed = rows.find((r) => r.entry === "E257_01")!;
    expect(passed.kernels).toEqual(["Lean’s default kernel", "nanoda"]);
    expect(passed.axioms).toEqual(["propext", "Quot.sound", "Classical.choice"]);
    expect(passed.theorems).toHaveLength(2);
    expect(passed.receipt).toBe("verification/comparator/receipt-E257_01.json");
    expect(passed.doesNotShow).toContain("Whether the challenge statements say what the papers say");
  });

  it("shows a long kind as one summary row with its counts and a list that opens, failures in the same table", async () => {
    const view = await render(<RunTable ledger={ledger()} />);
    expect(ledger().groups[1].rows.length).toBeGreaterThan(SUMMARY_OVER);
    const summary = view.querySelector(".runs__row--summary")!;
    expect(summary.querySelector("th")!.textContent).toContain("Comparator receipts: 11");
    expect(summary.textContent).toContain("10 passed and 1 failed");
    expect(summary.querySelectorAll("details.runs__list tbody > tr")).toHaveLength(11);
    // The failed Actions run, and the failed receipt both in the summary's list and in view above it.
    expect(view.querySelectorAll(".runs__row--failed").length).toBe(3);
    expect(view.querySelector(".runs__row--unavailable")).not.toBeNull();
    expect([...view.querySelectorAll("thead th")].slice(0, 7).map((th) => th.textContent)).toEqual(["What ran", "Where", "Commit", "Date", "Outcome", "What it shows", "What it does not show"]);
  });

  it("shows nothing for an instance with no receipts", async () => {
    const view = await render(<RunTable ledger={{ groups: [], missing: [] }} />);
    expect(view.innerHTML).toBe("");
  });
});

describe("the edition's facts about ties", () => {
  const facts = siteFacts(FIXTURE, resolve(FIXTURE, "edition"), { example: "example", theorem: { record: null, paper: "short", pattern: null }, observation: null, tieAudit: null });

  it("counts ties by who made them", () => {
    expect(facts.origins).toEqual({ evidenceRecord: 3, ai: 2, unmarked: 1 });
    expect(facts.ties?.total).toBe(6);
  });

  it("finds the main theorem from the graph's first goal when the instance names none", () => {
    expect(facts.mainRecord).toBe("goal.main");
    expect(facts.theorem1).toEqual({ at: "b0-10", anchor: null });
  });

  it("puts both counts in the front page's line, from the facts", () => {
    const line = countsLine(facts, "Caveat.", "Review.");
    expect(line).toContain("6 ties: 3 copied from the papers’ published evidence mapping and 2 made by an AI agent for this site, and 1 that do not say who made them. Review.");
    expect(line).not.toContain("Caveat.");
    expect(line).toMatch(/^The three papers have \d+ marked statements/);
  });
});

describe("what the Lean says against the paper, and who made a tie", () => {
  it("words each comparison and who made it", async () => {
    expect(verdictWords("same")).toBe("Says the same as the paper");
    expect(fidelitySentence("stronger")).toBe("The Lean statement says more than the paper.");
    expect(fidelitySentence("weaker")).toBe("The Lean statement says less than the paper.");
    const view = await render(<FidelityLine row={{ fidelity: "weaker", fidelity_note: "It needs an extra hypothesis.", fidelity_source: "recorded" }} />);
    expect(view.textContent).toBe("The Lean statement says less than the paper. It needs an extra hypothesis. Compared in the source repository’s own evidence record.");
  });

  it("says nothing where the data has no comparison or origin", async () => {
    const view = await render(
      <>
        <FidelityLine row={{}} />
        <OriginLine origin={undefined} />
      </>,
    );
    expect(view.innerHTML).toBe("");
    expect(originWords("evidence_record")).toContain("copied from the papers’ published evidence mapping");
    expect(originWords("ai")).toContain("An AI agent");
  });

  it("puts the comparison in the Lean panel under the relation, from the alignment row", async () => {
    const row = json("edition/alignment.json").data.records["goal.main"].lean[0];
    const source = "theorem main (x : Nat) : x = x := by\n  rfl";
    const decl: LeanDeclaration = { name: "Synthetic.main", short: "main", kind: "theorem", namespace: "Synthetic", line: 1, signature_end_line: 1, end_line: 2, doc: null, private: false, uses: [], used_by: [] };
    const module: LeanModule = { module: "Synthetic", path: "Synthetic.lean", sha256: "", imports: [], source, declarations: [decl] };
    const shell: LeanShell = {
      plain: new Map(),
      modules: { base_url: "https://github.com/o/r/blob/abc/", revision: "abc", dependency_source: "source_text" } as LeanModules,
      index: buildIndex({ modules: ["Synthetic"], names: [["Synthetic.main", "theorem", 0, 1, 2]] }),
      paths: new Map([["Synthetic", { module: "Synthetic", path: "Synthetic.lean", lines: 2, declarations: 1, sha256: "" }]]),
      terms: new Map(),
      linked: new Map(),
    };
    const view = await render(<DeclView decl={decl} module={module} shell={shell} relation={row.relation} note={row.note} fidelity={row} noTerms noDependencies noPapers />);
    const line = view.querySelector(".lean-block__link .fidelity")!;
    expect(line.getAttribute("data-fidelity")).toBe("stronger");
    expect(line.textContent).toContain("The Lean statement says more than the paper. The Lean drops a hypothesis the paper keeps.");
    expect(line.querySelector(".fidelity__who")!.textContent).toContain("Compared by an AI agent for this site");
    // An edition without the fields shows the relation alone, as before.
    const plain = await render(<DeclView decl={decl} module={module} shell={shell} relation="states" note="Synthetic." noTerms noDependencies noPapers />);
    expect(plain.querySelector(".fidelity")).toBeNull();
  });
});

describe("image figures", () => {
  const prepared = () =>
    prepareDocument({
      stage: "expository",
      bytes: new Uint8Array(readFileSync(resolve(FIXTURE, "papers/expository/main.md"))),
      documentPath: "expository/main.md",
      documentPaths: { long: "long/reasoning-record.md", short: "short/paper.md", expository: "expository/main.md" },
    });

  it("turns a Markdown image and a LaTeX figure with includegraphics into slots for the shipped file, with captions", () => {
    const html = prepared()
      .renderAll()
      .map((part) => part.html)
      .join("\n");
    const box = document.createElement("div");
    box.innerHTML = html;
    const slots = [...box.querySelectorAll<HTMLElement>("[data-figure-image]")];
    expect(slots.map((slot) => slot.dataset.figureImage)).toEqual(["/paper-figures/expository/synthetic.svg", "/paper-figures/expository/synthetic.svg"]);
    expect([...box.querySelectorAll("figure.paper-figure figcaption")].map((c) => c.textContent?.trim())).toEqual([
      "A synthetic picture, as a Markdown image.",
      "A synthetic picture, as a LaTeX figure.",
    ]);
    expect(box.querySelector("img")).toBeNull();
  });

  it("mounts the image where no drawn figure claims the slot, and removes it again", () => {
    const box = document.createElement("div");
    box.innerHTML = prepared()
      .renderAll()
      .map((part) => part.html)
      .join("\n");
    const unmount = mountFigures(box);
    const images = [...box.querySelectorAll<HTMLImageElement>("img.paper-figure__image")];
    expect(images).toHaveLength(2);
    expect(images[0].getAttribute("src")).toBe("/paper-figures/expository/synthetic.svg");
    expect(images[0].alt).toBe("A synthetic picture, as a Markdown image.");
    unmount();
    expect(box.querySelectorAll("img").length).toBe(0);
  });
});

describe("the erdos257 instance", () => {
  it("has every copy slot written, and the build can list any left", () => {
    expect(copyTodos(COPY)).toEqual([]);
    expect(copyTodos({ a: "TODO(copy): a", b: ["x", "TODO(copy): b.1"] })).toEqual(["a", "b.1"]);
    expect(copyTodos(INSTANCES["qaoa-sk"].copySlots)).toEqual([]);
  });

  it("types no count of the edition into its copy", () => {
    // Years, theorem numbers and the formulas' own numbers are the papers' words; a count of
    // records, ties, files or runs belongs to the page around the copy.
    const text = JSON.stringify(COPY).replace(/\$[^$]*\$/g, "");
    expect(text).not.toMatch(/\b\d+ (?:records?|steps?|ties|statements|files|runs|declarations|modules|pages)\b/);
  });

  it("writes the first screen with the clause table's verdict column", () => {
    const facts = siteFacts(FIXTURE, resolve(FIXTURE, "edition"), { example: "example", theorem: { record: null, paper: "short", pattern: null }, observation: null, tieAudit: null });
    const html = erdosHero("/x/", facts, (tex) => `<math>${tex}</math>`, "Caveat.", "Review.");
    expect(html).toContain('<h1 id="front-title" class="front__title">');
    expect(html).toContain('<td class="rosetta__verdict" data-verdict="same">');
    expect(html).not.toContain("TODO(copy)");
    expect(html).toContain('href="/x/read/short?l=b0-10&n=goal.main"');
    expect(html).not.toContain("film-slot");
  });

  it("leaks no SK address, path or film into its build", () => {
    const facts = siteFacts("/no/such/place", "/no/such/place", erdos);
    const published = [erdos.readme("", facts), erdos.llms("", facts), JSON.stringify(erdos.pdfs), JSON.stringify(erdos.html)].join("\n");
    expect(published).not.toMatch(/lean-exposition-site|qaoa-sk|Sherrington|OpenAI/);
    expect(erdos.defaultSiteUrl).toBeNull();
    expect(Object.values(erdos.pdfs).every((pdf) => pdf.file.startsWith("papers/erdos257/"))).toBe(true);
    expect(siteFilms("/", erdos.films).map((f) => f.id)).toEqual(["short-mathematics", "mathematics", "short-funnel"]);
  });

  it("is chosen by LX_INSTANCE, and an unknown name says which exist", () => {
    expect(selectInstance("erdos257").id).toBe("erdos257");
    expect(selectInstance(undefined).id).toBe(process.env.LX_INSTANCE || "qaoa-sk");
    expect(() => selectInstance("nope")).toThrow(/Known: qaoa-sk, erdos257/);
  });
});

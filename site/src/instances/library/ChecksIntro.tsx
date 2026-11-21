// What ran, for a library paper: the terms, then, for a paper that publishes its runs, one row
// for each thing a Lean reader asks first (instance.json "reader.checks_lead"). "ledger" builds
// the rows from the run receipts, the evidence records, the Lean text scan and the tie index;
// "observation" from the published build and extraction observation (the SK paper's table).
// Each row says what ran and its result, then what that leaves open. The table by kind follows.

import type { ReactNode } from "react";
import { SITE_FACTS } from "virtual:site-facts";
import { RUN_LEDGER } from "virtual:run-ledger";
import site from "./site";
import { PAPER } from "./data";
import { Standing } from "../qaoa-sk/Standing";
import { countsInWords, type EvidenceCard, type KindGroup } from "../../checks/summary";

const n = (value: number) => value.toLocaleString("en-GB");
const list = (items: string[]) => (items.length < 2 ? items.join("") : `${items.slice(0, -1).join(", ")} and ${items[items.length - 1]}`);
const R = PAPER.reader ?? {};

function Row({ name, did, open }: { name: string; did: ReactNode; open: ReactNode }) {
  return (
    <tr>
      <th scope="row">{name}</th>
      <td>{did}</td>
      <td className="standing__open">{open}</td>
    </tr>
  );
}

function Ledger({ groups }: { groups: KindGroup[] }) {
  const { scan, ties, origins } = SITE_FACTS;
  const actions = RUN_LEDGER.groups.find((group) => group.type === "github_actions_run");
  const comparator = RUN_LEDGER.groups.find((group) => group.type === "comparator_receipt");
  const builds = groups.find((group) => group.kind === "lean_build");
  const kernels = [...new Set(comparator?.rows.flatMap((row) => row.kernels ?? []) ?? [])];
  const axioms = [...new Set(comparator?.rows.flatMap((row) => row.axioms ?? []) ?? [])];
  const theorems = comparator?.rows.reduce((total, row) => total + (row.theorems?.length ?? 0), 0) ?? 0;
  const sorry = scan?.sorry.reduce((total, row) => total + row.count, 0) ?? 0;
  return (
    <>
      <p className="standing-terms">Nothing was compiled or compared again for this reader. Every outcome below is the one the run itself recorded, failures included.</p>
      <div className="standing-wrap">
        <table className="standing">
          <caption className="visually-hidden">What ran on the Lean and the papers, the result and what that leaves open</caption>
          <thead>
            <tr>
              <th scope="col">
                <span className="visually-hidden">Question</span>
              </th>
              <th scope="col">What ran, and the result</th>
              <th scope="col">What that leaves open</th>
            </tr>
          </thead>
          <tbody>
            <Row
              name="Lean builds"
              did={
                actions || builds?.cards.length ? (
                  <>
                    {actions ? <>GitHub Actions: {n(actions.rows.length)} recorded {actions.rows.length === 1 ? "run" : "runs"}, {countsInWords(actions.counts)}. </> : null}
                    {builds?.cards.length ? <>Lean build records: {countsInWords(builds.counts)}.</> : null}
                  </>
                ) : (
                  "No Lean build is recorded."
                )
              }
              open="A build shows that the code compiles. It does not show that a statement means what a paper says."
            />
            <Row
              name="Comparator"
              did={
                comparator ? (
                  <>
                    {n(comparator.rows.length)} receipts, {countsInWords(comparator.counts)}, covering {n(theorems)} theorem statements
                    {kernels.length ? <>, checked by {list(kernels)}</> : null}
                    {axioms.length ? <>, with the permitted axioms {list(axioms)}</> : null}.
                  </>
                ) : (
                  "No Comparator receipt is recorded."
                )
              }
              open="Comparator checks a proof against a separately written statement. Whether that statement says what the papers say is the comparison shown on each step."
            />
            <Row
              name="Any sorry"
              did={scan ? (sorry ? <>A text scan of the Lean in this reader finds the word {n(sorry)} {sorry === 1 ? "time" : "times"}, in {n(scan.sorry.length)} {scan.sorry.length === 1 ? "file" : "files"}.</> : <>A text scan of the {n(scan.files)} Lean files in this reader finds no <code>sorry</code>.</>) : "No scan of the Lean source is recorded."}
              open="The scan reads text only."
            />
            {(R.checks_rows ?? []).map((row) => (
              <Row key={row.name} name={row.name} did={row.did} open={row.open} />
            ))}
            {ties && (
              <Row
                name="Ties to the papers"
                did={
                  <>
                    {n(ties.statements)} marked statements, {n(ties.withLean)} of them with Lean, in {n(ties.total)} ties.
                    {origins ? <> {n(origins.evidenceRecord)} were copied from the papers’ published evidence mapping, {n(origins.ai)} were made by an AI agent{origins.unmarked ? `, ${n(origins.unmarked)} do not say` : ""}.</> : null}
                  </>
                }
                open="No independent mathematician has reviewed the ties, and no program tests whether the two sides say the same thing."
              />
            )}
          </tbody>
        </table>
      </div>
    </>
  );
}

export function ChecksIntro({ groups }: { groups: KindGroup[] }) {
  return (
    <>
      <p className="standing-terms">{site.words.checksTerms}</p>
      {R.checks_lead === "ledger" ? <Ledger groups={groups} /> : R.checks_lead === "observation" ? <Standing groups={groups} /> : null}
    </>
  );
}

/** A note under the table on one published observation, when its run record is listed. */
export function ChecksNote({ cards }: { cards: readonly EvidenceCard[] }) {
  const note = R.checks_note;
  if (!note || !cards.some((card) => card.id === note.card)) return null;
  return (
    <p className="checks__edition">
      {note.before}
      <a href={`${import.meta.env.BASE_URL}${note.file}`}>{note.link}</a>
      {note.after}
    </p>
  );
}

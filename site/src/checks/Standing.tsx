// The first screen of Checks, for a reader who knows Lean: what ran, its result and what
// that leaves open, one row for each thing such a reader asks. Build and axiom facts are read
// at build time from the published observation (siteFacts.ts), outcomes from the run records,
// so a row can never say more than its source. The checker is named in every row.

import type { ReactNode } from "react";
import { SITE_FACTS } from "virtual:site-facts";
import { routeHref } from "../app/router";
import { MODELS_STEP } from "../app/caveat";
import { MAIN_THEOREM, VALUE_THEOREM } from "../lean/data";
import { countsInWords, type KindGroup } from "./summary";

const observation = `${import.meta.env.BASE_URL}verification/full-support-build-extraction-observation-20261026.json`;
const base = "https://github.com/openai/math/tree/";
const leanHref = (decl: string) => routeHref({ view: "lean", decl });
const leanWord = (name: string) => <code className="lean" translate="no">{name}</code>;

function list(items: string[]): ReactNode {
  return items.map((item, i) => (
    <span key={item}>
      {i > 0 && (i === items.length - 1 ? " and " : ", ")}
      {leanWord(item)}
    </span>
  ));
}

function Row({ name, did, open }: { name: string; did: ReactNode; open: ReactNode }) {
  return (
    <tr>
      <th scope="row">{name}</th>
      <td>{did}</td>
      <td className="standing__open">{open}</td>
    </tr>
  );
}

/** The page's lead when the published observation is present; null sends the page to its plain paragraph. */
export function Standing({ groups }: { groups: KindGroup[] }) {
  const { build, extraction, scan, ties, lean, audit } = SITE_FACTS;
  if (!build || !extraction) return null;
  const comparator = groups.find((group) => group.kind === "comparator");
  const reviews = groups.find((group) => group.kind === "semantic_review");
  const version = build.toolchain.split(":").pop()!;
  const jobs = /\((\d+) jobs\)/.exec(build.finalLine)?.[1];
  const elaborated = lean?.dependencySource === "elaborated";
  const sorryCount = scan?.sorry.reduce((n, row) => n + row.count, 0) ?? 0;
  return (
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
            name="Lean compile"
            did={
              <>
                <code className="lean" translate="no">{build.command}</code> exited {build.returncode}
                {jobs ? `, ${Number(jobs).toLocaleString("en-GB")} jobs,` : ""} on Lean {version} at OpenAI’s commit{" "}
                <a href={`${base}${build.revision}`} className="lean" translate="no">{build.revision.slice(0, 7)}</a>, so Lean’s kernel accepted the
                full-support tree. Recorded {build.date}.
              </>
            }
            open={
              <>
                <a href={leanHref(VALUE_THEOREM)}>The value theorem</a> has no successful build on record. Cached dependencies may have been reused, and no separate kernel replayed the proof.
              </>
            }
          />
          <Row
            name="Statement"
            did={
              <>
                <a href={leanHref(MAIN_THEOREM)}>The main theorem</a> says that a minimiser of the Parisi functional satisfies the full-support conclusion, for an order parameter on a given Brownian system.
              </>
            }
            open="It assumes a minimiser. That one exists is a separate input."
          />
          <Row
            name="Axioms"
            did={
              <>
                The extraction of {extraction.date} lists {list(extraction.axioms)} for the main theorem.{" "}
                {scan?.axiomDeclarations === 0 && "A text scan finds no axiom declaration in OpenAI’s source."}
              </>
            }
            open="OpenAI’s Comparator setup permits these axioms. No list is recorded for the value theorem."
          />
          <Row
            name={"Any sorry"}
            did={
              <>
                {extraction.hasSorry ? "The extraction lists sorryAx among the main theorem’s axioms." : <>The extraction’s list for the main theorem has no {leanWord("sorryAx")}.</>}{" "}
                {scan && sorryCount > 0 && (
                  <>
                    A text scan finds the word {sorryCount === 2 ? "twice" : `${sorryCount} times`}, once in each Comparator challenge file, where it stands in for the proof.
                  </>
                )}
              </>
            }
            open="The scan reads text only. The extraction’s list covers the main theorem only."
          />
          <Row
            name="Comparator"
            did={
              <>
                No accepted run{comparator ? <>: of {comparator.cards.length} run records, {countsInWords(comparator.counts)}</> : null}. The two failed runs stopped on a missing compiled file, before any comparison. The last attempt, on 25 October 2026, ended with no result.
              </>
            }
            open="Comparator has neither accepted nor rejected either theorem. No proof has been compared with its separately written statement."
          />
          <Row
            name="Two Lean models"
            did={
              <>
                The main theorem is in OpenAI’s full-support model, and <a href={leanHref(VALUE_THEOREM)}>the value theorem</a> is in a separate value model. Each defines its own objects.
              </>
            }
            open={
              <>
                No Lean theorem connects them, so <a href={routeHref({ view: "map", node: MODELS_STEP })}>combining them in Lean needs that connection first</a>. It is not a missing premise in the manuscript proof.
              </>
            }
          />
          <Row
            name="Dependencies"
            did={
              elaborated ? (
                <>The uses and used-by lines come from Lean’s compiled declarations.</>
              ) : (
                <>
                  The uses and used-by lines on this site come from a scan of the source text. The one extraction that finished, on {extraction.date}, ran on the main theorem only and listed {extraction.declarations.toLocaleString("en-GB")} declarations it reaches in OpenAI’s modules. <a href={observation}>A summary of that run</a> is published. It is counted under Source files below, because its run record is a hash comparison of the report. The two records under Dependency extraction are a planned run that never started and an attempt on 25 October 2026 that ended with no result.
                </>
              )
            }
            open={elaborated ? "Names outside the selected modules are boundaries." : "The scan misses names reached through tactics or notation. The extraction’s graph is partial and is not on this site. No extraction is recorded for the value theorem."}
          />
          {ties && (
            <Row
              name="Read by an AI agent"
              did={
                <>
                  AI agents marked {ties.statements.toLocaleString("en-GB")} statements in the papers, {ties.withLean} of them with Lean, by reading both sides. That makes {ties.total.toLocaleString("en-GB")} ties, because one statement can tie to several steps.{" "}
                  {audit && <>AI agents then read the {audit.read} ties that had Lean against the source and changed {audit.changed}. Another agent looked for Lean for the {audit.absencesChecked} statements recorded as having none, and changed {audit.absencesChanged} of them. A separate AI agent then read {audit.sampled} statements drawn at random from those with Lean: {audit.right} right, {audit.loose} right but loosely worded, {audit.wrong} wrong. Those were corrected. The other statements with Lean were not read a second time. </>}A program confirms only that both ends of each tie still exist.
                </>
              }
              open={
                <>
                  No independent mathematician has reviewed the ties, and no program tests whether the two sides say the same thing.{audit ? " The audit’s ledger is not public." : ""}{reviews?.cards.length ? <> Authors wrote {reviews.cards.length} explanations of single steps for a second reader to compare with their sources, and no second reader has done so.</> : null}
                </>
              }
            />
          )}
        </tbody>
      </table>
    </div>
  );
}

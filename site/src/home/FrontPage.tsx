// The front page, for a reader arriving for the first time: what the site is
// (one theorem, three accounts, the steps of the proof linked to passages), the
// theorem itself, the three accounts with their reading strips, the argument
// for the main result drawn by the map's own engine, and the recorded checks
// counted from the edition. Every number on the page is computed.

import { useEdition } from "../app/data";
import { routeHref } from "../app/router";
import { EDITION_TITLE } from "../app/PageTitle";
import { PAPER_NAMES, STAGE_ORDER, statedIn } from "../app/papers";
import { TheoremBody, mainGoal, startingGoals } from "../map/TheoremPlate";
import { Sample, SourceSwatches } from "../map/MapKey";
import { statusWords } from "../reader/page/model";
import { countsInWords } from "../checks/summary";
import { useReadings } from "../ribbons/useReadings";
import { StripMarks } from "../ribbons/StripMarks";
import { ArgumentFigure } from "./ArgumentFigure";
import "../map/tree.css";
import "../ribbons/dock.css";
import "./front.css";

const plural = (n: number, one: string, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;

export function FrontPage() {
  const edition = useEdition();
  const { graph } = edition;
  const goal = mainGoal(edition);
  const goals = startingGoals(edition);
  const readings = useReadings();
  const goalTitle = graph.nodes.get(goal)?.label ?? goal;
  const goalShort = goals.find((g) => g.id === goal)?.title ?? goalTitle;
  const shared = sharedStatus(STAGE_ORDER.map((stage) => edition.overview.papers.find((p) => p.stage === stage)));
  // "One theorem" in the hero, three results here: say which accounts cover which.
  const others = goals.filter((g) => g.id !== goal);
  const coverage =
    goals[0]?.id === goal &&
    goals[0].stages.length === STAGE_ORDER.length &&
    others.length > 0 &&
    others.every((g) => g.stages.length === 1 && g.stages[0] === "long")
      ? `All three accounts prove the first of these. The long record also covers the other ${others.length === 1 ? "one" : others.length === 2 ? "two" : others.length}.`
      : null;

  return (
    <div className="front">
      <section className="front__hero" aria-labelledby="front-title">
        <div className="front__intro">
          <h1 id="front-title" className="front__title">
            {EDITION_TITLE}
          </h1>
          <p className="front__lede">
            One theorem about the Sherrington–Kirkpatrick spin glass, written up three ways, with the steps of its proof linked
            to the passages that discuss them.
          </p>
          <p className="front__actions">
            <a className="front__primary" href={routeHref({ view: "read", stage: "expository" })}>
              Read the exposition
            </a>
            <a className="front__secondary" href={routeHref({ view: "map" })}>
              Open the argument map
            </a>
          </p>
        </div>
        <figure className="front__plate">
          <TheoremBody goal={goal} lean={false} foot={false} first />
        </figure>
      </section>

      <section className="front__band" aria-labelledby="front-accounts">
        <h2 id="front-accounts">Three accounts of the proof</h2>
        <p className="front__text">
          Each account proves the same theorem for a different reader. If the field is new to you, start with the exposition.
          {shared ? ` ${shared}` : ""}
        </p>
        {/* The strips' colours, beside the strips rather than only in the map's key below. */}
        <SourceSwatches origins={graph.origins} className="front__sources front__sources--inline" />
        <ol className="accounts">
          {STAGE_ORDER.map((stage) => {
            const paper = edition.overview.papers.find((p) => p.stage === stage);
            const strip = readings.status === "ready" ? readings.value.strips.find((s) => s.stage === stage) : undefined;
            const linked = strip?.passages.filter((p) => p.claims.length).length;
            return (
              <li key={stage} className="account">
                <div className="account__about">
                  <h3 className="account__name">
                    <a href={routeHref({ view: "read", stage })}>{PAPER_NAMES[stage].short}</a>
                  </h3>
                  <p className="account__job">
                    {PAPER_NAMES[stage].job} {PAPER_NAMES[stage].reader}
                  </p>
                </div>
                <div className="account__facts">
                  <p className="account__meta">
                    {paper && <span className="num">{plural(paper.sections, "section")}</span>}
                    {paper && !shared && `. ${statusWords(paper.state, paper.review_state)}`}
                  </p>
                  <div
                    className="account__strip"
                    role="img"
                    aria-label={
                      linked === undefined
                        ? `${PAPER_NAMES[stage].short} in reading order`
                        : `${PAPER_NAMES[stage].short}: ${plural(linked, "passage")} linked to steps of the argument, placed where each falls in the paper and coloured by the source of its steps`
                    }
                  >
                    <StripMarks strip={strip} className="account__bars" />
                  </div>
                  {linked !== undefined && (
                    <p className="account__count num">
                      {plural(linked, "passage")} linked to steps of the argument, where they fall in the paper
                    </p>
                  )}
                </div>
              </li>
            );
          })}
        </ol>
      </section>

      {/* Wide: the words, key and results on the left, the drawing beside them. Narrow: in reading order. */}
      <section className="front__band mapband" aria-labelledby="front-map">
        <div className="mapband__head">
          <h2 id="front-map">The argument map</h2>
          <p className="front__text">
            Each step of the argument is stored as a record: a claim, an assumption, or a declaration in Lean, a language in
            which a computer can check proofs. In the drawing, the main result is the box at the top. Each box under it is a
            record that its proof uses, and a line runs up from a record to the result that uses it. The colour of a box says
            which source the record comes from.
          </p>
        </div>
        <a className="front__figure" href={routeHref({ view: "map" })} aria-label={`Open the argument map for ${goalTitle}`}>
          <ArgumentFigure graph={graph} goal={goal} version={edition.context} />
          <span className="front__figcap">
            <span>{goalShort}, with every branch open</span>
            <span className="front__figopen">Open it in the map</span>
          </span>
        </a>
        <div className="front__key" aria-label="Key to the drawing" role="group">
          <SourceSwatches origins={graph.origins} className="front__sources" />
          <ul className="front__lines">
            <li>
              <Sample kind="supports" head={false} />
              Used in the argument for the result above it
            </li>
            <li>
              <Sample kind="formalizes" head={false} />
              Joins a result to its Lean declaration
            </li>
          </ul>
        </div>
        <div className="mapband__results">
          <h3 className="front__subhead">Main results in this edition</h3>
          {coverage && <p className="results__lead">{coverage}</p>}
          <ul className="results">
            {goals.map((g) => (
              <li key={g.id}>
                <a href={routeHref({ view: "map", goal: g.id })}>{graph.nodes.get(g.id)?.label ?? g.title}</a>
                <span className="results__where">{statedIn(g.stages)}</span>
              </li>
            ))}
          </ul>
        </div>
      </section>

      <section className="front__band" aria-labelledby="front-checks">
        <h2 id="front-checks">Recorded checks</h2>
        <p className="front__text">
          A check is a recorded test of one thing, for example whether a cited file still has its recorded hash or whether a
          Lean project compiles.
        </p>
        <CheckCounts />
        <p className="front__more">
          <a href={routeHref({ view: "checks" })}>See the recorded checks</a>
        </p>
      </section>

      <footer className="front__foot">
        <a href={routeHref({ view: "about" })}>About this site</a>
        <a href={routeHref({ view: "about", anchor: "edition" })}>Edition and citation</a>
      </footer>
    </div>
  );
}

/**
 * One sentence for a status the three accounts share ("All three are drafts, and each
 * review is recorded as needing revision."), so it is said once; null when they differ.
 */
function sharedStatus(papers: ({ state?: string; review_state?: string } | undefined)[]): string | null {
  const first = papers[0];
  if (!first || papers.some((p) => !p || p.state !== first.state || p.review_state !== first.review_state)) return null;
  const words = (s: string) => s.replace(/_/g, " ");
  const parts: string[] = [];
  if (first.state) parts.push(first.state === "draft" ? "All three are drafts" : `All three are recorded as ${words(first.state)}`);
  if (first.review_state)
    parts.push(`each review is recorded as ${first.review_state === "needs_revision" ? "needing revision" : words(first.review_state)}`);
  if (!parts.length) return null;
  const sentence = parts.join(", and ");
  return `${sentence.charAt(0).toUpperCase()}${sentence.slice(1)}.`;
}

const OUTCOMES = ["passed", "failed", "unavailable", "not_run"];

/** "This edition records 222 checks: 3 passed, 2 failed, 3 unavailable and 214 not run.", each count in its outcome's mark. */
function CheckCounts() {
  const { map } = useEdition();
  const counts: Record<string, number> = {};
  for (const e of map.records.evidence) counts[e.status] = (counts[e.status] ?? 0) + 1;
  const total = map.records.evidence.length;
  const keys = [...OUTCOMES.filter((s) => counts[s]), ...Object.keys(counts).filter((s) => !OUTCOMES.includes(s)).sort()];
  return (
    <p className="front__counts">
      This edition records <span className="num">{plural(total, "check")}</span>
      {keys.length ? ": " : "."}
      {keys.map((status, i) => (
        <span key={status}>
          <span className={`outcome outcome--${status}`}>{countsInWords({ [status]: counts[status] })}</span>
          {i < keys.length - 2 ? ", " : i === keys.length - 2 ? " and " : "."}
        </span>
      ))}
    </p>
  );
}

// The front page, for a reader arriving for the first time: the theorem in plain
// words and as the short paper states it; the problem it answers; how the proof
// rules out a gap, with the exposition's two figures; what follows from it; the
// three accounts with their reading strips; the argument drawn by the map's own
// engine; and what has been checked. The mathematical prose follows the papers'
// own statements and attributions. Every number taken from the edition is computed.

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
import { Rich, texHtml } from "../figures/tex";
import { GapFigure } from "../figures/GapFigure";
import { AreaFigure } from "../figures/AreaFigure";
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
      ? `All three accounts present the proof of the first of these. The long record also covers the other ${others.length === 1 ? "one" : others.length === 2 ? "two" : others.length}.`
      : null;

  return (
    <div className="front">
      <section className="front__hero" aria-labelledby="front-title">
        <div className="front__intro">
          <h1 id="front-title" className="front__title">
            {EDITION_TITLE}
          </h1>
          <p className="front__lede">
            Parisi’s formula gives the largest energy per spin in the Sherrington–Kirkpatrick spin glass as a minimum over
            nondecreasing functions, called order parameters. A minimising order parameter increases across every interval in
            [0, 1), and its derivative is positive between 0 and 1.
          </p>
          <p className="front__site">
            This site has three written accounts of the proof, with its steps linked to the passages that discuss them.
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

      {/* The mathematics in plain words, from the papers: the problem, the proof, what follows.
          Facts and attributions follow the exposition §§1–6, the short paper §§1–5 and the long
          record §13; nothing here goes beyond what those passages state. */}
      <section className="front__band front__pair" aria-labelledby="front-question">
        <div className="front__prose">
          <h2 id="front-question">Choosing signs to maximise a random energy</h2>
          <p>
            <Rich src="At each of $n$ sites choose a sign, $+1$ or $-1$, called a spin. Every pair of sites gets its own random weight $J_{ij}$, drawn independently from the standard Gaussian distribution, and a choice of signs $\sigma$ has energy" />
          </p>
          <div className="front__display" dangerouslySetInnerHTML={{ __html: texHtml("H_n(\\sigma)=\\frac{1}{\\sqrt n}\\sum_{i<j}J_{ij}\\,\\sigma_i\\sigma_j.") }} />
          <p>
            <Rich src="A positive weight rewards equal signs and a negative weight rewards opposite signs, so usually no choice satisfies every pair. The question is the largest energy per spin, averaged over the weights, as $n$ grows; call this limit $P_*$." />
          </p>
          <p>
            <Rich src="The overlap of two sign choices is their average agreement per site, which is $1$ when they are identical and $0$ when they differ on half the sites. Parisi’s formula, proved for this problem by Auffinger and Chen (2017), gives $P_*$ as the smallest value of a functional $\mathcal P(\gamma)$ over order parameters $\gamma$, nondecreasing functions of an overlap scale $t$ between $0$ and $1$. A gap is an interval of scales on which $\gamma$ stays flat, so that its increments put no weight there." />
          </p>
          <p>
            <Rich src="The theorem says that a minimising $\gamma$ has no gaps; in the papers’ terms, its increments have full support. Auffinger, Chen and Zeng (2020) had shown that a minimiser increases at infinitely many scales, which still leaves room for gaps. H.‑B. Chen (2026) first proved that there are none, by a different method. The accounts here follow OpenAI’s quantitative proof (2026a), which also shows that the derivative of $\gamma$ is positive." />
          </p>
        </div>
        <figure className="front__fig">
          <GapFigure />
          <figcaption>
            <Rich src="An example candidate with a gap, from Section 2 of the exposition. Above, $\gamma$ stays flat at $1/3$ between $1/3$ and $2/3$; below, its increments put no weight on that interval. This candidate is not a minimiser." />
          </figcaption>
        </figure>
      </section>

      <section className="front__band front__pair front__pair--flip" aria-labelledby="front-proof">
        <div className="front__prose">
          <h2 id="front-proof">How the proof rules out a gap</h2>
          <p>
            <Rich src="Suppose a minimising $\gamma$ were flat between two scales $r$ and $s$ at which it increases. The proof follows an auxiliary curve $q(t)$, the mean square of a slope measured along a random path that $\gamma$ determines." />
          </p>
          <p>
            <Rich src="Because $\gamma$ minimises $\mathcal P$, no allowed small change of $\gamma$ lowers $\mathcal P$. Testing changes that add or remove weight gives $q(r)=r$ and $q(s)=s$, with slope $q'\le 1$ at both ends." />
          </p>
          <p>
            <Rich src="Across the flat stretch, $\gamma$ equals a positive constant. There an estimate proved by OpenAI (2026a, Proposition 5.1) makes the third derivative of $q$ positive, so the slope $q'$ is strictly convex and stays below $1$ between $r$ and $s$. Then $q$ rises by less than $s-r$, which contradicts $q(r)=r$ and $q(s)=s$." />
          </p>
          <p>
            <Rich src="A flat stretch that starts at $0$, or one that reaches $1$, needs a separate argument. Once $\gamma$ is known to have no gaps, the same estimate is used a second time to show that its derivative is positive." />
          </p>
          <p>
            The estimate is the hard step. OpenAI proves it from sign properties of a backward equation and a forward
            probability density, combined with an explicit polynomial identity with rational coefficients. The short paper and
            the exposition cite it; the long record reconstructs its parts.
          </p>
        </div>
        <figure className="front__fig">
          <AreaFigure />
          <figcaption>
            <Rich src="From Section 5.3 of the exposition. Between the ends $r$ and $s$ of a supposed flat stretch, $q'$ starts and ends at $1$ in the case drawn; in general each end slope is at most $1$. A strictly convex $q'$ sags below $1$, and the shaded area is how far $q$ falls short of rising by $s-r$. The curve is a calculus model, not a computed SK curve." />
          </figcaption>
        </figure>
      </section>

      <section className="front__band" aria-labelledby="front-follows">
        <h2 id="front-follows">What follows from it</h2>
        <ul className="follows">
          <li>
            <h3>For the spins</h3>
            <p>
              <Rich src="For every overlap $r$ between $0$ and $1$, the same random weights have, with probability tending to one as $n$ grows, two sign choices whose energies per spin are close to $P_*$ and whose overlap is close to $r$. With $r=1/2$, for example, the two choices differ on between 24 and 26 per cent of the sites. This combines a theorem of Auffinger, Chen and Zeng (2020) with the absence of gaps; it shows that such pairs exist, not how to find them." />
            </p>
          </li>
          <li>
            <h3>A classical algorithm</h3>
            <p>
              <Rich src="The existence of a minimiser without gaps is the assumption under which the message-passing algorithm of El Alaoui, Montanari and Sellke (2021) finds, for any fixed $\varepsilon>0$, a sign choice whose energy is within $\varepsilon n$ of the largest, with probability tending to one. Once the functions it uses are given, it takes a number of arithmetic operations proportional to $n^2$, with a constant that depends on $\varepsilon$; computing those functions, and rounding error, are not counted." />
            </p>
          </li>
          <li>
            <h3>A quantum circuit</h3>
            <p>
              <Rich src="A second OpenAI manuscript (2026b) proves that for each $\varepsilon>0$ one fixed circuit of the quantum approximate optimization algorithm (QAOA), with depth and angles that depend on $\varepsilon$ but not on $n$ or the weights, reaches an expected energy per spin within $\varepsilon$ of $P_*$ as $n$ grows. Basso, Farhi, Marwaha, Villalonga and Zhou conjectured this in 2022. The proof uses the absence of gaps and a separate circuit construction, which the long record follows." />
            </p>
          </li>
        </ul>
      </section>

      <section className="front__band" aria-labelledby="front-accounts">
        <h2 id="front-accounts">Three accounts of the proof</h2>
        <p className="front__text">
          Each account presents the same proof for a different reader. If the field is new to you, start with the exposition.
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
        <h2 id="front-checks">What has been checked</h2>
        <p className="front__text">
          OpenAI’s repository has two statements written in Lean, each with a Lean proof: one of the full-support theorem, which
          assumes a minimiser, and one of the value identities and their finite Gaussian approximation. Comparator, a program that checks a Lean proof against a
          separately written statement, has not finished on either. One run stopped while building both proofs, and a later run on
          the full-support statement stopped without a result, so whether Comparator accepts them is unknown.
        </p>
        <p className="front__text">
          An exact calculation in rational arithmetic confirmed the 22 positive coefficients of the polynomial identity behind
          the curvature estimate; it does not check the analysis around that identity. The statements in each account were
          checked against its sources, by AI agents for the exposition and the long record. No independent mathematical review
          has been done.
        </p>
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

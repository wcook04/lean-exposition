// The front page, for a reader arriving for the first time: the theorem in plain
// words and as the short paper states it; what OpenAI's release asked and proved,
// with where each result is explained here; the technical explanation behind one
// disclosure (the problem, how the proof rules out a gap with the exposition's two
// figures, and what follows); the layers from OpenAI's release down to the
// exposition and the video in preparation, each linked; the argument drawn by the
// map's own engine; and what has been checked. The mathematical prose follows the
// papers' own statements and attributions (audited against them, claim by claim).
// Every number taken from the edition or the PDFs is computed.

import type { ReactNode } from "react";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { routeHref } from "../app/router";
import { EDITION_TITLE } from "../app/PageTitle";
import { PAPER_NAMES } from "../app/papers";
import { TheoremBody, mainGoal } from "../map/TheoremPlate";
import { Sample, SourceSwatches } from "../map/MapKey";
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

/** OpenAI's mathematics release, at the revision the three accounts cite. */
const RELEASE = "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a";
const RELEASE_TREE = "https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a";
const FAMILY_SCOPE = `${RELEASE}/lean/docs/281.md`;
const SUPPORT_PDF = `${RELEASE}/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf`;
const QAOA_PDF = `${RELEASE}/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf`;
const LEAN_SOURCE = `${RELEASE_TREE}/lean/OAI/Probability`;
const ATLAS_FAMILY = "https://wcook04.github.io/plectis-atlas/families/281.html";
const SITE_REPOSITORY = "https://github.com/wcook04/lean-exposition-site#readme";

const pdfHref = (stage: Stage) => `${import.meta.env.BASE_URL}${PAPER_PDFS[stage].path}`;

/** A link that leaves the site, marked with an arrow that stays on its last word. */
function Out({ href, children }: { href: string; children: ReactNode }) {
  return (
    <a className="front__out" href={href} target="_blank" rel="noopener noreferrer">
      {children}
    </a>
  );
}

export function FrontPage() {
  const edition = useEdition();
  const { graph } = edition;
  const goal = mainGoal(edition);
  const goalTitle = graph.nodes.get(goal)?.label ?? goal;
  const readings = useReadings();
  const shared = sharedStatus((["long", "short", "expository"] as Stage[]).map((stage) => edition.overview.papers.find((p) => p.stage === stage)));
  // The edition's own counts, as the About page gives them: records and the links between them.
  const recordCount = edition.overview.record_counts.nodes ?? graph.nodes.size;
  const linkCount = edition.overview.record_counts.edges ?? graph.edges.length;

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
            [0, 1), and its derivative is positive between 0{" "}and{" "}1.
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

      {/* What was asked and proved, for any mathematical reader. Each answer and attribution
          follows the papers (short paper §§1, 5; exposition §6 and further reading; long
          record §§1, 6–8); the technical explanation below expands the first answer. */}
      <section className="front__band" aria-labelledby="front-asked">
        <h2 id="front-asked" className="front__bandtitle">
          What was asked, and what was proved
        </h2>
        <p className="front__text">
          OpenAI’s mathematics release includes two manuscripts on this model, dated September 2026 and grouped as its family
          281, with Lean code for two of their statements. Between them they answer three questions.
        </p>
        <ol className="asked">
          <li>
            <h3 className="asked__q">Can a minimising order parameter stay flat on some interval below one?</h3>
            <div className="asked__a">
              <p>
                <Rich src="No. Every minimiser increases across every interval in $[0,1)$, and its derivative is positive between $0$ and $1$. OpenAI (2026a) proved both; H.‑B. Chen (2026) had already proved that there are no flat stretches, by a different method." />
              </p>
              <p className="asked__where">
                Explained in all three accounts:{" "}
                <a href={routeHref({ view: "read", stage: "expository" })}>the exposition</a>,{" "}
                <a href={routeHref({ view: "read", stage: "short", anchor: "model-and-result" })}>the short paper</a> and{" "}
                <a href={routeHref({ view: "read", stage: "long", anchor: "model-and-three-targets" })}>the long record</a>.{" "}
                <a href={routeHref({ view: "map", goal: "full_support" })}>Its argument on the map</a>.
              </p>
            </div>
          </li>
          <li>
            <h3 className="asked__q">Can the largest energy be computed from that minimiser?</h3>
            <div className="asked__a">
              <p>
                <Rich src="Yes. The largest energy per spin equals an integral computed along a random path driven by the minimiser, and finite sums of Gaussian correlations approach it. OpenAI (2026a) proved this." />
              </p>
              <p className="asked__where">
                Explained in <a href={routeHref({ view: "read", stage: "short", anchor: "value-and-qaoa" })}>the short paper, §5.1</a>{" "}
                and <a href={routeHref({ view: "read", stage: "long", anchor: "scalar-value-identities" })}>the long record, §§6–7</a>.{" "}
                <a href={routeHref({ view: "map", goal: "scalar_value" })}>Its argument on the map</a>.
              </p>
            </div>
          </li>
          <li>
            <h3 className="asked__q">Can one quantum circuit, fixed before the number of spins is chosen, reach that energy?</h3>
            <div className="asked__a">
              <p>
                <Rich src="Yes. For every $\varepsilon>0$ there is one circuit of the quantum approximate optimization algorithm (QAOA), its depth and angles chosen for $\varepsilon$ but not for the number of spins or the weights, whose expected energy per spin comes within $\varepsilon$ of the largest as the number of spins grows. OpenAI (2026b) proved this; Basso, Farhi, Marwaha, Villalonga and Zhou had conjectured it in 2022." />
              </p>
              <p className="asked__where">
                Explained in <a href={routeHref({ view: "read", stage: "long", anchor: "qaoa-construction" })}>the long record, §8</a>,
                and summarised in <a href={routeHref({ view: "read", stage: "short", anchor: "value-and-qaoa" })}>the short paper, §5.3</a>.{" "}
                <a href={routeHref({ view: "map", goal: "qaoa_thermodynamic_first" })}>Its argument on the map</a>.
              </p>
            </div>
          </li>
        </ol>

        <details className="tech">
          <summary>
            <span className="tech__label">The technical explanation</span>
            <span className="tech__hint">The problem, how the proof rules out a gap, and what follows from it</span>
          </summary>
          <TechnicalExplanation />
        </details>
      </section>

      {/* The layers, from OpenAI's release down to the shortest account: each one linked,
          to read on this site or as a PDF. The narrowing shows their order, not their length. */}
      <section className="front__band" aria-labelledby="front-layers">
        <h2 id="front-layers" className="front__bandtitle">
          From OpenAI’s release to the exposition
        </h2>
        <p className="front__text">
          The layers run from OpenAI’s release and its Lean code down to the exposition, and then a video in preparation.
          Each is linked here, to read on this site or as a PDF. {shared ?? ""}
        </p>
        <ol className="funnel">
          <li className="funnel__layer" style={{ ["--step" as string]: 0 }}>
            <div className="funnel__body">
              <h3 className="funnel__name">OpenAI’s release, family 281</h3>
              <p className="funnel__what">Two manuscripts dated September 2026, and Lean code for two of their statements.</p>
            </div>
            <p className="funnel__links">
              <Out href={FAMILY_SCOPE}>Family 281 and its Lean scope</Out>
              <Out href={SUPPORT_PDF}>Full-support manuscript, PDF</Out>
              <Out href={QAOA_PDF}>QAOA manuscript, PDF</Out>
              <Out href={LEAN_SOURCE}>Lean source</Out>
            </p>
          </li>
          <li className="funnel__layer" style={{ ["--step" as string]: 1 }}>
            <div className="funnel__body">
              <h3 className="funnel__name">The argument map</h3>
              <p className="funnel__what">
                {plural(recordCount, "record")} and the {plural(linkCount, "link")} between them: the claims, assumptions and Lean
                declarations the argument uses, and which result uses which.
              </p>
            </div>
            <p className="funnel__links">
              <a href={routeHref({ view: "map" })}>Open the argument map</a>
            </p>
          </li>
          {(["long", "short", "expository"] as Stage[]).map((stage, i) => {
            const paper = edition.overview.papers.find((p) => p.stage === stage);
            const strip = readings.status === "ready" ? readings.value.strips.find((s) => s.stage === stage) : undefined;
            const linked = strip?.passages.filter((p) => p.claims.length).length;
            const pdf = PAPER_PDFS[stage];
            return (
              <li key={stage} className="funnel__layer" style={{ ["--step" as string]: i + 2 }}>
                <div className="funnel__body">
                  <h3 className="funnel__name">{PAPER_NAMES[stage].short}</h3>
                  <p className="funnel__what">
                    {PAPER_NAMES[stage].job} {PAPER_NAMES[stage].reader}
                  </p>
                  <div
                    className="funnel__strip"
                    role="img"
                    aria-label={
                      linked === undefined
                        ? `${PAPER_NAMES[stage].short} in reading order`
                        : `${PAPER_NAMES[stage].short}: ${plural(linked, "passage")} linked to steps of the argument, placed where each falls in the paper and coloured by the source of its steps`
                    }
                  >
                    <StripMarks strip={strip} className="account__bars" />
                  </div>
                </div>
                <p className="funnel__links">
                  <a href={routeHref({ view: "read", stage })}>
                    Read it here{paper ? `, ${plural(paper.sections, "section")}` : ""}
                  </a>
                  <a href={pdfHref(stage)}>
                    PDF, {plural(pdf.pages, "page")}
                  </a>
                </p>
              </li>
            );
          })}
          <li className="funnel__layer funnel__layer--video" style={{ ["--step" as string]: 5 }}>
            <p className="funnel__video">Video, in preparation</p>
          </li>
        </ol>
        <SourceSwatches origins={graph.origins} className="front__sources front__sources--inline" />
        <ul className="elsewhere">
          <li>
            <Out href={ATLAS_FAMILY}>Plectis Atlas, family 281</Out> is an independent website with a page for this family: OpenAI’s
            two papers, their theorems beside the Lean statements, and what outside groups report about them.
          </li>
          <li>
            <Out href={SITE_REPOSITORY}>The public repository of this website</Out> holds the built pages and the three PDFs, with a
            README that links back to the release and to Plectis Atlas.
          </li>
        </ul>
      </section>

      {/* Wide: the words and key on the left, the drawing beside them. Narrow: in reading order. */}
      <section className="front__band mapband" aria-labelledby="front-map">
        <div className="mapband__head">
          <h2 id="front-map" className="front__bandtitle">
            The argument map
          </h2>
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
            <span>Full support, with every branch open</span>
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
      </section>

      <section className="front__band" aria-labelledby="front-checks">
        <h2 id="front-checks" className="front__bandtitle">
          What has been checked
        </h2>
        <p className="front__text">
          OpenAI’s repository has two statements written in Lean, each with a Lean proof: one of the full-support theorem, which
          assumes a minimiser, and one of the value identities and their finite Gaussian approximation. Comparator, a program
          that checks a Lean proof against a separately written statement, has not finished on either. One run stopped while
          building both proofs, and a later run on the full-support statement stopped without a result, so whether Comparator
          accepts them is unknown.
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
 * The first answer in technical terms, from the papers: the problem (exposition §§1–3),
 * how the proof rules out a gap (exposition §5, short paper §§2–4) and what follows
 * (exposition §6, short paper §5). Nothing here goes beyond what those passages state.
 */
function TechnicalExplanation() {
  return (
    <div className="tech__body">
      <section className="front__band front__pair" aria-labelledby="front-question">
        <div className="front__prose">
          <h3 id="front-question" className="front__bandtitle">
            Choosing signs to maximise a random energy
          </h3>
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
          <h3 id="front-proof" className="front__bandtitle">
            How the proof rules out a gap
          </h3>
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
        <h3 id="front-follows" className="front__bandtitle">
          What follows from it
        </h3>
        <ul className="follows">
          <li>
            <h4>For the spins</h4>
            <p>
              <Rich src="For every overlap $r$ between $0$ and $1$, the same random weights have, with probability tending to one as $n$ grows, two sign choices whose energies per spin are close to $P_*$ and whose overlap is close to $r$. With $r=1/2$, for example, the two choices differ on between 24 and 26 per cent of the sites. This combines a theorem of Auffinger, Chen and Zeng (2020) with the absence of gaps; it shows that such pairs exist, not how to find them." />
            </p>
          </li>
          <li>
            <h4>A classical algorithm</h4>
            <p>
              <Rich src="The existence of a minimiser without gaps is the assumption under which the message-passing algorithm of El Alaoui, Montanari and Sellke (2021) finds, for any fixed $\varepsilon>0$, a sign choice whose energy is within $\varepsilon n$ of the largest, with probability tending to one. Once the functions it uses are given, it takes a number of arithmetic operations proportional to $n^2$, with a constant that depends on $\varepsilon$; computing those functions, and rounding error, are not counted." />
            </p>
          </li>
          <li>
            <h4>A quantum circuit</h4>
            <p>
              <Rich src="A second OpenAI manuscript (2026b) proves that for each $\varepsilon>0$ one fixed circuit of the quantum approximate optimization algorithm (QAOA), with depth and angles that depend on $\varepsilon$ but not on $n$ or the weights, reaches an expected energy per spin within $\varepsilon$ of $P_*$ as $n$ grows. Basso, Farhi, Marwaha, Villalonga and Zhou conjectured this in 2022. The proof uses the absence of gaps and a separate circuit construction, which the long record follows." />
            </p>
          </li>
        </ul>
      </section>
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
  if (first.state) parts.push(first.state === "draft" ? "All three accounts are drafts" : `All three accounts are recorded as ${words(first.state)}`);
  if (first.review_state)
    parts.push(`each review is recorded as ${first.review_state === "needs_revision" ? "needing revision" : words(first.review_state)}`);
  if (!parts.length) return null;
  const sentence = parts.join(", and ");
  return `${sentence.charAt(0).toUpperCase()}${sentence.slice(1)}.`;
}

const OUTCOMES = ["passed", "failed", "unavailable", "not_run"];

/** "This site records 222 checks: 3 passed, 2 failed, 3 unavailable and 214 not run.", each count in its outcome's mark. */
function CheckCounts() {
  const { map } = useEdition();
  const counts: Record<string, number> = {};
  for (const e of map.records.evidence) counts[e.status] = (counts[e.status] ?? 0) + 1;
  const total = map.records.evidence.length;
  const keys = [...OUTCOMES.filter((s) => counts[s]), ...Object.keys(counts).filter((s) => !OUTCOMES.includes(s)).sort()];
  return (
    <p className="front__counts">
      This site records <span className="num">{plural(total, "check")}</span>
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

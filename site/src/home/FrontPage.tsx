// The front page, for a reader arriving for the first time. The first screen is the
// theorem itself, clause by clause, with Lean beside the mathematics, and the way into
// reading a paper (heroMarkup.ts; the build puts it in the HTML), then the two films. The
// levels band shows the same argument
// narrowing from the Lean through the three papers, and doubles as the shelf of papers.
// Then what OpenAI's release asked and proved, with where each result is explained here;
// the mathematics of the proof with the exposition's two figures; and what has been
// checked. The mathematical prose follows the papers' own statements and attributions
// (audited against them, claim by claim). Every number taken from the edition or the PDFs
// is computed; the films come from the family registry (app/family.json).

import { useEffect } from "react";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import { SITE_FACTS } from "virtual:site-facts";
import { useEdition } from "../app/data";
import { routeHref, useRoute } from "../app/router";
import { AUTHOR, LINKS } from "../app/author";
import { familyFilm } from "../app/family";
import { FilmSlot } from "../app/FilmSlot";
import { SisterSites } from "../app/SisterSites";
import { PAPERS_ANCHOR } from "../app/TopBar";
import { Out } from "../app/Out";
import { LINK_CAVEAT } from "../app/caveat";
import { CHECK_KINDS, CHECK_ORDER, STATUS_WORDS, outcomeCounts } from "../checks/summary";
import { FrontHeroBody } from "./FrontHero";
import { LevelsBand } from "./LevelsBand";
import { Rich, texHtml } from "../figures/tex";
import { GapFigure } from "../figures/GapFigure";
import { AreaFigure } from "../figures/AreaFigure";
import "./front.css";

const plural = (n: number, one: string, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;

/** OpenAI's mathematics release, at the revision the three accounts cite. */
const RELEASE = "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a";
const RELEASE_TREE = "https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a";
const FAMILY_SCOPE = `${RELEASE}/lean/docs/281.md`;
const SUPPORT_PDF = `${RELEASE}/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf`;
const QAOA_PDF = `${RELEASE}/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf`;
const LEAN_SOURCE = `${RELEASE_TREE}/lean/OAI/Probability`;
const SOURCE_REPOSITORY = "https://github.com/wcook04/lean-exposition#readme";

/** The Lean modules in the vendored tree, as the edition's index counts them. */
const LEAN_MODULES = SITE_FACTS.lean?.modules ?? null;

/** The films this site holds a place for, and the released film the mathematics one will be like. */
const SITE_FILM = familyFilm("interfaces");
const MATHS_FILM = familyFilm("sk-no-gap");

export function FrontPage() {
  const route = useRoute();
  const anchor = route.view === "home" ? route.anchor : undefined;
  // An address that names a band (the header's "Papers" is /#papers) opens the page there.
  useEffect(() => {
    if (anchor) requestAnimationFrame(() => document.getElementById(anchor)?.scrollIntoView({ block: "start" }));
  }, [anchor]);
  return (
    <div className="front">
      <FrontHeroBody />

      {/* The site walkthrough and the mathematics explanation, right under the theorem. */}
      <div className="front__films">
        <FilmSlot film={SITE_FILM} size="small" className="front__film" sizes="200px" />
        <FilmSlot film={MATHS_FILM} size="small" className="front__film" sizes="200px" />
      </div>

      <ReaderStill />

      <LevelsBand id={PAPERS_ANCHOR} leanModules={LEAN_MODULES} />

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
                <Rich src="No. Every minimiser increases across every interval in $[0,1)$, and its derivative is positive between $0$ and $1$. OpenAI (2026a) proved both in a manuscript, and the Lean has the increase but not the derivative. H.‑B. Chen (2026) had already proved that there are no flat stretches, by a different method." />
              </p>
              <p className="asked__where">
                Explained in all three papers:{" "}
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

      </section>

      <TechnicalExplanation />

      <section className="front__band checksband" aria-labelledby="front-checks">
        <div className="checksband__words">
          <h2 id="front-checks" className="front__bandtitle">
            What ran on this proof
          </h2>
          <p className="front__text">
            OpenAI’s repository has two statements written in Lean, each with a Lean proof: one of the full-support theorem, which
            assumes a minimiser, and one of the value identities and their finite Gaussian approximation.{" "}
            {SITE_FACTS.build && SITE_FACTS.extraction && (
              <>
                On {SITE_FACTS.build.date}, Lean {SITE_FACTS.build.toolchain.split(":").pop()?.replace(/^v/, "")} compiled the
                full-support tree without an error, and a program run inside Lean lists {SITE_FACTS.extraction.axioms.length} axioms for the theorem and no <code>sorry</code>.{" "}
              </>
            )}
            Comparator tests a proof against a separately written statement; it has accepted neither statement, and the second
            statement has no successful build on record. The failed and interrupted runs are listed on the same page as the others.
          </p>
          <p className="front__text">
            An exact calculation in rational arithmetic confirmed the 22 positive coefficients of the polynomial identity behind
            the curvature estimate; it says nothing about the analysis around that identity. The statements in each paper were compared with its sources, by AI agents for the exposition and the long record. No independent mathematical review
            has been done.
          </p>
        </div>
        <div className="checksband__table">
          <CheckTable />
          <p className="front__more">
            <a href={routeHref({ view: "checks" })}>What ran, with every outcome</a>
          </p>
        </div>
      </section>

      <section className="front__band front__sources-band" aria-labelledby="front-sources">
        <h2 id="front-sources" className="front__bandtitle">
          Where this comes from
        </h2>
        <ul className="elsewhere">
          <li>
            <Out href={FAMILY_SCOPE}>OpenAI’s release, family 281</Out> holds two manuscripts dated September 2026 and Lean code for
            two of their statements: the <Out href={SUPPORT_PDF}>full-support manuscript</Out>, the{" "}
            <Out href={QAOA_PDF}>QAOA manuscript</Out> and the <Out href={LEAN_SOURCE}>Lean source</Out>.
          </li>
          <li>
            <Out href={LINKS.atlasFamily}>Plectis Atlas, family 281</Out> is this family’s page on Plectis Atlas, another of{" "}
            {AUTHOR}’s websites: OpenAI’s two papers, their theorems beside the Lean statements, and what outside groups report
            about them.
          </li>
          <li>
            <Out href={SOURCE_REPOSITORY}>The source repository</Out> holds the papers, the steps of the argument and the software, with
            instructions for running the tools and building this website. The{" "}
            <a href={routeHref({ view: "about", anchor: "companion" })}>architectural companion</a> (
            <a href={`${import.meta.env.BASE_URL}${PAPER_PDFS.architecture.path}`} target="_blank" rel="noopener">
              PDF, {plural(PAPER_PDFS.architecture.pages, "page")}
            </a>
            ) gives the reasons for writing the result up this way.
          </li>
          <li>
            <a href={routeHref({ view: "about", anchor: "made-by" })}>Who made this site</a>: {AUTHOR}, for{" "}
            <Out href={LINKS.plectis}>Plectis</Out>, his projects on researching mathematics with AI and on tools that help
            people follow what AI produces. How this site fits with his other projects, with links to his videos, is on the
            About page.
          </li>
        </ul>
      </section>

      <footer className="front__foot">
        <div className="front__footrow">
          <a href={routeHref({ view: "about" })}>About this site</a>
          <a href={routeHref({ view: "about", anchor: "edition" })}>Edition and citation</a>
          <span className="front__byline">
            Made by <a href={routeHref({ view: "about", anchor: "made-by" })}>{AUTHOR}</a> for <Out href={LINKS.plectis}>Plectis</Out>
          </span>
        </div>
        <SisterSites />
      </footer>
    </div>
  );
}

const STILL_BASE = `${import.meta.env.BASE_URL}stills/reader-theorem-1`;
const STILL_ALT = "The short paper open at Theorem 1, with the theorem highlighted. Beside it are the theorem’s card on the graph of the proof and OpenAI’s Lean for it, with the lines that state it lit.";

/** A real capture of the reader, in the reader's scheme: the hidden one is never fetched (`loading="lazy"`). */
function ReaderStill() {
  const place = SITE_FACTS.theorem1;
  const open = routeHref({ view: "read", stage: "short", at: place?.at, node: place ? "full_support" : undefined, anchor: place?.anchor ?? undefined });
  const ties = SITE_FACTS.ties;
  return (
    <section className="front__band front__pair readerstill" aria-labelledby="front-reading">
      <div className="front__prose">
        <h2 id="front-reading" className="front__bandtitle">
          A paper beside its Lean
        </h2>
        <p>
          In the picture, a reader has clicked Theorem 1 of the short paper. The Lean has opened at the lines that state the theorem, and the paper has not moved.
        </p>
        {ties && (
          <p>
            The three papers have {ties.statements.toLocaleString("en-GB")} marked statements, {ties.withLean} of them with Lean. {LINK_CAVEAT}
          </p>
        )}
        <p>
          <a href={open}>Open this statement</a>
        </p>
      </div>
      <figure className="front__fig">
        <a href={open} className="readerstill__link" aria-label="Open Theorem 1 of the short paper with its Lean">
          {(["light", "dark"] as const).map((scheme) => (
            <img
              key={scheme}
              className={`readerstill__img readerstill__img--${scheme}`}
              src={`${STILL_BASE}-${scheme}-1440.webp`}
              srcSet={`${STILL_BASE}-${scheme}-1440.webp 1440w, ${STILL_BASE}-${scheme}-2880.webp 2880w`}
              sizes="(min-width: 68.75em) 66vw, 100vw"
              alt={STILL_ALT}
              width={1440}
              height={790}
              loading="lazy"
              decoding="async"
            />
          ))}
        </a>
      </figure>
    </section>
  );
}

/**
 * The first answer in technical terms, from the papers: the problem (exposition §§1–3),
 * how the proof rules out a gap (exposition §5, short paper §§2–4) and what follows
 * (exposition §6, short paper §5). Nothing here goes beyond what those passages state.
 */
function TechnicalExplanation() {
  return (
    <>
      <section className="front__band front__pair" aria-labelledby="front-question">
        <div className="front__prose">
          <h2 id="front-question" className="front__bandtitle">
            Choosing signs to maximise a random energy
          </h2>
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
          <h2 id="front-proof" className="front__bandtitle">
            How the proof rules out a gap
          </h2>
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
            the exposition cite it; the long record reconstructs its components.
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
        <h2 id="front-follows" className="front__bandtitle">
          What follows from it
        </h2>
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
    </>
  );
}

const COLUMNS = ["passed", "failed", "unavailable", "not_run"] as const;

/** The recorded checks by kind, and the links this site adds, each named for what it tests. */
function CheckTable() {
  const { map } = useEdition();
  const counts = outcomeCounts(map.records.evidence);
  const { ties, leanLinks, audit } = SITE_FACTS;
  return (
    <>
      <table className="checktable">
        <caption className="visually-hidden">The runs this site records, by kind and outcome</caption>
        <thead>
          <tr>
            <th scope="col">Kind of test</th>
            {COLUMNS.map((status) => (
              <th key={status} scope="col" className="checktable__n">
                {STATUS_WORDS[status].replace(/^./, (c) => c.toUpperCase())}
              </th>
            ))}
          </tr>
        </thead>
        <tbody>
          {CHECK_ORDER.filter((kind) => counts.has(kind)).map((kind) => (
            <tr key={kind}>
              <th scope="row">{CHECK_KINDS[kind]?.title ?? kind}</th>
              {COLUMNS.map((status) => {
                const n = counts.get(kind)?.[status] ?? 0;
                return (
                  <td key={status} className={`checktable__n${n === 0 ? " is-none" : ""}${status === "failed" && n ? " is-failed" : ""}`}>
                    {n}
                  </td>
                );
              })}
            </tr>
          ))}
        </tbody>
      </table>
      <p className="checktable__note">
        Each row counts one kind of recorded test, for example whether a cited file still has its recorded hash or whether a Lean project compiles.{" "}
        {ties && (
          <>
            AI agents also marked {ties.statements.toLocaleString("en-GB")} statements in the papers, {ties.withLean} of them with Lean,
            and tied them to the steps of the argument.{" "}
          </>
        )}
        {leanLinks && <>They made {leanLinks.links} links from steps to Lean, reaching {leanLinks.declarations} declarations. </>}
        {audit && <>AI agents then read the {audit.read} ties that had Lean against the source and changed {audit.changed}. A separate AI agent then read {audit.sampled} statements drawn at random from those with Lean: {audit.right} were right, {audit.loose} right but loosely worded and {audit.wrong} wrong, and those were corrected too. The other statements with Lean were not read a second time.</>}
        A program confirms that both ends of each one still exist. No independent mathematician has reviewed them.
      </p>
    </>
  );
}

// The Erdős #257 front page. The first screen (hero.ts, built into index.html) is the title,
// the opening and the videos; then the levels band (the shelf of papers), the main theorem
// clause by clause (the second part of hero.ts's markup), what was asked, proved and left open, how the proof goes, what ran and where
// it comes from. Every sentence of the mathematics is the author's, from copy.ts; every
// number is read from the edition, the run receipts or the PDFs.

import { useEffect } from "react";
import { SITE_FACTS } from "virtual:site-facts";
import { RUN_LEDGER } from "virtual:run-ledger";
import { routeHref, useRoute } from "../../app/router";
import { AUTHOR, LINKS } from "../../app/author";
import { SisterSites } from "../../app/SisterSites";
import { PAPERS_ANCHOR } from "../../app/TopBar";
import { Out } from "../../app/Out";
import { CheckCounts } from "../../home/CheckCounts";
import { FrontHeroBody } from "../../home/FrontHero";
import { LevelsBand } from "../../home/LevelsBand";
import { Rich } from "../../figures/tex";
import { countsInWords } from "../../checks/summary";
import { COPY } from "./copy";
import { Elsewhere } from "./Elsewhere";
import "../../home/front.css";

const n = (value: number) => value.toLocaleString("en-GB");

/** The id of "What was asked, what was proved and what stays open": old problem-page addresses land here (forward-map.json). */
export const ASKED_ANCHOR = "asked";

export function FrontPage() {
  const route = useRoute();
  const anchor = route.view === "home" ? route.anchor : undefined;
  useEffect(() => {
    if (anchor) requestAnimationFrame(() => document.getElementById(anchor)?.scrollIntoView({ block: "start" }));
  }, [anchor]);
  return (
    <div className="front front--wide">
      <FrontHeroBody part="first" />

      <LevelsBand id={PAPERS_ANCHOR} leanModules={SITE_FACTS.lean?.modules ?? null} />

      <FrontHeroBody part="rest" />

      <section className="front__band" id={ASKED_ANCHOR} aria-labelledby="front-asked">
        <h2 id="front-asked" className="front__bandtitle">
          What was asked, what was proved and what stays open
        </h2>
        <ol className="asked asked--three">
          {COPY.asked.map((entry, i) => (
            <li key={i}>
              <h3 className="asked__q">
                <Rich src={entry.asked} />
              </h3>
              <div className="asked__a">
                <p>
                  <span className="asked__label">Proved. </span>
                  <Rich src={entry.proved} />
                </p>
                <p>
                  <span className="asked__label">Open. </span>
                  <Rich src={entry.open} />
                </p>
                {entry.goal && (
                  <p className="asked__where">
                    <a href={routeHref({ view: "map", goal: entry.goal })}>Its argument on the map</a>
                  </p>
                )}
              </div>
            </li>
          ))}
        </ol>
      </section>

      <section className="front__band" aria-labelledby="front-proof">
        <h2 id="front-proof" className="front__bandtitle">
          How the proof goes
        </h2>
        <ol className="proofsteps">
          {COPY.proofSteps.map((step, i) => (
            <li key={i}>
              <h3>
                <Rich src={step.title} />
              </h3>
              <p>
                <Rich src={step.text} />
              </p>
            </li>
          ))}
        </ol>
      </section>

      <section className="front__band checksband" aria-labelledby="front-checks">
        <div className="checksband__words">
          <h2 id="front-checks" className="front__bandtitle">
            What ran on this proof
          </h2>
          <RunWords />
        </div>
        <div className="checksband__table">
          <CheckCounts />
          <TieWords />
          <p className="front__more">
            <a href={routeHref({ view: "checks" })}>What ran, with every outcome</a>
          </p>
        </div>
      </section>

      <Elsewhere id="front-elsewhere" className="front__band" />

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

/** One sentence per kind of run with receipts, from the receipts themselves. */
function RunWords() {
  if (!RUN_LEDGER.groups.length) return <p className="front__text">No run with a receipt is recorded for this edition.</p>;
  return (
    <ul className="front__text runwords">
      {RUN_LEDGER.groups.map((group) => {
        const dates = [...new Set(group.rows.map((row) => row.date).filter(Boolean))];
        return (
          <li key={group.type}>
            <strong>{group.title}</strong>: {n(group.rows.length)}, {countsInWords(group.counts)}
            {dates.length === 1 ? `, on ${dates[0]}` : dates.length > 1 ? `, from ${dates[0]} to ${dates[dates.length - 1]}` : ""}.
          </li>
        );
      })}
    </ul>
  );
}

/** The links to Lean; the ties and who made them are counted once, on the first screen. */
function TieWords() {
  const { ties, leanLinks } = SITE_FACTS;
  if (!ties) return null;
  return (
    <p className="checktable__note">
      {leanLinks && <>The records have {n(leanLinks.links)} links to Lean, reaching {n(leanLinks.declarations)} declarations. </>}
      A program confirms that both ends of each tie still exist.
    </p>
  );
}

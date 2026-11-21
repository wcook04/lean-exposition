// About: one line for each of the site's routes, how to use the site (marks, clicks, keys,
// feedback), then what the site
// is, a key to the map's drawing, the edition it serves (with edition-pinned link and
// citation), the architectural companion on request, and who made it. The companion is
// not served by the API; it is read from the repository at build time, so it always
// matches the checkout the site was built from.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import source from "../../../../papers/architecture/paper.md?raw";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import { SITE_FACTS } from "virtual:site-facts";
import type { Route } from "../../app/router";
import { routeHref } from "../../app/router";
import { useEdition, useResource } from "../../app/data";
import { loadLeanModules } from "../../api/lean";
import { useAlignment } from "../../compare/useAlignment";
import { AUTHOR, LINKS } from "../../app/author";
import { clockTime, familyFilm, type FamilyFilm } from "../../app/family";
import { FilmSlot } from "../../app/FilmSlot";
import { SisterSites } from "../../app/SisterSites";
import { Out } from "../../app/Out";
import { LINK_CAVEAT } from "../../app/caveat";
import { AboutEdition, AboutKey, AboutUsing } from "../../reader/aboutParts";
import { prepareDocument } from "../../reader/engine";
import { prefixPaths } from "../../reader/links";
import { documentPaths } from "../../reader/documents";
import { mountFigures } from "../../reader/mount";
import "../../reader/reader-content.css";
import "../../reader/about.css";

const COMPANION = "companion";

/** His released films closest to this result, each with what it shows, from the family registry. */
const RELATED_FILMS: { film: FamilyFilm; shows: string }[] = [
  { film: familyFilm("long-lean-readers"), shows: "This site and his two other reader websites, each with a paper open beside its Lean." },
  { film: familyFilm("mathematics"), shows: "A walkthrough of his work on one Erdős problem, from the question to the formal proof." },
  { film: familyFilm("mathematics-overview"), shows: "A tour of the maths map, including the long record and the papers for problem #257." },
  { film: familyFilm("atlas"), shows: "One result followed through Plectis Atlas, its claims compared with the formal statement." },
];
const INTRODUCTION = familyFilm("introduction");
const WALKTHROUGH = familyFilm("short-sk-website");

/** A released film as a line of the list: its title, opening YouTube, and its length. */
function FilmLink({ film }: { film: FamilyFilm }) {
  const seconds = film.duration_seconds;
  if (!film.youtube) return <span>{film.title}</span>;
  return (
    <>
      <Out href={film.youtube}>{film.title}</Out>
      {seconds ? <span className="about__len">{clockTime(seconds)}</span> : null}
    </>
  );
}

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  const { map } = useEdition();
  const checks = map.records.evidence;
  const mostNotRun = checks.filter((c) => c.status === "not_run").length * 2 > checks.length;
  const ties = SITE_FACTS.ties;
  const prose = useRef<HTMLDivElement>(null);
  // Both sidecars load only on this page, and their counts simply stay away if an edition has none.
  const alignment = useAlignment();
  const lean = useResource("about-lean-modules", () => loadLeanModules().catch(() => null));
  const leanRows = lean.status === "ready" && lean.value ? lean.value.folders.flatMap((f) => f.modules) : null;
  const leanLinks = alignment ? Object.values(alignment.records).reduce((n, r) => n + r.lean.length, 0) : null;
  // A link into the companion (any fragment other than the edition facts) opens it.
  const [companion, setCompanion] = useState(!!route.anchor && route.anchor !== "edition");

  const prepared = useMemo(() => {
    const bytes = new TextEncoder().encode(source);
    const doc = prepareDocument({
      stage: "architecture",
      bytes,
      documentPath: "architecture/paper.md",
      documentPaths: prefixPaths(documentPaths(), "qaoa-sk/"),
    });
    return { html: doc.renderAll().map((p) => p.html).join("\n"), front: doc.frontMatter ?? {} };
  }, []);

  const title = String(prepared.front.title ?? "The architectural companion");
  const subtitle = prepared.front.subtitle ? String(prepared.front.subtitle) : null;
  const date = prepared.front.date ? String(prepared.front.date) : null;

  useLayoutEffect(() => {
    const el = prose.current;
    if (!el || !companion) return;
    // Fresh slots on every mount: mountFigures marks a slot as mounted and
    // unmounts its roots after a tick, so reusing slots (as React's strict
    // mode does by running effects twice) would leave them empty.
    el.innerHTML = prepared.html;
    return mountFigures(el);
  }, [prepared, companion]);

  useEffect(() => {
    if (!route.anchor) return;
    if (route.anchor !== "edition") setCompanion(true);
    requestAnimationFrame(() => document.getElementById(route.anchor!)?.scrollIntoView({ block: "start" }));
  }, [route.anchor]);


  return (
    <article className="about">
      <header className="about__intro">
        <h1>About this site</h1>
        <p className="about__lede">
          This site holds three papers on one theorem about the Sherrington–Kirkpatrick (SK) spin glass, from OpenAI’s mathematics release, with OpenAI’s proof beside the text. That proof is written in Lean, a programming language whose compiler rejects a proof with a wrong step. You read a paper as you would any paper. Each phrase that a Lean declaration states is underlined in the colour of its topic, and clicking it opens that Lean with a plain title, whether the Lean states the same as the phrase, more or less, and a reading note drafted by an AI agent.
        </p>
      </header>

      <section className="about__use" aria-labelledby="about-use">
        <h2 id="about-use" className="visually-hidden">
          How to use this site
        </h2>
        <ol className="about__routes">
          <li>
            <a href={routeHref({ view: "read", stage: "short" })}>The papers</a>
            <span>Start here. An underlined phrase opens the Lean that states it beside the text, with a plain title, a comparison and an AI-drafted reading note, and a graph of the proof beside the paper moves to the statement you are reading.</span>
          </li>
          <li>
            <a href={routeHref({ view: "compare" })}>Compare</a>
            <span>Every step of the proof in a table: its Lean and its statement in each paper, side by side.</span>
          </li>
          <li>
            <a href={routeHref({ view: "map" })}>The argument map</a>
            <span>The proof as a drawing, from the theorem down. Beside each paper the site draws the steps of the section you are reading.</span>
          </li>
          <li>
            <a href={routeHref({ view: "checks" })}>What ran</a>
            <span>What passed, what failed and what was never run.{mostNotRun ? " Most have not been run." : ""}</span>
          </li>
          <li>
            <a href={routeHref({ view: "lean" })}>The Lean index</a>
            <span>
              OpenAI’s source, for those who want the files themselves
              {leanRows ? (
                <>
                  : <span className="num">{leanRows.length}</span> modules,{" "}
                  <span className="num">{leanRows.reduce((n, m) => n + m.declarations, 0).toLocaleString("en-GB")}</span> declarations
                </>
              ) : null}
              .
            </span>
          </li>
        </ol>
        <p className="about__watch">
          To see them in use, watch <FilmLink film={WALKTHROUGH} />.
        </p>
      </section>

      <AboutUsing />

      <section className="about__what" aria-labelledby="about-what">
        <h2 id="about-what">What this site is</h2>
        <p>
          There are three papers on the result. The <a href={routeHref({ view: "read", stage: "expository" })}>exposition</a>{" "}
          has the ideas, with worked examples. The <a href={routeHref({ view: "read", stage: "short" })}>short paper</a>{" "}
          has the result and its proof, for readers who know the field. The{" "}
          <a href={routeHref({ view: "read", stage: "long" })}>long record</a> has each step of the argument with the source it comes from.
        </p>
        <p>
          Each step of the argument is one entry in a graph: a claim, an assumption, or a declaration in Lean. Links between steps say which steps the argument for a result uses. Statements in the three papers are tied to the steps they state, explain or use
          {ties ? (
            <>
              : <span className="num">{ties.statements.toLocaleString("en-GB")}</span> marked statements, <span className="num">{ties.withLean}</span> of them with Lean, joined to steps by{" "}
              <span className="num">{ties.total.toLocaleString("en-GB")}</span> ties
            </>
          ) : null}
          {leanLinks !== null ? (
            <>
              . Another <span className="num">{leanLinks}</span> links join steps to Lean declarations
            </>
          ) : null}
          {SITE_FACTS.references ? (
            <>
              , and <span className="num">{SITE_FACTS.references}</span> references in the papers open in place
            </>
          ) : null}
          . {LINK_CAVEAT} The site adds layout and wording; it says what was recorded and no more.
        </p>
      </section>

      <AboutKey />

      <AboutEdition copied="The architectural companion and downloadable PDFs are copied separately from the same source checkout when the website is built." />

      <section className="about__companion" aria-labelledby="companion-title">
        <h2 id="companion-title">The architectural companion</h2>
        <p className="about__open-note">
          A longer paper, written for this project, on why the result is written up as three papers linked to one set of steps, and on how those steps and links are made.
        </p>
        <div className="about__copies">
          <button
            type="button"
            className="control about__open"
            aria-expanded={companion}
            aria-controls={COMPANION}
            onClick={() => setCompanion((open) => !open)}
          >
            {companion ? "Close the architectural companion" : "Read the architectural companion"}
          </button>
          <a className="control" href={`${import.meta.env.BASE_URL}${PAPER_PDFS.architecture.path}`} target="_blank" rel="noopener">
            Open the companion PDF, <span className="num">{PAPER_PDFS.architecture.pages} pages</span>
          </a>
        </div>
        <div id={COMPANION} hidden={!companion}>
          <header className="about__head">
            <h1>{title}</h1>
            {subtitle && <p className="about__subtitle">{subtitle}</p>}
            {date && <p className="about__date">{date}</p>}
          </header>
          <div ref={prose} className="prose about__prose" />
        </div>
      </section>

      <section className="about__made" id="made-by" aria-labelledby="made-by-title">
        <h2 id="made-by-title">Who made this site</h2>
        <p>
          {AUTHOR} made this site with AI agents, which wrote its code, its steps and its ties under his direction. The
          proof and its Lean are OpenAI’s. Hong-Bin Chen first proved full support in a July 2026 paper, and the earlier
          results are credited in the papers. The site belongs to{" "}
          <Out href={LINKS.plectis}>Plectis</Out>, his projects on researching mathematics with AI and on tools that help people
          follow what AI produces. His own research is on Erdős problems, questions posed by the mathematician Paul Erdős.
        </p>
        <p>
          Two of his other projects are the closest to this one. On his <Out href={LINKS.mathsMap}>maths map</Out> on Plectis you can see how the proofs, papers and explanations of his Erdős problem research connect. On{" "}
          <Out href={LINKS.atlas}>Plectis Atlas</Out>, the results in OpenAI’s mathematics release are set beside the outside
          reports that assess them, and family 281, the result explained here, has <Out href={LINKS.atlasFamily}>its own page</Out>.
          This site covers that one result in more depth, with an argument map of its proof and three papers on it, each linked to the map.
        </p>
        <p>
          Two videos go with this result: in one he goes through how to use this site, and in the other he explains the mathematics. His
          walkthrough of Erdős problem #257 is linked below.
        </p>
        <div className="about__films">
          <FilmSlot film={WALKTHROUGH} size="small" sizes="(min-width: 700px) 320px, 100vw" />
          <FilmSlot film={familyFilm("sk-no-gap")} size="small" sizes="(min-width: 700px) 320px, 100vw" />
        </div>
        <ul className="about__links">
          {RELATED_FILMS.map(({ film, shows }) => (
            <li key={film.id}>
              <FilmLink film={film} />
              <span>{shows}</span>
            </li>
          ))}
        </ul>
        <p>
          All his videos are on <Out href={LINKS.youtube}>his YouTube channel</Out>, and his public repositories are{" "}
          <Out href={LINKS.github}>on GitHub</Out>. To get in touch about collaboration, use the{" "}
          <Out href={LINKS.contact}>contact page on Plectis</Out>; he posts updates on <Out href={LINKS.x}>X</Out>.
        </p>
        <p className="about__start">
          An introduction to his work: <FilmLink film={INTRODUCTION} />
        </p>
        <SisterSites className="about__sisters" />
      </section>
    </article>
  );
}


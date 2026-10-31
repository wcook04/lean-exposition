// About: one line for each of the site's routes, then what the site
// is, a key to the map's drawing, the edition it serves (with edition-pinned link and
// citation), the architectural companion on request, and who made it. The companion is
// not served by the API; it is read from the repository at build time, so it always
// matches the checkout the site was built from.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import source from "../../../papers/architecture/paper.md?raw";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import type { Route } from "../app/router";
import { routeHref } from "../app/router";
import { useEdition, useResource } from "../app/data";
import { loadLeanModules } from "../api/lean";
import { useAlignment } from "../compare/useAlignment";
import { citationText, copyText, editionLink } from "../app/cite";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { AUTHOR, LINKS } from "../app/author";
import { familyFilm, minutesOf, type FamilyFilm } from "../app/family";
import { FilmSlot } from "../app/FilmSlot";
import { SisterSites } from "../app/SisterSites";
import { Out } from "../app/Out";
import { prepareDocument } from "./engine";
import { prefixPaths } from "./links";
import { documentPaths } from "./documents";
import { mountFigures } from "./mount";
import "./reader-content.css";
import "./about.css";

const RECORD_MEANINGS: { table: string; noun: string; meaning: string }[] = [
  { table: "nodes", noun: "records", meaning: "claims, assumptions, main results and Lean declarations" },
  { table: "edges", noun: "links", meaning: "each saying that one record is used in the argument for another, that a Lean declaration corresponds to a result, or that one record cites another" },
  { table: "citations", noun: "citations", meaning: "links from a record to a place in a source" },
  { table: "sources", noun: "sources", meaning: "papers and files, identified by address and, for files, by a hash of their bytes" },
  { table: "evidence", noun: "check records", meaning: "checks, including those planned but not run" },
];

const STATE_WORDS: Record<string, string> = {
  draft: "draft",
  needs_revision: "needs revision",
  approved: "approved",
  reviewed: "reviewed",
};

function words(value: string): string {
  return STATE_WORDS[value] ?? value.replace(/_/g, " ");
}

const COMPANION = "companion";

/** His released films closest to this result, each with what it shows, from the family registry. */
const RELATED_FILMS: { film: FamilyFilm; shows: string }[] = [
  { film: familyFilm("mathematics"), shows: "A walkthrough of his work on one Erdős problem, from the question to the formal proof." },
  { film: familyFilm("mathematics-overview"), shows: "A tour of the maths map, including the long record and the papers for problem #257." },
  { film: familyFilm("atlas"), shows: "One result followed through Plectis Atlas, its claims compared with the checked statement." },
];
const INTRODUCTION = familyFilm("introduction");
const WALKTHROUGH = familyFilm("interfaces");

/** A released film as a line of the list: its title, opening YouTube, and its length. */
function FilmLink({ film }: { film: FamilyFilm }) {
  const minutes = minutesOf(film);
  if (!film.youtube) return <span>{film.title}</span>;
  return (
    <>
      <Out href={film.youtube}>{film.title}</Out>
      {minutes ? <span className="about__len">{minutes} min</span> : null}
    </>
  );
}

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  const { snapshot, overview, graph, map } = useEdition();
  const checks = map.records.evidence;
  const mostNotRun = checks.filter((c) => c.status === "not_run").length * 2 > checks.length;
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

  const papers = STAGE_ORDER.map((stage) => overview.papers.find((p) => p.stage === stage)).filter((p) => !!p);
  const long = overview.papers.find((p) => p.stage === "long");
  const goal = (long?.paper_scope.selected_goal_ids ?? graph.goals).find((g) => graph.nodes.has(g));
  const goalLabel = goal ? graph.nodes.get(goal)!.label : null;

  return (
    <article className="about">
      <header className="about__intro">
        <h1>About this site</h1>
        <p className="about__lede">
          This site explains one theorem from OpenAI’s mathematics release
          {goalLabel ? (
            <>
              , <a href={routeHref({ view: "map", node: goal })}>{goalLabel}</a>,
            </>
          ) : null}{" "}
          at every level from its Lean source to a plain exposition.
        </p>
      </header>

      <section className="about__use" aria-labelledby="about-use">
        <h2 id="about-use" className="visually-hidden">
          How to use this site
        </h2>
        <ol className="about__routes">
          <li>
            <a href={routeHref({ view: "map" })}>The argument map</a>
            <span>The proof as a drawing, from the theorem down. Start here.</span>
          </li>
          <li>
            <a href={routeHref({ view: "compare" })}>Compare</a>
            <span>Every step of the proof in a table: its Lean and its statement in each paper, side by side.</span>
          </li>
          <li>
            <a href={routeHref({ view: "read", stage: "expository" })}>The reader</a>
            <span>A paper with the map following along, passage by passage.</span>
          </li>
          <li>
            <a href={routeHref({ view: "lean" })}>The Lean browser</a>
            <span>
              OpenAI’s source
              {leanRows ? (
                <>
                  : <span className="num">{leanRows.length}</span> modules,{" "}
                  <span className="num">{leanRows.reduce((n, m) => n + m.declarations, 0).toLocaleString("en-GB")}</span> declarations
                </>
              ) : null}
              .
            </span>
          </li>
          <li>
            <a href={routeHref({ view: "checks" })}>The checks</a>
            <span>What passed, what failed and what was never run.{mostNotRun ? " Most have not been run." : ""}</span>
          </li>
        </ol>
        <p className="about__watch">
          To see them in use, watch <FilmLink film={WALKTHROUGH} />.
        </p>
      </section>

      <section className="about__what" aria-labelledby="about-what">
        <h2 id="about-what">What this site is</h2>
        <p>
          The result has three written accounts. The <a href={routeHref({ view: "read", stage: "expository" })}>exposition</a>{" "}
          explains the ideas with worked examples. The <a href={routeHref({ view: "read", stage: "short" })}>short paper</a>{" "}
          states the result and proves it for readers who know the field. The{" "}
          <a href={routeHref({ view: "read", stage: "long" })}>long record</a> reconstructs each step of the argument and names
          the source each step comes from.
        </p>
        <p>
          Each step of the argument is stored as a record: a claim, an assumption, or a declaration in Lean, a language in
          which a computer can check proofs. Links between records say which records the argument for a result uses. Passages
          in the three accounts are linked to the records they discuss
          {leanLinks !== null ? (
            <>
              , and <span className="num">{leanLinks}</span> authored links join records to Lean declarations
            </>
          ) : null}
          . The site adds layout and wording; the records say what was recorded and no more.
        </p>
      </section>

      <section className="about__key" aria-labelledby="about-key">
        <h2 id="about-key">How the argument map is drawn</h2>
        <ul className="about__keylist">
          <li>
            <span className="about__sample">
              {graph.origins
                .filter((o) => o.slot > 0)
                .map((o) => (
                  <span key={o.family} className="src-sq" data-slot={o.slot} aria-hidden="true" />
                ))}
              <span className="src-sq" data-slot={0} aria-hidden="true" />
            </span>
            <span>
              Each record has a small coloured square and the name of the source it comes from. Records from the same source
              have the same colour.
            </span>
          </li>
          <li>
            <span className="about__sample about__sample--lines" aria-hidden="true">
              <span className="rel-sample" />
              <span className="rel-sample rel-sample--formalizes" />
            </span>
            <span>
              A line joins a record to a result whose argument uses it, with the arrowhead at the result. A grey, solid line
              is a recorded use. A cyan, dashed line joins a result to the Lean declaration recorded as corresponding to it.
            </span>
          </li>
          <li>
            <span className="about__sample" aria-hidden="true">
              <span className="about__tag">Assumes</span>
            </span>
            <span>
              An assumption is a violet tag with a dotted border, shown on each result that assumes it. When several results
              use a record that has no recorded inputs of its own, the record is drawn under each of them, with a coloured
              band along the bottom of each copy.
            </span>
          </li>
          <li>
            <span className="about__sample" aria-hidden="true">
              <span className="rel-sample rel-sample--lit" />
            </span>
            <span>
              Amber outlines the record or link you have selected, and the keyboard focus. When you trace what a record rests
              on, its grey lines turn amber; assumption tags and Lean lines on the traced route keep their own colours and
              are drawn brighter.
            </span>
          </li>
        </ul>
        <p className="about__keynote">
          The <a href={routeHref({ view: "map" })}>argument map</a>’s Key button says the rest in words, with its keyboard
          controls. On the checks page each outcome is written as a word, and only a failed outcome is shown in colour.
        </p>
      </section>

      <section className="about__serves" id="edition" aria-labelledby="serves">
        <h2 id="serves">The edition you are reading</h2>
        <p>
          The records and the three accounts belong to one captured edition, a fixed set of files identified below. The
          published website includes that capture. When run against the local read-only server, the site pins requests to
          the same edition and asks you to reload if the server changes it. The architectural companion and downloadable
          PDFs are copied separately from the same source checkout when the website is built.
        </p>
        <dl className="facts">
          <div>
            <dt>Edition</dt>
            <dd>
              Bundle <code translate="no">{snapshot.bundle_id}</code>, version {snapshot.bundle_version}. Manifest SHA-256{" "}
              <code translate="no" className="about__hash">
                {snapshot.manifest_sha256}
              </code>
              <span className="about__copies">
                <CopyButton label="Copy link to this edition" text={() => editionLink({ view: "map" }, snapshot)} />
                <CopyButton
                  label="Copy citation"
                  text={() => citationText({ place: goalLabel ?? undefined }, { view: "map", node: goal }, snapshot)}
                />
              </span>
            </dd>
          </div>
          <div>
            <dt>Accounts</dt>
            <dd>
              <ul>
                {papers.map((p) => (
                  <li key={p.stage}>
                    <a href={routeHref({ view: "read", stage: p.stage })}>{PAPER_NAMES[p.stage].short}</a>: {words(p.state)},{" "}
                    {words(p.review_state)}; {p.passages} passages linked to records, in {p.sections} sections.
                  </li>
                ))}
              </ul>
            </dd>
          </div>
          <div>
            <dt>Records</dt>
            <dd>
              <ul>
                {RECORD_MEANINGS.filter((r) => overview.record_counts[r.table] !== undefined).map((r) => (
                  <li key={r.table}>
                    <span className="num">{overview.record_counts[r.table]}</span> {r.noun}: {r.meaning}.
                  </li>
                ))}
              </ul>
            </dd>
          </div>
          <div>
            <dt>Run it yourself</dt>
            <dd>
              <code>lean-exposition serve</code> starts the read-only server, and <code>npm run dev</code> in <code>site/</code>{" "}
              starts this site. The repository’s <code>site/README.md</code> lists the full commands.
            </dd>
          </div>
        </dl>
      </section>

      <section className="about__companion" aria-labelledby="companion-title">
        <h2 id="companion-title">The architectural companion</h2>
        <p className="about__open-note">
          A longer paper, written for this project, on why the result is written up as three accounts linked to one set of
          records, and on how those records and links are made.
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
          {AUTHOR} made this site. It is one part of <Out href={LINKS.plectis}>Plectis</Out>, his projects on researching
          mathematics with AI and on tools that help people follow what AI produces. His own research is on Erdős problems,
          questions posed by the mathematician Paul Erdős.
        </p>
        <p>
          Two of his other projects sit closest to this one. His <Out href={LINKS.mathsMap}>maths map</Out> on Plectis lets
          you see how the proofs, papers and explanations of his Erdős problem research connect. On{" "}
          <Out href={LINKS.atlas}>Plectis Atlas</Out>, the results in OpenAI’s mathematics release are set beside the outside
          reports that assess them, and family 281, the result explained here, has <Out href={LINKS.atlasFamily}>its own page</Out>.
          Here that one result is taken further: an argument map of its proof, and three written accounts of it, each linked
          to the map.
        </p>
        <p>
          Two films accompany this result: one shows how to use this site, and one explains the mathematics. His
          walkthrough of Erdős problem #257 is linked below.
        </p>
        <div className="about__films">
          <FilmSlot film={familyFilm("interfaces")} size="small" sizes="(min-width: 700px) 320px, 100vw" />
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
          New to his work? Start here: <FilmLink film={INTRODUCTION} />
        </p>
        <SisterSites className="about__sisters" />
      </section>
    </article>
  );
}

/** A copy action that says what happened, and offers the text when the browser refuses. */
function CopyButton({ label, text }: { label: string; text: () => string }) {
  const [state, setState] = useState<{ status: "idle" } | { status: "copied" } | { status: "manual"; text: string }>({ status: "idle" });
  useEffect(() => {
    if (state.status !== "copied") return;
    const timer = window.setTimeout(() => setState({ status: "idle" }), 2400);
    return () => window.clearTimeout(timer);
  }, [state]);
  return (
    <span className="copyact">
      <button
        type="button"
        className="control copyact__button"
        onClick={async () => {
          const value = text();
          setState((await copyText(value)) ? { status: "copied" } : { status: "manual", text: value });
        }}
      >
        {label}
      </button>
      <span className="copyact__status" role="status">
        {state.status === "copied" ? "Copied" : ""}
      </span>
      {state.status === "manual" && (
        <textarea className="copyact__manual" readOnly value={state.text} aria-label={`${label}: select and copy`} rows={3} onFocus={(e) => e.currentTarget.select()} />
      )}
    </span>
  );
}

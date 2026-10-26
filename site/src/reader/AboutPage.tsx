// About: a short authored introduction to what the site is, a small key to
// its visual language, the edition it serves (with edition-pinned link and
// citation), and the architectural companion paper on request. The paper is
// not served by the API; it is read from the repository at build time, so it
// always matches the checkout the site was built from.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import source from "../../../papers/architecture/paper.md?raw";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import type { Route } from "../app/router";
import { routeHref } from "../app/router";
import { useEdition } from "../app/data";
import { citationText, copyText, editionLink } from "../app/cite";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { AUTHOR, LINKS, VIDEOS } from "../app/author";
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

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  const { snapshot, overview, graph, map } = useEdition();
  const checks = map.records.evidence;
  const mostNotRun = checks.filter((c) => c.status === "not_run").length * 2 > checks.length;
  const prose = useRef<HTMLDivElement>(null);
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
          This site presents one mathematical result
          {goalLabel ? (
            <>
              , <a href={routeHref({ view: "map", node: goal })}>{goalLabel}</a>,
            </>
          ) : null}{" "}
          and three written accounts of it. The <a href={routeHref({ view: "read", stage: "expository" })}>exposition</a>{" "}
          explains the ideas with worked examples. The <a href={routeHref({ view: "read", stage: "short" })}>short paper</a>{" "}
          states the result and proves it for readers who know the field. The{" "}
          <a href={routeHref({ view: "read", stage: "long" })}>long record</a> reconstructs each step of the argument and names
          the source each step comes from.
        </p>
        <p className="about__lede">
          Each step of the argument is stored as a record: a claim, an assumption, or a declaration in Lean, a language in
          which a computer can check proofs. Links between records say which records the argument for a result uses. Passages
          in the three accounts are linked to the records they discuss, so from a passage you can open its records, and from
          a record you can open the passages about it.
        </p>
        <p className="about__lede">
          Some records have <a href={routeHref({ view: "checks" })}>checks</a> attached, for example whether a cited file still
          has its recorded hash, or whether a Lean project compiles. Each check has a recorded outcome: passed, failed,
          unavailable or not run.{mostNotRun ? " Most checks on this site have not been run." : ""}
        </p>
      </header>

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
          A word in small capitals on each card names the kind of record: claim, assumption, main result or Lean declaration.
          Only assumption cards have a dashed border. When you choose an account under “Records used by”, each card carries one
          of three marks: the record has a passage of its own in that account, the account uses it without a passage of its
          own, or the account does not use it.
        </p>
        <p className="about__keynote">
          The map has three views. Steps opens the main result at reading size. Overview fits the whole argument on the
          screen; as you zoom out, each card first shows only its title and then becomes a small tile in its source’s colour,
          which keeps its title for as long as the tile has room for it. Outline shows the same argument as a list you scroll.
          Scrolling up or down zooms in and out around the pointer, and dragging moves the map.
        </p>
        <p className="about__keynote">
          Clicking a card opens its record in a panel, opens every record below it, and moves the map so that the card and
          all of those records are in view. Clicking an empty part of the map closes the panel and puts the map back as it
          was. Resting the pointer on a card draws the records below it at half strength until the pointer leaves. The
          card’s “Inputs” button, or the Space key, draws only the records it uses directly, and the arrow keys move between
          cards. Pointing at a line shows a short description of that step, and
          selecting the line opens the step. “Show all branches” and “Collapse branches”, at the bottom right of the map, open
          or close every branch at once.
        </p>
        <p className="about__keynote">
          The key row under the <a href={routeHref({ view: "map" })}>argument map</a>’s header shows the colours, lines and
          marks in short; the Key button shows or hides it. On the checks page each outcome is written as a word, and only a
          failed outcome is shown in colour.
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
        <h2 id="companion-title" className="visually-hidden">
          The architectural companion
        </h2>
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
          <a className="control" href={`${import.meta.env.BASE_URL}${PAPER_PDFS.architecture.path}`}>
            Companion PDF <span className="num">({PAPER_PDFS.architecture.pages} pages)</span>
          </a>
        </div>
        <p className="about__open-note">
          A longer paper, written for this project, on why the result is written up as three accounts linked to one set of
          records, and on how those records and links are made.
        </p>
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
          A walkthrough video of this result is planned but not yet recorded. It will be like his walkthrough of Erdős
          problem #257, the first video below.
        </p>
        <ul className="about__links">
          <li>
            <Out href={VIDEOS.erdos257.url}>{VIDEOS.erdos257.title}</Out>
            <span className="about__len">{VIDEOS.erdos257.minutes} min</span>
            <span>A walkthrough of his work on one Erdős problem, from the question to the formal proof.</span>
          </li>
          <li>
            <Out href={VIDEOS.mathsMap.url}>{VIDEOS.mathsMap.title}</Out>
            <span className="about__len">{VIDEOS.mathsMap.minutes} min</span>
            <span>A tour of the maths map, including the long record and the papers for problem #257.</span>
          </li>
          <li>
            <Out href={VIDEOS.atlas.url}>{VIDEOS.atlas.title}</Out>
            <span className="about__len">{VIDEOS.atlas.minutes} min</span>
            <span>One result followed through Plectis Atlas, its claims compared with the checked statement.</span>
          </li>
        </ul>
        <p>
          All his videos are on <Out href={LINKS.youtube}>his YouTube channel</Out>, and his public repositories are{" "}
          <Out href={LINKS.github}>on GitHub</Out>. To get in touch about collaboration, use the{" "}
          <Out href={LINKS.contact}>contact page on Plectis</Out>; he posts updates on <Out href={LINKS.x}>X</Out>.
        </p>
        <p className="about__start">
          New to his work? Start here: <Out href={VIDEOS.introduction.url}>{VIDEOS.introduction.title}</Out>
          <span className="about__len">{VIDEOS.introduction.minutes} min</span>
        </p>
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

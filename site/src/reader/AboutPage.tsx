// The architectural companion paper, rendered with the same engine as the
// three accounts, followed by a factual note on what this site serves.
// The paper is not served by the API; it is read from the repository at
// build time, so it always matches the checkout the site was built from.

import { useEffect, useLayoutEffect, useMemo, useRef } from "react";
import source from "../../../papers/architecture/paper.md?raw";
import type { Route } from "../app/router";
import { routeHref } from "../app/router";
import { useEdition } from "../app/data";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { prepareDocument } from "./engine";
import { prefixPaths } from "./links";
import { documentPaths } from "./documents";
import { mountFigures } from "./mount";
import "./reader-content.css";
import "./about.css";

const RECORD_MEANINGS: { table: string; noun: string; meaning: string }[] = [
  { table: "nodes", noun: "nodes", meaning: "claims, assumptions, goals and Lean statements" },
  { table: "edges", noun: "edges", meaning: "recorded relations between them, such as one claim supporting another" },
  { table: "citations", noun: "citations", meaning: "pointers from a record to a place in a source" },
  { table: "sources", noun: "sources", meaning: "files and publications, identified by address and, for files, by hash" },
  { table: "evidence", noun: "evidence records", meaning: "checks, including those planned but not run" },
];

const STATE_WORDS: Record<string, string> = {
  draft: "draft",
  needs_revision: "review asks for revision",
  approved: "review approved",
  reviewed: "reviewed",
};

function words(value: string): string {
  return STATE_WORDS[value] ?? value.replace(/_/g, " ");
}

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  const { snapshot, overview } = useEdition();
  const prose = useRef<HTMLDivElement>(null);

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

  const title = String(prepared.front.title ?? "About this site");
  const subtitle = prepared.front.subtitle ? String(prepared.front.subtitle) : null;
  const date = prepared.front.date ? String(prepared.front.date) : null;

  useEffect(() => {
    document.title = `About: ${title}`;
  }, [title]);

  useLayoutEffect(() => {
    const el = prose.current;
    if (!el) return;
    // Fresh slots on every mount: mountFigures marks a slot as mounted and
    // unmounts its roots after a tick, so reusing slots (as React's strict
    // mode does by running effects twice) would leave them empty.
    el.innerHTML = prepared.html;
    return mountFigures(el);
  }, [prepared]);

  useEffect(() => {
    if (!route.anchor) return;
    const el = document.getElementById(route.anchor);
    if (el) requestAnimationFrame(() => el.scrollIntoView({ block: "start" }));
  }, [route.anchor]);

  const papers = STAGE_ORDER.map((stage) => overview.papers.find((p) => p.stage === stage)).filter((p) => !!p);

  return (
    <article className="about">
      <p className="about__note">
        This page is the project’s own explanation of why one result is written up as three accounts that share one
        record. To read the mathematics instead, start with the <a href={routeHref({ view: "read", stage: "expository" })}>exposition</a> or
        open the <a href={routeHref({ view: "map" })}>argument map</a>.
      </p>

      <header className="about__head">
        <h1>{title}</h1>
        {subtitle && <p className="about__subtitle">{subtitle}</p>}
        {date && <p className="about__date">{date}</p>}
      </header>

      <div ref={prose} className="prose about__prose" />

      <section className="about__serves" aria-labelledby="serves">
        <h2 id="serves">What this site serves</h2>
        <p>
          One captured edition, read from a local read-only server. Every request names the edition, so a server
          that changes edition mid-visit is noticed rather than mixed in.
        </p>
        <dl className="facts">
          <div>
            <dt>Edition</dt>
            <dd>
              Bundle <code translate="no">{snapshot.bundle_id}</code>, version {snapshot.bundle_version}. Its manifest’s
              SHA-256 begins <code translate="no">{snapshot.manifest_sha256.slice(0, 12)}</code>.
            </dd>
          </div>
          <div>
            <dt>Accounts</dt>
            <dd>
              <ul>
                {papers.map((p) => (
                  <li key={p.stage}>
                    <a href={routeHref({ view: "read", stage: p.stage })}>{PAPER_NAMES[p.stage].short}</a>: {words(p.state)},{" "}
                    {words(p.review_state)}; {p.passages} mapped passages in {p.sections} sections.
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
              Start the reading server with <code>lean-exposition serve</code> and this site with <code>npm run dev</code> in{" "}
              <code>site/</code>. The repository’s <code>site/README.md</code> gives the steps.
            </dd>
          </div>
        </dl>
      </section>
    </article>
  );
}

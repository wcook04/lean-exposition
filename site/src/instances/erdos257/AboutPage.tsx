// The Erdős #257 About page: the author's sections from copy.ts, then the parts every
// instance shares (how to use the site, how the map is drawn, the edition), then who made
// it. The SK site's architectural companion is not shown here; its PDF is not part of this
// edition.

import { useEffect } from "react";
import type { Route } from "../../app/router";
import { routeHref } from "../../app/router";
import { useEdition } from "../../app/data";
import { AUTHOR, LINKS } from "../../app/author";
import { SisterSites } from "../../app/SisterSites";
import { Out } from "../../app/Out";
import { LINK_CAVEAT } from "../../app/caveat";
import { Rich } from "../../figures/tex";
import { AboutEdition, AboutKey, AboutUsing } from "../../reader/aboutParts";
import { COPY } from "./copy";
import { Elsewhere } from "./Elsewhere";
import "../../reader/reader-content.css";
import "../../reader/about.css";

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  const { map } = useEdition();
  const checks = map.records.evidence;
  const mostNotRun = checks.filter((c) => c.status === "not_run").length * 2 > checks.length;
  useEffect(() => {
    if (route.anchor) requestAnimationFrame(() => document.getElementById(route.anchor!)?.scrollIntoView({ block: "start" }));
  }, [route.anchor]);
  return (
    <article className="about">
      <header className="about__intro">
        <h1>About this site</h1>
      </header>

      <section className="about__use" aria-labelledby="about-use">
        <h2 id="about-use" className="visually-hidden">
          The parts of this site
        </h2>
        <ol className="about__routes">
          <li>
            <a href={routeHref({ view: "read", stage: "short" })}>The papers</a>
            <span>Start here. An underlined phrase opens the Lean that states it beside the text, with a plain title, a comparison and an AI-drafted reading note, and a graph of the proof beside the paper moves to the statement you are reading.</span>
          </li>
          <li>
            <a href={routeHref({ view: "compare" })}>Compare</a>
            <span>Every step of the proof in a table: its Lean and its statement in each paper, side by side, with what the Lean says against each paper where that has been compared.</span>
          </li>
          <li>
            <a href={routeHref({ view: "map" })}>The argument map</a>
            <span>The proof as a drawing, from the theorem down.</span>
          </li>
          <li>
            <a href={routeHref({ view: "checks" })}>What ran</a>
            <span>Every recorded run, where and when it ran, passed or not.{mostNotRun ? " Most run records describe a run that has not happened." : ""}</span>
          </li>
          <li>
            <a href={routeHref({ view: "lean" })}>The Lean index</a>
            <span>The Lean source, for those who want the files themselves.</span>
          </li>
        </ol>
      </section>

      {COPY.about.map((section, i) => (
        <section className="about__what" key={i} aria-labelledby={`about-${i}`}>
          <h2 id={`about-${i}`}>
            <Rich src={section.heading} />
          </h2>
          {section.paragraphs.map((text, j) => (
            <p key={j}>
              <Rich src={text} />
            </p>
          ))}
        </section>
      ))}

      <section className="about__what" aria-labelledby="about-ties">
        <h2 id="about-ties">Who linked the papers to the Lean</h2>
        <p>{LINK_CAVEAT}</p>
      </section>

      <Elsewhere id="about-elsewhere" className="about__what" />

      <AboutUsing />

      <AboutKey />

      <AboutEdition copied="The downloadable PDFs are copied separately from the same source checkout when the website is built." />

      <section className="about__made" id="made-by" aria-labelledby="made-by-title">
        <h2 id="made-by-title">Who made this site</h2>
        <p>
          <Rich src={COPY.credit} />
        </p>
        <p>
          The site belongs to <Out href={LINKS.plectis}>Plectis</Out>, {AUTHOR}’s projects on researching mathematics with AI and on tools that help people follow what AI produces. His videos are on{" "}
          <Out href={LINKS.youtube}>his YouTube channel</Out>, and his public repositories are <Out href={LINKS.github}>on GitHub</Out>. To get in touch, use the{" "}
          <Out href={LINKS.contact}>contact page on Plectis</Out>.
        </p>
        <SisterSites className="about__sisters" />
      </section>
    </article>
  );
}

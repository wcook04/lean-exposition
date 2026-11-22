// About one library paper: who wrote it, where it comes from, how the links were made and
// that no mathematician has reviewed them. Every sentence about the paper is its data's.
import { useEffect } from "react";
import type { Route } from "../../app/router";
import { routeHref } from "../../app/router";
import { Out } from "../../app/Out";
import { AboutKey, AboutUsing } from "../../reader/aboutParts";
import { PAPER, MAIN, LIBRARY_ROOT } from "./data";

const ADAPTED = PAPER.documents.find((d) => d.kind === "adapted");
const AUTHORS = (ADAPTED && PAPER.documents.find((d) => d.id === ADAPTED.of)) || MAIN;
import { SupplementaryChecks } from "./Checks";
import { ComparatorSection } from "./Comparator";
import "../../reader/reader-content.css";
import "../../reader/about.css";

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  useEffect(() => {
    if (route.anchor) requestAnimationFrame(() => document.getElementById(route.anchor!)?.scrollIntoView({ block: "start" }));
  }, [route.anchor]);
  const up = PAPER.source.upstream;
  return (
    <article className="about">
      <header className="about__intro">
        <h1>{PAPER.title}</h1>
        <p>By {PAPER.authors.join(", ")}.</p>
      </header>
      <section aria-labelledby="about-credit">
        <h2 id="about-credit">Who wrote what</h2>
        {PAPER.credit_lines.map((line) => <p key={line}>{line}</p>)}
        <p>
          Their repository: <Out href={`${up.repository}/tree/${up.commit}`}>{up.repository.replace("https://github.com/", "")} at {up.commit.slice(0, 7)}</Out>.
          {up.paper ? <> The authors’ <Out href={up.paper}>paper</Out>.</> : null}
        </p>
        {PAPER.licence ? <p>Licence of the paper and its Lean: {PAPER.licence}.</p> : null}
        {PAPER.source.lean_scope ? <p>{PAPER.source.lean_scope}</p> : null}
        <p>{PAPER.host} <a href={LIBRARY_ROOT}>The library</a> lists every paper it holds.</p>
      </section>
      {ADAPTED && (
        <section aria-labelledby="about-adapted">
          <h2 id="about-adapted">The adapted edition</h2>
          <p>{ADAPTED.credit}</p>
          <p>
            <a href={routeHref({ view: "read", stage: ADAPTED.slot })}>Read the adapted edition</a>, where each change is marked in the margin and
            “Show changes” lists all of them, or <a href={routeHref({ view: "read", stage: AUTHORS.slot })}>read the authors’ paper</a>, which keeps
            the authors’ own credit above. The switch “Authors’ paper / Adapted edition” keeps your place by paragraph.
          </p>
          <p>
            {[ADAPTED.pdf, ADAPTED.aux_pdf].filter((p) => !!p).map((p, i) => (
              <span key={p!.file}>
                {i ? " · " : ""}
                <a className="pdf-link" href={`${import.meta.env.BASE_URL}pdf/${p!.name ?? p!.file}`} target="_blank" rel="noopener">{p!.label ?? "PDF"}</a>
              </span>
            ))}
            . Each PDF marks every change with a bar in the margin and its id, and lists every change at its end.
          </p>
        </section>
      )}
      <section aria-labelledby="about-review">
        <h2 id="about-review">How the links were made</h2>
        <p>{PAPER.review}</p>
        <p>Comparisons are marked AI-assessed; plain titles and reading notes are marked AI-drafted. Topics are AI-assigned.</p>
      </section>
      <ComparatorSection />
      <SupplementaryChecks />
      <AboutUsing />
      <AboutKey />
      <p><a href={routeHref({ view: "read", stage: MAIN.slot })}>Back to the paper</a></p>
    </article>
  );
}

// About one library paper: who wrote it, where it comes from, how the links were made and
// that no mathematician has reviewed them. Every sentence about the paper is its data's.
import { useEffect, useRef } from "react";
import type { Route } from "../../app/router";
import { routeHref } from "../../app/router";
import { Out } from "../../app/Out";
import { Rich } from "../../figures/tex";
import { AboutKey, AboutUsing } from "../../reader/aboutParts";
import { PAPER, MAIN, BUILT, LIBRARY_ROOT } from "./data";

const ADAPTED = BUILT.find((d) => d.adapted);
const AUTHORS = (ADAPTED && BUILT.find((d) => d.id === ADAPTED.of)) || MAIN;
/** The edition's other downloads, as its edition.json declares them (the build checks and copies each). */
const ADAPTED_DOWNLOADS = ADAPTED
  ? [
      { entry: ADAPTED.reading_pdf, pdf: true, label: "PDF without change marks" },
      { entry: ADAPTED.aux_reading_pdf, pdf: true, label: "Auxiliary note, PDF without change marks" },
      { entry: ADAPTED.source_overlay, pdf: false, label: "TeX revisions against the authors’ source (ZIP)" },
      { entry: ADAPTED.result_comparison?.data, pdf: false, label: "Comparison data" },
    ]
      .filter((d) => !!d.entry)
      .map((d) => ({ href: supplementHref(ADAPTED, d.entry!.name ?? d.entry!.file, d.pdf), pdf: d.pdf, label: d.entry!.label ?? d.label }))
  : [];
import { SupplementaryChecks } from "./Checks";
import { ComparatorSection } from "./Comparator";
import { DifferencesSection } from "./Differences";
import { COMPARISON_ANCHOR, ResultComparison, supplementHref } from "./ResultComparison";
import "../../reader/reader-content.css";
import "../../reader/about.css";

export function AboutPage({ route }: { route: Extract<Route, { view: "about" }> }) {
  const page = useRef<HTMLElement>(null);
  // An address with a section in it (about/#result-comparison) lands there once. Several sections fill
  // in after first paint (the differences, the Comparator receipts, the comparison), so the page is
  // held undrawn, in place, until it has stopped growing and the section is filled, then shown at the
  // section: it never shows the top and then jumps.
  useEffect(() => {
    const anchor = route.anchor;
    const root = document.documentElement;
    if (!anchor || !page.current) return;
    root.classList.add("about-landing");
    let height = -1;
    let still = 0;
    let done = false;
    const land = () => {
      if (done) return;
      done = true;
      window.clearInterval(watch);
      window.clearTimeout(cap);
      document.getElementById(anchor)?.scrollIntoView({ block: "start" });
      requestAnimationFrame(() => requestAnimationFrame(() => root.classList.remove("about-landing")));
    };
    const watch = window.setInterval(() => {
      const target = document.getElementById(anchor);
      const now = page.current?.offsetHeight ?? 0;
      still = now === height ? still + 1 : 0;
      height = now;
      if (target && target.getAttribute("aria-busy") !== "true" && still >= 3) land();
    }, 100);
    const cap = window.setTimeout(land, 2500);
    return () => {
      done = true;
      window.clearInterval(watch);
      window.clearTimeout(cap);
      root.classList.remove("about-landing");
    };
  }, [route.anchor]);
  const up = PAPER.source.upstream;
  return (
    <article className="about" ref={page}>
      <header className="about__intro">
        <h1>{PAPER.title}</h1>
        <p>By {PAPER.authors.join(", ")}.</p>
      </header>
      {(PAPER.about ?? []).map((section, i) => (
        <section className="about__what" key={section.heading} aria-labelledby={`about-own-${i}`}>
          <h2 id={`about-own-${i}`}>
            <Rich src={section.heading} />
          </h2>
          {(section.paragraphs ?? []).map((text) => (
            <p key={text}>
              <Rich src={text} />
            </p>
          ))}
          {section.links?.length ? (
            <ul className="about__links">
              {section.links.map((link) => (
                <li key={link.href}>
                  {/^https?:/.test(link.href) ? <Out href={link.href}>{link.label}</Out> : <a href={`${import.meta.env.BASE_URL}${link.href}`}>{link.label}</a>}
                </li>
              ))}
            </ul>
          ) : null}
        </section>
      ))}
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
            <a href={routeHref({ view: "read", stage: ADAPTED.slot })}>Read the adapted edition</a> and open “Show changes” to compare both texts, or <a href={routeHref({ view: "read", stage: AUTHORS.slot })}>read the authors’ paper</a>, which keeps
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
          {ADAPTED_DOWNLOADS.length > 0 && (
            <p>
              {ADAPTED_DOWNLOADS.map((d, i) => (
                <span key={d.href}>
                  {i ? " · " : ""}
                  <a className={d.pdf ? "pdf-link" : undefined} href={d.href} target="_blank" rel="noopener">{d.label}</a>
                </span>
              ))}
              .
            </p>
          )}
          {ADAPTED.result_comparison?.reading && (
            <p>
              <a href={routeHref({ view: "about", anchor: COMPARISON_ANCHOR })}>Read the result-by-result comparison</a> to open each numbered
              statement in the authors’ paper and in the adapted edition.
            </p>
          )}
        </section>
      )}
      {ADAPTED && <ResultComparison doc={ADAPTED} />}
      <section aria-labelledby="about-review">
        <h2 id="about-review">How the links were made</h2>
        <p>{PAPER.review}</p>
        <p>Comparisons are marked AI-assessed; plain titles and reading notes are marked AI-drafted. Topics are AI-assigned.</p>
      </section>
      <DifferencesSection />
      <ComparatorSection />
      <SupplementaryChecks />
      <AboutUsing />
      <AboutKey />
      <p><a href={routeHref({ view: "read", stage: MAIN.slot })}>Back to the paper</a></p>
    </article>
  );
}

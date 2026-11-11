// The site in five pictures, in the order the short video goes through it: the graph
// that follows the paper, a tick that opens the Lean, a card that opens its step, the
// Compare page and the What ran page. Each picture is a capture of the real page
// (scripts/capture-tour-stills.py), in the scheme the reader has, and each opens the view
// it is of. In a wide window the pictures share one frame and the one named under the
// pointer or the focus is drawn; in a narrow one each stands under its own words.

import { useState } from "react";
import { SITE_FACTS } from "virtual:site-facts";
import { routeHref } from "../app/router";
import { LINK_CAVEAT } from "../app/caveat";

interface View {
  id: "follow" | "tick" | "card" | "compare" | "checks";
  name: string;
  text: string;
  link: string;
  href: string;
  alt: string;
}

function views(): View[] {
  const place = SITE_FACTS.theorem1;
  return [
    {
      id: "follow",
      name: "The graph follows the paper",
      text: "Beside each paper is a graph of its argument, with a card for each step. As the paper scrolls, the cards for the passage on screen are outlined in amber.",
      link: "Open the exposition",
      href: routeHref({ view: "read", stage: "expository" }),
      alt: "The exposition open at its third section. On the graph beside it, three cards are outlined in amber.",
    },
    {
      id: "tick",
      name: "A tick opens the Lean",
      text: "In the picture, a reader has clicked Theorem 1 of the short paper. The Lean has opened at the lines that state the theorem, and the paper has not moved.",
      link: "Open this statement",
      href: routeHref({ view: "read", stage: "short", at: place?.at, node: place ? "full_support" : undefined, anchor: place?.anchor ?? undefined }),
      alt: "The short paper open at Theorem 1, with the theorem highlighted. Beside it is OpenAI’s Lean for it, with the lines that state it lit.",
    },
    {
      id: "card",
      name: "A card opens its step",
      text: "Here a reader has clicked the card “Controlled diffusion exists uniquely” on the graph. The paper has moved to the passage that states the step, and the Lean for the step has opened beside it.",
      link: "Open this step",
      href: routeHref({ view: "read", stage: "expository", node: "support.diffusion" }),
      alt: "The exposition at the passage on the controlled diffusion, highlighted. Beside it is the Lean definition IsDiffusion with its lines lit.",
    },
    {
      id: "compare",
      name: "Compare sets one step side by side",
      text: "For one step of the argument, the Compare page sets the Lean beside the passages on that step in the papers.",
      link: "Open Compare at the main theorem",
      href: routeHref({ view: "compare", node: "full_support" }),
      alt: "The Compare page at the main theorem: a column with its Lean statement, a column of passages from the long record and a column from the short paper.",
    },
    {
      id: "checks",
      name: "What ran, and what did not",
      text: "The What ran page lists each recorded run with its result, and beside each result what it leaves open.",
      link: "Open What ran",
      href: routeHref({ view: "checks" }),
      alt: "The What ran page: a table with a row for the Lean compile, the statement, the axioms, any sorry, Comparator and more, each with what ran and what that leaves open.",
    },
  ];
}

const still = (id: string, scheme: string, width: number) => `${import.meta.env.BASE_URL}stills/tour-${id}-${scheme}-${width}.webp`;

export function Tour() {
  const [on, setOn] = useState(0);
  const ties = SITE_FACTS.ties;
  return (
    <section className="front__band" aria-labelledby="front-tour">
      <h2 id="front-tour" className="front__bandtitle">
        The site in five pictures
      </h2>
      <div className="tour">
        {views().map((view, i) => (
          <div key={view.id} className={`tour__item${i === on ? " is-on" : ""}`}>
            <div className="tour__words" style={{ gridRow: i + 1 }} onPointerEnter={() => setOn(i)} onFocus={() => setOn(i)}>
              <h3 className="tour__name">{view.name}</h3>
              <p className="tour__text">
                {view.text}{" "}
                <a href={view.href} className="tour__open">
                  {view.link}
                </a>
              </p>
            </div>
            <figure className="tour__fig">
              <a href={view.href} className="tour__piclink" tabIndex={-1} aria-label={`${view.link}: the view in this picture`}>
                {(["light", "dark"] as const).map((scheme) => (
                  <img
                    key={scheme}
                    className={`readerstill__img readerstill__img--${scheme}`}
                    src={still(view.id, scheme, 1440)}
                    srcSet={`${still(view.id, scheme, 1440)} 1440w, ${still(view.id, scheme, 2880)} 2880w`}
                    sizes="(min-width: 68.75em) 66vw, 100vw"
                    alt={view.alt}
                    width={1440}
                    height={790}
                    loading="lazy"
                    decoding="async"
                  />
                ))}
              </a>
            </figure>
          </div>
        ))}
      </div>
      {ties && (
        <p className="tour__limit">
          The three papers have {ties.statements.toLocaleString("en-GB")} marked statements, {ties.withLean} of them with Lean. {LINK_CAVEAT}
        </p>
      )}
    </section>
  );
}

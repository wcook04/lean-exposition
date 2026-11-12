// The first screen as plain HTML. The build puts it in index.html, so the theorem paints
// before any script runs, and React then shows the same markup from the same function.
// This module runs in the browser and in vite.config.ts: it may use no browser API and
// no import.meta. The rows are checked against examples/qaoa-sk/alignment/main-theorem.json
// by tests/front-hero.test.ts: every Lean fragment is an exact substring of the statement
// in OpenAI's Comparator challenge, and every formula is Theorem 1 of the short paper.

import { LINK_CAVEAT, MODELS_STEP } from "../app/caveat.ts";
import { siteFilms, type SiteFilm } from "../app/siteFilms.ts";

export interface HeroRow {
  /** Exact text of the Lean statement. */
  lean: string;
  /** The same clause in the short paper's notation, as TeX. */
  tex: string;
  /** What a reader who knows no Lean needs in order to match the two. */
  words: string;
  /** The record that opens when the clause is chosen. */
  record: string;
}

export const HERO_ROWS: HeroRow[] = [
  {
    lean: "(hmin : IsMinimizer W γ)",
    tex: "\\gamma\\in\\mathcal U\\text{ minimises }\\mathcal P",
    words: "The hypothesis. That a minimiser exists is a separate input.",
    record: "assumptions.full_support_minimizer",
  },
  {
    lean: "μ.support = Set.univ",
    tex: "\\operatorname{supp}\\mu_\\gamma=[0,1)",
    words: "Full support. In Lean, Set.univ is all of Time, the interval [0, 1).",
    record: "support.full_relative_support",
  },
  {
    lean: "∀ a b : Time, a < b → γ.val a < γ.val b",
    tex: "\\gamma(t_2)>\\gamma(t_1)\\quad(0\\leq t_1<t_2<1)",
    words: "Strict increase, the same inequality written the other way round.",
    record: "support.strict_increase",
  },
  {
    lean: "squareMoment W γ X t = (t : ℝ)",
    tex: "q(t)=t",
    words: "The square moment of the gradient along the diffusion equals time.",
    record: "support.moment_saturation",
  },
  {
    lean: "(∫ ω, (curvature W γ t (X (Real.toNNReal t) ω))^2 ∂W.law) = 1",
    tex: "\\mathbb E[a(t,X_t)^2]=1",
    words: "The curvature moment, with the expectation written as an integral.",
    record: "support.moment_saturation",
  },
];

const escapeHtml = (text: string) => text.replace(/[&<>"]/g, (c) => `&#${c.charCodeAt(0)};`);

/** Colours the small part of Lean these rows use, in the classes the Lean viewer also uses. */
function leanHtml(source: string): string {
  return source
    .split(/(\s+|[()]|[∀∃→∧=<∫∂:,]|\^2|\.)/)
    .filter((part) => part !== "")
    .map((part) => {
      if (/^[∀∃→∧=<∫∂:,]$/.test(part)) return `<span class="lean-t lean-t--op">${escapeHtml(part)}</span>`;
      if (/^[A-Z][A-Za-z]*$/.test(part) || part === "ℝ") return `<span class="lean-t lean-t--type">${escapeHtml(part)}</span>`;
      if (/^[a-z][A-Za-z]+$/.test(part)) return `<span class="lean-t lean-t--name">${escapeHtml(part)}</span>`;
      return escapeHtml(part);
    })
    .join("");
}

export interface HeroLinks {
  short: string;
  exposition: string;
  /** The short paper at Theorem 1, with its Lean open. */
  beside: string;
  compare: string;
  theorem: string;
  /** The step that records that the two Lean models are not connected. */
    models: string;
  about: string;
  checks: string;
  /** A step of the exposition, opened from its card on the graph. */
  step: string;
  /** The site's base path, for the pictures under public/stills/. */
  base: string;
  /** How many statements the papers have marked, and how many of those have Lean, when the edition says. */
  ties: { statements: number; withLean: number } | null;
  /** The videos on the first screen: the short one of this website first, then the two about the result. */
  films: SiteFilm[];
}

/** `theorem1` is the statement's place in the short paper, from the alignment (the build derives it). */
export const heroLinks = (base: string, theorem1?: { at: string; anchor: string | null } | null, ties?: { statements: number; withLean: number } | null): HeroLinks => ({
  short: `${base}read/short`,
  exposition: `${base}read/expository`,
  beside: theorem1 ? `${base}read/short?l=${theorem1.at}&n=full_support${theorem1.anchor ? `#${theorem1.anchor}` : ""}` : `${base}read/short`,
  compare: `${base}compare`,
  theorem: `${base}compare?n=full_support`,
    models: `${base}map?n=${MODELS_STEP}`,
  about: `${base}about#made-by`,
  checks: `${base}checks`,
  step: `${base}read/expository?n=support.diffusion`,
  base,
  ties: ties ?? null,
  films: siteFilms(base),
});

/** The id of the first screen's row of videos, which the bar's Videos menu and other pages may link to. */
export const VIDEOS_ANCHOR = "videos";

/**
 * A video in the family's film-slot markup (docs/family.md in wcook04.github.io): the picture
 * and the title open the same YouTube address, so only the title is in the Tab order, and it
 * says the running time in words. The lead's still loads with the page; the others wait.
 */
function filmHtml(film: SiteFilm, lead: boolean): string {
  const open = `href="${film.href}" target="_blank" rel="noopener noreferrer"`;
  const image = `<img src="${film.src}" srcset="${film.srcSet}" sizes="${lead ? "(max-width: 37.5em) 100vw, 300px" : "160px"}" alt="" width="1280" height="720" decoding="async"${lead ? ' fetchpriority="high"' : ' loading="lazy"'} />`;
  return `<figure class="film-slot ${lead ? "front__lead" : "film-slot--small front__minor"}">
<a class="film-slot__frame" ${open} aria-hidden="true" tabindex="-1">${image}<span class="film-slot__play"></span><span class="film-slot__time">${film.clock}</span></a>
<figcaption class="film-slot__caption"><p class="front__kicker">${escapeHtml(film.kicker)}</p><p class="film-slot__title"><a ${open}>${escapeHtml(film.title)}<span class="sr-only">, video on YouTube, ${film.spoken}</span></a></p></figcaption>
</figure>`;
}

/**
 * Five pictures of the site in use, in the order the short video goes through it. Each is a
 * capture of the real page (scripts/capture-tour-stills.py) in the reader's scheme, and each
 * opens the view it is of. They are radio buttons and plain CSS, so the first one is drawn
 * before any script runs and the keyboard's arrow keys move between them.
 */
interface Shot {
  id: "follow" | "tick" | "card" | "compare" | "checks";
  tab: string;
  text: string;
  link: string;
  href: string;
  alt: string;
}

const heroShots = (links: HeroLinks): Shot[] => [
  {
    id: "follow",
    tab: "Paper and graph",
    text: "Beside each paper is a graph of its argument, with a card for each step. As the paper scrolls, the cards for the passage on screen are outlined in amber.",
    link: "Open the exposition",
    href: links.exposition,
    alt: "The exposition open at its third section. On the graph beside it, three cards are outlined in amber.",
  },
  {
    id: "tick",
    tab: "A statement and its Lean",
    text: "A reader has clicked Theorem 1 of the short paper. The Lean has opened at the lines that state the theorem, and the paper has not moved.",
    link: "Open this statement",
    href: links.beside,
    alt: "The short paper open at Theorem 1, with the theorem highlighted. Beside it is OpenAI’s Lean for the theorem, with the lines of its statement highlighted.",
  },
  {
    id: "card",
    tab: "A card and its step",
    text: "A reader has clicked the card “Controlled diffusion exists uniquely” on the graph. The paper has moved to the passage that states the step, and the Lean for the step has opened beside it.",
    link: "Open this step",
    href: links.step,
    alt: "The exposition at its passage on the controlled diffusion, highlighted. Beside it is the Lean definition IsDiffusion, with its lines highlighted.",
  },
  {
    id: "compare",
    tab: "Compare",
    text: "On the Compare page, the Lean for one step is set beside the passages on that step in the papers.",
    link: "Open Compare at the main theorem",
    href: links.theorem,
    alt: "The Compare page at the main theorem: a column with its Lean statement, a column of passages from the long record and a column of passages from the short paper.",
  },
  {
    id: "checks",
    tab: "What ran",
    text: "On the What ran page, each recorded run is listed with its result, and beside each result is what it leaves open.",
    link: "Open What ran",
    href: links.checks,
    alt: "The What ran page: a table with rows for the Lean compile, the statement, the axioms, any sorry and Comparator. Each row has what ran with its result, and what that leaves open.",
  },
];

function shotsHtml(links: HeroLinks): string {
  const shots = heroShots(links);
  const still = (id: string, scheme: string, width: number) => `${links.base}stills/tour-${id}-${scheme}-${width}.webp`;
  const tabs = shots
    .map((shot, i) => `<label class="shots__tab"><input type="radio" name="front-shot" value="${shot.id}"${i === 0 ? " checked" : ""} /><span>${escapeHtml(shot.tab)}</span></label>`)
    .join("");
  const pics = shots
    .map(
      (shot) =>
        `<a class="shots__pic shots__pic--${shot.id}" href="${shot.href}" tabindex="-1" aria-label="${escapeHtml(shot.link)}, the view in this picture">${["light", "dark"]
          .map(
            (scheme) =>
              `<img class="shots__img shots__img--${scheme}" src="${still(shot.id, scheme, 1440)}" srcset="${still(shot.id, scheme, 1440)} 1440w, ${still(shot.id, scheme, 2880)} 2880w" sizes="(min-width: 68.75em) 58vw, 100vw" alt="${escapeHtml(shot.alt)}" width="1440" height="790" loading="lazy" decoding="async" />`,
          )
          .join("")}</a>`,
    )
    .join("\n");
  const caps = shots.map((shot) => `<p class="shots__cap shots__cap--${shot.id}">${escapeHtml(shot.text)} <a href="${shot.href}">${escapeHtml(shot.link)}</a></p>`).join("\n");
  return `<figure class="shots">
<div class="shots__tabs" role="radiogroup" aria-label="Pictures of this website in use">${tabs}</div>
<div class="shots__frame">
${pics}
</div>
<figcaption class="shots__caps">
${caps}
</figcaption>
</figure>`;
}

/** The hero, typeset with `tex`, a function from TeX source to KaTeX HTML. */
export function heroHtml(links: HeroLinks, tex: (source: string) => string): string {
  const rows = HERO_ROWS.map(
    (row) => `<tr class="rosetta__row">
<td class="rosetta__lean"><code translate="no">${leanHtml(row.lean)}</code></td>
<td class="rosetta__math"><a class="rosetta__formula" href="${links.compare}?n=${row.record}" aria-label="Compare this clause across the levels">${tex(row.tex)}</a><span class="rosetta__words">${escapeHtml(row.words)}</span></td>
</tr>`,
  ).join("\n");
  return `<section class="front__hero" aria-labelledby="front-title">
<div class="front__intro">
<p class="front__what">Three papers on a theorem of OpenAI’s, read beside its Lean proof and a graph of the argument</p>
<h1 id="front-title" class="front__title">Why the Sherrington–Kirkpatrick order parameter has no gaps</h1>
<p class="front__lede">Parisi’s formula gives the largest energy per spin in the Sherrington–Kirkpatrick (SK) spin glass as a minimum over nondecreasing functions, called order parameters. A gap is an interval on which an order parameter stays flat. A minimising order parameter has none: it increases across every interval in [0, 1), and its derivative is positive between 0&nbsp;and&nbsp;1.</p>
<p class="front__actions"><a class="front__primary" href="${links.short}">Read the short paper</a><a class="front__secondary" href="${links.exposition}">Read the exposition</a></p>
<p class="front__made">Made by <a href="${links.about}">Will Cook</a> using AI. The theorem and the Lean proof are OpenAI’s. Lean is a programming language whose compiler rejects a proof with a wrong step.</p>
</div>
${shotsHtml(links)}
${
  links.films.length
    ? `<div class="front__watch" id="${VIDEOS_ANCHOR}" role="group" aria-label="Videos">
${filmHtml(links.films[0], true)}
<div class="front__others">
${links.films.slice(1).map((film) => filmHtml(film, false)).join("\n")}
</div>
</div>`
    : ""
}
</section>
<section class="front__theorem" aria-labelledby="front-clauses">
<div class="front__theorem-words">
<h2 id="front-clauses" class="front__clauses-title">Theorem 1, clause by clause</h2>
<p class="front__site">OpenAI’s proof of the increase is written in Lean, a programming language whose compiler rejects a proof with a wrong step; the positive derivative is proved in OpenAI’s manuscript and is not in the Lean. In a paper here, click a statement with a dark tick in the margin and its Lean opens beside the text. A graph of the proof beside the paper moves to the statement you are reading.</p>
<p class="front__guide-link"><a href="${links.beside}">Theorem 1 with its Lean open</a></p>
<p class="rosetta__models">This Lean is OpenAI’s full-support model. OpenAI’s value theorem is in a separate model, and no Lean theorem connects the two, so combining them in Lean <a href="${links.models}">needs that connection first</a>.</p>${links.ties ? `
<p class="front__limit">The three papers have ${links.ties.statements.toLocaleString("en-GB")} marked statements, ${links.ties.withLean} of them with Lean. ${escapeHtml(LINK_CAVEAT)}</p>` : ""}
</div>
<figure class="rosetta">
<table class="rosetta__table">
<caption class="visually-hidden">The main theorem, clause by clause: OpenAI’s Lean statement beside Theorem 1 of the short paper.</caption>
<thead><tr><th scope="col">In OpenAI’s Lean</th><th scope="col">In the short paper, Theorem 1</th></tr></thead>
<tbody>
${rows}
</tbody>
</table>
<figcaption class="rosetta__foot"><a href="${links.theorem}">Compare the whole theorem, its proof and its definitions</a></figcaption>
</figure>
</section>`;
}

/** The frame as plain HTML, the same markup TopBar renders, so the bar is there before the scripts. */
export function frameHtml(base: string): string {
  const job = (href: string, name: string, quiet = false) => `<a class="topnav__job${quiet ? " topnav__job--quiet" : ""}" href="${base}${href}">${name}</a>`;
  return `<header class="topbar"><span class="fam-lockup"><a class="fam-lockup__home" href="https://wcook04.github.io/" rel="author" title="All of Will Cook's websites and videos"><img src="${base}plectis.svg" alt="Will Cook: all websites and videos" width="26" height="26" /></a><span class="fam-lockup__rule" aria-hidden="true"></span><a class="fam-lockup__site" href="${base}" aria-label="Lean Exposition, front page"><svg viewBox="0 0 32 32" aria-hidden="true" class="wordmark__mark"><path d="M4 27 L4 5 M4 27 L28 27" fill="none" stroke-width="2" stroke-linecap="round"></path><path d="M5 26 C10 22 13 17 16 14 C19 11 22 9 27 6" fill="none" stroke-width="2.6" stroke-linecap="round"></path><circle cx="16" cy="14" r="3"></circle></svg><span class="fam-lockup__name" translate="no">Lean Exposition</span></a></span><nav class="topnav" aria-label="Main">${job("read/short", "Read")}${job("map", "Map")}${job("compare", "Compare")}${job("checks", "What ran")}${job("lean", "Lean index", true)}</nav></header>`;
}

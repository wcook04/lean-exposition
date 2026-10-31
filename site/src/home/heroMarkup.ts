// The first screen as plain HTML. The build puts it in index.html, so the theorem paints
// before any script runs, and React then shows the same markup from the same function.
// This module runs in the browser and in vite.config.ts: it may use no browser API and
// no import.meta. The rows are checked against examples/qaoa-sk/alignment/main-theorem.json
// by tests/front-hero.test.ts: every Lean fragment is an exact substring of the statement
// in OpenAI's Comparator challenge, and every formula is Theorem 1 of the short paper.

import { MODELS_STEP } from "../app/caveat.ts";

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
  map: string;
  /** The step that records that the two Lean models are not connected. */
    models: string;
  about: string;
}

/** `theorem1` is the statement's place in the short paper, from the alignment (the build derives it). */
export const heroLinks = (base: string, theorem1?: { at: string; anchor: string | null } | null): HeroLinks => ({
  short: `${base}read/short`,
  exposition: `${base}read/expository`,
  beside: theorem1 ? `${base}read/short?l=${theorem1.at}&n=full_support${theorem1.anchor ? `#${theorem1.anchor}` : ""}` : `${base}read/short`,
  compare: `${base}compare`,
  theorem: `${base}compare?n=full_support`,
  map: `${base}map`,
    models: `${base}map?n=${MODELS_STEP}`,
  about: `${base}about#made-by`,
});

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
<h1 id="front-title" class="front__title">Why the Sherrington–Kirkpatrick order parameter has no gaps</h1>
<p class="front__lede">Parisi’s formula gives the largest energy per spin in the Sherrington–Kirkpatrick (SK) spin glass as a minimum over nondecreasing functions, called order parameters. A gap is an interval on which an order parameter stays flat. A minimising order parameter has none: it increases across every interval in [0, 1), and its derivative is positive between 0&nbsp;and&nbsp;1.</p>
<p class="front__site">OpenAI’s proof of the increase is written in Lean, a programming language whose compiler rejects a proof with a wrong step; the positive derivative is proved in OpenAI’s manuscript and is not in the Lean. In a paper here, click a statement with a dark tick in the margin and its Lean opens beside the text. A graph of the proof beside the paper moves to the statement you are reading.</p>
<p class="front__actions"><a class="front__primary" href="${links.short}">Read the short paper</a><a class="front__secondary" href="${links.exposition}">Read the exposition</a></p>
<p class="front__tertiary"><a href="${links.beside}">Theorem 1 with its Lean open</a><a href="${links.compare}">Compare Lean and papers</a><a href="${links.map}">The argument map</a></p>
<p class="front__made">Made by <a href="${links.about}">Will Cook</a> using AI. The theorem and the Lean proof are OpenAI’s.</p>
</div>
<figure class="rosetta">
<table class="rosetta__table">
<caption class="visually-hidden">The main theorem, clause by clause: OpenAI’s Lean statement beside Theorem 1 of the short paper.</caption>
<thead><tr><th scope="col">In OpenAI’s Lean</th><th scope="col">In the short paper, Theorem 1</th></tr></thead>
<tbody>
${rows}
</tbody>
</table>
<figcaption class="rosetta__foot"><a href="${links.theorem}">Compare the whole theorem, its proof and its definitions</a><p class="rosetta__models">This Lean is OpenAI’s full-support model. OpenAI’s value theorem is in a separate model, and no Lean theorem connects the two, so combining them in Lean <a href="${links.models}">needs that connection first</a>.</p></figcaption>
</figure>
</section>`;
}

/** The frame as plain HTML, the same markup TopBar renders, so the bar is there before the scripts. */
export function frameHtml(base: string): string {
  const job = (href: string, name: string, quiet = false) => `<a class="topnav__job${quiet ? " topnav__job--quiet" : ""}" href="${base}${href}">${name}</a>`;
  return `<header class="topbar"><span class="fam-lockup"><a class="fam-lockup__home" href="https://wcook04.github.io/" rel="author" title="All of Will Cook's websites and videos"><img src="${base}plectis.svg" alt="Will Cook: all websites and videos" width="26" height="26" /></a><span class="fam-lockup__rule" aria-hidden="true"></span><a class="fam-lockup__site" href="${base}" aria-label="Lean Exposition, front page"><svg viewBox="0 0 32 32" aria-hidden="true" class="wordmark__mark"><path d="M4 27 L4 5 M4 27 L28 27" fill="none" stroke-width="2" stroke-linecap="round"></path><path d="M5 26 C10 22 13 17 16 14 C19 11 22 9 27 6" fill="none" stroke-width="2.6" stroke-linecap="round"></path><circle cx="16" cy="14" r="3"></circle></svg><span class="fam-lockup__name" translate="no">Lean Exposition</span></a></span><nav class="topnav" aria-label="Main">${job("read/short", "Read")}${job("map", "Map")}${job("compare", "Compare")}${job("checks", "What ran")}${job("lean", "Lean index", true)}</nav></header>`;
}

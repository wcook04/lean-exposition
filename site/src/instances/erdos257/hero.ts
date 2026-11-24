// The Erdős #257 site's first screen: its title, opening and credit from copy.ts, then the
// main theorem clause by clause, each clause with what its Lean says against the paper.
// Every number is read from the edition (SiteFacts); the wording is the author's. No
// browser API and no import.meta: vite.config.ts runs this too.

import type { SiteFacts } from "../../home/siteFacts.ts";
import { escapeHtml, filmHtml, HERO_BREAK, leanHtml, VIDEOS_ANCHOR } from "../../home/heroMarkup.ts";
import type { SiteFilm } from "../../app/siteFilms.ts";
import { COPY, isTodo, type ClauseRow } from "./copy.ts";
import { verdictWords } from "../../compare/fidelityWords.ts";

/** Text with inline TeX between single dollar signs typeset, everything else escaped. An unwritten slot stays plain. */
export function richHtml(text: string, tex: (source: string) => string): string {
  if (isTodo(text)) return escapeHtml(text);
  return text
    .split(/(\$[^$]+\$)/)
    .map((part) => (/^\$[^$]+\$$/.test(part) ? tex(part.slice(1, -1)) : escapeHtml(part)))
    .join("");
}

const n = (value: number) => value.toLocaleString("en-GB");

/** The counts line under the clause table, every number from the edition. */
export function countsLine(facts: SiteFacts, caveat: string, review: string): string {
  const { ties, origins } = facts;
  if (!ties) return "";
  if (!origins) return `The three papers have ${n(ties.statements)} marked statements, ${n(ties.withLean)} of them with Lean. ${caveat}`;
  return `The three papers have ${n(ties.statements)} marked statements, ${n(ties.withLean)} of them with Lean, joined to the records by ${n(ties.total)} ties: ${n(origins.evidenceRecord)} copied from the papers’ published evidence mapping and ${n(origins.ai)} made by an AI agent for this site${origins.unmarked ? `, and ${n(origins.unmarked)} that do not say who made them` : ""}. ${review}`;
}

function clauseRow(row: ClauseRow, base: string, goal: string | null, tex: (source: string) => string): string {
  const record = row.record ?? goal;
  const href = record ? `${base}compare?n=${encodeURIComponent(record)}` : `${base}compare`;
  const verdict = isTodo(row.verdict) ? escapeHtml(row.verdict) : escapeHtml(verdictWords(row.verdict as "same" | "stronger" | "weaker", "paper"));
  const formula = isTodo(row.tex) ? escapeHtml(row.tex) : tex(row.tex);
  const code = isTodo(row.lean) ? escapeHtml(row.lean) : leanHtml(row.lean);
  return `<tr class="rosetta__row">
<td class="rosetta__lean"><code translate="no">${code}</code></td>
<td class="rosetta__math"><a class="rosetta__formula" href="${href}" aria-label="Compare this clause across the levels">${formula}</a><span class="rosetta__words">${richHtml(row.note, tex)}</span></td>
<td class="rosetta__verdict" data-verdict="${isTodo(row.verdict) ? "todo" : row.verdict}">${verdict}</td>
</tr>`;
}

/** The videos: the lead with its picture large, the others beside it, as on the SK front page. */
function watchHtml(films: SiteFilm[]): string {
  if (!films.length) return "";
  return `<div class="front__watch" id="${VIDEOS_ANCHOR}" role="group" aria-label="Videos">
${filmHtml(films[0], true)}
<div class="front__others">
${films.slice(1).map((film) => filmHtml(film, false)).join("\n")}
</div>
</div>`;
}

export function heroHtml(base: string, facts: SiteFacts, tex: (source: string) => string, caveat: string, review: string, films: SiteFilm[] = []): string {
  const goal = facts.mainRecord;
  const beside = facts.theorem1 ? `${base}read/short?l=${facts.theorem1.at}${goal ? `&n=${encodeURIComponent(goal)}` : ""}${facts.theorem1.anchor ? `#${facts.theorem1.anchor}` : ""}` : `${base}read/short`;
  const theorem = goal ? `${base}compare?n=${encodeURIComponent(goal)}` : `${base}compare`;
  const counts = countsLine(facts, caveat, review);
  return `<section class="front__hero front__hero--single" aria-labelledby="front-title">
<div class="front__intro">
<p class="front__what">${richHtml(COPY.strapline, tex)}</p>
<h1 id="front-title" class="front__title">${richHtml(COPY.title, tex).replace(/ − /g, "\u00a0−\u00a0")}</h1>
<p class="front__lede">${richHtml(COPY.opening, tex)}</p>
<p class="front__actions"><a class="front__primary" href="${base}read/short">Read the short paper</a><a class="front__secondary" href="${base}read/expository">Read the exposition</a></p>
<p class="front__made">${richHtml(COPY.credit, tex)}</p>
</div>
${watchHtml(films)}
</section>${HERO_BREAK}
<section class="front__theorem front__theorem--verdicts" aria-labelledby="front-clauses">
<div class="front__theorem-words">
<h2 id="front-clauses" class="front__clauses-title">${richHtml(COPY.clauses.heading, tex)}</h2>
<p class="front__site">${richHtml(COPY.clauses.intro, tex)}</p>
<p class="front__guide-link"><a href="${beside}">The main theorem with its Lean open</a></p>${counts ? `
<p class="front__limit">${escapeHtml(counts)}</p>` : ""}
</div>
<figure class="rosetta">
<table class="rosetta__table">
<caption class="visually-hidden">The main theorem, clause by clause: the Lean statement beside the short paper's statement, with what the Lean says against it.</caption>
<thead><tr><th scope="col">In the Lean</th><th scope="col">In the short paper</th><th scope="col">The Lean</th></tr></thead>
<tbody>
${COPY.clauses.rows.map((row) => clauseRow(row, base, goal, tex)).join("\n")}
</tbody>
</table>
<figcaption class="rosetta__foot"><a href="${theorem}">Compare the whole theorem, its proof and its definitions</a></figcaption>
</figure>
</section>`;
}

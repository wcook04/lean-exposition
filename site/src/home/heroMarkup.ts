// The first screen as plain HTML. The build puts it in index.html, so the theorem paints
// before any script runs, and React then shows the same markup from the same function.
// This module runs in the browser and in vite.config.ts: it may use no browser API and
// no import.meta. Each instance writes its own first screen (src/instances/<id>/hero.ts)
// from the shared parts here.

import type { SiteFilm } from "../app/siteFilms.ts";
import family from "../app/family.json";
import { LIBRARY_HOME, LIBRARY_NAME } from "../app/libraryHome.ts";
import { paperMarkHtml } from "../app/paperMarks.ts";

export const escapeHtml = (text: string) => text.replace(/[&<>"]/g, (c) => `&#${c.charCodeAt(0)};`);

/** Colours the small part of Lean these rows use, in the classes the Lean viewer also uses. */
export function leanHtml(source: string): string {
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

/** The id of the first screen's row of videos, which the bar's Videos menu and other pages may link to. */
export const VIDEOS_ANCHOR = "videos";

/** Where an instance's first-screen HTML may divide, so its front page can put a band between the two parts. */
export const HERO_BREAK = "<!--hero-break-->";

/**
 * A video in the family's film-slot markup (docs/family.md in wcook04.github.io): the picture
 * and the title open the same YouTube address, so only the title is in the Tab order, and it
 * says the running time in words. The lead's still loads with the page; the others wait.
 */
export function filmHtml(film: SiteFilm, lead: boolean): string {
  const open = `href="${film.href}" target="_blank" rel="noopener noreferrer"`;
  const image = `<img src="${film.src}" srcset="${film.srcSet}" sizes="${lead ? "(max-width: 37.5em) 100vw, 300px" : "160px"}" alt="" width="1280" height="720" decoding="async"${lead ? ' fetchpriority="high"' : ' loading="lazy"'} />`;
  return `<figure class="film-slot ${lead ? "front__lead" : "film-slot--small front__minor"}">
<a class="film-slot__frame" ${open} aria-hidden="true" tabindex="-1">${image}<span class="film-slot__play"></span><span class="film-slot__time">${film.clock}</span></a>
<figcaption class="film-slot__caption"><p class="front__kicker">${escapeHtml(film.kicker)}</p><p class="film-slot__title"><a ${open}>${escapeHtml(film.title)}<span class="sr-only">, video on YouTube, ${film.spoken}</span></a></p></figcaption>
</figure>`;
}

/** The title and available routes before the interactive shell loads. */
export function frameHtml(
  base: string,
  siteName: string,
  paperId: string,
  accounts: readonly [href: string, name: string][] = [["read/short/", "Short paper"], ["read/expository/", "Exposition"], ["read/long/", "Long record"]],
): string {
  const link = (href: string, name: string) => `<li><a class="readmenu__item" href="${escapeHtml(`${base}${href}`)}">${escapeHtml(name)}</a></li>`;
  const mark = paperMarkHtml(paperId);
  const { home, name } = family.owner;
  return `<header class="topbar">
<a class="skip-link" href="#main">Skip to content</a>
<a class="topbar__library" href="${LIBRARY_HOME}" translate="no" aria-label="${LIBRARY_NAME}, all papers">${mark ? `<span class="topbar__mark" aria-hidden="true">${mark}</span>` : ""}<span class="topbar__library-full">${LIBRARY_NAME}</span><span class="topbar__library-short" aria-hidden="true">Library</span></a>
<span class="topbar__sep" aria-hidden="true">/</span>
<a class="topbar__title" href="${base}" translate="no"><span class="topbar__title-text">${escapeHtml(siteName)}</span></a>
<div class="topbar__right">
<details class="site-menu"><summary class="control control--plain menu-toggle"><svg viewBox="0 0 16 16" width="16" height="16" fill="none" aria-hidden="true"><path d="M2 4h12M2 8h12M2 12h12" stroke="currentColor" stroke-width="1.4" stroke-linecap="round"/></svg>Menu</summary>
<div class="site-menu__panel"><nav aria-label="Main"><p class="site-menu__label" id="static-read">Read</p><ul class="site-menu__list" aria-labelledby="static-read">${accounts.map(([href, title]) => link(href, title)).join("")}</ul><ul class="site-menu__list site-menu__routes">${link("map/", "Map")}${link("compare/", "Compare")}${link("lean/", "Lean index")}</ul></nav></div>
</details>
<a class="topbar__brand" href="${escapeHtml(home)}" rel="author" translate="no"><img src="${base}plectis.svg" alt="" width="22" height="22">${escapeHtml(name)}</a>
</div>
</header>`;
}

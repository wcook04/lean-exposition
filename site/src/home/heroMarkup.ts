// The first screen as plain HTML. The build puts it in index.html, so the theorem paints
// before any script runs, and React then shows the same markup from the same function.
// This module runs in the browser and in vite.config.ts: it may use no browser API and
// no import.meta. Each instance writes its own first screen (src/instances/<id>/hero.ts)
// from the shared parts here.

import type { SiteFilm } from "../app/siteFilms.ts";

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

/** The frame as plain HTML, the same markup TopBar renders, so the bar is there before the scripts. */
export function frameHtml(base: string, siteName: string): string {
  const job = (href: string, name: string, quiet = false) => `<a class="topnav__job${quiet ? " topnav__job--quiet" : ""}" href="${base}${href}">${name}</a>`;
  return `<header class="topbar"><span class="fam-lockup"><a class="fam-lockup__home" href="https://wcook04.github.io/" rel="author" title="All of Will Cook's websites and videos"><img src="${base}plectis.svg" alt="Will Cook: all websites and videos" width="26" height="26" /></a><span class="fam-lockup__rule" aria-hidden="true"></span><a class="fam-lockup__site" href="${base}" aria-label="${siteName}, front page"><svg viewBox="0 0 32 32" aria-hidden="true" class="wordmark__mark"><path d="M4 27 L4 5 M4 27 L28 27" fill="none" stroke-width="2" stroke-linecap="round"></path><path d="M5 26 C10 22 13 17 16 14 C19 11 22 9 27 6" fill="none" stroke-width="2.6" stroke-linecap="round"></path><circle cx="16" cy="14" r="3"></circle></svg><span class="fam-lockup__name" translate="no">${siteName}</span></a></span><nav class="topnav" aria-label="Main">${job("read/short", "Read")}${job("map", "Map")}${job("compare", "Compare")}${job("checks", "What ran")}${job("lean", "Lean index", true)}</nav></header>`;
}

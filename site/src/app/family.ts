// Will Cook's websites and films, as the family registry lists them. family.json is an
// unchanged copy of sites.json from https://github.com/wcook04/wcook04.github.io, whose
// docs/family.md is the contract: the header's ladder, the film slots and the footer's
// sister sites are rendered from this copy at build time, so the page requests nothing
// from another host. To show a released film, copy the new sites.json here and its two
// stills into public/films/.

import registry from "./family.json";

export interface FamilyLink {
  label: string;
  href: string;
}

export interface FamilySite {
  id: string;
  name: string;
  /** The name in the sister-sites list. */
  short: string;
  url: string;
  purpose: string;
  status: string | null;
  films: string[];
  repos: FamilyLink[];
}

export interface FamilyFilm {
  id: string;
  /** The published title, or the working title while the film is in preparation. */
  title: string;
  /** The name on a held frame. */
  short: string;
  description: string;
  /** Set only once the film is on YouTube. */
  youtube: string | null;
  duration_seconds: number | null;
  /** The registry's path to the stills without the width, e.g. "assets/films/atlas". */
  still: string | null;
}

export interface Family {
  owner: { name: string; home: string; lede: string; contact: FamilyLink[] };
  sites: FamilySite[];
  films: FamilyFilm[];
}

export const FAMILY: Family = registry;

/** This website's entry in the registry. */
export const THIS_SITE_ID = "lean-exposition";

export function familySite(id: string): FamilySite {
  const site = FAMILY.sites.find((s) => s.id === id);
  if (!site) throw new Error(`family.json lists no website "${id}"`);
  return site;
}

export function familyFilm(id: string): FamilyFilm {
  const film = FAMILY.films.find((f) => f.id === id);
  if (!film) throw new Error(`family.json lists no film "${id}"`);
  return film;
}

/** The series name a held frame carries: this website's name. */
export const FILM_SERIES = familySite(THIS_SITE_ID).name;

const YOUTUBE = /^https:\/\/(?:www\.youtube\.com\/watch\?v=|youtu\.be\/)[\w-]+/;

/** A film is released once the registry gives its YouTube address; until then it is held in preparation. */
export function isReleased(film: FamilyFilm): film is FamilyFilm & { youtube: string } {
  return typeof film.youtube === "string" && YOUTUBE.test(film.youtube);
}

/** The still's two copies, served from public/films/ under the site's base path. */
export function stillSources(film: FamilyFilm, base: string = import.meta.env.BASE_URL ?? "/"): { src: string; srcSet: string } | null {
  if (!film.still) return null;
  const name = film.still.split("/").pop();
  if (!name) return null;
  const at = (width: number) => `${base}films/${name}-${width}.webp`;
  return { src: at(640), srcSet: `${at(640)} 640w, ${at(1280)} 1280w` };
}

/** A running time as a player shows it: "5:27", "1:02:03". */
export function clockTime(seconds: number): string {
  const s = Math.max(0, Math.round(seconds));
  const h = Math.floor(s / 3600);
  const m = Math.floor((s % 3600) / 60);
  const pad = (n: number) => String(n).padStart(2, "0");
  return h ? `${h}:${pad(m)}:${pad(s % 60)}` : `${m}:${pad(s % 60)}`;
}

/** A running time in words: "5 minutes 27 seconds", "30 minutes". */
export function spokenTime(seconds: number): string {
  const s = Math.max(0, Math.round(seconds));
  const unit = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`;
  const parts = [
    Math.floor(s / 3600) && unit(Math.floor(s / 3600), "hour"),
    Math.floor((s % 3600) / 60) && unit(Math.floor((s % 3600) / 60), "minute"),
    s % 60 && unit(s % 60, "second"),
  ].filter(Boolean);
  return parts.length ? parts.join(" ") : unit(0, "second");
}

/** Whole minutes, for a sentence that names a film's length. */
export function minutesOf(film: FamilyFilm): number | null {
  return film.duration_seconds ? Math.round(film.duration_seconds / 60) : null;
}

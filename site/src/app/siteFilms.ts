// The videos this site puts in front of a reader, in the order it shows them: the short
// video of this website first and largest, then the two about the mathematics. Titles,
// addresses, lengths and stills come from the family registry (family.json); only the
// few words above each title are this site's. The front page's first screen (heroMarkup.ts,
// which also runs in vite.config.ts) and the bar's Videos menu both read this list, so the
// module uses no browser API and no import.meta.

import registry from "./family.json" with { type: "json" };

export interface SiteFilm {
  id: string;
  /** What the video is of, in this site's words. */
  kicker: string;
  title: string;
  /** The YouTube watch address. */
  href: string;
  /** "1:32" */
  clock: string;
  /** "1 minute 32 seconds" */
  spoken: string;
  /** The still at 640 and 1280 pixels wide, under the site's base path. */
  src: string;
  srcSet: string;
}

const SHOWN: { id: string; kicker: string }[] = [
  { id: "short-sk-website", kicker: "This website in use" },
  { id: "sk-no-gap", kicker: "The result explained" },
  { id: "short-sk-no-gap", kicker: "The result in brief" },
];

const unit = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`;

function clock(seconds: number): string {
  const m = Math.floor(seconds / 60);
  return `${m}:${String(seconds % 60).padStart(2, "0")}`;
}

function spoken(seconds: number): string {
  const m = Math.floor(seconds / 60);
  const s = seconds % 60;
  return [m && unit(m, "minute"), s && unit(s, "second")].filter(Boolean).join(" ");
}

/** The site's videos, lead first. `base` is the site's base path, ending in a slash. */
export function siteFilms(base: string): SiteFilm[] {
  return SHOWN.map(({ id, kicker }) => {
    const film = registry.films.find((f) => f.id === id);
    if (!film || !film.youtube || !film.duration_seconds || !film.still) throw new Error(`family.json has no released film "${id}"`);
    const name = film.still.split("/").pop();
    const at = (width: number) => `${base}films/${name}-${width}.webp`;
    return {
      id,
      kicker,
      title: film.title,
      href: film.youtube,
      clock: clock(film.duration_seconds),
      spoken: spoken(film.duration_seconds),
      src: at(640),
      srcSet: `${at(640)} 640w, ${at(1280)} 1280w`,
    };
  });
}

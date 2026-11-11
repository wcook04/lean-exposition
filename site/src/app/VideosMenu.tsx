// Videos: a quiet button in the bar on every page that opens a small popover of the
// site's three videos, so a reader can reach them from a paper without leaving it.
// It is a disclosure, not a menu: the popover holds ordinary links, each opening
// YouTube in a new tab. The lead film shows a full-width still; the others sit in
// compact rows. As in FilmSlot, the picture and the title open the same video, so
// only the title is in the Tab order and it says the running time in words. On
// phones the button is hidden and the phone menu lists the same rows (VideoRows).

import { useEffect, useId, useRef, useState } from "react";
import { siteFilms, type SiteFilm } from "./siteFilms";
import "./videos-menu.css";

const FILMS = siteFilms(import.meta.env.BASE_URL);

function Frame({ film, sizes }: { film: SiteFilm; sizes: string }) {
  return (
    <a className="film-slot__frame" href={film.href} target="_blank" rel="noopener noreferrer" aria-hidden="true" tabIndex={-1}>
      <img src={film.src} srcSet={film.srcSet} sizes={sizes} alt="" width={1280} height={720} loading="lazy" decoding="async" />
      <span className="film-slot__play" />
      <span className="film-slot__time">{film.clock}</span>
    </a>
  );
}

function TitleLink({ film }: { film: SiteFilm }) {
  return (
    <a className="videos__link" href={film.href} target="_blank" rel="noopener noreferrer">
      {film.title}
      <span className="sr-only">, video on YouTube, {film.spoken}</span>
    </a>
  );
}

/** One film as a compact row: a small still on the left, its kicker and title on the right. */
function Row({ film }: { film: SiteFilm }) {
  return (
    <div className="film-slot film-slot--small videos__row" data-film={film.id}>
      <Frame film={film} sizes="112px" />
      <div className="videos__words">
        <span className="videos__kicker">{film.kicker}</span>
        <span className="videos__title">
          <TitleLink film={film} />
        </span>
      </div>
    </div>
  );
}

/** The site's films as compact rows, for the phone menu. */
export function VideoRows({ labelledBy }: { labelledBy: string }) {
  return (
    <ul className="videos__rows videos__rows--phone" aria-labelledby={labelledBy}>
      {FILMS.map((film) => (
        <li key={film.id}>
          <Row film={film} />
        </li>
      ))}
    </ul>
  );
}

export function VideosMenu() {
  const id = useId();
  const [open, setOpen] = useState(false);
  // Opened from the keyboard, the popover appears at once with no entrance.
  const [instant, setInstant] = useState(false);
  const buttonRef = useRef<HTMLButtonElement>(null);
  const wrapRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!open) return;
    const onPointer = (event: PointerEvent) => {
      if (!wrapRef.current?.contains(event.target as Node)) setOpen(false);
    };
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape") return;
      event.preventDefault();
      setOpen(false);
      buttonRef.current?.focus({ preventScroll: true });
    };
    document.addEventListener("pointerdown", onPointer);
    document.addEventListener("keydown", onKey);
    return () => {
      document.removeEventListener("pointerdown", onPointer);
      document.removeEventListener("keydown", onKey);
    };
  }, [open]);

  const [lead, ...rest] = FILMS;
  return (
    <div
      className="videos"
      ref={wrapRef}
      onBlur={(event) => {
        const next = event.relatedTarget as Node | null;
        if (open && next && !wrapRef.current?.contains(next)) setOpen(false);
      }}
    >
      <button
        ref={buttonRef}
        type="button"
        className="videos__button"
        aria-expanded={open}
        aria-controls={`${id}-pop`}
        onClick={(event) => {
          setInstant(event.detail === 0);
          setOpen((o) => !o);
        }}
      >
        <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true" className="videos__icon">
          <path d="M2.5 1.6v6.8L8.4 5z" fill="currentColor" />
        </svg>
        Videos
      </button>
      <div id={`${id}-pop`} className={`videos__pop${instant ? " videos__pop--instant" : ""}`} hidden={!open}>
        <div className="film-slot videos__lead" data-film={lead.id}>
          <Frame film={lead} sizes="320px" />
          <span className="videos__kicker">{lead.kicker}</span>
          <span className="videos__title videos__title--lead">
            <TitleLink film={lead} />
          </span>
        </div>
        <ul className="videos__rows">
          {rest.map((film) => (
            <li key={film.id}>
              <Row film={film} />
            </li>
          ))}
        </ul>
      </div>
    </div>
  );
}

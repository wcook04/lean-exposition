// A film's place on a page, in the family's markup (docs/family.md in
// wcook04.github.io; styles in styles/family.css). A released film shows its still,
// play chip and running time, and its title opens YouTube in a new tab; the picture
// opens the same video, so only the title is in the Tab order and it says the running
// time in words. A film without a YouTube address is held in preparation: the frame
// with this site's registration marks, the film's short name and no link. The slot
// switches by itself when family.json gives the film's address and still.

import { clockTime, FILM_SERIES, isReleased, spokenTime, stillSources, type FamilyFilm } from "./family";

interface Props {
  film: FamilyFilm;
  /** film-slot--small or film-slot--large: the play chip and the title size. */
  size?: "small" | "large";
  /** The still's displayed width, for the browser's choice between its two copies. */
  sizes?: string;
  className?: string;
}

export function FilmSlot({ film, size, sizes = "(min-width: 960px) 480px, 100vw", className }: Props) {
  const classes = ["film-slot", size && `film-slot--${size}`, !isReleased(film) && "film-slot--pending", className].filter(Boolean).join(" ");
  if (!isReleased(film)) {
    return (
      <figure className={classes}>
        <div className="film-slot__frame film-slot__frame--pending" aria-hidden="true">
          <span className="film-slot__series">{FILM_SERIES}</span>
          <span className="film-slot__name">{film.short}</span>
          <span className="film-slot__status">In preparation</span>
        </div>
        <figcaption className="film-slot__caption">
          <p className="film-slot__title">{film.title}</p>
          <p className="film-slot__meta">Video in preparation</p>
          <p className="film-slot__text">{film.description}</p>
        </figcaption>
      </figure>
    );
  }
  const still = stillSources(film);
  const seconds = film.duration_seconds;
  return (
    <figure className={classes}>
      <a className="film-slot__frame" href={film.youtube} target="_blank" rel="noopener noreferrer" aria-hidden="true" tabIndex={-1}>
        {still && (
          <img src={still.src} srcSet={still.srcSet} sizes={sizes} alt="" width={1280} height={720} loading="lazy" decoding="async" />
        )}
        <span className="film-slot__play" />
        {seconds ? <span className="film-slot__time">{clockTime(seconds)}</span> : null}
      </a>
      <figcaption className="film-slot__caption">
        <p className="film-slot__title">
          <a href={film.youtube} target="_blank" rel="noopener noreferrer">
            {film.title}
            <span className="sr-only">, video on YouTube{seconds ? `, ${spokenTime(seconds)}` : ""}</span>
          </a>
        </p>
        <p className="film-slot__text">{film.description}</p>
      </figcaption>
    </figure>
  );
}

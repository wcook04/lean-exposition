// The front page's first screen. Its markup is the HTML the build put in index.html
// (heroMarkup.ts), so taking over from that HTML changes nothing on the screen.
import { HERO_HTML } from "virtual:front-hero";

export function FrontHero() {
  return <div className="front" dangerouslySetInnerHTML={{ __html: HERO_HTML }} />;
}

/** The same markup inside the page's own container. */
export function FrontHeroBody() {
  return <div className="front__herowrap" dangerouslySetInnerHTML={{ __html: HERO_HTML }} />;
}

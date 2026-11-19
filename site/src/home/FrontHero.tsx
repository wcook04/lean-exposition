// The front page's first screen. Its markup is the HTML the build put in index.html
// (heroMarkup.ts), so taking over from that HTML changes nothing on the screen.
import { useLayoutEffect, useRef } from "react";
import { HERO_HTML } from "virtual:front-hero";
import { HERO_BREAK } from "./heroMarkup";

// The pictures in the first screen are radio buttons that work before any script runs. A
// reader may choose one while the scripts are still loading, and React then draws the markup
// again with the first picture chosen. So the choice is read here, when this module loads and
// at every change, and put back whenever the markup is drawn.
const SHOT = 'input[name="front-shot"]';
let chosen: string | undefined = typeof document === "undefined" ? undefined : document.querySelector<HTMLInputElement>(`${SHOT}:checked`)?.value;
if (typeof document !== "undefined") {
  document.addEventListener("change", (event) => {
    const input = event.target;
    if (input instanceof HTMLInputElement && input.name === "front-shot" && input.checked) chosen = input.value;
  });
}

function useChosenShot() {
  const ref = useRef<HTMLDivElement>(null);
  useLayoutEffect(() => {
    if (!chosen) return;
    const input = ref.current?.querySelector<HTMLInputElement>(`${SHOT}[value="${chosen}"]`);
    if (input) input.checked = true;
  }, []);
  return ref;
}

export function FrontHero() {
  const ref = useChosenShot();
  return <div ref={ref} className="front" dangerouslySetInnerHTML={{ __html: HERO_HTML }} />;
}

/**
 * The same markup inside the page's own container. An instance whose markup divides at
 * HERO_BREAK may draw the two parts separately, with a band between them in reading order.
 */
export function FrontHeroBody({ part }: { part?: "first" | "rest" } = {}) {
  const ref = useChosenShot();
  const [first, rest = ""] = HERO_HTML.split(HERO_BREAK);
  const html = part === "first" ? first : part === "rest" ? rest : HERO_HTML;
  return <div ref={ref} className="front__herowrap" dangerouslySetInnerHTML={{ __html: html }} />;
}

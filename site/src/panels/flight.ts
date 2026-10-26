// The title flight: when a visible card on the map is clicked, its title travels from
// the card into the panel's heading, so the reader sees which card the panel
// now describes. A FLIP ghost of the panel title starts over the card title
// (scaled to its size) and settles into place; the real heading is revealed
// when it lands.
//
// The card's position is read at the moment of the click, in the capture
// phase, before the map handles the click and before the panel swaps its
// content or the canvas changes width. Nothing in the map is modified.

import { prefersReducedMotion } from "../app/theme";

interface Captured {
  id: string;
  rect: DOMRect;
  fontSize: number;
  at: number;
}

let captured: Captured | null = null;
let installed = false;

function measure(card: Element): { rect: DOMRect; fontSize: number } {
  const title = card.querySelector<HTMLElement>(".card__title") ?? (card as HTMLElement);
  const rect = title.getBoundingClientRect();
  const fontSize = parseFloat(getComputedStyle(title).fontSize) || 16;
  return { rect, fontSize };
}

function capture(event: Event): void {
  const target = event.target as Element | null;
  const card = target?.closest?.("[data-card]");
  if (!card) return;
  const id = card.getAttribute("data-card");
  if (!id) return;
  captured = { id, ...measure(card), at: performance.now() };
}

/** Listen, in the capture phase, for clicks and Enter on map cards. Idempotent. */
export function installCardCapture(): void {
  if (installed || typeof document === "undefined") return;
  installed = true;
  document.addEventListener("pointerdown", capture, true);
  document.addEventListener("click", capture, true);
  document.addEventListener(
    "keydown",
    (event) => {
      if (event.key === "Enter" || event.key === " ") capture(event);
    },
    true,
  );
}

function onScreen(rect: DOMRect): boolean {
  return (
    rect.width > 0 &&
    rect.height > 0 &&
    rect.bottom > 0 &&
    rect.right > 0 &&
    rect.top < window.innerHeight &&
    rect.left < window.innerWidth
  );
}

/**
 * Where the card for `id` was: from the click that chose it, if recent, or
 * (when `allowLive`) from the card where it stands now.
 */
export function sourceFor(id: string, allowLive: boolean): { rect: DOMRect; fontSize: number } | null {
  const fresh = captured && captured.id === id && performance.now() - captured.at < 1200 ? captured : null;
  captured = null;
  if (fresh) return onScreen(fresh.rect) ? fresh : null;
  if (!allowLive) return null;
  const card = document.querySelector(`[data-card="${CSS.escape(id)}"]`);
  if (!card) return null;
  const live = measure(card);
  return onScreen(live.rect) ? live : null;
}

const FLIGHT_MS = 240;
/** A reselection sooner than this after the last flight lands at once. */
const RAPID_MS = 600;
let lastFlight = -Infinity;

/** Fly a ghost of `target` from `from` into place. Returns a cancel function. */
export function flyTitle(target: HTMLElement, from: { rect: DOMRect; fontSize: number }): () => void {
  if (prefersReducedMotion() || typeof target.animate !== "function") return () => undefined;
  const now = performance.now();
  const rapid = now - lastFlight < RAPID_MS;
  lastFlight = now;
  if (rapid) return () => undefined;
  const to = target.getBoundingClientRect();
  if (!onScreen(to)) return () => undefined;
  const style = getComputedStyle(target);
  const scale = from.fontSize / (parseFloat(style.fontSize) || 16);
  const dx = from.rect.left - to.left;
  const dy = from.rect.top - to.top;

  const ghost = target.cloneNode(true) as HTMLElement;
  ghost.removeAttribute("id");
  ghost.removeAttribute("tabindex");
  ghost.setAttribute("aria-hidden", "true");
  ghost.className = `${target.className} title-ghost`;
  Object.assign(ghost.style, {
    position: "fixed",
    left: `${to.left}px`,
    top: `${to.top}px`,
    width: `${to.width}px`,
    margin: "0",
    color: style.color,
    transformOrigin: "0 0",
    pointerEvents: "none",
    zIndex: "60",
  });
  document.body.appendChild(ghost);
  // Opacity, not visibility: the real heading stays in the accessibility tree
  // and keeps the focus it was given while the ghost travels.
  target.style.opacity = "0";

  const ease = getComputedStyle(document.documentElement).getPropertyValue("--ease-move").trim() || "ease-in-out";
  const animation = ghost.animate(
    [
      { transform: `translate(${dx}px, ${dy}px) scale(${scale})`, opacity: 0.9 },
      { transform: "translate(0, 0) scale(1)", opacity: 1 },
    ],
    { duration: FLIGHT_MS, easing: ease, fill: "both" },
  );
  let done = false;
  const finish = () => {
    if (done) return;
    done = true;
    target.style.opacity = "";
    ghost.remove();
  };
  animation.onfinish = finish;
  animation.oncancel = finish;
  return () => {
    animation.cancel();
    finish();
  };
}

// Day and night schemes. A stored choice is kept only when it differs from
// the system's, so choosing the system's own scheme follows the system again.

import { useSyncExternalStore } from "react";

export type Scheme = "light" | "dark";
const KEY = "lx-theme";

export function systemScheme(): Scheme {
  return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
}

export function currentScheme(): Scheme {
  const forced = document.documentElement.getAttribute("data-theme");
  return forced === "light" || forced === "dark" ? forced : systemScheme();
}

export function setScheme(next: Scheme): void {
  const root = document.documentElement;
  root.classList.add("no-transitions");
  if (next === systemScheme()) {
    root.removeAttribute("data-theme");
    try {
      localStorage.removeItem(KEY);
    } catch {
      /* storage unavailable */
    }
  } else {
    root.setAttribute("data-theme", next);
    try {
      localStorage.setItem(KEY, next);
    } catch {
      /* storage unavailable */
    }
  }
  document.dispatchEvent(new CustomEvent("lx:scheme"));
  requestAnimationFrame(() => requestAnimationFrame(() => root.classList.remove("no-transitions")));
}

export function onSchemeChange(listener: () => void): () => void {
  const media = window.matchMedia("(prefers-color-scheme: dark)");
  document.addEventListener("lx:scheme", listener);
  media.addEventListener("change", listener);
  return () => {
    document.removeEventListener("lx:scheme", listener);
    media.removeEventListener("change", listener);
  };
}

export function prefersReducedMotion(): boolean {
  return window.matchMedia("(prefers-reduced-motion: reduce)").matches;
}

const REDUCE = "(prefers-reduced-motion: reduce)";

function subscribeReducedMotion(listener: () => void): () => void {
  const media = window.matchMedia(REDUCE);
  media.addEventListener("change", listener);
  return () => media.removeEventListener("change", listener);
}

/**
 * Whether the reader asks for reduced motion, read live: a component using
 * this re-renders when the system setting changes mid-visit.
 */
export function useReducedMotion(): boolean {
  return useSyncExternalStore(subscribeReducedMotion, prefersReducedMotion, () => false);
}

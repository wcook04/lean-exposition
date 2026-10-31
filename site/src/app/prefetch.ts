// Each page's code, fetched once. Pointing at or focusing a link starts the fetch, so
// the page is usually ready by the time the click lands; nothing loads until then.

import { useEffect } from "react";
import { parseRoute, type Route } from "./router";

export const PAGES = {
  home: () => import("../home/FrontPage"),
  map: () => import("../map/MapPage"),
  read: () => import("../reader/ReaderPage"),
  compare: () => import("../compare/ComparePage"),
  lean: () => import("../lean/LeanPage"),
  checks: () => import("../checks/ChecksPage"),
  about: () => import("../reader/AboutPage"),
  search: () => import("../search/SearchPage"),
} satisfies Partial<Record<Route["view"], () => Promise<unknown>>>;

const started = new Set<string>();

function prefetch(view: Route["view"]): void {
  if (started.has(view) || !(view in PAGES)) return;
  started.add(view);
  void PAGES[view as keyof typeof PAGES]().catch(() => started.delete(view));
}

/** Start fetching the page behind any link of this site that the reader points at or tabs to. */
export function usePrefetchOnIntent(): void {
  useEffect(() => {
    const onIntent = (event: Event) => {
      const link = (event.target as Element | null)?.closest?.("a[href]") as HTMLAnchorElement | null;
      if (!link || link.origin !== window.location.origin) return;
      prefetch(parseRoute(new URL(link.href)).view);
    };
    document.addEventListener("pointerover", onIntent, { passive: true });
    document.addEventListener("focusin", onIntent);
    return () => {
      document.removeEventListener("pointerover", onIntent);
      document.removeEventListener("focusin", onIntent);
    };
  }, []);
}

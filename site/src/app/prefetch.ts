// Each page's code, fetched once. The page being opened starts at once, so its code and
// its data download together. Pointing at or focusing a link starts that page's fetch, so
// it is usually ready by the time the click lands.

import { useEffect } from "react";
import { code, type Code } from "./code";
import { parseRoute, type Route } from "./router";

export const PAGES = {
  home: code(() => import("../home/FrontPage")),
  map: code(() => import("../map/MapPage")),
  read: code(() => import("../reader/ReaderPage")),
  compare: code(() => import("../compare/ComparePage")),
  lean: code(() => import("../lean/LeanPage")),
  checks: code(() => import("../checks/ChecksPage")),
  about: code(() => import("../reader/AboutPage")),
  search: code(() => import("../search/SearchPage")),
} satisfies Partial<Record<Route["view"], Code<unknown>>>;

export function prefetch(view: Route["view"]): void {
  if (view in PAGES) PAGES[view as keyof typeof PAGES].start();
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

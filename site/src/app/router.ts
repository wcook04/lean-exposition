// Every navigational state lives in the URL, so Back, reload and shared links
// return to the same view, selection and reading position.

import { useEffect, useSyncExternalStore } from "react";
import type { Stage } from "../api/types";
import { arrive, pushEntry, replaceEntry, setDefaultLabel } from "./trail";

export type Trace = "rests" | "uses";

export type Route =
  | { view: "home"; anchor?: string }
  | {
      view: "map";
      node?: string;
      trace?: Trace;
      lens?: Stage;
      goal?: string;
      /** A selected step between two records: an `ArgEdge.key`. */
      edge?: string;
    }
  | {
      view: "read";
      stage: Stage;
      anchor?: string;
      /** The exact source to land on: a line ("120"), lines ("120-134") or a byte range ("b4521-5120"). */
      at?: string;
      node?: string;
      beside?: { stage: Stage; anchor: string };
    }
  | { view: "checks"; node?: string }
  | {
      view: "compare";
      /** The record read across its levels. Without one, the table of every step. */
      node?: string;
      /** The table, opened at this record. */
      at?: string;
      /** Which levels show, in order, when the reader has chosen. */
      levels?: Level[];
      /** The table with the steps only some of the levels have, as well as those all of them have. */
      any?: boolean;
    }
  | {
      view: "lean";
      module?: string;
      decl?: string;
      /** A folder of the tree, as its path. */
      folder?: string;
      /** The list of declarations linked to the papers. */
      index?: "papers";
    }
  | { view: "about"; anchor?: string }
  | {
      view: "search";
      /** The exact words typed, as given. */
      q: string;
      /** Which kind of result to list; absent means the first kind with matches. */
      type?: SearchType;
      /** 1-based page of results within that kind. */
      page?: number;
    }
  | { view: "missing"; path: string };

/** The levels of the funnel, from the Lean down to the exposition. */
export const LEVELS = ["lean", "long", "short", "expository"] as const;
export type Level = (typeof LEVELS)[number];

function isLevel(value: string): value is Level {
  return (LEVELS as readonly string[]).includes(value);
}

/** The kinds of result search lists, each one table of the edition. */
export const SEARCH_TYPES = ["records", "statements", "sections", "text", "passages", "citations", "sources", "checks"] as const;
export type SearchType = (typeof SEARCH_TYPES)[number];

function isSearchType(value: string | null): value is SearchType {
  return !!value && (SEARCH_TYPES as readonly string[]).includes(value);
}

const STAGE_SET = new Set(["long", "short", "expository"]);
const BASE = (import.meta.env.BASE_URL ?? "/").replace(/\/$/, "");

function isStage(value: string | null | undefined): value is Stage {
  return !!value && STAGE_SET.has(value);
}

function fragmentOf(url: URL): string | undefined {
  const raw = url.hash.replace(/^#/, "");
  if (!raw) return undefined;
  try {
    return decodeURIComponent(raw);
  } catch {
    // A malformed fragment should reach the reader's missing-anchor notice,
    // rather than preventing the whole application from opening.
    return raw;
  }
}

const AT_PARAM = /^(?:\d+(?:-\d+)?|b\d+-\d+)$/;

export function parseRoute(url: URL): Route {
  let path = url.pathname;
  if (BASE && path.startsWith(BASE)) path = path.slice(BASE.length) || "/";
  path = path.replace(/\/+$/, "") || "/";
  const q = url.searchParams;
  const hash = fragmentOf(url);
  // The front page lives at "/". The map moved to "/map"; a link to "/" that
  // carries any map parameter was made when the map lived there, so it still
  // opens the map.
  const MAP_PARAMS = ["g", "n", "t", "lens", "e"];
  if (path === "/" && !MAP_PARAMS.some((name) => q.has(name))) return hash ? { view: "home", anchor: hash } : { view: "home" };
  if (path === "/" || path === "/map") {
    const trace = q.get("t");
    const lens = q.get("lens");
    return {
      view: "map",
      node: q.get("n") ?? undefined,
      trace: trace === "rests" || trace === "uses" ? trace : undefined,
      lens: isStage(lens) ? lens : undefined,
      goal: q.get("g") ?? undefined,
      edge: edgeKeyFromParam(q.get("e")),
    };
  }
  const read = path.match(/^\/read\/([a-z]+)$/);
  if (read && isStage(read[1])) {
    const beside = q.get("beside");
    const [bStage, ...bAnchor] = beside ? beside.split(":") : [];
    return {
      view: "read",
      stage: read[1],
      anchor: hash,
      at: AT_PARAM.test(q.get("l") ?? "") ? q.get("l")! : undefined,
      node: q.get("n") ?? undefined,
      beside: isStage(bStage) && bAnchor.length ? { stage: bStage, anchor: bAnchor.join(":") } : undefined,
    };
  }
  if (path === "/checks") return { view: "checks", node: q.get("n") ?? undefined };
  if (path === "/compare") {
    const levels = q.get("levels")?.split(",").filter(isLevel);
    return { view: "compare", node: q.get("n") ?? undefined, at: q.get("at") ?? undefined, levels: levels?.length ? levels : undefined, any: q.get("in") === "any" || undefined };
  }
  if (path === "/lean") return { view: "lean", module: q.get("m") ?? undefined, decl: q.get("d") ?? undefined, folder: q.get("f") ?? undefined, index: q.get("list") === "papers" ? "papers" : undefined };
  if (path === "/about") return { view: "about", anchor: hash };
  if (path === "/search") {
    const type = q.get("type");
    const page = Number(q.get("p"));
    return {
      view: "search",
      q: q.get("q") ?? "",
      type: isSearchType(type) ? type : undefined,
      page: Number.isInteger(page) && page > 1 ? page : undefined,
    };
  }
  return { view: "missing", path };
}

// Edges travel as `from~to~kind`; the key itself uses arrows, which read badly in a URL.
function edgeKeyFromParam(value: string | null): string | undefined {
  const parts = value?.split("~") ?? [];
  return parts.length === 3 && parts.every(Boolean) ? parts.join("→") : undefined;
}

function edgeParam(key: string): string {
  return key.split("→").join("~");
}

/** Like URLSearchParams, but keeps `:` and `,` readable; both are legal in a query. */
class Query {
  private pairs: [string, string][] = [];
  set(name: string, value: string): void {
    this.pairs.push([name, value]);
  }
  toString(): string {
    const encode = (v: string) => encodeURIComponent(v).replace(/%3A/gi, ":").replace(/%2C/gi, ",");
    return this.pairs.map(([k, v]) => `${encode(k)}=${encode(v)}`).join("&");
  }
}

export function routeHref(route: Route): string {
  const q = new Query();
  switch (route.view) {
    case "home":
      return `${BASE}/${route.anchor ? `#${encodeURIComponent(route.anchor)}` : ""}`;
    case "map": {
      if (route.goal) q.set("g", route.goal);
      if (route.node) q.set("n", route.node);
      if (route.trace) q.set("t", route.trace);
      if (route.lens) q.set("lens", route.lens);
      if (route.edge) q.set("e", edgeParam(route.edge));
      const s = q.toString();
      return `${BASE}/map${s ? `?${s}` : ""}`;
    }
    case "read": {
      if (route.at) q.set("l", route.at);
      if (route.node) q.set("n", route.node);
      if (route.beside) q.set("beside", `${route.beside.stage}:${route.beside.anchor}`);
      const s = q.toString();
      return `${BASE}/read/${route.stage}${s ? `?${s}` : ""}${route.anchor ? `#${encodeURIComponent(route.anchor)}` : ""}`;
    }
    case "checks":
      if (route.node) q.set("n", route.node);
      return `${BASE}/checks${q.toString() ? `?${q}` : ""}`;
    case "compare": {
      if (route.node) q.set("n", route.node);
      if (route.at) q.set("at", route.at);
      if (route.levels) q.set("levels", route.levels.join(","));
      if (route.any) q.set("in", "any");
      const s = q.toString();
      return `${BASE}/compare${s ? `?${s}` : ""}`;
    }
    case "lean": {
      if (route.module) q.set("m", route.module);
      if (route.decl) q.set("d", route.decl);
      if (route.folder) q.set("f", route.folder);
      if (route.index) q.set("list", route.index);
      const s = q.toString();
      return `${BASE}/lean${s ? `?${s}` : ""}`;
    }
    case "about":
      return `${BASE}/about${route.anchor ? `#${encodeURIComponent(route.anchor)}` : ""}`;
    case "search": {
      q.set("q", route.q);
      if (route.type) q.set("type", route.type);
      if (route.page && route.page > 1) q.set("p", String(route.page));
      return `${BASE}/search?${q}`;
    }
    case "missing":
      return route.path;
  }
}

let current = parseRoute(new URL(window.location.href));
const listeners = new Set<() => void>();

function emit() {
  current = parseRoute(new URL(window.location.href));
  listeners.forEach((l) => l());
}

window.addEventListener("popstate", () => {
  arrive();
  emit();
});

/**
 * Push when what the reader is looking at changes (page, pinned record, passage,
 * Lean declaration, search query). Replace for refinements (tabs, scroll, camera,
 * filters). Leave hooks run first, so every link keeps its place with no special
 * cases. Following and pointing never push.
 */
export function navigate(to: Route | string, options: { replace?: boolean } = {}): void {
  const href = typeof to === "string" ? to : routeHref(to);
  const next = new URL(href, window.location.href);
  if (next.href === window.location.href) return;
  if (options.replace) replaceEntry(next);
  else pushEntry(next);
  emit();
}

/** What a page is called on the Back control when it has not named its place more exactly. */
export function placeOf(route: Route): string {
  switch (route.view) {
    case "home":
      return "the front page";
    case "map":
      return "the map";
    case "read":
      return { long: "Long paper", short: "Short paper", expository: "Exposition" }[route.stage];
    case "checks":
      return "Checks";
    case "compare":
      return "Compare";
    case "lean":
      return route.decl?.split(".").pop() ?? "the Lean";
    case "about":
      return "About";
    case "search":
      return route.q ? `search for “${route.q}”` : "search";
    case "missing":
      return "the previous page";
  }
}

setDefaultLabel((href) => placeOf(parseRoute(new URL(href))));

export function useRoute(): Route {
  return useSyncExternalStore(
    (l) => {
      listeners.add(l);
      return () => listeners.delete(l);
    },
    () => current,
  );
}

/**
 * Whether a link opens one of this site's own views. On GitHub Pages the sister
 * sites share the origin, so a path outside the site's base belongs to another site;
 * a path naming a file (a PDF, a JSON observation) is a file, and the API is the API.
 * The browser opens all of those itself.
 */
export function isAppPath(url: URL, origin: string = window.location.origin): boolean {
  if (url.origin !== origin) return false;
  if (BASE && url.pathname !== BASE && !url.pathname.startsWith(`${BASE}/`)) return false;
  if (url.pathname.startsWith(`${BASE}/api/`)) return false;
  return !/\.[a-z0-9]+$/i.test(url.pathname);
}

/** Intercept same-origin anchor clicks so internal links route without reload. */
export function useLinkInterception(): void {
  useEffect(() => {
    const onClick = (event: MouseEvent) => {
      if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
      const anchor = (event.target as Element | null)?.closest?.("a");
      if (!anchor || anchor.target || anchor.hasAttribute("download") || anchor.dataset.external !== undefined) return;
      const href = anchor.getAttribute("href");
      if (!href || href.startsWith("#") || href.startsWith("mailto:")) return;
      const url = new URL(href, window.location.href);
      if (!isAppPath(url)) return;
      event.preventDefault();
      navigate(url.pathname + url.search + url.hash);
    };
    document.addEventListener("click", onClick);
    return () => document.removeEventListener("click", onClick);
  }, []);
}

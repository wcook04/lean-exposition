// Every navigational state lives in the URL, so Back, reload and shared links
// return to the same view, selection and reading position.

import { useEffect, useSyncExternalStore } from "react";
import type { Stage } from "../api/types";

export type Trace = "rests" | "uses";

export type Route =
  | {
      view: "map";
      node?: string;
      trace?: Trace;
      lens?: Stage;
      goal?: string;
      /** A selected step between two records: an `ArgEdge.key`. */
      edge?: string;
    }
  | { view: "read"; stage: Stage; anchor?: string; node?: string; beside?: { stage: Stage; anchor: string } }
  | { view: "checks"; node?: string }
  | { view: "about"; anchor?: string }
  | { view: "missing"; path: string };

const STAGE_SET = new Set(["long", "short", "expository"]);
const BASE = (import.meta.env.BASE_URL ?? "/").replace(/\/$/, "");

function isStage(value: string | null | undefined): value is Stage {
  return !!value && STAGE_SET.has(value);
}

export function parseRoute(url: URL): Route {
  let path = url.pathname;
  if (BASE && path.startsWith(BASE)) path = path.slice(BASE.length) || "/";
  path = path.replace(/\/+$/, "") || "/";
  const q = url.searchParams;
  const hash = decodeURIComponent(url.hash.replace(/^#/, "")) || undefined;
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
      node: q.get("n") ?? undefined,
      beside: isStage(bStage) && bAnchor.length ? { stage: bStage, anchor: bAnchor.join(":") } : undefined,
    };
  }
  if (path === "/checks") return { view: "checks", node: q.get("n") ?? undefined };
  if (path === "/about") return { view: "about", anchor: hash };
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
    case "map": {
      if (route.goal) q.set("g", route.goal);
      if (route.node) q.set("n", route.node);
      if (route.trace) q.set("t", route.trace);
      if (route.lens) q.set("lens", route.lens);
      if (route.edge) q.set("e", edgeParam(route.edge));
      const s = q.toString();
      return `${BASE}/${s ? `?${s}` : ""}`;
    }
    case "read": {
      if (route.node) q.set("n", route.node);
      if (route.beside) q.set("beside", `${route.beside.stage}:${route.beside.anchor}`);
      const s = q.toString();
      return `${BASE}/read/${route.stage}${s ? `?${s}` : ""}${route.anchor ? `#${encodeURIComponent(route.anchor)}` : ""}`;
    }
    case "checks":
      if (route.node) q.set("n", route.node);
      return `${BASE}/checks${q.toString() ? `?${q}` : ""}`;
    case "about":
      return `${BASE}/about${route.anchor ? `#${encodeURIComponent(route.anchor)}` : ""}`;
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

window.addEventListener("popstate", emit);

export function navigate(to: Route | string, options: { replace?: boolean } = {}): void {
  const href = typeof to === "string" ? to : routeHref(to);
  const next = new URL(href, window.location.href);
  if (next.href === window.location.href) return;
  // A replaced entry keeps its state (the reader keys reading positions on it).
  if (options.replace) window.history.replaceState(window.history.state, "", next);
  else window.history.pushState(null, "", next);
  emit();
}

export function useRoute(): Route {
  return useSyncExternalStore(
    (l) => {
      listeners.add(l);
      return () => listeners.delete(l);
    },
    () => current,
  );
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
      if (url.origin !== window.location.origin) return;
      if (url.pathname.startsWith(`${BASE}/api/`)) return;
      event.preventDefault();
      navigate(url.pathname + url.search + url.hash);
    };
    document.addEventListener("click", onClick);
    return () => document.removeEventListener("click", onClick);
  }, []);
}

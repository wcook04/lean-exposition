// Links and citations that name the exact edition. A session is pinned to one
// edition already; these carry that pin into a saved link or a reference, so
// a reader who returns later can tell whether they are seeing the same one.

import type { Snapshot, Stage } from "../api/types";
import { PAPER_NAMES } from "./papers";
import { routeHref, type Route } from "./router";

/** The query parameter an edition-pinned link carries: a manifest hash prefix. */
export const EDITION_PARAM = "edition";
/** Enough hex digits to tell editions apart in a link; citations carry the full hash. */
export const EDITION_PREFIX = 16;

/** An absolute link to `route` that names the edition it was read in. */
export function editionLink(route: Route, snapshot: Snapshot, origin = window.location.origin): string {
  const url = new URL(routeHref(route), origin);
  url.searchParams.set(EDITION_PARAM, snapshot.manifest_sha256.slice(0, EDITION_PREFIX));
  return url.href;
}

/** The edition a link names, if it names one. */
export function linkedEdition(href = window.location.href): string | null {
  const value = new URL(href).searchParams.get(EDITION_PARAM);
  return value && /^[0-9a-f]{6,64}$/i.test(value) ? value.toLowerCase() : null;
}

/** Whether the pinned edition is the one a link names (by hash prefix). */
export function sameEdition(linked: string, snapshot: Snapshot): boolean {
  return snapshot.manifest_sha256.toLowerCase().startsWith(linked);
}

export interface CitationTarget {
  /** The account cited, if any. */
  stage?: Stage;
  /** A record's title, or a passage's section, as shown on the page. */
  place?: string;
}

/**
 * A plain-text reference: what is cited (account, record or passage), the
 * edition (bundle, version and full manifest SHA-256) and an edition link.
 */
export function citationText(target: CitationTarget, route: Route, snapshot: Snapshot, origin = window.location.origin): string {
  const what = [target.stage ? PAPER_NAMES[target.stage].short : null, target.place ?? null].filter(Boolean).join(", ");
  return [
    `Lean Exposition${what ? `: ${what}` : ""}.`,
    `Edition ${snapshot.bundle_id} ${snapshot.bundle_version}, manifest SHA-256 ${snapshot.manifest_sha256}.`,
    editionLink(route, snapshot, origin),
  ].join(" ");
}

/** Copy text to the clipboard; resolves false when the browser refuses. */
export async function copyText(text: string): Promise<boolean> {
  try {
    await navigator.clipboard.writeText(text);
    return true;
  } catch {
    return false;
  }
}

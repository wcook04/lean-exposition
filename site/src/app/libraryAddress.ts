// The addresses of a library paper (docs/library-architecture.md, "URL scheme"), on top of the
// reader's own routes. Relative to the paper's base:
//   /                     the main document, at the top (a #fragment names a section: #5.6)
//   /theorem-1.1/         a numbered result in the authors' numbering: its statement, selected
//   /@<tie id>            one phrase, selected, with its card open
//   /lean/<full.name>     a Lean declaration, its card open beside the paper
// Query parameters keep the reader's names (v, d, dm, l). Only a library instance uses them;
// every other instance's addresses are unchanged. The table of phrases (addresses.json, written
// by scripts/library-instance.mjs from the edition) is loaded before the first render.

import site from "@instance/site";
import type { Route } from "./router";

/** A numbered result's address: kind and number, in lower case. */
export const RESULT = /^(theorem|proposition|lemma|corollary|definition|remark|conjecture|problem|example|assumption|claim|step)-[0-9a-z.]+$/;

export interface PhraseAddress { record: string | null; at: string }
let phrases: Record<string, PhraseAddress> = {};
const byPlace = new Map<string, string>();

export const LIBRARY = site.library ?? null;

/** Load the phrase table; a failure leaves phrase addresses to open the paper at its top. */
export async function loadLibraryAddresses(base: string): Promise<void> {
  if (!LIBRARY) return;
  try {
    const response = await fetch(`${base}/addresses.json`);
    if (response.ok) setLibraryAddresses((await response.json()).phrases ?? {});
  } catch {
    // The paper still opens; a phrase address then lands at the top of the paper.
  }
}

export function setLibraryAddresses(table: Record<string, PhraseAddress>): void {
  phrases = table;
  byPlace.clear();
  for (const [id, row] of Object.entries(table)) byPlace.set(`${row.record ?? `phrase:${id}`}|${row.at}`, id);
}

type Read = Extract<Route, { view: "read" }>;

/** The route a library address names, or null when the path is one of the reader's own. */
export function parseLibraryPath(path: string, q: URLSearchParams, hash: string | undefined, lib = LIBRARY): Read | null {
  if (!lib) return null;
  const stage = lib.main;
  const v = q.get("v");
  const common = { view: "read" as const, stage, anchor: hash, lean: v === "lean" || undefined, graph: v === "graph" || undefined,
    decl: q.get("d") ?? undefined, declModule: q.get("dm") ?? undefined };
  if (path === "/") return { ...common, node: q.get("n") ?? undefined, at: q.get("l") ?? undefined };
  const tie = path.match(/^\/@([^/]+)$/);
  if (tie) {
    const id = decodeURIComponent(tie[1]);
    const row = phrases[id];
    return row ? { ...common, node: row.record ?? `phrase:${id}`, at: row.at } : { ...common, node: `phrase:${id}` };
  }
  const lean = path.match(/^\/lean\/(.+)$/);
  if (lean) return { ...common, decl: decodeURIComponent(lean[1]), lean: v === "graph" ? undefined : true };
  const result = path.match(/^\/([a-z]+-[0-9a-z.]+)$/);
  if (result && RESULT.test(result[1])) return { ...common, node: `${lib.paper}.${result[1]}` };
  return null;
}

/** The library address of a read route of the main document, or null to keep the reader's own. */
export function libraryHref(route: Read, base: string, lib = LIBRARY): string | null {
  if (!lib || route.stage !== lib.main || route.beside) return null;
  const q = new URLSearchParams();
  const view = route.lean ? "lean" : route.graph && (route.node || route.decl) ? "graph" : null;
  const tail = route.anchor ? `#${encodeURIComponent(route.anchor)}` : "";
  const query = () => (q.size ? `?${q}` : "");
  const phrase = route.node && route.at ? byPlace.get(`${route.node}|${route.at}`) : route.node?.startsWith("phrase:") ? route.node.slice(7) : undefined;
  if (phrase) {
    if (view) q.set("v", view);
    if (route.decl) q.set("d", route.decl);
    return `${base}/@${encodeURIComponent(phrase)}${query()}${tail}`;
  }
  const prefix = `${lib.paper}.`;
  if (route.node?.startsWith(prefix) && RESULT.test(route.node.slice(prefix.length)) && !route.at) {
    if (view) q.set("v", view);
    if (route.decl) q.set("d", route.decl);
    return `${base}/${route.node.slice(prefix.length)}/${query()}${tail}`;
  }
  // The reader adds the place the declaration is stated (l=) as it follows it; the address stays the declaration's.
  if (route.decl && !route.node) {
    if (route.graph) q.set("v", "graph");
    if (route.declModule) q.set("dm", route.declModule);
    return `${base}/lean/${encodeURIComponent(route.decl).replace(/%2E/g, ".")}${query()}${tail}`;
  }
  if (route.node) q.set("n", route.node);
  if (route.at) q.set("l", route.at);
  if (view) q.set("v", view);
  if (route.decl) q.set("d", route.decl);
  if (route.declModule) q.set("dm", route.declModule);
  return `${base}/${query()}${tail}`;
}

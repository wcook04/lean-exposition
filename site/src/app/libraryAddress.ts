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

/** `view=pdf` and `page=N`: the PDF view of a paper and its page. */
export function pdfParams(q: URLSearchParams): { pdf?: true; page?: number } {
  if (q.get("view") !== "pdf") return {};
  const page = Number(q.get("page"));
  return Number.isInteger(page) && page >= 1 ? { pdf: true, page } : { pdf: true };
}

/** A numbered result's address: kind and number, in lower case; a result the paper states without a number keeps its claim id (`claim-reference-np-equivalence`). */
export const RESULT = /^(theorem|proposition|lemma|corollary|definition|remark|conjecture|problem|example|assumption|claim|step)-[0-9a-z.]+(?:-[0-9a-z.]+)*$/;

/** A phrase's record and place; `host` names the phrase an old (merged or replaced) id now opens. */
export interface PhraseAddress { record: string | null; at: string; host?: string }
/** A phrase link a re-import retired: the date, and the nearest current phrase (null when none). */
export interface RetiredAddress { retired: string; nearest: string | null }
let phrases: Record<string, PhraseAddress> = {};
let retiredLinks: Record<string, RetiredAddress> = {};
/**
 * A page that moved (instance.json `moved_pages`): the page it now opens, and the page each of its
 * phrases stands on where that is another one. /accounts/@<id> opens the phrase on its new page.
 */
export interface MovedPage { to: string; phrases?: Record<string, string> }
let movedPages: Record<string, MovedPage> = {};
/**
 * A later check readers may ask about (a library paper's ours.json `checks`): the Lean constant it
 * concerns (its last name), the question and its answer, and the runs and pull request behind it.
 */
export interface LaterCheck { constant: string; question: string; answer: string; runs?: string[]; pr?: string; merge?: string }
let laterChecks: LaterCheck[] = [];
/** The later checks of this paper. */
export function libraryChecks(): readonly LaterCheck[] {
  return laterChecks;
}
/**
 * Each numbered result's canonical target in the main document: the place of the tie at its statement
 * block, and the block itself (`theorem-1.1` → ["b4521-4600", "b4521-5120"]). Either place, or none,
 * is the result's own address.
 */
let resultTargets: Record<string, readonly [tie: string, block: string, record?: string]> = {};
/** A result's record when its id is not `<paper>.<address>` (a reader that moved in keeps its records' ids): record → address. */
const resultOfRecord = new Map<string, string>();
const byPlace = new Map<string, string>();
/** Each companion page's phrases, by the page's slug: `/<slug>/@<tie id>`. */
let pagePhrases: Record<string, Record<string, PhraseAddress>> = {};
const pageByPlace = new Map<string, string>();

export const LIBRARY = site.library ?? null;

/** Load the phrase table; a failure leaves phrase addresses to open the paper at its top. */
export async function loadLibraryAddresses(base: string): Promise<void> {
  if (!LIBRARY) return;
  try {
    const response = await fetch(`${base}/addresses.json`);
    if (response.ok) {
      const table = await response.json();
      setLibraryAddresses(table.phrases ?? {}, table.retired ?? {}, table.results ?? {}, table.moved ?? {}, table.pages ?? {});
      laterChecks = table.checks ?? [];
    }
  } catch {
    // The paper still opens; a phrase address then lands at the top of the paper.
  }
}

export function setLibraryAddresses(
  table: Record<string, PhraseAddress>,
  retired: Record<string, RetiredAddress> = {},
  results: Record<string, readonly [string, string, string?]> = {},
  moved: Record<string, MovedPage> = {},
  pages: Record<string, Record<string, PhraseAddress>> = {},
): void {
  phrases = table;
  movedPages = moved;
  pagePhrases = pages;
  pageByPlace.clear();
  for (const [slug, rows] of Object.entries(pages))
    for (const [id, row] of Object.entries(rows)) if (!row.host) pageByPlace.set(`${slug}|${row.record ?? `phrase:${id}`}|${row.at}`, id);
  retiredLinks = retired;
  resultTargets = results;
  resultOfRecord.clear();
  for (const [address, row] of Object.entries(results)) if (row[2]) resultOfRecord.set(row[2], address);
  byPlace.clear();
  // Copy link names the phrase itself, never an old id that redirects to it.
  for (const [id, row] of Object.entries(table)) if (!row.host) byPlace.set(`${row.record ?? `phrase:${id}`}|${row.at}`, id);
}

type Read = Extract<Route, { view: "read" }>;

/**
 * The current address of a moved page's address (relative to the paper's base, no trailing slash),
 * or null when the page did not move: /accounts → /digest, /accounts/@<id> → /<its page>/@<id>,
 * /accounts/lean/<name> → /digest/lean/<name>.
 */
export function movedLibraryPath(path: string): string | null {
  const m = path.match(/^\/([a-z0-9-]+)(\/.*)?$/);
  const moved = m ? movedPages[m[1]] : undefined;
  if (!m || !moved) return null;
  const rest = m[2] ?? "";
  const tie = rest.match(/^\/@([^/]+)$/);
  const page = tie ? (moved.phrases?.[decodeURIComponent(tie[1])] ?? moved.to) : moved.to;
  return `/${page}${rest}`;
}

/** The route a library address names, or null when the path is one of the reader's own. */
export function parseLibraryPath(path: string, q: URLSearchParams, hash: string | undefined, lib = LIBRARY): Read | null {
  if (!lib) return null;
  const stage = lib.main;
  const v = q.get("v");
  const common = { view: "read" as const, stage, anchor: hash, lean: v === "lean" || undefined, graph: v === "graph" || undefined,
    decl: q.get("d") ?? undefined, declModule: q.get("dm") ?? undefined, ...pdfParams(q) };
  if (path === "/") return { ...common, node: q.get("n") ?? undefined, at: q.get("l") ?? undefined };
  const tie = path.match(/^\/@([^/]+)$/);
  if (tie) {
    const id = decodeURIComponent(tie[1]);
    const row = phrases[id];
    if (row) return { ...common, node: row.record ?? `phrase:${row.host ?? id}`, at: row.at };
    // A retired link opens the paper with its notice; it never lands on a neighbouring phrase.
    if (retiredLinks[id]) return { ...common, retired: id };
    // An id no phrase has: the paper opens at its top and says so, never at a guessed place.
    return { ...common, missing: id };
  }
  const lean = path.match(/^\/lean\/(.+)$/);
  if (lean) return { ...common, decl: decodeURIComponent(lean[1]), lean: v === "graph" ? undefined : true };
  const moved = movedLibraryPath(path);
  if (moved && moved !== path) return parseLibraryPath(moved, q, hash, lib);
  const page = path.match(/^\/([a-z0-9-]+)$/);
  if (page && lib.pages?.[page[1]]) return { ...common, stage: lib.pages[page[1]], node: q.get("n") ?? undefined, at: q.get("l") ?? undefined };
  // A companion page's phrase (/<slug>/@<tie id>) and a declaration read beside it (/<slug>/lean/<name>).
  const inPage = path.match(/^\/([a-z0-9-]+)\/(@[^/]+|lean\/.+)$/);
  if (inPage && lib.pages?.[inPage[1]]) {
    const stage = lib.pages[inPage[1]];
    if (inPage[2].startsWith("lean/")) return { ...common, stage, decl: decodeURIComponent(inPage[2].slice(5)), lean: v === "graph" ? undefined : true };
    const id = decodeURIComponent(inPage[2].slice(1));
    // A page whose phrases this build did not list (a companion answered from its own edition) opens
    // the phrase by its id, at the place the address names.
    if (!pagePhrases[inPage[1]]) return { ...common, stage, node: `phrase:${id}`, at: q.get("l") ?? undefined };
    const row = pagePhrases[inPage[1]][id];
    return row ? { ...common, stage, node: row.record ?? `phrase:${row.host ?? id}`, at: row.at } : { ...common, stage, missing: id };
  }
  const result = path.match(/^\/([a-z]+-[0-9a-z.-]+)$/);
  // A numbered result lands on its canonical target, the statement block, never an earlier mention.
  if (result && RESULT.test(result[1])) return { ...common, node: resultTargets[result[1]]?.[2] ?? `${lib.paper}.${result[1]}`, at: resultTargets[result[1]]?.[0] || undefined };
  return null;
}

/** The library address of a read route of the main document, or null to keep the reader's own. */
/** A numbered result's canonical place in the main document, or undefined. */
export function resultTarget(address: string): readonly [tie: string, block: string, record?: string] | undefined {
  return resultTargets[address];
}

/** The retirement of a phrase link, or null for a link that is current or unknown. */
export function retiredLink(id: string | undefined): RetiredAddress | null {
  return id ? (retiredLinks[id] ?? null) : null;
}

export function libraryHref(route: Read, base: string, lib = LIBRARY): string | null {
  if (!lib || route.beside) return null;
  // A retired link keeps its own address while its notice shows.
  if (route.retired && !route.node && !route.decl && route.stage === lib.main) return `${base}/@${encodeURIComponent(route.retired)}`;
  // A phrase address that names nothing keeps its address while its notice shows.
  if (route.missing && !route.node && !route.decl) {
    const slug = route.stage === lib.main ? "" : Object.entries(lib.pages ?? {}).find(([, stage]) => stage === route.stage)?.[0];
    if (slug !== undefined) return `${base}${slug ? `/${slug}` : ""}/@${encodeURIComponent(route.missing)}`;
  }
  if (route.stage !== lib.main) {
    // A companion page of the paper: its slug, with the reader's own parameters.
    const slug = Object.entries(lib.pages ?? {}).find(([, stage]) => stage === route.stage)?.[0];
    if (!slug) return null;
    const q = new URLSearchParams();
    const view = route.lean ? "lean" : route.graph ? "graph" : null;
    const tail = route.anchor ? `#${encodeURIComponent(route.anchor)}` : "";
    const phrase = route.node && route.at ? pageByPlace.get(`${slug}|${route.node}|${route.at}`) : route.node?.startsWith("phrase:") ? route.node.slice(7) : undefined;
    if (phrase && (!pagePhrases[slug] || pagePhrases[slug][phrase])) {
      if (view) q.set("v", view);
      if (route.decl) q.set("d", route.decl);
      return `${base}/${slug}/@${encodeURIComponent(phrase)}${q.size ? `?${q}` : ""}${tail}`;
    }
    if (route.decl && !route.node) {
      if (route.graph) q.set("v", "graph");
      return `${base}/${slug}/lean/${encodeURIComponent(route.decl).replace(/%2E/g, ".")}${q.size ? `?${q}` : ""}${tail}`;
    }
    if (route.node) q.set("n", route.node);
    if (route.at) q.set("l", route.at);
    if (route.lean) q.set("v", "lean");
    else if (route.graph) q.set("v", "graph");
    if (route.decl) q.set("d", route.decl);
    if (route.pdf) q.set("view", "pdf");
    if (route.pdf && route.page) q.set("page", String(route.page));
    return `${base}/${slug}/${q.size ? `?${q}` : ""}${route.anchor ? `#${encodeURIComponent(route.anchor)}` : ""}`;
  }
  const q = new URLSearchParams();
  const view = route.lean ? "lean" : route.graph && (route.node || route.decl) ? "graph" : null;
  const tail = route.anchor ? `#${encodeURIComponent(route.anchor)}` : "";
  const query = () => {
    if (route.pdf) q.set("view", "pdf");
    if (route.pdf && route.page) q.set("page", String(route.page));
    return q.size ? `?${q}` : "";
  };
  // A numbered result at its canonical target (or at no place) keeps the result's own address.
  const prefix = `${lib.paper}.`;
  const resultId =
    (route.node && resultOfRecord.get(route.node)) ??
    (route.node?.startsWith(prefix) && RESULT.test(route.node.slice(prefix.length)) ? route.node.slice(prefix.length) : null);
  if (resultId && (!route.at || resultTargets[resultId]?.includes(route.at))) {
    if (view) q.set("v", view);
    if (route.decl) q.set("d", route.decl);
    return `${base}/${resultId}/${query()}${tail}`;
  }
  const phrase = route.node && route.at ? byPlace.get(`${route.node}|${route.at}`) : route.node?.startsWith("phrase:") ? route.node.slice(7) : undefined;
  if (phrase) {
    if (view) q.set("v", view);
    if (route.decl) q.set("d", route.decl);
    return `${base}/@${encodeURIComponent(phrase)}${query()}${tail}`;
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

// The reader's trail: one record per history entry, so Back, Forward and reload
// return to exactly where the reader was. The URL says what is selected and can
// be shared; the entry says how it was being looked at (scroll, tab, camera).
//
// Every entry has a key. Its state lives in `history.state`, mirrored in
// sessionStorage, because a popstate has already moved `history.state` to the
// entry arrived at and the one being left can then only be written through the
// mirror. So: writes go to memory first, keyed by the entry on screen; a short
// debounce carries them to both stores; leaving writes them at once.
//
// The mirror also holds each entry's identity, and which entry the tab is on,
// because `history.state` is not a promise: a redirect drops it, and Firefox
// drops it on a plain reload. A load that finds no key looks itself up there, so
// a lost `history.state` loses nothing. Every read and write of sessionStorage
// may fail (private windows, full storage); the page then works from
// `history.state` and memory alone.
//
// This module knows nothing about routes. router.ts calls `pushEntry`,
// `replaceEntry` and `arrive`, and pages use the five functions the brief names.

import { useSyncExternalStore } from "react";

type Values = Record<string, unknown>;

/** How the entry on screen was reached: fresh, by push, or by Back or Forward. */
export type Arrival = "load" | "push" | "pop";

const KEY = "lxKey";
const DEPTH = "lxDepth";
const PREVIOUS = "lxPrevious";
const ENTRY = "lxEntry";
/** The name of an entry's place, held with its values so a later visit can refresh it. */
const LABEL = "lxLabel";

/** What else stood in history.state (a visit's origin), kept to restore with the key. */
const OTHERS = "lxOthers";

const STORE = "lx-entry:";
const STORE_INDEX = "lx-entries";
const STORE_LIVE = "lx-live";
/** Entries kept in sessionStorage; older ones keep only what history.state holds. */
const STORE_LIMIT = 200;
const WRITE_DELAY = 200;
/**
 * How long after leaving a load still counts as coming back to the same entry
 * when the browser calls it a new navigation, as Firefox does for a reload.
 */
const RELOAD_WINDOW = 30_000;

/** Who an entry is, in the mirror: enough to put it back when history.state is gone. */
interface Head {
  key: string;
  depth: number;
  previous: string | null;
  href: string;
}

const hooks = new Set<() => void>();
const memory = new Map<string, Values>();
const listeners = new Set<() => void>();

let liveKey = "";
let liveHref = "";
let arrival: Arrival = "load";
let pendingLabel: string | null = null;
let pageLabel: (() => string | null | undefined) | null = null;
let defaultLabel: (href: string) => string = () => "the previous page";
let timer: ReturnType<typeof setTimeout> | null = null;
let dirty = false;
let liveDepth = 0;
let livePrevious: string | null = null;
let leaving = false;

function newKey(): string {
  return Math.random().toString(36).slice(2, 10) + Date.now().toString(36);
}

function historyState(): Values {
  const s = window.history.state as unknown;
  return s && typeof s === "object" ? (s as Values) : {};
}

function setHistory(state: Values, url?: URL): void {
  try {
    window.history.replaceState(state, "", url ?? window.location.href);
  } catch {
    /* A sandboxed frame or Safari's rate limit may refuse; the mirror still has it. */
  }
}

function loadStored(key: string): Values | null {
  try {
    const raw = sessionStorage.getItem(STORE + key);
    return raw ? (JSON.parse(raw) as Values) : null;
  } catch {
    return null;
  }
}

function valuesOf(key: string): Values {
  const held = memory.get(key);
  if (held) return held;
  const state = historyState();
  const own = state[KEY] === key && state[ENTRY] && typeof state[ENTRY] === "object" ? (state[ENTRY] as Values) : {};
  // The mirror is the newer of the two: it alone can be written after a pop.
  const values = { ...own, ...(loadStored(key) ?? {}) };
  memory.set(key, values);
  return values;
}

function loadHeads(): Head[] {
  try {
    const raw = sessionStorage.getItem(STORE_INDEX);
    const heads = raw ? (JSON.parse(raw) as unknown) : [];
    return Array.isArray(heads) ? heads.filter((h: Head) => typeof h?.key === "string" && typeof h.href === "string") : [];
  } catch {
    return [];
  }
}

/** The entry on screen, in the mirror: its values, its identity, and that the tab is on it. */
function mirror(values: Values): void {
  try {
    sessionStorage.setItem(STORE + liveKey, JSON.stringify(values));
    const index = loadHeads().filter((h) => h.key !== liveKey);
    index.push({ key: liveKey, depth: liveDepth, previous: livePrevious, href: liveHref });
    while (index.length > STORE_LIMIT) sessionStorage.removeItem(STORE + index.shift()!.key);
    sessionStorage.setItem(STORE_INDEX, JSON.stringify(index));
    sessionStorage.setItem(STORE_LIVE, JSON.stringify({ key: liveKey, at: Date.now() }));
  } catch {
    /* Storage can be unavailable; history.state still has it. */
  }
}

/** An address as a place: the host's slash after a directory makes no difference to it. */
function placeOfHref(href: string): string {
  const url = new URL(href);
  return url.pathname.replace(/\/+$/, "") + url.search + url.hash;
}

/** The newest entry at this address. */
function headAt(href: string): Head | null {
  const place = placeOfHref(href);
  return loadHeads().reverse().find((h) => placeOfHref(h.href) === place) ?? null;
}

/** The entry this load came back to, when history.state has lost it. */
function recover(): Head | null {
  try {
    const type = (performance.getEntriesByType?.("navigation")[0] as PerformanceNavigationTiming | undefined)?.type;
    if (type === "back_forward") return headAt(window.location.href);
    const raw = sessionStorage.getItem(STORE_LIVE);
    const live = raw ? (JSON.parse(raw) as { key?: string; at?: number }) : null;
    const head = loadHeads().find((h) => h.key === live?.key);
    if (!head) return null;
    if (type !== "reload" && !(Date.now() - (live?.at ?? 0) < RELOAD_WINDOW)) return null;
    return placeOfHref(head.href) === placeOfHref(window.location.href) ? head : null;
  } catch {
    return null;
  }
}

/** Write the entry on screen to both stores now. */
function flush(): void {
  if (timer) clearTimeout(timer);
  timer = null;
  if (!dirty || !liveKey) return;
  dirty = false;
  const values = valuesOf(liveKey);
  const state = historyState();
  if (state[KEY] === liveKey) {
    const { [KEY]: _key, [DEPTH]: _depth, [PREVIOUS]: _previous, [ENTRY]: _entry, ...others } = state;
    if (Object.keys(others).length) values[OTHERS] = others;
    else delete values[OTHERS];
    setHistory({ ...state, [ENTRY]: values });
  }
  mirror(values);
}

/** Stamp an entry that has no key (a first visit, or a browser fragment navigation). */
function stamp(depth: number, previous: string | null): void {
  const key = newKey();
  setHistory({ ...historyState(), [KEY]: key, [DEPTH]: depth, [PREVIOUS]: previous });
}

/** Give an entry back the identity history.state lost. */
function restamp(head: Head): void {
  const others = loadStored(head.key)?.[OTHERS];
  setHistory({ ...(others && typeof others === "object" ? (others as Values) : {}), ...historyState(), [KEY]: head.key, [DEPTH]: head.depth, [PREVIOUS]: head.previous });
}

/** Adopt the current history entry as the one on screen. */
function adopt(how: Arrival): void {
  const state = historyState();
  liveKey = state[KEY] as string;
  liveDepth = (state[DEPTH] as number | undefined) ?? 0;
  livePrevious = (state[PREVIOUS] as string | null | undefined) ?? null;
  liveHref = window.location.href;
  arrival = how;
  // A new entry has nothing to write yet, but the mirror must know who it is.
  dirty = true;
}

function notify(): void {
  listeners.forEach((l) => l());
}

function leave(): void {
  // A leaving page may name itself, and may write what it wants kept. On a pop
  // history.state has already moved on, so writes must keep to the entry on screen.
  leaving = true;
  hooks.forEach((hook) => {
    try {
      hook();
    } catch (error) {
      console.error(error);
    }
  });
  leaving = false;
  const label = pendingLabel ?? pageLabel?.() ?? defaultLabel(liveHref);
  pendingLabel = null;
  if (liveKey && label) {
    valuesOf(liveKey)[LABEL] = label;
    dirty = true;
  }
  flush();
}

function ensureCurrent(): void {
  if (leaving) return;
  if (typeof historyState()[KEY] !== "string") stamp(0, null);
  if (historyState()[KEY] !== liveKey) adopt("load");
}

// ---- What router.ts calls ------------------------------------------------------------

/** A new history entry: the one being left keeps its state, and the new one starts clean. */
export function pushEntry(url: URL): void {
  ensureCurrent();
  leave();
  window.history.pushState({ [KEY]: newKey(), [DEPTH]: liveDepth + 1, [PREVIOUS]: liveKey }, "", url);
  adopt("push");
  flush();
  notify();
}

const placePath = (href: string) => new URL(href).pathname.replace(/\/+$/, "");

/**
 * The same entry at a refined address. It keeps its state, which is what a tab,
 * a camera or a followed statement wants; a replace onto another page does not.
 */
export function replaceEntry(url: URL): void {
  ensureCurrent();
  flush();
  if (placePath(liveHref) === placePath(url.href)) {
    setHistory(historyState(), url);
    liveHref = window.location.href;
    // The mirror keeps up within the debounce: a reload must find this address.
    dirty = true;
    if (!timer) timer = setTimeout(flush, WRITE_DELAY);
    return;
  }
  const state = historyState();
  setHistory({ [KEY]: newKey(), [DEPTH]: state[DEPTH], [PREVIOUS]: state[PREVIOUS] }, url);
  adopt(arrival);
  flush();
  notify();
}

/** Back, Forward, or a fragment link the browser followed itself. Call before rendering. */
export function arrive(): void {
  leave();
  let known = typeof historyState()[KEY] === "string";
  if (!known) {
    // Unkeyed: a fragment link the browser followed, one step on from the entry left,
    // or an entry that has lost its state, which the mirror can name.
    const left = new URL(liveHref);
    const here = new URL(window.location.href);
    const fragment = left.pathname === here.pathname && left.search === here.search;
    const head = fragment ? null : headAt(here.href);
    if (head) restamp(head);
    else stamp(liveDepth + 1, liveKey);
    known = !!head;
  }
  adopt(known ? "pop" : "push");
  flush();
  notify();
}

/** Set the name used for an address when no page has named itself. */
export function setDefaultLabel(label: (href: string) => string): void {
  defaultLabel = label;
}

// ---- What pages call -----------------------------------------------------------------

/** A page registers what to save just before the reader leaves this history entry. */
export function onLeave(snapshot: () => void): () => void {
  hooks.add(snapshot);
  return () => {
    hooks.delete(snapshot);
  };
}

/** Per-entry state, kept in history.state and mirrored in sessionStorage. */
export function readEntry<T>(name: string): T | undefined {
  ensureCurrent();
  return valuesOf(liveKey)[name] as T | undefined;
}

/** A value saved in another entry, by its key: "Return to …" reads the origin's position. */
export function readEntryOf<T>(key: string, name: string): T | undefined {
  return valuesOf(key)[name] as T | undefined;
}

export function writeEntry(name: string, value: unknown): void {
  ensureCurrent();
  const values = valuesOf(liveKey);
  if (value === undefined) delete values[name];
  else values[name] = value;
  dirty = true;
  if (timer) clearTimeout(timer);
  timer = setTimeout(flush, WRITE_DELAY);
}

/**
 * Name the place being left, for the visible Back control on the next page:
 * "Short paper §2.3", "the map". Applies to the next leave only.
 */
export function leaveAs(label: string): void {
  pendingLabel = label;
}

/** A page names itself once, for every way of leaving it. Returns the unregister. */
export function namePlace(label: () => string | null | undefined): () => void {
  pageLabel = label;
  return () => {
    if (pageLabel === label) pageLabel = null;
  };
}

/** The key of the entry on screen. */
export function entryKey(): string {
  ensureCurrent();
  return liveKey;
}

/** How the entry on screen was reached. */
export function arrivedBy(): Arrival {
  ensureCurrent();
  return arrival;
}

function backLabel(): string | null {
  ensureCurrent();
  const state = historyState();
  const previous = state[PREVIOUS];
  if (!((state[DEPTH] as number | undefined) ?? 0) || typeof previous !== "string") return null;
  const label = valuesOf(previous)[LABEL];
  return typeof label === "string" ? label : "the previous page";
}

/** The key of the entry on screen, as a React value: it changes on every arrival. */
export function useEntryKey(): string {
  return useSyncExternalStore(subscribe, entryKey);
}

/**
 * A piece of view state that belongs to the history entry: a tab, an open panel.
 * Back and Forward restore it because the entry owns it. `initial` must be a
 * primitive or a stable object; a saved object keeps its identity until written.
 */
export function useEntryState<T>(name: string, initial: T): [T, (value: T) => void] {
  const value = useSyncExternalStore(subscribe, () => readEntry<T>(name) ?? initial);
  return [
    value,
    (next: T) => {
      writeEntry(name, next);
      notify();
    },
  ];
}

function subscribe(listener: () => void): () => void {
  listeners.add(listener);
  return () => {
    listeners.delete(listener);
  };
}

/**
 * The visible control's data; null when there is nothing in this site to go back
 * to. `label` is the place, as `leaveAs` named it; BackControl says "Back to …".
 * `back` is the browser's own Back, so the two can never disagree.
 */
export function useBack(): { label: string; back(): void } | null {
  const label = useSyncExternalStore(subscribe, backLabel);
  return label === null ? null : { label, back: () => window.history.back() };
}

// ---- Leaving the page altogether ------------------------------------------------------

function onHide(): void {
  if (!liveKey) return;
  leave();
}

/** The first thing on load: which entry is this? */
function boot(): void {
  if (typeof historyState()[KEY] !== "string") {
    const head = recover();
    if (head) restamp(head);
  }
  ensureCurrent();
  flush();
}

if (typeof window !== "undefined") {
  boot();
  // The browser's own restoration lands before the page has its height and cannot
  // know inner scrollers. There is one restore path: this one.
  if ("scrollRestoration" in window.history) window.history.scrollRestoration = "manual";
  window.addEventListener("pagehide", onHide);
  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "hidden") onHide();
  });
}

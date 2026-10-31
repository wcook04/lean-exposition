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

const STORE = "lx-entry:";
const STORE_INDEX = "lx-entries";
/** Entries kept in sessionStorage; older ones keep only what history.state holds. */
const STORE_LIMIT = 200;
const WRITE_DELAY = 200;

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

function mirror(key: string, values: Values): void {
  try {
    sessionStorage.setItem(STORE + key, JSON.stringify(values));
    const raw = sessionStorage.getItem(STORE_INDEX);
    const index = (raw ? (JSON.parse(raw) as string[]) : []).filter((k) => k !== key);
    index.push(key);
    while (index.length > STORE_LIMIT) sessionStorage.removeItem(STORE + index.shift()!);
    sessionStorage.setItem(STORE_INDEX, JSON.stringify(index));
  } catch {
    /* Storage can be unavailable (private windows); history.state still has it. */
  }
}

/** Write the entry on screen to both stores now. */
function flush(): void {
  if (timer) clearTimeout(timer);
  timer = null;
  if (!dirty || !liveKey) return;
  dirty = false;
  const values = valuesOf(liveKey);
  mirror(liveKey, values);
  const state = historyState();
  if (state[KEY] === liveKey) setHistory({ ...state, [ENTRY]: values });
}

/** Stamp an entry that has no key (a first visit, or a browser fragment navigation). */
function stamp(depth: number, previous: string | null): void {
  const key = newKey();
  setHistory({ ...historyState(), [KEY]: key, [DEPTH]: depth, [PREVIOUS]: previous });
}

/** Adopt the current history entry as the one on screen. */
function adopt(how: Arrival): void {
  const state = historyState();
  liveKey = state[KEY] as string;
  liveDepth = (state[DEPTH] as number | undefined) ?? 0;
  liveHref = window.location.href;
  arrival = how;
}

function notify(): void {
  listeners.forEach((l) => l());
}

function leave(): void {
  // A leaving page may name itself, and may write what it wants kept.
  hooks.forEach((hook) => {
    try {
      hook();
    } catch (error) {
      console.error(error);
    }
  });
  const label = pendingLabel ?? pageLabel?.() ?? defaultLabel(liveHref);
  pendingLabel = null;
  if (liveKey && label) {
    valuesOf(liveKey)[LABEL] = label;
    dirty = true;
  }
  flush();
}

function ensureCurrent(): void {
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
  notify();
}

/**
 * The same entry at a refined address. It keeps its state, which is what a tab,
 * a camera or a followed statement wants; a replace onto another page does not.
 */
export function replaceEntry(url: URL): void {
  ensureCurrent();
  const samePage = new URL(liveHref).pathname === url.pathname;
  if (samePage) {
    flush();
    setHistory(historyState(), url);
    liveHref = window.location.href;
    return;
  }
  flush();
  const state = historyState();
  setHistory({ [KEY]: newKey(), [DEPTH]: state[DEPTH], [PREVIOUS]: state[PREVIOUS] }, url);
  adopt(arrival);
  notify();
}

/** Back, Forward, or a fragment link the browser followed itself. Call before rendering. */
export function arrive(): void {
  leave();
  const known = typeof historyState()[KEY] === "string";
  // Only a fragment navigation arrives unkeyed: it is one step on from the entry left.
  if (!known) stamp(liveDepth + 1, liveKey);
  adopt(known ? "pop" : "push");
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

if (typeof window !== "undefined") {
  ensureCurrent();
  window.addEventListener("pagehide", onHide);
  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "hidden") onHide();
  });
}

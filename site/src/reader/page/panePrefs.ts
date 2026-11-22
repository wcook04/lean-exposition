// What a reader chose for the right pane, kept in this browser: which view, and how much of the
// Graph view the dock under the graph takes. Small on purpose: the paper's own code reads the
// view at startup, and nothing here brings the Lean or the map with it.

const KEEP_KEY = "lx-reader-keep-lean";
const DOCK_KEY = "lx-reader-graph-dock";
/** The dock's height as a share of the Graph view: 40% until a reader draws the handle, so the comparison under the drawing can be read. */
export const DOCK_DEFAULT = 0.4;
export const DOCK_MIN = 0.15;
export const DOCK_MAX = 0.7;

export function clampDock(share: number): number {
  return Math.min(DOCK_MAX, Math.max(DOCK_MIN, share));
}

export function readDockShare(): number {
  try {
    const value = Number(localStorage.getItem(DOCK_KEY));
    return value ? clampDock(value) : DOCK_DEFAULT;
  } catch {
    return DOCK_DEFAULT;
  }
}

export function saveDockShare(share: number) {
  try {
    localStorage.setItem(DOCK_KEY, String(clampDock(share)));
  } catch {
    /* storage unavailable: the height lasts until the page closes */
  }
}

/** Whether this reader's pane is in the Lean view. Graph unless they chose it. */
export function readKeepLean(): boolean {
  try {
    return localStorage.getItem(KEEP_KEY) === "open";
  } catch {
    return false;
  }
}

export function saveKeepLean(open: boolean) {
  try {
    if (open) localStorage.setItem(KEEP_KEY, "open");
    else localStorage.removeItem(KEEP_KEY);
  } catch {
    /* storage unavailable: the choice lasts until the page closes */
  }
}

const VIEW_KEY = "lx-reader-view";

/**
 * The view this reader chose with the tabs, or null if they never chose. The older key could not
 * tell "chose Graph" from "never chose" (it was removed for Graph), so only its Lean is read.
 */
export function readView(): "graph" | "lean" | null {
  try {
    const stored = localStorage.getItem(VIEW_KEY);
    if (stored === "graph" || stored === "lean") return stored;
    return localStorage.getItem(KEEP_KEY) === "open" ? "lean" : null;
  } catch {
    return null;
  }
}

export function saveView(view: "graph" | "lean") {
  try {
    localStorage.setItem(VIEW_KEY, view);
  } catch {
    /* storage unavailable: the choice lasts until the page closes */
  }
}

const TONES_KEY = "lx-reader-tones";

/** Whether underlines carry their topics' colours. On unless the reader turned it off. */
export function readTones(): boolean {
  // Topic colours are always on (Will, 22 Nov). Clear any old "off" choice a reader saved.
  try {
    localStorage.removeItem(TONES_KEY);
  } catch {
    /* storage unavailable */
  }
  return true;
}

/** Set on the root, so the paper, the key and the graph's cards all follow one switch. */
export function applyTones(_on: boolean) {
  document.documentElement.removeAttribute("data-tones");
}

export function saveTones(on: boolean) {
  try {
    if (on) localStorage.removeItem(TONES_KEY);
    else localStorage.setItem(TONES_KEY, "off");
  } catch {
    /* storage unavailable: the choice lasts until the page closes */
  }
  applyTones(on);
}

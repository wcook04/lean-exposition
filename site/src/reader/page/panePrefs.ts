// What a reader chose for the right pane, kept in this browser: which view, and how much of the
// Graph view the dock under the graph takes. Small on purpose: the paper's own code reads the
// view at startup, and nothing here brings the Lean or the map with it.

const KEEP_KEY = "lx-reader-keep-lean";
const DOCK_KEY = "lx-reader-graph-dock";
/** The dock's height as a share of the Graph view: 30% until a reader draws the handle. */
export const DOCK_DEFAULT = 0.3;
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

// What a reader chose for the right pane, kept in this browser: which mode, and how much of the
// pane the Lean takes when they have drawn the graph back above it. Small on purpose: the paper's
// own code reads the mode at startup, and nothing here brings the Lean or the map with it.

const SHARE_KEY = "lx-reader-lean-share";
const KEEP_KEY = "lx-reader-keep-lean";
export const DOCK_MIN = 0.3;
export const DOCK_MAX = 1;

export function clampDock(share: number): number {
  return Math.min(DOCK_MAX, Math.max(DOCK_MIN, share));
}

const shareKey = (side: boolean) => `${SHARE_KEY}${side ? "-side" : ""}`;

/** The Lean has the whole pane until a reader draws the handle to show the graph as well. */
export function readDockShare(side = false): number {
  try {
    const value = Number(localStorage.getItem(shareKey(side)));
    return value ? clampDock(value) : DOCK_MAX;
  } catch {
    return DOCK_MAX;
  }
}

export function saveDockShare(share: number, side = false) {
  try {
    localStorage.setItem(shareKey(side), String(share));
  } catch {
    /* storage unavailable: the height lasts until the page closes */
  }
}

/** Whether this reader's pane is in Lean mode. Graph unless they chose it. */
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

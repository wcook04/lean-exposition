// The reading position of each history entry, so Back returns to the line a
// reader left rather than to the top or to a stale #anchor. A position is a
// part and an offset into it, which survives parts above it changing height.

export interface ReadingPosition {
  stage: string;
  part: number;
  offset: number;
}

const PREFIX = "lx-read:";

/** The key of the current history entry, assigning one when it has none. */
export function historyKey(): string {
  const state = (window.history.state ?? {}) as Record<string, unknown>;
  if (typeof state.lxKey === "string") return state.lxKey;
  const key = Math.random().toString(36).slice(2, 10) + Date.now().toString(36);
  try {
    window.history.replaceState({ ...state, lxKey: key }, "", window.location.href);
  } catch {
    /* A sandboxed frame may refuse; the position is then not kept. */
  }
  return key;
}

export function savePosition(key: string, position: ReadingPosition): void {
  try {
    sessionStorage.setItem(PREFIX + key, JSON.stringify(position));
  } catch {
    /* Storage can be unavailable (private windows); Back then opens at the anchor. */
  }
}

export function loadPosition(key: string): ReadingPosition | null {
  try {
    const raw = sessionStorage.getItem(PREFIX + key);
    if (!raw) return null;
    const value = JSON.parse(raw) as ReadingPosition;
    return typeof value.part === "number" && typeof value.offset === "number" ? value : null;
  } catch {
    return null;
  }
}

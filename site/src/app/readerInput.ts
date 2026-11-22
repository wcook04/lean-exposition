// When the reader last pressed, tapped or typed. A change the page makes on its own (data arriving,
// an address opened on load) never moves anything; one that follows the reader's own act may.

let inputAt = -Infinity;
if (typeof window !== "undefined") {
  for (const type of ["pointerdown", "keydown"]) window.addEventListener(type, () => (inputAt = performance.now()), { capture: true, passive: true });
}

/** How long after the reader's act a change may still move the page in answer to it: the column
 * of a selection waits for its data, which can take a few seconds on a slow connection. */
export const READER_ACT_MS = 6000;

/** Milliseconds since the reader last pressed, tapped or typed (Infinity before they have). */
export function sinceInput(): number {
  return performance.now() - inputAt;
}

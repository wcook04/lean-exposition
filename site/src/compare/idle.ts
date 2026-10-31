/** Run once the page is quiet; returns the cancel. */
export function onIdle(work: () => void, timeout: number): () => void {
  if (typeof window.requestIdleCallback === "function") {
    const id = window.requestIdleCallback(work, { timeout });
    return () => window.cancelIdleCallback(id);
  }
  const id = setTimeout(work, Math.min(timeout, 200));
  return () => clearTimeout(id);
}

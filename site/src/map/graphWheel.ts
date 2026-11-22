/** Both graph canvases use the same wheel gestures; each keeps its own camera bounds. */
export function graphWheel(event: WheelEvent, canvas: HTMLElement): { zoom: number } | { panX: number } {
  // Firefox can expose different delta units depending on whether deltaMode was read first.
  const mode = event.deltaMode;
  const { deltaX, deltaY, shiftKey, ctrlKey, metaKey } = event;
  const pinch = ctrlKey || metaKey;
  if (deltaY && (pinch || (!shiftKey && Math.abs(deltaY) >= Math.abs(deltaX)))) {
    // One mouse detent (about 100 px) zooms by roughly 16%. Trackpad fractions accumulate smoothly.
    const gain = mode === 1 ? 0.05 : mode === 2 ? 1 : 0.0022;
    return { zoom: 2 ** (-deltaY * gain * (pinch ? 3.2 : 1)) };
  }
  const unit = mode === 1 ? 16 : mode === 2 ? canvas.clientWidth : 1;
  return { panX: -(deltaX || (shiftKey ? deltaY : 0)) * unit };
}

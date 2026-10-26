// Keep the panel mounted briefly after the selection clears, so it can slide
// out instead of vanishing.

import { useEffect, useState } from "react";
import { prefersReducedMotion } from "../app/theme";

export const PANEL_EXIT_MS = 200;

export function usePresence<T>(value: T | undefined): { value: T | undefined; leaving: boolean } {
  const [shown, setShown] = useState<{ value: T | undefined; leaving: boolean }>({ value, leaving: false });
  useEffect(() => {
    if (value !== undefined) {
      setShown({ value, leaving: false });
      return;
    }
    if (shown.value === undefined) return;
    if (prefersReducedMotion()) {
      setShown({ value: undefined, leaving: false });
      return;
    }
    setShown((s) => ({ value: s.value, leaving: true }));
    const timer = window.setTimeout(() => setShown({ value: undefined, leaving: false }), PANEL_EXIT_MS);
    return () => window.clearTimeout(timer);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [value]);
  // A new value shows at once, without waiting for the effect.
  if (value !== undefined && shown.value !== value) return { value, leaving: false };
  return shown;
}

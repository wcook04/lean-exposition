// The right page below 1024px: the inspector over the whole screen under the top bar, opened by
// tapping linked words or from a button. "Back to paper" closes it and the paper is exactly where
// it was; what was selected stays selected (HeldBar). Scrolling never opens it.

import { useEffect, useRef, type ReactNode } from "react";

export function RightSheet({ onClose, children }: { onClose(): void; children: ReactNode }) {
  const ref = useRef<HTMLElement>(null);
  useEffect(() => {
    const opener = document.activeElement as HTMLElement | null;
    ref.current?.focus({ preventScroll: true });
    document.documentElement.setAttribute("data-right-sheet", "");
    return () => {
      document.documentElement.removeAttribute("data-right-sheet");
      if (opener?.isConnected && opener !== document.body) opener.focus({ preventScroll: true });
    };
  }, []);
  return (
    <aside ref={ref} className="right-sheet" aria-label="The Lean and the graph for what you selected" tabIndex={-1}>
      <PaneClose onClose={onClose} />
      {children}
    </aside>
  );
}

export function PaneClose({ onClose, label = "Close pane" }: { onClose(): void; label?: string }) {
  return (
    <button type="button" className="reader-pane-close" aria-label={label} title={label} onClick={onClose}>
      <svg viewBox="0 0 12 12" width="13" height="13" aria-hidden="true">
        <path d="M2.5 2.5l7 7m0-7l-7 7" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
      </svg>
    </button>
  );
}

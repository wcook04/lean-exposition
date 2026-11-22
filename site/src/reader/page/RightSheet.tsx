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
      <button type="button" className="right-sheet__back" onClick={onClose}>
        <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
          <path d="M7.5 2.5L4 6l3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
        Back to paper
      </button>
      {children}
    </aside>
  );
}

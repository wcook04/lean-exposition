// The right page below 1280px: a sheet opened on demand, from a button or by tapping a
// statement. It is a plain region, not a modal: the paper stays where it is, can still be
// scrolled and tapped, and Escape, Back, the close button or scrolling the pinned statement
// away all let go of it.

import { useEffect, useRef, type ReactNode } from "react";

export function RightSheet({ phone, onClose, children }: { phone: boolean; onClose(): void; children: ReactNode }) {
  const ref = useRef<HTMLElement>(null);
  useEffect(() => {
    const opener = document.activeElement as HTMLElement | null;
    ref.current?.focus({ preventScroll: true });
    document.documentElement.toggleAttribute("data-right-sheet", phone);
    return () => {
      document.documentElement.removeAttribute("data-right-sheet");
      if (opener?.isConnected && opener !== document.body) opener.focus({ preventScroll: true });
    };
  }, [phone]);
  return (
    <aside ref={ref} className={`right-sheet right-sheet--${phone ? "phone" : "side"}`} aria-label="The proof" tabIndex={-1}>
      <button type="button" className="right-sheet__close" aria-label="Close the proof" onClick={onClose}>
        <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
          <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
        </svg>
      </button>
      {children}
    </aside>
  );
}

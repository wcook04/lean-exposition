// The visible Back: the browser's own, with the name of the place it returns to.

import "./back.css";
import { useBack } from "./trail";

/** `words` lets a page say what going back does, where the place's name would not tell a reader. */
export function BackControl({ className, words }: { className?: string; words?(label: string): string }) {
  const back = useBack();
    if (!back) return null;
  const text = words?.(back.label) ?? `Back to ${back.label}`;

  return (
    <button
      type="button"
      className={`back-control${className ? ` ${className}` : ""}`}
      aria-keyshortcuts="["
      title={`${text} ( [ )`}
      onClick={back.back}
    >
      <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
        <path d="M7.5 2.5L4 6l3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
      </svg>
      <span className="back-control__words">{text}</span>
    </button>
  );
}

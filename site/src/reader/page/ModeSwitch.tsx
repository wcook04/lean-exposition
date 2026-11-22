// Auto | Manual: whether the pane follows the passage being read or stays on what was selected.
// It makes the reader's two states (Following and Selected, docs/reader-design.md) visible and
// directly switchable. Auto lets a selection go and follows the paper from where the reader is,
// without moving it; Manual keeps what the pane shows now. Selecting anything turns it to Manual.

import { useEffect, useRef, useState } from "react";

export const AUTO_TITLE = "Auto: the pane follows the passage you are reading";
export const MANUAL_TITLE = "Manual: the pane stays on what you selected";

/** When the reader last pressed, tapped or typed: a mode change soon after it is the reader's own. */
let inputAt = -Infinity;
if (typeof window !== "undefined") {
  for (const type of ["pointerdown", "keydown"]) window.addEventListener(type, () => (inputAt = performance.now()), { capture: true, passive: true });
}

interface Props {
  manual: boolean;
  /** Follow the paper again (Escape does the same). */
  onAuto?(): void;
  /** Keep what the pane shows now; absent when it shows nothing that can be kept. */
  onManual?(): void;
  className?: string;
}

export function ModeSwitch({ manual, onAuto, onManual, className }: Props) {
  // One glow when the reader changes the mode; none on load, none for a change the page made itself.
  const [pulse, setPulse] = useState(0);
  const last = useRef(manual);
  useEffect(() => {
    if (last.current === manual) return;
    last.current = manual;
    if (performance.now() - inputAt < 1500) setPulse((n) => n + 1);
  }, [manual]);
  const side = (isManual: boolean) => {
    const on = manual === isManual;
    const act = isManual ? onManual : onAuto;
    return (
      <button
        type="button"
        className={`mode-switch__side${on ? " is-on" : ""}`}
        aria-pressed={on}
        title={isManual ? MANUAL_TITLE : AUTO_TITLE}
        aria-label={isManual ? MANUAL_TITLE : AUTO_TITLE}
        aria-keyshortcuts={isManual ? undefined : "Escape"}
        disabled={!on && !act}
        onClick={on ? undefined : act}
      >
        {on && pulse > 0 && <span key={pulse} className="mode-switch__pulse" aria-hidden="true" />}
        {isManual ? "Manual" : "Auto"}
      </button>
    );
  };
  return (
    <div className={`mode-switch${className ? ` ${className}` : ""}`} role="group" aria-label="What the pane shows">
      {side(false)}
      {side(true)}
    </div>
  );
}

// Reopen the selected passage or resume following the paper on a narrow window.

import { ModeSwitch } from "./ModeSwitch";

export function HeldBar({ state, place, onView, onResume }: { state: string; place: string; onView(): void; onResume(): void }) {
  const words = (
    <>
      <span className="held-bar__state">{state}</span>
      {place && <span className="held-bar__place">in {place}</span>}
    </>
  );
  return (
    <div className="held-bar" role="region" aria-label="What you selected">
      <span className="held-bar__where">{words}</span>
      <button type="button" className="held-bar__view" onClick={onView}>
        View
      </button>
      <ModeSwitch manual onAuto={onResume} className="held-bar__mode" />
    </div>
  );
}

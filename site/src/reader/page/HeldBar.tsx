// On a narrow window, the bar at the foot while the inspector is closed over a selection that is
// still held. Go back to the selected words in the paper, open the inspector again, or switch to
// Auto: let the selection go and follow the paper from here.

import { ModeSwitch } from "./ModeSwitch";

export function HeldBar({ state, place, onReturn, onView, onResume }: { state: string; place: string; onReturn?(): void; onView(): void; onResume(): void }) {
  const words = (
    <>
      <span className="held-bar__state">{state}</span>
      {place && <span className="held-bar__place">in {place}</span>}
    </>
  );
  return (
    <div className="held-bar" role="region" aria-label="What you selected">
      {onReturn ? (
        <button type="button" className="held-bar__where" onClick={onReturn} aria-label={`Return to ${state.toLowerCase()}${place ? ` in ${place}` : ""}`}>
          {words}
        </button>
      ) : (
        <span className="held-bar__where">{words}</span>
      )}
      <button type="button" className="held-bar__view" onClick={onView}>
        View
      </button>
      <ModeSwitch manual onAuto={onResume} className="held-bar__mode" />
    </div>
  );
}

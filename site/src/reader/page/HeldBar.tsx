// On a narrow window, the bar at the foot while the inspector is closed over a selection that is
// still held. Three acts, each its own control: go back to the selected words in the paper, open
// the inspector again, or let the selection go and follow the paper from here.

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
      <button type="button" className="held-bar__resume" onClick={onResume}>
        Resume
      </button>
    </div>
  );
}

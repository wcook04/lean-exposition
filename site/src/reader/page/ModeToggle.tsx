// The right pane's two views, and the one control that chooses between them. Graph draws the
// subject with its neighbours; Lean gives the pane to the subject's Lean. Pressing the view
// already on does nothing, and says so by being marked.

export type PaneMode = "graph" | "lean";

export function ModeToggle({ mode, onMode }: { mode: PaneMode; onMode(mode: PaneMode): void }) {
  return (
    <div className="mode-toggle" role="group" aria-label="What the right pane shows">
      <button type="button" aria-pressed={mode === "lean"} title="The words, how the Lean compares with them, and the Lean" onClick={() => onMode("lean")}>
        Lean
      </button>
      <button type="button" aria-pressed={mode === "graph"} title="What this uses and what uses it" onClick={() => onMode("graph")}>
        Graph
      </button>
    </div>
  );
}

// The right pane's two modes, and the one control that chooses between them. Graph follows the
// reading with the graph; Lean gives the pane to the Lean. Pressing the mode already on does
// nothing, and says so by being marked.

export type PaneMode = "graph" | "lean";

export function ModeToggle({ mode, onMode }: { mode: PaneMode; onMode(mode: PaneMode): void }) {
  return (
    <div className="mode-toggle" role="group" aria-label="What the right pane shows">
      <button type="button" aria-pressed={mode === "graph"} onClick={() => onMode("graph")}>
        Graph
      </button>
      <button type="button" aria-pressed={mode === "lean"} onClick={() => onMode("lean")}>
        Lean
      </button>
    </div>
  );
}

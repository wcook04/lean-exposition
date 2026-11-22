// The right pane's two views, and the one control that chooses between them. Graph draws the
// subject with its neighbours; Lean gives the pane to the subject's Lean. Pressing the view
// already on does nothing, and says so by being marked.

export type PaneMode = "graph" | "lean";

/** `graphCount`: how many neighbours the subject has in the recorded graph, shown on the Graph tab; at none the tab is dimmed, so the reader knows why nothing is drawn. */
export function ModeToggle({ mode, onMode, graphCount = null }: { mode: PaneMode; onMode(mode: PaneMode): void; graphCount?: number | null }) {
  return (
    <div className="mode-toggle" role="group" aria-label="What the right pane shows">
      <button type="button" aria-pressed={mode === "lean"} title="The words, how the Lean compares with them, and the Lean" onClick={() => onMode("lean")}>
        Lean
      </button>
      <button
        type="button"
        aria-pressed={mode === "graph"}
        aria-label="Graph"
        aria-description={graphCount === null ? undefined : graphCount === 0 ? "Nothing recorded uses this or is used by it" : `${graphCount} recorded ${graphCount === 1 ? "neighbour" : "neighbours"}`}
        data-empty={graphCount === 0 ? "" : undefined}
        title={graphCount === 0 ? "Nothing in the recorded graph uses this or is used by it" : "What this uses and what uses it"}
        onClick={() => onMode("graph")}
      >
        {/* The count's room is kept before it arrives, so the tabs never move when it does. */}
        Graph<span className="mode-toggle__count">{graphCount !== null ? ` · ${graphCount}` : ""}</span>
      </button>
    </div>
  );
}

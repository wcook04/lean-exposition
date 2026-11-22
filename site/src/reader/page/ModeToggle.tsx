// The right pane's two views, and the one control that chooses between them. Graph draws the
// subject with its neighbours; Lean gives the pane to the subject's Lean. Pressing the view
// already on does nothing, and says so by being marked.

import type { Ref } from "react";

export type PaneMode = "graph" | "lean";

export function ModeToggle({ mode, onMode, leanButtonRef }: { mode: PaneMode; onMode(mode: PaneMode): void; leanButtonRef?: Ref<HTMLButtonElement> }) {
  return (
    <div className="mode-toggle" role="group" aria-label="What the right pane shows">
      <button type="button" aria-pressed={mode === "graph"} onClick={() => onMode("graph")}>
        Graph
      </button>
      <button ref={leanButtonRef} type="button" aria-pressed={mode === "lean"} onClick={() => onMode("lean")}>
        Lean
      </button>
    </div>
  );
}

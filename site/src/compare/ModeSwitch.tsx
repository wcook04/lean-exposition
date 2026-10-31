import type { Stage } from "../api/types";
import { routeHref } from "../app/router";

/** The two ways of reading the table. Both are plain links, so either can be opened on its own. */
export function ModeSwitch({ mode, papers, node }: { mode: "steps" | "papers"; papers?: { a: Stage; b: Stage }; node?: string }) {
  return (
    <nav className="compare-mode" aria-label="How to compare">
      <a href={routeHref({ view: "compare", node })} aria-current={mode === "steps" ? "page" : undefined}>
        One step, all levels
      </a>
      <a href={routeHref({ view: "compare", node, papers: papers ?? { a: "short", b: "expository" } })} aria-current={mode === "papers" ? "page" : undefined}>
        Two papers
      </a>
    </nav>
  );
}

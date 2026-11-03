import { routeHref, type Level } from "../app/router";

/** The table, or one of its rows in full. Both are plain links, and each leads to the same step. */
export function ModeSwitch({ mode, step, levels }: { mode: "table" | "step"; step?: string; levels?: Level[] }) {
  return (
    <nav className="compare-words compare-mode" aria-label="How much to compare">
      <a href={routeHref({ view: "compare", at: step, levels })} aria-current={mode === "table" ? "page" : undefined}>
        All steps
      </a>
      <a href={routeHref({ view: "compare", node: step, levels })} aria-current={mode === "step" ? "page" : undefined}>
        One step
      </a>
    </nav>
  );
}

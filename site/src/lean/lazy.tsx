// The map, the reader and the compare bench show Lean through this wrapper, so none of
// the Lean code reaches their first load.

import { lazy, Suspense } from "react";
import type { LeanBlockProps } from "./LeanBlock";

const LeanBlock = lazy(() => import("./LeanBlock").then((m) => ({ default: m.LeanBlock })));

export function LazyLeanBlock(props: LeanBlockProps) {
  return (
    <Suspense
      fallback={
        <div style={{ minHeight: props.compact ? 200 : 260, padding: "12px 0", fontSize: "var(--fs-sm)", color: "var(--ink-3)" }}>
          Loading the Lean source
        </div>
      }
    >
      <LeanBlock {...props} />
    </Suspense>
  );
}

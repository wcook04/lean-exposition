// The map, the reader and the compare bench show Lean through this wrapper, so none of
// the Lean code reaches their first load.

import { Suspense } from "react";
import { code, lazyCode } from "../app/code";
import type { LeanBlockProps } from "./LeanBlock";

const viewer = code(() => import("./LeanBlock"));
const LeanBlock = lazyCode(viewer, (m) => m.LeanBlock);

/** Start the viewer now, so it is ready when the first block is. */
export const startLeanViewer = viewer.start;

export function LazyLeanBlock(props: LeanBlockProps) {
  return (
    <Suspense
      fallback={
        <div className={`lean-wait${props.compact ? " is-compact" : ""}`} style={{ padding: "12px 0", fontSize: "var(--fs-sm)", color: "var(--ink-3)" }}>
          Loading the Lean source
        </div>
      }
    >
      <LeanBlock {...props} />
    </Suspense>
  );
}

// The map, the reader and the compare bench show Lean through this wrapper, so none of
// the Lean code reaches their first load.

import { lazy, Suspense, useState, type ComponentType } from "react";
import type { LeanBlockProps } from "./LeanBlock";

let ready: ComponentType<LeanBlockProps> | null = null;
const load = () =>
  import("./LeanBlock").then((m) => {
    ready = m.LeanBlock;
    return { default: m.LeanBlock };
  });
const LeanBlock = lazy(load);

/** Start the viewer now, so it is ready when the first block is. */
export function startLeanViewer(): void {
  void load();
}

export function LazyLeanBlock(props: LeanBlockProps) {
  // Code that has arrived skips the boundary: React holds a revealed one back for about 300ms.
  const [Ready] = useState(() => ready);
  if (Ready) return <Ready {...props} />;
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

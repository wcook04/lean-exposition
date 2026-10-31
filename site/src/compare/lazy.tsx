// The statement slice, loaded when first shown. The placeholder is the slice's own text,
// kept invisible: it holds the height while the typesetter arrives, and raw TeX never shows.

import { Suspense, lazy, useState, type ComponentType } from "react";
import type { AlignedStatement } from "../api/lean";
import type { StatementSliceProps } from "./StatementSlice";
import "./slice.css";

let ready: ComponentType<StatementSliceProps> | null = null;
const load = () =>
  import("./StatementSlice").then((m) => {
    ready = m.StatementSlice;
    return m;
  });
const Slice = lazy(() => load().then((m) => ({ default: m.StatementSlice })));

export function RawSlice({ markdown, compact }: { markdown: string; compact?: boolean }) {
  return (
    <p className={`slice-raw${compact ? " slice-raw--compact" : ""}`} aria-busy="true">
      {markdown}
    </p>
  );
}

export function LazyStatementSlice(props: StatementSliceProps) {
  // Code that has arrived skips the boundary: React holds a revealed one back for about 300ms.
  const [Ready] = useState(() => ready);
  if (Ready) return <Ready {...props} />;
  return (
    <Suspense fallback={<RawSlice markdown={props.statement.markdown} compact={props.compact} />}>
      <Slice {...props} />
    </Suspense>
  );
}

/** Start the typesetter now, so it is ready when the first statements are. */
export function startTypesetter(): void {
  void load();
}

/** Typeset slices ahead of time, on idle, from any page. */
export function primeSlices(statements: readonly AlignedStatement[]): void {
  void load().then((m) => statements.forEach(m.primeSlice));
}

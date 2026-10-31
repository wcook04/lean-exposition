// The statement slice, loaded when first shown. The placeholder is the slice's own
// text, dimmed, so a page holds its words and its height while the typesetter arrives.

import { Suspense, lazy } from "react";
import type { AlignedStatement } from "../api/lean";
import type { StatementSliceProps } from "./StatementSlice";
import "./slice.css";

const load = () => import("./StatementSlice");
const Slice = lazy(() => load().then((m) => ({ default: m.StatementSlice })));

export function RawSlice({ markdown, compact }: { markdown: string; compact?: boolean }) {
  return (
    <p className={`slice-raw${compact ? " slice-raw--compact" : ""}`} aria-busy="true">
      {markdown}
    </p>
  );
}

export function LazyStatementSlice(props: StatementSliceProps) {
  return (
    <Suspense fallback={<RawSlice markdown={props.statement.markdown} compact={props.compact} />}>
      <Slice {...props} />
    </Suspense>
  );
}

/** Typeset slices ahead of time, on idle, from any page. */
export function primeSlices(statements: readonly AlignedStatement[]): void {
  void load().then((m) => statements.forEach(m.primeSlice));
}

// The statement slice, loaded when first shown. The placeholder is the slice's own text,
// kept invisible: it holds the height while the typesetter arrives, and raw TeX never shows.

import { Suspense } from "react";
import type { AlignedStatement } from "../api/lean";
import { code, lazyCode } from "../app/code";
import type { StatementSliceProps } from "./StatementSlice";
import "./slice.css";

const typesetter = code(() => import("./StatementSlice"));
const Slice = lazyCode(typesetter, (m) => m.StatementSlice);

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

/** Start the typesetter now, so it is ready when the first statements are. */
export const startTypesetter = typesetter.start;

/** Typeset slices ahead of time, on idle, from any page. */
export function primeSlices(statements: readonly AlignedStatement[]): void {
  typesetter.load().then((m) => statements.forEach(m.primeSlice), () => undefined);
}

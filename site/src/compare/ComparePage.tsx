// Compare reads the table the whole site is built on: rows are the steps of the
// argument, columns are the levels from the Lean to the exposition. By step, one row
// is read across. Two papers, the rows are aligned so two columns read down together.

import { Suspense, lazy } from "react";
import type { Route } from "../app/router";
import { useAlignment } from "./useAlignment";
import { StepBench } from "./StepBench";
import "./compare.css";

const PaperCompare = lazy(() => import("./PaperCompare").then((m) => ({ default: m.PaperCompare })));

export function ComparePage({ route }: { route: Extract<Route, { view: "compare" }> }) {
  // Asked for here so the bench and its first slices arrive together.
  useAlignment();
  if (route.papers) {
    return (
      <Suspense fallback={<div className="bench bench--loading" />}>
        <PaperCompare a={route.papers.a} b={route.papers.b} node={route.node} />
      </Suspense>
    );
  }
  return <StepBench route={route} />;
}

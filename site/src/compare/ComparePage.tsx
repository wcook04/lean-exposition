// Compare reads the table the whole site is built on: rows are the steps of the
// argument, columns are the levels from the Lean to the exposition. It opens on the
// table; a step's title opens that one row in full.

import { useEffect } from "react";
import type { Route } from "../app/router";
import { startLeanViewer } from "../lean/lazy";
import { startTypesetter } from "./lazy";
import { useAlignment } from "./useAlignment";
import { StepBench } from "./StepBench";
import { StepTable } from "./StepTable";
import "./compare.css";

export function ComparePage({ route }: { route: Extract<Route, { view: "compare" }> }) {
  // Asked for here so the page and its first statements arrive together.
  useAlignment();
  useEffect(() => {
    startTypesetter();
    startLeanViewer();
  }, []);
  return route.node ? <StepBench route={route} /> : <StepTable route={route} />;
}

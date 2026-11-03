// Compare reads the table the whole site is built on: rows are the steps of the
// argument, columns are the levels from the Lean to the exposition. It opens on the
// table; a step's title opens that one row in full.

import { useEffect, useState } from "react";
import type { Route } from "../app/router";
import { startLeanViewer } from "../lean/lazy";
import { startTypesetter } from "./lazy";
import { fullAlignmentResource } from "./useAlignment";
import { StepBench } from "./StepBench";
import { StepTable } from "./StepTable";
import "./compare.css";

export function ComparePage({ route }: { route: Extract<Route, { view: "compare" }> }) {
  // Asked for while rendering, before any child's effect, so the page and its first statements
  // arrive together and a child that wants less does not start a smaller download first.
  useState(fullAlignmentResource);
  useEffect(() => {
    startTypesetter();
    startLeanViewer();
  }, []);
  return route.node ? <StepBench route={route} /> : <StepTable route={route} />;
}

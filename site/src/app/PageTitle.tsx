// One owner for the browser title across route changes and closed panels.
import { useLayoutEffect } from "react";
import { useEdition } from "./data";
import { PAPER_NAMES } from "./papers";
import type { Route } from "./router";

export function PageTitle({ route }: { route: Route }) {
  const { graph } = useEdition();
  const label = "node" in route && route.node ? graph.nodes.get(route.node)?.label : undefined;
  let title: string;
  switch (route.view) {
    case "map":
      title = route.edge ? "Argument step" : label ?? "Argument map";
      break;
    case "read":
      title = PAPER_NAMES[route.stage].short;
      break;
    case "checks":
      title = label ? `Checks: ${label}` : "Recorded checks";
      break;
    case "about":
      title = "About";
      break;
    case "search":
      title = route.q.trim() ? `Search: ${route.q.trim()}` : "Search";
      break;
    case "missing":
      title = "Page not found";
      break;
  }
  useLayoutEffect(() => {
    document.title = `${title} · Lean Exposition`;
  }, [title]);
  return null;
}

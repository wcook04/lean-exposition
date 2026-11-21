// One quiet line when an address names something that is not in this edition.

import { useMemo, useRef } from "react";
import { addressProblem } from "./address";
import { useEdition, usePaper } from "./data";
import type { Route } from "./router";
import { PHRASE_RECORD } from "../reader/ties";
import { useEntryKey } from "./trail";
import { retiredLink } from "./libraryAddress";
import { routeHref } from "./router";

export function AddressNotice({ route }: { route: Route }) {
  const { graph } = useEdition();
  // The router drops a malformed `l=` and the reader rewrites it as it follows, so what was
  // asked for is what the address held when this entry opened.
  const key = useEntryKey();
  const opened = useRef({ key: "", at: undefined as string | undefined });
  if (opened.current.key !== key) opened.current = { key, at: route.view === "read" ? (new URLSearchParams(window.location.search).get("l") ?? undefined) : undefined };
  const asked = route.view === "read" ? { ...route, at: opened.current.at } : route;
  const wantsPaper = asked.view === "read" && asked.at ? asked.stage : null;
  const paper = usePaper(wantsPaper);
  const size = useMemo(() => {
    if (paper.status !== "ready" || !wantsPaper) return undefined;
    const { bytes } = paper.value;
    return { bytes: bytes.length, lines: bytes.reduce((n, byte) => (byte === 10 ? n + 1 : n), 1) };
  }, [paper, wantsPaper]);
  const retired = route.view === "read" ? retiredLink(route.retired) : null;
  if (route.view === "read" && route.retired && retired) return <RetiredNotice id={route.retired} retired={retired.retired} nearest={retired.nearest} stage={route.stage} />;
  const words = addressProblem(asked, (id) => graph.nodes.has(id) || (asked.view === "read" && id.startsWith(PHRASE_RECORD)), size);
  return words ? (
    <p className="address-notice" role="status">
      {words}
    </p>
  ) : null;
}

/** "This phrase link was retired on …; nearest current phrase: …". The reader decides whether to follow it. */
export function RetiredNotice({ id, retired, nearest, stage }: { id: string; retired: string; nearest: string | null; stage: Extract<Route, { view: "read" }>["stage"] }) {
  return (
    <p className="address-notice address-notice--retired" role="status" data-retired={id}>
      This phrase link was retired on {retired}
      {nearest ? (
        <>
          ; nearest current phrase: <a href={routeHref({ view: "read", stage, node: `${PHRASE_RECORD}${nearest}` })}>{nearest}</a>.
        </>
      ) : (
        "; this paper has no current phrase near it."
      )}
    </p>
  );
}

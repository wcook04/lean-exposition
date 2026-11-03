// One quiet line when an address names something that is not in this edition.

import { useMemo, useRef } from "react";
import { addressProblem } from "./address";
import { useEdition, usePaper } from "./data";
import type { Route } from "./router";
import { useEntryKey } from "./trail";

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
  const words = addressProblem(asked, (id) => graph.nodes.has(id), size);
  return words ? (
    <p className="address-notice" role="status">
      {words}
    </p>
  ) : null;
}

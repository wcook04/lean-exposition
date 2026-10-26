import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { navigate, type Route } from "../app/router";
import { PAPER_NAMES } from "../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "./ArgumentTree";
import { goalFor, pathFromGoal, reach } from "./treeModel";
import { TheoremBody, mainGoal, startingGoals } from "./TheoremPlate";
import { RecordPanel } from "../panels/RecordPanel";
import { EdgePanel } from "../panels/EdgePanel";
import { usePresence } from "../panels/presence";
import { chooseAccount } from "../panels/accountStore";
import { AccountSwitch } from "../panels/AccountSwitch";
import { MapKey, SourceSwatches } from "./MapKey";
import { ReadingsDock } from "../ribbons/ReadingsDock";
import { prefersReducedMotion } from "../app/theme";
import "./map-page.css";

type MapRoute = Extract<Route, { view: "map" }>;

const INTRO_KEY = "lx-map-intro";

export function MapPage({ route }: { route: MapRoute }) {
  const edition = useEdition();
  const { graph } = edition;
  const treeRef = useRef<MapViewHandle>(null);
  const [echo, setEcho] = useState<ReadonlySet<string> | null>(null);
  const [intro] = useState(() => {
    try {
      if (prefersReducedMotion() || sessionStorage.getItem(INTRO_KEY)) return false;
      sessionStorage.setItem(INTRO_KEY, "1");
      return true;
    } catch {
      return false;
    }
  });

  const allGoals = useMemo(() => startingGoals(edition), [edition]);
  // With an account chosen, the map shows that account's records and starts from its goals.
  const within = useMemo(
    () => (route.lens ? new Set(graph.order.filter((id) => graph.nodes.get(id)!.papers[route.lens!])) : undefined),
    [graph, route.lens],
  );
  const goals = useMemo(() => {
    if (!route.lens) return allGoals;
    const own = allGoals.filter((g) => g.stages.includes(route.lens!));
    return own.length ? own : allGoals;
  }, [allGoals, route.lens]);
  const fallbackGoal = mainGoal(edition);
  const selected = route.node && graph.nodes.has(route.node) ? route.node : undefined;
  const edgeKey = route.edge && graph.edges.some((e) => e.key === route.edge) ? route.edge : undefined;
  const requestedGoal = route.goal && graph.nodes.has(route.goal) ? route.goal : fallbackGoal;
  const goal = useMemo(() => {
    if (!selected || reach(graph, requestedGoal).has(selected)) return requestedGoal;
    return goalFor(graph, selected, goals.map((g) => g.id)) ?? goalFor(graph, selected, graph.goals) ?? requestedGoal;
  }, [selected, requestedGoal, graph, goals]);

  const go = useCallback(
    (patch: Partial<MapRoute>, replace = false) => {
      const next: MapRoute = { view: "map", node: route.node, trace: route.trace, lens: route.lens, goal: route.goal, edge: route.edge, ...patch };
      if (!next.node) next.trace = undefined;
      if (patch.node) next.edge = patch.edge;
      if (next.goal === fallbackGoal) next.goal = undefined;
      navigate(next, { replace });
    },
    [route, fallbackGoal],
  );

  // Escape steps back out: the trace, then the selection.
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      if (document.querySelector("[data-modal-open]")) return;
      if (route.edge) go({ edge: undefined });
      else if (route.trace) go({ trace: undefined });
      else if (route.node) go({ node: undefined });
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [route, go]);

  // An account chosen on the map becomes the account the panel shows.
  useEffect(() => {
    if (route.lens) chooseAccount(route.lens);
  }, [route.lens]);

  const panelKey = edgeKey ? `e:${edgeKey}` : selected ? `n:${selected}` : undefined;
  const shown = usePresence(panelKey);
  const shownNode = shown.value?.startsWith("n:") ? shown.value.slice(2) : undefined;
  const shownEdge = shown.value?.startsWith("e:") ? shown.value.slice(2) : undefined;
  const panelOpen = !!shown.value;
  // On a phone the panel is a bottom sheet over the canvas; the camera keeps
  // the selection above it.
  const canvasRef = useRef<HTMLDivElement>(null);
  const [sheetInset, setSheetInset] = useState(0);
  useEffect(() => {
    if (!panelOpen) {
      setSheetInset(0);
      return;
    }
    // Layout sizes, not client rects: the sheet slides in with a transform.
    const sheet = () => document.querySelector<HTMLElement>(".map-page > .panel");
    const measure = () => {
      const canvas = canvasRef.current?.getBoundingClientRect();
      const el = sheet();
      const phone = window.matchMedia("(max-width: 900px)").matches;
      const top = el ? window.innerHeight - el.offsetHeight : null;
      setSheetInset(phone && canvas && top !== null ? Math.max(0, Math.round(canvas.bottom - top)) : 0);
    };
    const frame = requestAnimationFrame(() => {
      measure();
      const el = sheet();
      if (el) observer.observe(el);
    });
    const observer = new ResizeObserver(measure);
    window.addEventListener("resize", measure);
    return () => {
      cancelAnimationFrame(frame);
      observer.disconnect();
      window.removeEventListener("resize", measure);
    };
  }, [panelOpen, shown.value]);
  const insets: Insets = useMemo(() => ({ top: 20, left: 20, right: 20, bottom: 20 + sheetInset }), [sheetInset]);

  const crumbs = useMemo(() => (shownNode ? pathFromGoal(graph, goal, shownNode) ?? [] : []), [graph, goal, shownNode]);

  return (
    <div className={`map-page${panelOpen ? " map-page--panel" : ""}`}>
      <div className="map-page__canvas" ref={canvasRef}>
        <ArgumentTree
          ref={treeRef}
          graph={graph}
          goal={goal}
          selected={selected}
          trace={route.trace}
          lens={route.lens}
          echo={echo}
          within={within}
          selectedEdge={edgeKey}
          onEdgeSelect={(key) => go({ edge: key ?? undefined, node: undefined, trace: undefined })}
          insets={insets}
          intro={intro}
          rootContent={<TheoremBody goal={goal} />}
          onSelect={(id) => go({ node: id ?? undefined, trace: undefined })}
          onTrace={(id) => {
            if (route.node === id && route.trace === "rests") go({ trace: "uses" });
            else if (route.node === id && route.trace === "uses") go({ trace: undefined });
            else go({ node: id, trace: "rests" });
          }}
        />
      </div>

      <div className="map-bar" role="toolbar" aria-label="What the map shows">
        <div className="goal-switch" role="radiogroup" aria-label="Start from">
          {goals.map((g) => (
            <button
              key={g.id}
              type="button"
              role="radio"
              aria-checked={g.id === goal}
              className="goal-switch__item"
              onClick={() => go({ goal: g.id, node: undefined, trace: undefined })}
            >
              <span className="goal-switch__name">{g.title}</span>
              <span className="goal-switch__note">
                {g.stages.length === 3 ? "in all three accounts" : g.stages.map((s) => `in the ${PAPER_NAMES[s].short.toLowerCase()}`).join(", ")}
              </span>
            </button>
          ))}
        </div>
        <AccountSwitch
          lens={route.lens}
          onLens={(stage) => go({ lens: stage, goal: undefined }, true)}
          onSelect={(id) => go({ node: id, trace: undefined })}
        />
        <div className="map-key">
          <SourceSwatches origins={graph.origins} />
        </div>
        <div className="map-bar__tools">
          <button type="button" className="control" onClick={() => treeRef.current?.expandAll()}>
            Unfold everything
          </button>
          <button
            type="button"
            className="control"
            onClick={() => {
              go({ node: undefined, trace: undefined });
              treeRef.current?.collapseAll();
            }}
          >
            Fold
          </button>
          <button type="button" className="control" aria-label="Fit to the screen" onClick={() => treeRef.current?.fitAll()}>
            Fit
          </button>
          <MapKey origins={graph.origins} />
        </div>
      </div>

      {shownNode && (
        <RecordPanel
          nodeId={shownNode}
          path={crumbs}
          trace={route.trace}
          leaving={shown.leaving}
          onClose={() => go({ node: undefined })}
          onSelect={(id) => go({ node: id, trace: undefined })}
          onTrace={(t) => go({ trace: t })}
          onEcho={setEcho}
          onEdge={(key) => go({ edge: key, node: undefined, trace: undefined })}
        />
      )}
      {shownEdge && (
        <EdgePanel
          edgeKey={shownEdge}
          leaving={shown.leaving}
          onClose={() => go({ edge: undefined })}
          onSelect={(id) => go({ node: id, edge: undefined, trace: undefined })}
          onEcho={setEcho}
        />
      )}

      <ReadingsDock
        lens={route.lens}
        selected={selected}
        onLens={(stage: Stage | undefined) => go({ lens: stage, goal: undefined }, true)}
        onEcho={setEcho}
      />
    </div>
  );
}

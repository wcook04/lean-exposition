// The map page: the bar that says what is drawn (goal, account, view), the
// argument itself (the canvas, or the outline of the same argument), the
// inspector as a full-height column beside it, and the account comparison as
// a dock under the canvas only.
//
// What is selected lives in the URL (none, one record, or one step). How it was
// being looked at (camera, unfolded branches, steps or overview) lives in the
// history entry, so Back returns to the same view; see scene.ts.

import { forwardRef, useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type KeyboardEvent as ReactKeyboardEvent, type RefObject } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { navigate, type Route } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "./ArgumentTree";
import { ArgumentOutline } from "./ArgumentOutline";
import { pathFromGoal, reach } from "./treeModel";
import { TheoremBody, mainGoal, startingGoals } from "./TheoremPlate";
import { RecordPanel } from "../panels/RecordPanel";
import { EdgePanel } from "../panels/EdgePanel";
import { usePresence } from "../panels/presence";
import { chooseAccount } from "../panels/accountStore";
import { AccountSwitch } from "../panels/AccountSwitch";
import { MapKey, SourceSwatches } from "./MapKey";
import { ReadingsDock } from "../ribbons/ReadingsDock";
import { prefersReducedMotion } from "../app/theme";
import { readScene, sceneWriter, type MapScene } from "./scene";
import "./map-page.css";

type MapRoute = Extract<Route, { view: "map" }>;
type Mode = MapScene["mode"];
type Display = "map" | "outline";

type TreeHandle = MapViewHandle;

const INTRO_KEY = "lx-map-intro";
const DISPLAY_KEY = "lx-map-display";

function useMedia(query: string): boolean {
  const [match, setMatch] = useState(() => typeof window !== "undefined" && !!window.matchMedia?.(query).matches);
  useEffect(() => {
    const m = window.matchMedia?.(query);
    if (!m) return;
    const on = () => setMatch(m.matches);
    on();
    m.addEventListener?.("change", on);
    return () => m.removeEventListener?.("change", on);
  }, [query]);
  return match;
}

function readSession(key: string): string | null {
  try {
    return sessionStorage.getItem(key);
  } catch {
    return null;
  }
}

function writeSession(key: string, value: string) {
  try {
    sessionStorage.setItem(key, value);
  } catch {
    /* storage unavailable */
  }
}

const accountWord = (lens: Stage) => PAPER_NAMES[lens].short;

export function MapPage({ route }: { route: MapRoute }) {
  const edition = useEdition();
  const { graph } = edition;
  const treeRef = useRef<TreeHandle>(null);
  const goalBarRef = useRef<HTMLDivElement>(null);
  const has = useCallback((id: string) => graph.nodes.has(id), [graph]);
  // Transient attention: what a pointer or focus is resting on in the dock or the inspector.
  const [preview, setPreview] = useState<ReadonlySet<string> | null>(null);
  const [intro] = useState(() => {
    try {
      if (prefersReducedMotion() || sessionStorage.getItem(INTRO_KEY)) return false;
      sessionStorage.setItem(INTRO_KEY, "1");
      return true;
    } catch {
      return false;
    }
  });

  // ---- Scope: goal and account --------------------------------------------------------

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

  // ---- Selection: none, one record, or one step ----------------------------------------

  const edgeObj = useMemo(() => (route.edge ? graph.edges.find((e) => e.key === route.edge) : undefined), [graph, route.edge]);
  const edgeKey = edgeObj?.key;
  const selected = !edgeKey && route.node && graph.nodes.has(route.node) ? route.node : undefined;
  const requestedGoal = route.goal && graph.nodes.has(route.goal) ? route.goal : fallbackGoal;
  const selectionIds = useMemo(() => (edgeObj ? [edgeObj.from, edgeObj.to] : selected ? [selected] : []), [edgeObj, selected]);
  // The goal drawn: the one asked for, unless it does not draw the selection; then the
  // smallest starting goal that draws all of it, then any recorded goal that does.
  const goal = useMemo(() => {
    const draws = (g: string) => {
      const r = reach(graph, g);
      return selectionIds.every((id) => r.has(id));
    };
    if (!selectionIds.length || draws(requestedGoal)) return requestedGoal;
    let best: { id: string; size: number } | null = null;
    for (const list of [goals.map((g) => g.id), graph.goals]) {
      for (const g of list) {
        if (!graph.nodes.has(g) || !draws(g)) continue;
        const size = reach(graph, g).size;
        if (!best || size < best.size) best = { id: g, size };
      }
      if (best) return best.id;
    }
    return requestedGoal;
  }, [selectionIds, requestedGoal, goals, graph]);
  const goalTitle = allGoals.find((g) => g.id === goal)?.title ?? graph.nodes.get(goal)?.label ?? goal;
  const goalReach = useMemo(() => reach(graph, goal), [graph, goal]);
  const scopedReach = useMemo(() => reach(graph, goal, within), [graph, goal, within]);
  const stepNotDrawn = !!edgeObj && !(goalReach.has(edgeObj.from) && goalReach.has(edgeObj.to));
  const outsideScope = !!route.lens && !stepNotDrawn && selectionIds.some((id) => !within?.has(id) || !scopedReach.has(id));

  // ---- View: steps, overview or outline -----------------------------------------------

  const phone = useMedia("(max-width: 700px)");
  const narrow = useMedia("(max-width: 1279px)");
  const [chosenDisplay, setChosenDisplay] = useState<Display | null>(() => {
    const v = readSession(DISPLAY_KEY);
    return v === "map" || v === "outline" ? v : null;
  });
  const display: Display = chosenDisplay ?? (phone ? "outline" : "map");
  const chooseDisplay = (d: Display) => {
    setChosenDisplay(d);
    writeSession(DISPLAY_KEY, d);
  };
  const initialScene = useRef<MapScene | null>(null);
  if (initialScene.current === null) initialScene.current = readScene(has) ?? ({} as MapScene);
  const [mode, setMode] = useState<Mode>(() => initialScene.current?.mode ?? "steps");

  // ---- Remembered scene per history entry -----------------------------------------------

  const writer = useMemo(() => sceneWriter(), []);
  useEffect(() => () => writer.cancel(), [writer]);
  const restoreRef = useRef<MapScene | null>(initialScene.current?.camera ? initialScene.current : null);
  const [restoreTick, setRestoreTick] = useState(0);
  useEffect(() => {
    const onPop = () => {
      writer.cancel();
      const scene = readScene(has);
      restoreRef.current = scene;
      if (scene) {
        setMode(scene.mode);
        setRestoreTick((t) => t + 1);
      }
    };
    window.addEventListener("popstate", onPop);
    return () => window.removeEventListener("popstate", onPop);
  }, [writer, has]);
  // After the tree has the new route, put the camera back before any automatic framing.
  useLayoutEffect(() => {
    const scene = restoreRef.current;
    if (!scene || display !== "map" || !treeRef.current) return;
    restoreRef.current = null;
    treeRef.current.restoreScene(scene);
  }, [restoreTick, display]);

  const onSceneSettled = useCallback((scene: MapScene) => writer.save(scene), [writer]);

  // ---- Navigation -------------------------------------------------------------------

  const go = useCallback(
    (patch: Partial<MapRoute>, replace = false) => {
      const next: MapRoute = { view: "map", node: route.node, trace: route.trace, lens: route.lens, goal: route.goal, edge: route.edge, ...patch };
      if (!next.node) next.trace = undefined;
      if (patch.node) next.edge = patch.edge;
      if (next.goal === fallbackGoal) next.goal = undefined;
      // The entry being left keeps the scene it showed, so Back can return to it.
      if (!replace) writer.flush(treeRef.current?.getScene() ?? null);
      navigate(next, { replace });
    },
    [route, fallbackGoal, writer],
  );

  // Focus: closing the inspector returns to what opened it.
  const openerRef = useRef<string | null>(null);
  const focusGoalControl = () => {
    const el = goalBarRef.current?.querySelector<HTMLElement>('[aria-checked="true"], select');
    el?.focus();
  };
  const returnFocus = (ids: (string | null | undefined)[]) => {
    const order = [openerRef.current, ...ids].filter((id): id is string => !!id);
    openerRef.current = null;
    requestAnimationFrame(() => {
      for (const id of order) {
        if (display === "outline") {
          const el =
            id === goal
              ? document.querySelector<HTMLElement>(".outline__inspect-goal")
              : document.querySelector<HTMLElement>(`.outline [data-outline-id="${CSS.escape(id)}"] .orow__inspect`);
          if (el) {
            el.focus();
            return;
          }
        } else if (treeRef.current?.focusCard(id)) return;
      }
      focusGoalControl();
    });
  };
  const closeSelection = () => {
    const ids = edgeObj ? [edgeObj.from] : [selected];
    if (edgeObj) go({ edge: undefined });
    else go({ node: undefined });
    returnFocus(ids);
  };
  const select = (id: string | null, opener?: string) => {
    if (id === null) {
      if (selected || edgeKey) closeSelection();
      return;
    }
    if (opener !== undefined && !selected && !edgeKey) openerRef.current = opener;
    go({ node: id, edge: undefined, trace: undefined });
  };
  const selectEdge = (key: string | null) => {
    if (key === null) {
      if (edgeKey) closeSelection();
      return;
    }
    const e = graph.edges.find((x) => x.key === key);
    if (!selected && !edgeKey && e) openerRef.current = e.from;
    go({ edge: key, node: undefined, trace: undefined });
  };

  // Escape steps back out: a popover first (they handle it themselves), then the trace,
  // then the step, then the record.
  const routeRef = useRef({ route, closeSelection });
  routeRef.current = { route, closeSelection };
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      if (document.querySelector("[data-modal-open]")) return;
      const { route: r, closeSelection: close } = routeRef.current;
      if (r.trace && r.node) go({ trace: undefined });
      else if (r.edge || r.node) close();
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [go]);

  // An account chosen on the map becomes the account the panel shows.
  useEffect(() => {
    if (route.lens) chooseAccount(route.lens);
  }, [route.lens]);

  const changeLens = (stage: Stage | undefined) => go({ lens: stage, goal: undefined, edge: undefined }, true);
  const changeGoal = (id: string) => go({ goal: id, node: undefined, edge: undefined, trace: undefined });
  const collapse = () => {
    go({ edge: undefined, trace: undefined });
    treeRef.current?.collapseAll();
  };

  // ---- Inspector ----------------------------------------------------------------------

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
      const isSheet = window.matchMedia("(max-width: 900px)").matches;
      const top = el ? window.innerHeight - el.offsetHeight : null;
      setSheetInset(isSheet && canvas && top !== null ? Math.max(0, Math.round(canvas.bottom - top)) : 0);
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
  const noteShown = outsideScope || stepNotDrawn;
  const insets: Insets = useMemo(
    () => ({ top: noteShown ? 64 : 20, left: 20, right: 20, bottom: 20 + sheetInset }),
    [sheetInset, noteShown],
  );

  // One recorded route from the goal, inside the chosen account; null when there is none.
  const crumbs = useMemo(() => (shownNode ? pathFromGoal(graph, goal, shownNode, within) : null), [graph, goal, shownNode, within]);

  const argumentSize = scopedReach.size;
  const scopeLine = `${route.lens ? `Records the ${accountWord(route.lens).toLowerCase()} uses` : "All accounts"} · ${argumentSize} ${argumentSize === 1 ? "record" : "records"} in this argument`;


  const viewButtons: { id: "steps" | "overview" | "outline"; label: string }[] = [
    { id: "steps", label: "Steps" },
    { id: "overview", label: "Overview" },
    { id: "outline", label: "Outline" },
  ];
  const viewPressed = (v: "steps" | "overview" | "outline") => (v === "outline" ? display === "outline" : display === "map" && mode === v);
  const chooseView = (v: "steps" | "overview" | "outline") => {
    if (v === "outline") return chooseDisplay("outline");
    if (display !== "map") {
      // The tree mounts afresh; give it this entry's remembered camera.
      const scene = readScene(has);
      restoreRef.current = scene ? { ...scene, mode: v } : null;
      setRestoreTick((t) => t + 1);
    }
    chooseDisplay("map");
    setMode(v);
  };

  return (
    <div className={`map-page${panelOpen ? " map-page--panel" : ""}${phone ? " map-page--phone" : ""}`}>
      <div className="map-bar" role="toolbar" aria-label="Argument map controls" aria-orientation="horizontal">
        {phone ? (
          <div className="map-bar__selects" ref={goalBarRef}>
            <label className="map-bar__field">
              <span className="map-bar__label">Main result</span>
              <select value={goal} onChange={(event) => changeGoal(event.target.value)}>
                {!goals.some((g) => g.id === goal) && <option value={goal}>{goalTitle}</option>}
                {goals.map((g) => (
                  <option key={g.id} value={g.id}>
                    {g.title}
                  </option>
                ))}
              </select>
            </label>
            <label className="map-bar__field">
              <span className="map-bar__label">Records used by</span>
              <select value={route.lens ?? ""} onChange={(event) => changeLens((event.target.value || undefined) as Stage | undefined)}>
                <option value="">All accounts</option>
                {STAGE_ORDER.map((s) => (
                  <option key={s} value={s}>
                    {PAPER_NAMES[s].short}
                  </option>
                ))}
              </select>
            </label>
          </div>
        ) : (
          <>
            <GoalSwitch ref={goalBarRef} goals={goals} goal={goal} onGoal={changeGoal} />
            <AccountPicker lens={route.lens} onLens={changeLens} onSelect={(id) => select(id)} />
          </>
        )}
        <div className="map-views" role="group" aria-label="View">
          {viewButtons.map((v) => (
            <button key={v.id} type="button" aria-pressed={viewPressed(v.id)} onClick={() => chooseView(v.id)}>
              {v.label}
            </button>
          ))}
        </div>
        <div className="map-key">
          <SourceSwatches origins={graph.origins} />
        </div>
        <div className="map-bar__tools">
          {!narrow && !phone && (
            <>
              <button type="button" className="map-tool" onClick={collapse} disabled={display !== "map"}>
                Collapse branches
              </button>
              <button type="button" className="map-tool" onClick={() => treeRef.current?.fitAll()} disabled={display !== "map"}>
                Show overview
              </button>
            </>
          )}
          <MoreMenu
            items={[
              ...(narrow || phone
                ? [
                    { label: "Collapse branches", run: collapse },
                    { label: "Show overview", run: () => treeRef.current?.fitAll() },
                  ]
                : []),
              { label: "Expand every branch", run: () => treeRef.current?.expandAll() },
            ]}
            disabled={display !== "map"}
          />
          <MapKey origins={graph.origins} />
        </div>
      </div>

      <div className="map-page__main" ref={canvasRef} style={{ ["--sheet-inset" as string]: `${sheetInset}px` }}>
        {noteShown && (
          <p className="map-note" role="status">
            {stepNotDrawn ? (
              <>
                <span>This step is not drawn in the argument for this main result</span>
                <span aria-hidden="true"> · </span>
                <button
                  type="button"
                  className="linklike"
                  title={`Open the argument for ${graph.nodes.get(edgeObj!.from)?.label ?? ""}`}
                  onClick={() => go({ goal: edgeObj!.from })}
                >
                  Open the argument for {graph.nodes.get(edgeObj!.from)?.label}
                </button>
              </>
            ) : (
              <>
                <span>
                  This {edgeObj ? "step" : "record"} is not among the records the {accountWord(route.lens!)} uses
                </span>
                <span aria-hidden="true"> · </span>
                <button type="button" className="linklike" onClick={() => changeLens(undefined)}>
                  Show the records used by all accounts
                </button>
              </>
            )}
          </p>
        )}
        {display === "map" ? (
          <ArgumentTree
            ref={treeRef}
            graph={graph}
            goal={goal}
            selected={selected}
            trace={route.trace}
            lens={route.lens}
            within={within}
            selectedEdge={edgeKey}
            onEdgeSelect={selectEdge}
            insets={insets}
            intro={intro}
            rootContent={<TheoremBody goal={goal} />}
            onSelect={(id) => select(id, id ?? undefined)}
            onTrace={(id) => {
              if (route.node === id && route.trace === "rests") go({ trace: "uses" });
              else if (route.node === id && route.trace === "uses") go({ trace: undefined });
              else go({ node: id, trace: "rests" });
            }}
            mode={mode}
            onModeChange={setMode}
            previewIds={preview}
            onSceneSettled={onSceneSettled}
          />
        ) : (
          <ArgumentOutline
            graph={graph}
            goal={goal}
            goalTitle={goalTitle}
            scope={scopeLine}
            within={within}
            selected={selected}
            selectedEdge={edgeKey}
            statement={<TheoremBody goal={goal} />}
            onSelect={(id) => select(id, id)}
            onEdgeSelect={(key) => selectEdge(key)}
            bottomInset={sheetInset}
          />
        )}
      </div>

      {shownNode && (
        <RecordPanel
          nodeId={shownNode}
          path={crumbs}
          trace={route.trace}
          leaving={shown.leaving}
          onClose={closeSelection}
          onSelect={(id) => select(id)}
          onTrace={(t) => go({ trace: t })}
          onEcho={setPreview}
          onEdge={(key) => selectEdge(key)}
        />
      )}
      {shownEdge && (
        <EdgePanel
          edgeKey={shownEdge}
          leaving={shown.leaving}
          onClose={closeSelection}
          onSelect={(id) => select(id)}
          onEcho={setPreview}
        />
      )}

      <ReadingsDock
        lens={route.lens}
        selected={selected}
        step={edgeKey}
        onLens={(stage: Stage | undefined) => changeLens(stage)}
        onPreview={setPreview}
      />
    </div>
  );
}

// ---- The bar's controls ---------------------------------------------------------------


/** Goal: a radio group with arrow keys, one tab stop, selection following focus. */
const GoalSwitch = forwardRef<HTMLDivElement, { goals: { id: string; title: string; stages: Stage[] }[]; goal: string; onGoal(id: string): void }>(
  function GoalSwitch({ goals, goal, onGoal }, ref) {
    const checked = goals.some((g) => g.id === goal) ? goal : goals[0]?.id;
    const onKey = (event: ReactKeyboardEvent<HTMLDivElement>) => {
      const i = goals.findIndex((g) => g.id === checked);
      let j = -1;
      if (event.key === "ArrowRight" || event.key === "ArrowDown") j = (i + 1) % goals.length;
      else if (event.key === "ArrowLeft" || event.key === "ArrowUp") j = (i - 1 + goals.length) % goals.length;
      else if (event.key === "Home") j = 0;
      else if (event.key === "End") j = goals.length - 1;
      if (j < 0) return;
      event.preventDefault();
      onGoal(goals[j].id);
      const el = event.currentTarget;
      requestAnimationFrame(() => el.querySelector<HTMLElement>(`[data-goal="${CSS.escape(goals[j].id)}"]`)?.focus());
    };
    return (
      <div className="goal-switch">
        <span className="map-bar__label" id="goal-switch-label">
          Main result
        </span>
        <div className="goal-switch__items" role="radiogroup" aria-labelledby="goal-switch-label" ref={ref} onKeyDown={onKey}>
          {goals.map((g) => (
            <button
              key={g.id}
              type="button"
              role="radio"
              data-goal={g.id}
              aria-checked={g.id === goal}
              tabIndex={g.id === checked ? 0 : -1}
              className="goal-switch__item"
              title={g.stages.length === 3 ? "A main result of all three accounts" : `A main result of the ${g.stages.map((s) => PAPER_NAMES[s].short.toLowerCase()).join(" and the ")}`}
              onClick={() => g.id !== goal && onGoal(g.id)}
            >
              {g.title}
            </button>
          ))}
        </div>
      </div>
    );
  },
);

function usePopover(open: boolean, close: () => void, root: RefObject<HTMLElement | null>) {
  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!root.current?.contains(event.target as Node)) close();
    };
    // Capture phase, so the page's own Escape (which clears the selection) waits.
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      event.preventDefault();
      close();
      root.current?.querySelector<HTMLElement>("button")?.focus();
    };
    document.addEventListener("pointerdown", onDown);
    window.addEventListener("keydown", onKey, true);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      window.removeEventListener("keydown", onKey, true);
    };
  }, [open, close, root]);
}

/** Records used by: a picker that opens the account switch with its coverage caption. */
function AccountPicker({ lens, onLens, onSelect }: { lens?: Stage; onLens(stage: Stage | undefined): void; onSelect(id: string): void }) {
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLDivElement>(null);
  const close = useCallback(() => setOpen(false), []);
  usePopover(open, close, root);
  return (
    <div className="acct-picker" ref={root}>
      <span className="map-bar__label" id="acct-picker-label">
        Records used by
      </span>
      <button
        type="button"
        className="acct-picker__button"
        aria-expanded={open}
        aria-haspopup="dialog"
        aria-labelledby="acct-picker-label acct-picker-value"
        onClick={() => setOpen((v) => !v)}
      >
        <span id="acct-picker-value">{lens ? PAPER_NAMES[lens].short : "All accounts"}</span>
        <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true">
          <path d="M2 3.5 L5 6.5 L8 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
      </button>
      {open && (
        <div className="acct-picker__pop" role="dialog" aria-label="Records used by">
          <AccountSwitch
            lens={lens}
            onLens={(s) => {
              onLens(s);
              if (!s) setOpen(false);
            }}
            onSelect={(id) => {
              setOpen(false);
              onSelect(id);
            }}
          />
        </div>
      )}
    </div>
  );
}

/** Secondary tools behind one button. */
function MoreMenu({ items, disabled }: { items: { label: string; run(): void }[]; disabled?: boolean }) {
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLDivElement>(null);
  const close = useCallback(() => setOpen(false), []);
  usePopover(open, close, root);
  return (
    <div className="map-more" ref={root}>
      <button type="button" className="map-tool" aria-expanded={open} aria-controls="map-more-list" onClick={() => setOpen((v) => !v)} disabled={disabled}>
        More
      </button>
      {open && (
        <ul id="map-more-list" className="map-more__list">
          {items.map((item) => (
            <li key={item.label}>
              <button
                type="button"
                className="map-more__item"
                onClick={() => {
                  setOpen(false);
                  item.run();
                  root.current?.querySelector<HTMLElement>("button")?.focus();
                }}
              >
                {item.label}
              </button>
            </li>
          ))}
        </ul>
      )}
    </div>
  );
}

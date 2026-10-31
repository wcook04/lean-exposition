// The map page: the bar that says what is drawn (goal, level, view), under a
// paper's lens one line about what that lens does to the drawing, the argument
// itself (the canvas, or the outline of the same argument), a foot bar with the
// branch controls and, under a paper's lens, the walk through its passages, and
// the record sheet as a full-height column beside them.
//
// What is selected lives in the URL (none, one record, or one step). How it was
// being looked at (camera, unfolded branches, steps or overview) lives in the
// history entry, so Back returns to the same view; see scene.ts.

import { forwardRef, useCallback, useEffect, useId, useLayoutEffect, useMemo, useRef, useState, type KeyboardEvent as ReactKeyboardEvent, type RefObject } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { navigate, type Route } from "../app/router";
import { PAPER_NAMES, statedIn } from "../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "./ArgumentTree";
import { ArgumentOutline } from "./ArgumentOutline";
import { lensArgument, pathFromGoal, reach, scopedGraph, usesOf } from "./treeModel";
import { GoalPlate, StatementExcerpt, TheoremBody, mainGoal, startingGoals } from "./TheoremPlate";
import { RecordPanel } from "../panels/RecordPanel";
import { EdgePanel } from "../panels/EdgePanel";
import { DeclPanel } from "../panels/DeclPanel";
import { usePresence } from "../panels/presence";
import { chooseAccount } from "../panels/accountStore";
import { KeyPopover } from "./MapKey";
import { MapStrip } from "./MapStrip";
import { LensControl } from "./LensControl";
import { WalkBar, useWalk } from "./WalkBar";
import { leanLevelCounts, leanSentence, levelCounts, levelRecords, lensSentence } from "./levels";
import { recordMark } from "./leanMarks";
import { declTitle } from "../model/declTitle";
import { useLeanGraph } from "./useLeanGraph";
import { useAlignment } from "../compare/useAlignment";
import type { LeanStep } from "../panels/model";
import { shortTitle as recordTitle } from "../compare/useAlignment";
import { startLeanViewer } from "../lean/lazy";
import type { WalkKey } from "./walk";
import { prefersReducedMotion } from "../app/theme";
import { namePlace, onLeave } from "../app/trail";
import { readScene, sceneWriter, type MapScene } from "./scene";
import "./map-page.css";

// The theorem's sheet opens with the map on anything wider than a phone, with its Lean first.
if (window.matchMedia?.("(min-width: 701px)").matches) startLeanViewer();

type MapRoute = Extract<Route, { view: "map" }>;
type Mode = MapScene["mode"];
type Display = "map" | "outline";

type TreeHandle = MapViewHandle;

const WALK_KEYS = new Set(["ArrowUp", "ArrowDown", "ArrowLeft", "ArrowRight"]);

/** Lean names break at their underscores, so a narrower tile than a record's holds them and the ranks stay on a monitor. */
const LEAN_TILE_W = 168;
/** On a laptop the sheet takes a third of the width: slimmer tiles keep the widest rank on the canvas. */
const LAPTOP_TILE_W = 174;
const LEAN_TILE_H = 66;
/** Far enough out to see the whole shape on a monitor; titles shorten there and the strip has them whole. */
const LEAN_MIN_K = 0.5;

const INTRO_KEY = "lx-map-intro";
const DISPLAY_KEY = "lx-map-display";
type View = "steps" | "overview" | "outline" | "lean";

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

/** Keys the map listens for go to it only when nothing else on the page wants them. */
function mapHasKeys(target: EventTarget | null, key: string): boolean {
  const el = target as HTMLElement | null;
  if (!el?.closest) return true;
  if (el.closest("input, textarea, select, [contenteditable], [role='menu'], [role='tablist'], [role='dialog'], .card")) return false;
  // Enter belongs to whatever button has focus.
  if (key === "Enter" && el.closest("a, button")) return false;
  if (WALK_KEYS.has(key) && el.closest("[role='radiogroup']")) return false;
  return !el.closest(".panel") || el.id === "panel-title";
}

export function MapPage({ route }: { route: MapRoute }) {
  const edition = useEdition();
  const { graph } = edition;
  const treeRef = useRef<TreeHandle>(null);
  const goalBarRef = useRef<HTMLDivElement>(null);
  const has = useCallback((id: string) => graph.nodes.has(id), [graph]);
  // Transient attention: what a pointer or focus is resting on in the inspector.
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
  const within = useMemo(() => (route.lens ? levelRecords(graph, route.lens) : undefined), [graph, route.lens]);
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
  // In the Lean graph, what is selected is a declaration or the goal; the record stays in the URL.
  const chosenDecl = route.decl;
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
  const goalFullTitle = recordTitle(goal, graph.nodes.get(goal)?.label ?? goalTitle);
  const menuGoals = useMemo(() => goals.map((g) => ({ ...g, full: recordTitle(g.id, graph.nodes.get(g.id)?.label ?? g.title) })), [goals, graph]);
  const goalReach = useMemo(() => reach(graph, goal), [graph, goal]);
  // Through a paper's lens the records it leaves out close up, so everything it uses stays connected.
  const argument = useMemo(() => {
    const scoped = scopedGraph(graph, goal);
    return within ? lensArgument(scoped, goal, within) : scoped;
  }, [graph, goal, within]);
  const scopedReach = useMemo(() => reach(argument, goal, within), [argument, goal, within]);
  const counts = useMemo(() => levelCounts(graph, reach(scopedGraph(graph, goal), goal)), [graph, goal]);
  const stepNotDrawn = !!edgeObj && !(goalReach.has(edgeObj.from) && goalReach.has(edgeObj.to));

  // ---- The Lean graph: the declarations this argument links, with their uses -------------

  const leanOn = !!route.lean;
  const leanRecords = useMemo(() => {
    const all = reach(scopedGraph(graph, goal), goal);
    return within ? new Set([...all].filter((id) => within.has(id) || id === goal)) : all;
  }, [graph, goal, within]);
  const leanGraph = useLeanGraph({ enabled: leanOn, graph, goal, records: leanRecords });
  const leanReady = leanOn && leanGraph.status === "ready" ? leanGraph : null;
  const alignment = useAlignment();
  const leanCounts = useMemo(() => (alignment ? leanLevelCounts(graph, reach(scopedGraph(graph, goal), goal), alignment) : null), [alignment, graph, goal]);
  const outsideScope = !!route.lens && !stepNotDrawn && selectionIds.some((id) => !within?.has(id) || !scopedReach.has(id));

  // ---- View: steps, overview or outline -----------------------------------------------

  const phone = useMedia("(max-width: 700px)");
  // Below about 1100px (in ems, so larger text compresses the header sooner) the header uses short names.
  const wide = useMedia("(min-width: 68.75em)");
  const [chosenDisplay, setChosenDisplay] = useState<Display | null>(() => {
    const v = readSession(DISPLAY_KEY);
    return v === "map" || v === "outline" ? v : null;
  });
  const display: Display = chosenDisplay ?? (phone ? "outline" : "map");
  const chooseDisplay = (d: Display) => {
    setChosenDisplay(d);
    writeSession(DISPLAY_KEY, d);
  };
  const laptop = useMedia("(max-width: 1400px)");
  const [notesHost, setNotesHost] = useState<HTMLElement | null>(null);
  const initialScene = useRef<MapScene | null>(null);
  if (initialScene.current === null) initialScene.current = readScene(has) ?? ({} as MapScene);
  // The whole argument, named, is what a reader comes to see. Unfolding step by step is a choice.
  const [mode, setMode] = useState<Mode>(() => initialScene.current?.mode ?? (phone ? "steps" : "overview"));

  // ---- Remembered scene per history entry -----------------------------------------------

  const writer = useMemo(() => sceneWriter(), []);
  useEffect(() => () => writer.cancel(), [writer]);
  // Every way of leaving keeps the scene: this page's own links, plain links, Back and reload.
  useEffect(() => onLeave(() => writer.flush(treeRef.current?.getScene() ?? null)), [writer]);
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
  }, [restoreTick, display, !!leanReady]);

  // Which branches are open, as the tree last reported it; the canvas buttons use it to say when they would change nothing.
  const [openIds, setOpenIds] = useState<ReadonlySet<string> | null>(null);
  const onSceneSettled = useCallback(
    (scene: MapScene) => {
      writer.save(scene);
      setOpenIds(new Set(scene.expanded));
    },
    [writer],
  );

  // ---- Navigation -------------------------------------------------------------------

  const go = useCallback(
    (patch: Partial<MapRoute>, replace = false) => {
      const next: MapRoute = { view: "map", node: route.node, trace: route.trace, lens: route.lens, goal: route.goal, edge: route.edge, lean: route.lean, decl: route.decl, declModule: route.declModule, ...patch };
      if (!next.node) next.trace = undefined;
      if (patch.node) next.edge = patch.edge;
      // Choosing a record or a step closes the declaration open in the sheet.
      if ((patch.node || patch.edge) && !("decl" in patch)) {
        next.decl = undefined;
        next.declModule = undefined;
      }
      if (next.goal === fallbackGoal) next.goal = undefined;
      navigate(next, { replace });
    },
    [route, fallbackGoal],
  );

  // Focus: closing the inspector returns to what opened it.
  const openerRef = useRef<string | null>(null);
  const focusGoalControl = () => {
    goalBarRef.current?.querySelector<HTMLElement>(".goal-menu__button")?.focus();
  };
  const returnFocus = (ids: (string | null | undefined)[]) => {
    const order = [openerRef.current, ...ids].filter((id): id is string => !!id);
    openerRef.current = null;
    requestAnimationFrame(() => {
      for (const id of order) {
        if (display === "outline") {
          const el =
            id === goal
              ? document.querySelector<HTMLElement>(".outline__open-goal")
              : document.querySelector<HTMLElement>(`.outline [data-outline-id="${CSS.escape(id)}"] .orow__open`);
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
    if (route.decl) {
      const name = route.decl;
      go({ decl: undefined, declModule: undefined });
      if (!route.node) returnFocus([name]);
      return;
    }
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
  /** One step to a declaration in the sheet: one history entry, and the sheet walks in place. */
  const walkDecl = (walk: LeanStep) => go({ decl: walk.name, declModule: walk.module, edge: undefined });
  /** A card of the Lean graph: a declaration, or the goal's record. */
  const selectLean = (id: string | null) => {
    if (id === null) {
      if (route.decl || route.node) go({ decl: undefined, declModule: undefined, node: undefined });
    } else if (id === goal) go({ node: goal, decl: undefined, declModule: undefined });
    else go({ decl: id, declModule: undefined, node: undefined, edge: undefined, trace: undefined });
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

  // The first view of the map shows the main theorem and its Lean beside the argument.
  const firstView = useRef(true);
  useEffect(() => {
    if (!firstView.current) return;
    firstView.current = false;
    if (!phone && display === "map" && !route.node && !route.edge && !initialScene.current?.camera) go({ node: goal }, true);
    // Only the page's first render decides this.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

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
      else if (r.decl || r.edge || r.node) close();
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

  const panelKey = chosenDecl ? `d:${chosenDecl}` : edgeKey ? `e:${edgeKey}` : selected ? `n:${selected}` : undefined;
  const shown = usePresence(panelKey);
  const shownNode = shown.value?.startsWith("n:") ? shown.value.slice(2) : undefined;
  const shownEdge = shown.value?.startsWith("e:") ? shown.value.slice(2) : undefined;
  const shownDecl = shown.value?.startsWith("d:") ? shown.value.slice(2) : undefined;
  const panelOpen = !!shown.value;
  // On a phone the panel is a bottom sheet over the canvas; the camera keeps
  // the selection above it.
  const canvasRef = useRef<HTMLDivElement>(null);
  const captionRef = useRef<HTMLParagraphElement>(null);
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
  const noteShown = (outsideScope || stepNotDrawn) && !leanOn;
  const insets: Insets = useMemo(() => ({ top: noteShown ? 64 : 20, left: 20, right: 20, bottom: 20 + sheetInset }), [sheetInset, noteShown]);

  // What "Show all branches" and "Collapse branches" would change.
  const expandable = useMemo(() => {
    const scoped = scopedGraph(graph, goal);
    return [...reach(scoped, goal, within)].filter((id) => id !== goal && usesOf(scoped, id, within).length > 0);
  }, [graph, goal, within]);
  // Overview draws every branch whatever is unfolded, so neither button would change it.
  const overview = mode === "overview";
  const allOpen = overview || (!!openIds && expandable.every((id) => openIds.has(id)));
  const noneOpen = overview || (!!openIds && !expandable.some((id) => openIds.has(id)) && !route.edge && !route.trace);

  // One recorded route from the goal; under a lens, through the records that paper uses. Null when there is none.
  const crumbs = useMemo(() => (shownNode ? pathFromGoal(argument, goal, shownNode, within) : null), [argument, goal, shownNode, within]);

  // In the Lean graph, the declarations of the record open in the sheet are lit.
  const litDecls = useMemo(() => {
    if (!leanOn || !route.node || route.node === goal || route.decl) return null;
    return new Set(alignment?.records[route.node]?.lean.map((row) => row.name) ?? []);
  }, [leanOn, route.node, route.decl, goal, alignment]);

  // ---- Paper walk ---------------------------------------------------------------------

  const walk = useWalk(route.lens, scopedReach);
  const [walkAt, setWalkAt] = useState<number | null>(null);
  useEffect(() => setWalkAt(null), [route.lens, goal]);
  const walkLit = useMemo(() => (walkAt === null ? null : new Set(walk.passages[walkAt]?.records ?? [])), [walk, walkAt]);
  const stepWalk = useCallback(
    (delta: number) => {
      const last = walk.passages.length - 1;
      if (last < 0) return;
      const next = walkAt === null ? (delta > 0 ? 0 : last) : Math.max(0, Math.min(last, walkAt + delta));
      setWalkAt(next);
      treeRef.current?.revealIds(walk.passages[next].records);
    },
    [walk, walkAt],
  );

  // ---- Keys: walking the graph, zooming, stepping through a paper ---------------------

  const keysRef = useRef({ selected, stepWalk, go, leanOn, selectLean });
  keysRef.current = { selected, stepWalk, go, leanOn, selectLean };
  const displayRef = useRef(display);
  displayRef.current = display;
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.defaultPrevented || event.metaKey || event.ctrlKey || event.altKey || displayRef.current !== "map") return;
      if (document.querySelector("[data-modal-open]") || !mapHasKeys(event.target, event.key)) return;
      const tree = treeRef.current;
      const k = keysRef.current;
      if (!tree) return;
      if (WALK_KEYS.has(event.key) && event.shiftKey) {
        event.preventDefault();
        const step = 96;
        tree.panBy(event.key === "ArrowLeft" ? step : event.key === "ArrowRight" ? -step : 0, event.key === "ArrowUp" ? step : event.key === "ArrowDown" ? -step : 0);
      } else if (WALK_KEYS.has(event.key)) {
        event.preventDefault();
        const id = tree.walk(event.key as WalkKey);
        if (id && k.leanOn) k.selectLean(id);
        else if (id) k.go({ node: id, edge: undefined, trace: undefined }, true);
      } else if (event.key === "0") tree.fit();
      else if (event.key === "+" || event.key === "=") tree.zoomBy(1.2);
      else if (event.key === "-" || event.key === "_") tree.zoomBy(1 / 1.2);
      else if (event.key === "[") k.stepWalk(-1);
      else if (event.key === "]") k.stepWalk(1);
      else if (event.key === "Enter" && k.selected) {
        event.preventDefault();
        tree.toggleInputs(k.selected);
      }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, []);

  const scopeLine = lensSentence(counts, route.lens);

  // The place being left, for the Back control on the next page.
  const placeRef = useRef<string | null>(null);
  placeRef.current = chosenDecl ? (declTitle(alignment, chosenDecl) ?? chosenDecl.slice(chosenDecl.lastIndexOf(".") + 1)) : selected ? recordTitle(selected, graph.nodes.get(selected)?.label ?? selected) : leanOn ? "the Lean graph" : "the map";
  useEffect(() => namePlace(() => placeRef.current), []);

  const chooseView = (v: View) => {
    // Pressing the view already shown frames it again: Steps around the selection, Overview the whole argument.
    if (viewPressed(v)) {
      if (v !== "outline") treeRef.current?.fitAll();
      return;
    }
    if (v === "lean") {
      chooseDisplay("map");
      return go({ lean: true });
    }
    // Leaving the Lean graph goes back to the record it was opened from.
    if (leanOn) go({ lean: undefined, decl: undefined, declModule: undefined, node: route.node ?? goal });
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
  const viewPressed = (v: View) => (v === "lean" ? leanOn && display === "map" : leanOn ? false : v === "outline" ? display === "outline" : display === "map" && mode === v);

  return (
    <div className={`map-page${panelOpen ? " map-page--panel" : ""}${phone ? " map-page--phone" : ""}`}>
      <div className="map-head" role="group" aria-label="Argument map controls">
        <GoalMenu ref={goalBarRef} goals={menuGoals} goal={goal} fullTitle={goalFullTitle} shortTitle={goalTitle} wide={wide} onGoal={changeGoal} />
        <LensControl lens={route.lens} counts={leanOn && leanCounts ? leanCounts : counts} unit={leanOn && leanCounts ? "declarations" : "records"} onLens={changeLens} />
        <ViewSwitch pressed={viewPressed} onView={chooseView} />
        <KeyPopover onNotesHost={setNotesHost} lean={leanReady ? { source: leanReady.source, note: leanReady.note, leftOut: leanReady.graph.leftOut } : undefined} />
      </div>
      {route.lens && display === "map" && <p className="map-sub">{leanOn && leanCounts ? `${leanSentence(leanCounts, route.lens)}` : `${scopeLine} A line may pass over records it leaves out.`}</p>}

      <div className="map-page__main" ref={canvasRef} style={{ ["--sheet-inset" as string]: `${sheetInset}px` }}>
        {noteShown && (
          <p className="map-note" role="status">
            {stepNotDrawn ? (
              <>
                <span>This step is not drawn in the argument for this main result.</span>{" "}
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
                  This {edgeObj ? "step" : "record"} is not among the records the {accountWord(route.lens!).toLowerCase()} uses.
                </span>{" "}
                <button type="button" className="linklike" onClick={() => changeLens(undefined)}>
                  Show all records
                </button>
              </>
            )}
          </p>
        )}
        {display === "map" && leanOn && !leanReady ? (
          <p className="map-loading" role="status">
            {leanGraph.status === "failed" ? "The Lean index could not be loaded." : "Reading the Lean modules this argument uses…"}
          </p>
        ) : display === "map" && leanReady ? (
          <ArgumentTree
            key={`lean:${route.lens ?? ""}`}
            ref={treeRef}
            graph={leanReady.graph}
            goal={goal}
            selected={chosenDecl && leanReady.graph.nodes.has(chosenDecl) ? chosenDecl : !chosenDecl && selected === goal ? goal : undefined}
            insets={insets}
            onSelect={selectLean}
            onTrace={() => undefined}
            litIds={litDecls}
            captionRef={captionRef}
            mode="overview"
            lens={undefined}
            persist={false}
            statusOf={leanReady.markOf}
            tileWidth={LEAN_TILE_W}
            tileHeight={LEAN_TILE_H}
            minScale={LEAN_MIN_K}
            onSceneSettled={onSceneSettled}
          />
        ) : display === "map" ? (
          <ArgumentTree
            key="argument"
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
            rootContent={<GoalPlate goal={goal} />}
            rootExcerpt={<StatementExcerpt goal={goal} />}
            onSelect={(id) => select(id, id ?? undefined)}
            onWalk={(id) => go({ node: id, edge: undefined, trace: undefined }, true)}
            sectionOf={walk.sections}
            litIds={walkLit}
            captionRef={captionRef}
            notesHost={notesHost}
            onTrace={(id) => {
              if (route.node === id && route.trace === "rests") go({ trace: "uses" });
              else if (route.node === id && route.trace === "uses") go({ trace: undefined });
              else go({ node: id, trace: "rests" });
            }}
            mode={mode}
            onModeChange={setMode}
            previewIds={preview}
            onSceneSettled={onSceneSettled}
            statusOf={recordMark}
            tileWidth={laptop ? LAPTOP_TILE_W : undefined}
          />
        ) : (
          <ArgumentOutline
            graph={argument}
            goal={goal}
            goalTitle={goalTitle}
            scope={scopeLine}
            within={within}
            selected={selected}
            selectedEdge={edgeKey}
            statement={<TheoremBody goal={goal} />}
            onSelect={(id) => select(id, id)}
            bottomInset={sheetInset}
          />
        )}
        {display === "map" && (
          <MapStrip
            lean={leanReady ? { source: leanReady.source, note: leanReady.note, leftOut: leanReady.graph.leftOut } : leanOn ? {} : undefined}
            captionRef={captionRef}
            onFit={() => treeRef.current?.fit()}
          />
        )}
      </div>

      {display === "map" && !leanOn && (route.lens || !overview) && (
        <div className="map-foot" style={{ marginBottom: sheetInset }}>
          {route.lens ? <WalkBar stage={route.lens} passages={walk.passages} at={walkAt} onStep={stepWalk} /> : <span />}
          {!overview && <div className="map-controls" role="group" aria-label="Branches of the argument">
            <button
              type="button"
              className="map-controls__button"
              aria-disabled={allOpen || undefined}
              title={allOpen ? "Every branch of this argument is already shown" : undefined}
              onClick={() => !allOpen && treeRef.current?.expandAll()}
            >
              <svg viewBox="0 0 16 16" width="15" height="15" aria-hidden="true">
                <path d="M8 2.5v11M2.5 8h11" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
              </svg>
              Show all branches
            </button>
            <button
              type="button"
              className="map-controls__button"
              aria-disabled={noneOpen || undefined}
              title={noneOpen ? "Only the main result and its direct inputs are shown" : undefined}
              onClick={() => !noneOpen && collapse()}
            >
              <svg viewBox="0 0 16 16" width="15" height="15" aria-hidden="true">
                <path d="M2.5 8h11" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
              </svg>
              Collapse branches
            </button>
          </div>}
        </div>
      )}

      {shownDecl && (
        <DeclPanel
          name={shownDecl}
          module={route.declModule}
          leaving={shown.leaving}
          onClose={closeSelection}
          onSelect={(id) => select(id)}
          onWalk={walkDecl}
          onEcho={setPreview}
        />
      )}
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
          onWalk={walkDecl}
          account={route.lens}
          goalBody={shownNode === goal ? <TheoremBody goal={goal} /> : undefined}
          onInputs={display === "map" && !overview ? (id) => treeRef.current?.toggleInputs(id) : undefined}
          onBelow={display === "map" && !overview ? (id) => treeRef.current?.openBelow(id) : undefined}
        />
      )}
      {shownEdge && (
        <EdgePanel
          edgeKey={shownEdge}
          leaving={shown.leaving}
          onClose={closeSelection}
          onSelect={(id) => select(id)}
          onWalk={walkDecl}
          onEcho={setPreview}
        />
      )}

    </div>
  );
}

// ---- The header's controls ------------------------------------------------------------

/** A main result: its short name, its full title and the accounts that state it. */
type GoalChoice = { id: string; title: string; full?: string; stages: Stage[] };

/**
 * "Argument for", then the main result's title as a menu button. The menu lists
 * the main results by full title with the accounts that state each, as
 * menuitemradio items: ↑ ↓ Home End move, Enter or Space chooses, Escape closes
 * and returns focus to the button. Below about 1100px, or when the full title
 * would not fit beside the other controls, the button carries the short name.
 */
const GoalMenu = forwardRef<
  HTMLDivElement,
  { goals: GoalChoice[]; goal: string; fullTitle: string; shortTitle: string; wide: boolean; onGoal(id: string): void }
>(function GoalMenu({ goals, goal, fullTitle, shortTitle, wide, onGoal }, ref) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLDivElement | null>(null);
  const button = useRef<HTMLButtonElement>(null);
  const measure = useRef<HTMLSpanElement>(null);
  const items = useRef<(HTMLButtonElement | null)[]>([]);
  const close = useCallback(() => setOpen(false), []);
  usePopover(open, close, root);
  const choices = goals.some((g) => g.id === goal) ? goals : [{ id: goal, title: shortTitle, stages: [] }, ...goals];

  // The full title only where it fits: the slot's width is set by the header, never by the title.
  const [fits, setFits] = useState(true);
  useLayoutEffect(() => {
    const slot = root.current;
    const probe = measure.current;
    if (!slot || !probe) return;
    const check = () => setFits(probe.offsetWidth <= slot.clientWidth);
    check();
    const observer = new ResizeObserver(check);
    observer.observe(slot);
    return () => observer.disconnect();
  }, [fullTitle]);
  const full = wide && fits;

  const focusItem = (i: number) => requestAnimationFrame(() => items.current[(i + choices.length) % choices.length]?.focus());
  const openAt = (i: number) => {
    setOpen(true);
    focusItem(i);
  };
  const checkedIndex = Math.max(0, choices.findIndex((g) => g.id === goal));
  const choose = (g: GoalChoice) => {
    setOpen(false);
    button.current?.focus();
    if (g.id !== goal) onGoal(g.id);
  };
  const onButtonKey = (event: ReactKeyboardEvent<HTMLButtonElement>) => {
    if (event.key === "ArrowDown" || event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      openAt(checkedIndex);
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      openAt(choices.length - 1);
    }
  };
  const onMenuKey = (event: ReactKeyboardEvent<HTMLDivElement>) => {
    const at = items.current.indexOf(document.activeElement as HTMLButtonElement);
    let j: number | null = null;
    if (event.key === "ArrowDown") j = at + 1;
    else if (event.key === "ArrowUp") j = at - 1;
    else if (event.key === "Home") j = 0;
    else if (event.key === "End") j = choices.length - 1;
    else if (event.key === "Tab") setOpen(false);
    if (j === null) return;
    event.preventDefault();
    focusItem(j);
  };

  return (
    <div
      className="goal-menu"
      ref={(el) => {
        root.current = el;
        if (typeof ref === "function") ref(el);
        else if (ref) ref.current = el;
      }}
    >
      <span className="goal-menu__label" id={`${id}-label`}>
        Argument for
      </span>
      <button
        ref={button}
        type="button"
        className="goal-menu__button"
        aria-haspopup="menu"
        aria-expanded={open}
        aria-controls={`${id}-menu`}
        aria-labelledby={`${id}-label ${id}-title`}
        title={full ? undefined : fullTitle}
        onClick={() => (open ? setOpen(false) : openAt(checkedIndex))}
        onKeyDown={onButtonKey}
      >
        <span className="goal-menu__title" id={`${id}-title`}>
          {full ? fullTitle : shortTitle}
        </span>
        <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true" className={`goal-menu__chev${open ? " is-open" : ""}`}>
          <path d="M2 3.5 L5 6.5 L8 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
      </button>
      <span ref={measure} className="goal-menu__button goal-menu__measure" aria-hidden="true">
        <span className="goal-menu__title">{fullTitle}</span>
        <svg viewBox="0 0 10 10" width="10" height="10" />
      </span>
      <div id={`${id}-menu`} role="menu" aria-label="Main results" className="goal-menu__menu" hidden={!open} onKeyDown={onMenuKey}>
        {choices.map((g, i) => (
          <button
            key={g.id}
            ref={(el) => {
              items.current[i] = el;
            }}
            type="button"
            role="menuitemradio"
            aria-checked={g.id === goal}
            tabIndex={-1}
            data-goal={g.id}
            className="goal-menu__item"
            onClick={() => choose(g)}
          >
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true" className="goal-menu__tick">
              <path d="M2 6.5 L5 9 L10 3" fill="none" stroke="currentColor" strokeWidth="1.6" strokeLinecap="round" strokeLinejoin="round" />
            </svg>
            <span className="goal-menu__name">{g.id === goal ? fullTitle : g.full ?? g.title}</span>
            {g.stages.length > 0 && <span className="goal-menu__where">{statedIn(g.stages)}</span>}
          </button>
        ))}
      </div>
    </div>
  );
});

/** Whole argument, Step by step, Outline: one pill whose thumb slides to the view shown. */
function ViewSwitch({ pressed, onView }: { pressed(v: View): boolean; onView(v: View): void }) {
  const group = useRef<HTMLDivElement>(null);
  const views: { id: View; label: string }[] = [
    { id: "overview", label: "Whole argument" },
    { id: "steps", label: "Step by step" },
    { id: "outline", label: "Outline" },
    { id: "lean", label: "Lean graph" },
  ];
  const current = views.find((v) => pressed(v.id))?.id;
  const [thumb, setThumb] = useState<{ x: number; w: number } | null>(null);
  useLayoutEffect(() => {
    const el = group.current;
    if (!el) return;
    const place = () => {
      const b = el.querySelector<HTMLElement>('[aria-pressed="true"]');
      setThumb(b ? { x: b.offsetLeft, w: b.offsetWidth } : null);
    };
    place();
    const observer = new ResizeObserver(place);
    observer.observe(el);
    return () => observer.disconnect();
  }, [current]);
  return (
    <div className="map-views" role="group" aria-label="View" ref={group}>
      {thumb && <span className="map-views__thumb" aria-hidden="true" style={{ transform: `translateX(${thumb.x}px)`, width: thumb.w }} />}
      {views.map((v) => (
        <button
          key={v.id}
          type="button"
          aria-pressed={pressed(v.id)}
          title={pressed(v.id) && v.id !== "outline" ? "Frame this view again" : undefined}
          onClick={() => onView(v.id)}
        >
          {v.label}
        </button>
      ))}
    </div>
  );
}

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

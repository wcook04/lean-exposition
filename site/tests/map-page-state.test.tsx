// The map page's state contract: one selection, honest scope notes, a scene
// remembered per history entry, transient previews and focus returned on close.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import type { Route } from "../src/app/router";
import type { ArgGraph } from "../src/model/graph";
import { reach } from "../src/map/treeModel";
import { graphFixture } from "./fixtures";

const calls = vi.hoisted(() => ({
  navigate: vi.fn(),
  restoreScene: vi.fn(),
  focusCard: vi.fn(() => true),
  getScene: vi.fn(),
  treeProps: {} as Record<string, unknown>,
  panelProps: {} as Record<string, unknown>,
  edition: {} as { graph?: unknown },
}));

vi.mock("../src/app/data", () => ({ useEdition: () => calls.edition }));
vi.mock("../src/app/router", () => ({ navigate: calls.navigate }));
vi.mock("../src/app/theme", () => ({ prefersReducedMotion: () => true }));
vi.mock("../src/panels/accountStore", () => ({ chooseAccount: vi.fn() }));
vi.mock("../src/panels/presence", () => ({ usePresence: (value: string | undefined) => ({ value, leaving: false }) }));
vi.mock("../src/panels/RecordPanel", () => ({
  RecordPanel: (props: Record<string, unknown>) => {
    calls.panelProps = props;
    return null;
  },
}));
vi.mock("../src/panels/EdgePanel", () => ({
  EdgePanel: (props: Record<string, unknown>) => {
    calls.panelProps = props;
    return null;
  },
}));
vi.mock("../src/map/MapKey", () => ({ KeyRow: () => null, SourceSwatches: () => null }));
vi.mock("../src/map/TheoremPlate", () => ({
  TheoremBody: () => null,
  mainGoal: () => "full_support",
  startingGoals: () => [
    { id: "full_support", title: "Full support", stages: ["long", "short", "expository"] },
    { id: "scalar_value", title: "Value identities", stages: ["long"] },
  ],
}));
vi.mock("../src/panels/AccountSwitch", () => ({ AccountSwitch: () => null }));
vi.mock("../src/ribbons/ReadingsDock", () => ({
  ReadingsDock: ({ onPreview }: { onPreview: (ids: ReadonlySet<string> | null) => void }) => (
    <button onPointerEnter={() => onPreview(new Set(["support.diffusion"]))} onClick={() => onPreview(new Set(["support.diffusion"]))}>
      Preview from dock
    </button>
  ),
}));
vi.mock("../src/map/ArgumentTree", async () => {
  const { forwardRef, useImperativeHandle } = await import("react");
  return {
    ArgumentTree: forwardRef(function Tree(props: Record<string, unknown>, ref) {
      calls.treeProps = props;
      useImperativeHandle(ref, () => ({
        collapseAll: vi.fn(),
        restoreScene: calls.restoreScene,
        focusCard: calls.focusCard,
        getScene: calls.getScene,
      }));
      return null;
    }),
  };
});

import { MapPage } from "../src/map/MapPage";

type MapRoute = Extract<Route, { view: "map" }>;
let root: Root;
let container: HTMLDivElement;
let graph: ArgGraph;
const scene = { camera: { x: 12, y: -40, k: 0.9 }, expanded: ["support.diffusion"], mode: "steps" as const };

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
  vi.stubGlobal("requestAnimationFrame", (fn: FrameRequestCallback) => {
    fn(0);
    return 0;
  });
  vi.stubGlobal("matchMedia", () => ({ matches: false, addEventListener() {}, removeEventListener() {} }));
  if (!(globalThis as { CSS?: unknown }).CSS) vi.stubGlobal("CSS", { escape: (s: string) => s });
  graph = graphFixture();
  calls.edition = { graph };
  for (const fn of [calls.navigate, calls.restoreScene, calls.focusCard, calls.getScene]) fn.mockClear();
  window.history.replaceState(null, "", "/");
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});

afterEach(() => {
  act(() => root.unmount());
  container.remove();
  vi.unstubAllGlobals();
  vi.useRealTimers();
});

function open(route: MapRoute) {
  act(() => root.render(<MapPage route={route} />));
}

function press(key: string) {
  act(() => {
    window.dispatchEvent(new KeyboardEvent("keydown", { key }));
  });
}

describe("selection", () => {
  it("draws a step in a goal that contains both of its endpoints", () => {
    const key = "scalar.formal_contact_input→assumptions.value_diffusion→assumes";
    open({ view: "map", edge: key });
    expect(calls.treeProps.goal).toBe("scalar_value");
    expect(calls.treeProps.selectedEdge).toBe(key);
    expect(container.querySelector(".map-note")).toBeNull();
  });

  it("says so when no goal draws a step, and offers one that does", () => {
    const key = "scalar.finite_maximum_concentration→assumptions.qaoa_model_and_limits→assumes";
    open({ view: "map", edge: key });
    const note = container.querySelector(".map-note");
    expect(note?.textContent).toContain("This step is not drawn in the argument for this main result");
    act(() => note!.querySelector("button")!.click());
    expect(calls.navigate.mock.calls.at(-1)![0]).toMatchObject({ goal: "scalar.finite_maximum_concentration", edge: key });
  });

  it("keeps a record outside the chosen account and says so", () => {
    const names = { expository: "Exposition", short: "Short paper", long: "Long record" } as const;
    const goalReach = new Set(graph.goals.flatMap((g) => [...reach(graph, g)]));
    let found: { id: string; stage: keyof typeof names } | undefined;
    for (const stage of ["expository", "short", "long"] as const) {
      const id = graph.order.find((x) => goalReach.has(x) && !graph.nodes.get(x)!.papers[stage]);
      if (id) {
        found = { id, stage };
        break;
      }
    }
    expect(found, "a record outside some account").toBeDefined();
    const { id, stage } = found!;
    open({ view: "map", node: id, lens: stage });
    expect(calls.treeProps.selected).toBe(id);
    const note = container.querySelector(".map-note");
    expect(note?.textContent).toContain(`This record is not among the records the ${names[stage]} uses`);
    // The inspector's route never passes through records outside the account.
    const path = (calls.panelProps.path as string[] | null) ?? [];
    expect(path.slice(0, -1).every((x) => graph.nodes.get(x)!.papers[stage])).toBe(true);
    act(() => note!.querySelector("button")!.click());
    expect(calls.navigate).toHaveBeenLastCalledWith(expect.objectContaining({ lens: undefined, node: id }), { replace: true });
  });

  it("computes the inspector's route within the account", () => {
    open({ view: "map", node: "support.diffusion", lens: "short" });
    const path = calls.panelProps.path as string[];
    expect(path[0]).toBe("full_support");
    expect(path.at(-1)).toBe("support.diffusion");
    for (const id of path.slice(1)) expect(graph.nodes.get(id)!.papers.short).toBeTruthy();
  });

  it("steps back out with Escape: trace, then record", () => {
    open({ view: "map", node: "support.diffusion", trace: "rests" });
    press("Escape");
    expect(calls.navigate.mock.calls.at(-1)![0]).toMatchObject({ node: "support.diffusion", trace: undefined });
    open({ view: "map", node: "support.diffusion" });
    press("Escape");
    expect(calls.navigate.mock.calls.at(-1)![0]).toMatchObject({ node: undefined });
  });

  it("returns focus to the card that opened the inspector", () => {
    open({ view: "map" });
    act(() => (calls.treeProps.onSelect as (id: string) => void)("support.diffusion"));
    open({ view: "map", node: "support.diffusion" });
    act(() => (calls.panelProps.onClose as () => void)());
    expect(calls.focusCard).toHaveBeenCalledWith("support.diffusion");
  });

  it("returns focus to a step's consumer card", () => {
    const edge = graph.edges.find((e) => e.from === "full_support")!;
    open({ view: "map", edge: edge.key });
    press("Escape");
    expect(calls.navigate.mock.calls.at(-1)![0]).toMatchObject({ edge: undefined });
    expect(calls.focusCard).toHaveBeenCalledWith("full_support");
  });
});

describe("preview", () => {
  it("passes dock attention to the tree as a transient preview, without navigating", () => {
    open({ view: "map" });
    const button = [...container.querySelectorAll("button")].find((b) => b.textContent === "Preview from dock")!;
    act(() => button.click());
    expect([...(calls.treeProps.previewIds as Set<string>)]).toEqual(["support.diffusion"]);
    expect(calls.treeProps.echo).toBeUndefined();
    expect(calls.navigate).not.toHaveBeenCalled();
    expect(window.history.state?.mapScene).toBeUndefined();
  });
});

describe("remembered scene", () => {
  it("saves a settled scene into the current entry, merged, debounced, without pushing", () => {
    vi.useFakeTimers();
    window.history.replaceState({ readerKey: "keep-me" }, "", "/");
    const length = window.history.length;
    open({ view: "map" });
    act(() => (calls.treeProps.onSceneSettled as (s: unknown) => void)(scene));
    expect(window.history.state.mapScene).toBeUndefined();
    act(() => vi.advanceTimersByTime(250));
    expect(window.history.state).toEqual({ readerKey: "keep-me", mapScene: scene });
    expect(window.history.length).toBe(length);
  });

  it("writes the scene being left before a selection pushes a new entry", () => {
    calls.getScene.mockReturnValue(scene);
    open({ view: "map" });
    act(() => (calls.treeProps.onSelect as (id: string) => void)("support.diffusion"));
    expect(window.history.state.mapScene).toEqual(scene);
    expect(calls.navigate).toHaveBeenLastCalledWith(expect.objectContaining({ node: "support.diffusion" }), { replace: false });
  });

  it("restores the entry's scene on Back", () => {
    open({ view: "map", node: "support.diffusion" });
    expect(calls.restoreScene).not.toHaveBeenCalled();
    window.history.replaceState({ mapScene: scene }, "", "/");
    act(() => {
      window.dispatchEvent(new PopStateEvent("popstate"));
    });
    open({ view: "map" });
    expect(calls.restoreScene).toHaveBeenCalledWith(scene);
  });

  it("restores a remembered scene when the page mounts in that entry", () => {
    window.history.replaceState({ mapScene: scene }, "", "/");
    open({ view: "map" });
    expect(calls.restoreScene).toHaveBeenCalledWith(scene);
  });

  it("ignores a scene that names records outside this edition", () => {
    window.history.replaceState({ mapScene: { ...scene, expanded: ["no.such.record"] } }, "", "/");
    open({ view: "map" });
    expect(calls.restoreScene).not.toHaveBeenCalled();
  });
});

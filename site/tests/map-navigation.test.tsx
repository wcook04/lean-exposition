import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import type { Route } from "../src/app/router";
import { graphFixture } from "./fixtures";

const calls = vi.hoisted(() => ({
  navigate: vi.fn(),
  collapseAll: vi.fn(),
  edition: {} as { graph?: unknown },
}));

vi.mock("../src/app/data", () => ({ useEdition: () => calls.edition }));
vi.mock("../src/app/router", () => ({ navigate: calls.navigate }));
vi.mock("../src/app/theme", () => ({ prefersReducedMotion: () => true }));
vi.mock("../src/panels/accountStore", () => ({ chooseAccount: vi.fn() }));
vi.mock("../src/panels/presence", () => ({ usePresence: (value: string | undefined) => ({ value, leaving: false }) }));
vi.mock("../src/panels/RecordPanel", () => ({ RecordPanel: () => null }));
vi.mock("../src/panels/EdgePanel", () => ({ EdgePanel: () => null }));
vi.mock("../src/map/MapKey", () => ({ KeyRow: () => null, SourceSwatches: () => null }));
vi.mock("../src/map/TheoremPlate", () => ({
  TheoremBody: () => null,
  StatementExcerpt: () => null,
  mainGoal: () => "full_support",
  startingGoals: () => [
    { id: "full_support", title: "Full support", stages: ["long", "short", "expository"] },
    { id: "scalar_value", title: "Value identities", stages: ["long"] },
  ],
}));
vi.mock("../src/panels/AccountSwitch", () => ({
  AccountSwitch: ({ onLens }: { onLens: (stage: "long") => void }) => (
    <button onClick={() => onLens("long")}>Choose long from bar</button>
  ),
}));
vi.mock("../src/ribbons/ReadingsDock", () => ({
  ReadingsDock: ({ onLens }: { onLens: (stage: "long") => void }) => (
    <button onClick={() => onLens("long")}>Choose long from dock</button>
  ),
}));
vi.mock("../src/map/ArgumentTree", async () => {
  const { forwardRef, useImperativeHandle } = await import("react");
  return {
    ArgumentTree: forwardRef(function Tree(_props, ref) {
      useImperativeHandle(ref, () => ({ collapseAll: calls.collapseAll, getScene: () => null, restoreScene() {}, focusCard: () => false }));
      return null;
    }),
  };
});

import { MapPage } from "../src/map/MapPage";

type MapRoute = Extract<Route, { view: "map" }>;
let root: Root;
let container: HTMLDivElement;
let edgeKey: string;

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
  const graph = graphFixture();
  calls.edition = { graph };
  edgeKey = graph.edges.find((edge) => edge.from === "full_support")!.key;
  calls.navigate.mockClear();
  calls.collapseAll.mockClear();
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});

afterEach(() => {
  act(() => root.unmount());
  container.remove();
  vi.unstubAllGlobals();
});

function open(route: MapRoute) {
  act(() => root.render(<MapPage route={route} />));
}

function click(label: string) {
  const button = [...container.querySelectorAll("button")].find((el) => el.textContent?.startsWith(label));
  expect(button, `control ${label}`).toBeDefined();
  act(() => button!.click());
}

describe("map scope changes with a selected step", () => {
  it("starts another goal without carrying a step from the previous argument", () => {
    open({ view: "map", goal: "full_support", edge: edgeKey, lens: "long" });
    act(() => container.querySelector<HTMLButtonElement>(".goal-menu__button")!.click());
    act(() => container.querySelector<HTMLButtonElement>('[role="menuitemradio"][data-goal="scalar_value"]')!.click());
    expect(calls.navigate).toHaveBeenLastCalledWith(
      { view: "map", goal: "scalar_value", lens: "long", node: undefined, edge: undefined, trace: undefined },
      { replace: false },
    );
  });

  it("collapses the branches of the active goal and closes its selected step", () => {
    open({ view: "map", goal: "scalar_value", edge: edgeKey, lens: "long" });
    click("Collapse branches");
    expect(calls.collapseAll).toHaveBeenCalledOnce();
    expect(calls.navigate).toHaveBeenLastCalledWith(
      { view: "map", goal: "scalar_value", lens: "long", node: undefined, edge: undefined, trace: undefined },
      { replace: false },
    );
  });

  it.each(["Choose long from bar", "Choose long from dock"])("clears the selected step when changing the account through %s", (control) => {
    open({ view: "map", edge: edgeKey });
    if (control.endsWith("bar")) click("All accounts");
    click(control);
    expect(calls.navigate).toHaveBeenLastCalledWith(
      { view: "map", goal: undefined, lens: "long", node: undefined, edge: undefined, trace: undefined },
      { replace: true },
    );
  });

  it("keeps the existing record-selection policy when an account changes", () => {
    open({ view: "map", node: "full_support", trace: "rests" });
    click("All accounts");
    click("Choose long from bar");
    expect(calls.navigate).toHaveBeenLastCalledWith(
      { view: "map", goal: undefined, lens: "long", node: "full_support", edge: undefined, trace: "rests" },
      { replace: true },
    );
  });
});

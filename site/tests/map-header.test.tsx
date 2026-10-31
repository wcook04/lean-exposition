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

vi.mock("../src/app/data", () => ({ useEdition: () => calls.edition, loadPaperStructure: () => new Promise(() => {}) }));
vi.mock("../src/app/router", () => ({ navigate: calls.navigate }));
vi.mock("../src/app/theme", () => ({ prefersReducedMotion: () => true }));
vi.mock("../src/panels/accountStore", () => ({ chooseAccount: vi.fn() }));
vi.mock("../src/panels/presence", () => ({ usePresence: (value: string | undefined) => ({ value, leaving: false }) }));
vi.mock("../src/panels/RecordPanel", () => ({ RecordPanel: () => null }));
vi.mock("../src/panels/EdgePanel", () => ({ EdgePanel: () => null }));
vi.mock("../src/map/MapKey", () => ({
  KeyPopover: () => <button>Key</button>,
}));
vi.mock("../src/map/TheoremPlate", () => ({
  TheoremBody: () => null,
  GoalPlate: () => null,
  StatementExcerpt: () => null,
  mainGoal: () => "full_support",
  startingGoals: () => [
    { id: "full_support", title: "Full support", stages: ["long", "short", "expository"] },
    { id: "scalar_value", title: "Value identities", stages: ["long"] },
  ],
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

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
  const graph = graphFixture();
  calls.edition = { graph };
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


const keyButton = () => [...container.querySelectorAll<HTMLButtonElement>("button")].find((b) => b.textContent?.trim() === "Key")!;

describe("the map header", () => {
  beforeEach(() => localStorage.clear());

  it("says what a line means in one sentence, with the rest behind the Key", () => {
    open({ view: "map" });
    expect(container.querySelector("#map-key-row")).toBeNull();
    expect(container.querySelector(".map-sub__line")!.textContent).toContain("Each line runs from a record up to the result that uses it.");
    expect(keyButton()).toBeDefined();
  });

  it("names the main result in the title button and lists the main results as radio items", () => {
    open({ view: "map" });
    const button = container.querySelector<HTMLButtonElement>(".goal-menu__button")!;
    expect(button.getAttribute("aria-haspopup")).toBe("menu");
    act(() => button.click());
    const items = [...container.querySelectorAll('[role="menuitemradio"]')];
    expect(items.map((i) => i.getAttribute("data-goal"))).toEqual(["full_support", "scalar_value"]);
    expect(items[0].getAttribute("aria-checked")).toBe("true");
    expect(items[1].textContent).toContain("In the long record");
  });

  it("offers the levels as a segmented control, with no dock and no account menu", () => {
    open({ view: "map" });
    const radios = [...container.querySelectorAll('.map-lens [role="radio"]')];
    expect(radios.map((r) => r.textContent?.replace(/\s*\d+$/, ""))).toEqual(["All", "Long record", "Short paper", "Exposition"]);
    expect(radios[0].getAttribute("aria-checked")).toBe("true");
    expect(container.querySelector(".dock")).toBeNull();
    expect(container.querySelector(".map-sub__line")!.textContent).toMatch(/^This argument uses \d+ of the \d+ records on this site\. /);
  });

  it("keeps the branch controls in a bar of their own, outside the canvas, for the view they change", () => {
    open({ view: "map" });
    expect(container.querySelector(".map-foot")).toBeNull();
    act(() => [...container.querySelectorAll<HTMLButtonElement>(".map-views button")].find((b) => b.textContent === "Step by step")!.click());
    expect(container.querySelector(".map-foot .map-controls")).not.toBeNull();
    expect(container.querySelector(".map-page__main .map-controls")).toBeNull();
  });

  it("has no Show overview control", () => {
    open({ view: "map" });
    expect([...container.querySelectorAll("button")].some((b) => b.textContent?.includes("Show overview"))).toBe(false);
  });
});

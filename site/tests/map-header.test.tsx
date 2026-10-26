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
vi.mock("../src/map/MapKey", () => ({
  KeyRow: ({ id, hidden }: { id: string; hidden?: boolean }) => <section id={id} hidden={hidden} />,
  SourceSwatches: () => null,
}));
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

import { KEY_ROW_KEY, MapPage } from "../src/map/MapPage";

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

  it("shows the key row by default and remembers the reader's choice to hide it", () => {
    open({ view: "map" });
    expect(keyButton().getAttribute("aria-expanded")).toBe("true");
    expect(container.querySelector("#map-key-row")!.hasAttribute("hidden")).toBe(false);
    act(() => keyButton().click());
    expect(keyButton().getAttribute("aria-expanded")).toBe("false");
    expect(container.querySelector("#map-key-row")!.hasAttribute("hidden")).toBe(true);
    expect(localStorage.getItem(KEY_ROW_KEY)).toBe("hidden");
    act(() => root.unmount());
    root = createRoot(container);
    open({ view: "map" });
    expect(keyButton().getAttribute("aria-expanded")).toBe("false");
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

  it("has no Show overview control", () => {
    open({ view: "map" });
    expect([...container.querySelectorAll("button")].some((b) => b.textContent?.includes("Show overview"))).toBe(false);
  });
});

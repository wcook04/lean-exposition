// A graph that throws while drawing must not take down what is beside it: the paper next to the
// pane, or the map page's own controls. The failure shows one notice in the graph's place.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture } from "./fixtures";

const calls = vi.hoisted(() => ({ edition: {} as { graph?: unknown }, throwTree: true }));

vi.mock("../src/app/data", () => ({ useEdition: () => calls.edition, loadPaperStructure: () => new Promise(() => {}) }));
vi.mock("../src/app/router", () => ({ navigate: vi.fn() }));
vi.mock("../src/app/theme", () => ({ prefersReducedMotion: () => true }));
vi.mock("../src/panels/accountStore", () => ({ chooseAccount: vi.fn() }));
vi.mock("../src/panels/presence", () => ({ usePresence: (value: string | undefined) => ({ value, leaving: false }) }));
vi.mock("../src/panels/RecordPanel", () => ({ RecordPanel: () => null }));
vi.mock("../src/panels/EdgePanel", () => ({ EdgePanel: () => null }));
vi.mock("../src/map/MapKey", () => ({ KeyRow: () => null, KeyPopover: () => null, SourceSwatches: () => null }));
vi.mock("../src/map/TheoremPlate", () => ({
  TheoremBody: () => null,
  GoalPlate: () => null,
  StatementExcerpt: () => null,
  mainGoal: () => "full_support",
  startingGoals: () => [{ id: "full_support", title: "Full support", stages: ["long", "short", "expository"] }],
}));
vi.mock("../src/map/ArgumentTree", async () => {
  const { forwardRef } = await import("react");
  return {
    ArgumentTree: forwardRef(function Tree() {
      if (calls.throwTree) throw new RangeError("Invalid array length");
      return <p className="drawn-tree">drawn</p>;
    }),
  };
});

import { GraphBoundary } from "../src/map/GraphBoundary";
import { MapPage } from "../src/map/MapPage";

let root: Root;
let container: HTMLDivElement;
let errors: { mock: { calls: unknown[][] } };

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
  calls.edition = { graph: graphFixture() };
  calls.throwTree = true;
  errors = vi.spyOn(console, "error").mockImplementation(() => {});
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});

afterEach(() => {
  act(() => root.unmount());
  container.remove();
  vi.unstubAllGlobals();
  vi.restoreAllMocks();
});

function Broken(): never {
  throw new RangeError("Invalid array length");
}

describe("a graph that fails to draw", () => {
  it("keeps the paper beside the pane and says the diagram could not be drawn", () => {
    act(() =>
      root.render(
        <div>
          <article className="paper">The paper's text</article>
          <GraphBoundary scope="whole proof map of g">
            <Broken />
          </GraphBoundary>
        </div>,
      ),
    );
    expect(container.querySelector(".paper")?.textContent).toBe("The paper's text");
    const alert = container.querySelector(".graph-boundary[role=alert]");
    expect(alert?.textContent).toContain("The diagram could not be drawn.");
    expect(errors.mock.calls.some(([m]) => String(m).includes("whole proof map of g"))).toBe(true);
  });

  it("tries again on request and when the subject changes", () => {
    let fail = true;
    function Sometimes() {
      if (fail) throw new Error("boom");
      return <p className="ok">drawn</p>;
    }
    act(() => root.render(<GraphBoundary scope="a"><Sometimes /></GraphBoundary>));
    expect(container.querySelector(".graph-boundary")).not.toBeNull();
    fail = false;
    act(() => container.querySelector<HTMLButtonElement>(".graph-boundary button")!.click());
    expect(container.querySelector(".ok")).not.toBeNull();
    fail = true;
    act(() => root.render(<GraphBoundary scope="b"><Sometimes /></GraphBoundary>));
    expect(container.querySelector(".graph-boundary")).not.toBeNull();
    fail = false;
    act(() => root.render(<GraphBoundary scope="c"><Sometimes /></GraphBoundary>));
    expect(container.querySelector(".ok")).not.toBeNull();
  });

  it("on the map page leaves the page's own controls in place", () => {
    act(() => root.render(<MapPage route={{ view: "map", goal: "full_support" }} />));
    expect(container.querySelector(".graph-boundary[role=alert]")).not.toBeNull();
    // The goal menu (part of the page, outside the drawing) is still there.
    expect(container.querySelector(".goal-menu__button")).not.toBeNull();
  });
});

// A preview (hover or focus on a passage elsewhere) tints drawn cards and
// offers to show folded ones; it never unfolds, moves or saves anything.
import { act, createRef } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture } from "./fixtures";
import { ArgumentTree, type MapViewHandle } from "../src/map/ArgumentTree";
import { neededExpansion, reach, scopedGraph } from "../src/map/treeModel";

let root: Root;
let container: HTMLDivElement;
const graph = graphFixture();
const goal = "full_support";
const insets = { top: 20, right: 20, bottom: 20, left: 20 };

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
  vi.stubGlobal("matchMedia", (q: string) => ({ matches: false, media: q, addEventListener() {}, removeEventListener() {} }));
  sessionStorage.clear();
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});

afterEach(() => {
  act(() => root.unmount());
  container.remove();
  vi.unstubAllGlobals();
});

function draw(previewIds: ReadonlySet<string> | null, ref = createRef<MapViewHandle>()) {
  act(() =>
    root.render(<ArgumentTree ref={ref} graph={graph} goal={goal} insets={insets} previewIds={previewIds} onSelect={() => {}} onTrace={() => {}} />),
  );
  return ref;
}

const cards = () => [...container.querySelectorAll<HTMLElement>(".card")].map((el) => el.dataset.card!);
const records = () => [...container.querySelectorAll<HTMLElement>(".card")].map((el) => el.dataset.record!);
// Assumptions are drawn as tags on their consumers, not as cards.
const claimsBelow = (drawn: string[]) => [...reach(graph, goal)].filter((id) => !drawn.includes(id) && graph.nodes.get(id)!.kind !== "assumption");

describe("preview never commits", () => {
  it("opens exactly the routes to previewed records, saves nothing, and folds them again afterwards", async () => {
    draw(null);
    const before = cards();
    const stored = { ...sessionStorage };
    const deep = claimsBelow(before).slice(0, 3);
    const outside = [...graph.nodes.keys()].find((id) => !reach(graph, goal).has(id) && graph.nodes.get(id)!.kind !== "assumption")!;
    draw(new Set([...deep, outside]));
    await act(() => new Promise((r) => setTimeout(r, 260)));
    for (const id of deep) expect(records()).toContain(id);
    const open = [...container.querySelectorAll<HTMLElement>(".card__inputs[aria-expanded='true']")].map((b) => b.closest<HTMLElement>(".card")!.dataset.record!).sort();
    expect(open).toEqual([...neededExpansion(scopedGraph(graph, goal), goal, deep)].sort());
    for (const id of deep) expect(container.querySelector(`.card[data-record="${id}"]`)!.className).toContain("is-passage");
    expect({ ...sessionStorage }).toEqual(stored);
    // Only a record this argument cannot draw is noted.
    expect(container.querySelector(".tree__note")!.textContent).toContain("1 linked record is not in the argument for this main result");
    draw(null);
    await act(() => new Promise((r) => setTimeout(r, 320)));
    await act(() => new Promise((r) => setTimeout(r, 10)));
    expect(container.querySelectorAll(".card__inputs[aria-expanded='true']").length).toBe(0);
    expect(container.querySelector(".tree__note")).toBeNull();
  });

  it("unfolds only when asked through revealIds", () => {
    const ref = draw(null);
    const before = cards();
    const deep = claimsBelow(before).slice(0, 2);
    act(() => ref.current!.revealIds(deep));
    for (const id of deep) expect(records()).toContain(id);
    expect(ref.current!.getScene().expanded.length).toBeGreaterThan(0);
  });

  it("shows each explicit assumption as a tag button on the card that assumes it", () => {
    draw(null);
    const tags = [...container.querySelectorAll<HTMLButtonElement>(".card__tags .tag")];
    expect(tags.length).toBeGreaterThan(0);
    for (const t of tags) expect(t.getAttribute("aria-label")).toMatch(/^Explicit assumption: /);
    expect(container.querySelector('.card[data-kind="assumption"]')).toBeNull();
  });

  it("gives every card a primary open button and a real inputs button", () => {
    draw(null);
    const card = container.querySelector<HTMLElement>(`.card:not(.card--root) .card__inputs`)!.closest(".card")!;
    expect(card.getAttribute("role")).toBe("group");
    expect(card.querySelector(".card__open")!.tagName).toBe("BUTTON");
    expect(card.querySelector(".card__inputs")!.getAttribute("tabindex")).not.toBeNull();
    expect(card.querySelector(".card__inputs")!.textContent).toMatch(/^\d+ inputs?/);
  });
});

// High-rate camera input must not turn into a title/layout pass and a complete
// card/connector render for every pointer event. Keep the world transform exact,
// then perform scale-dependent work once at the next animation frame.
describe("camera display work", () => {
  function frameQueue() {
    let serial = 0;
    const pending = new Map<number, FrameRequestCallback>();
    vi.stubGlobal("requestAnimationFrame", (callback: FrameRequestCallback) => {
      pending.set(++serial, callback);
      return serial;
    });
    vi.stubGlobal("cancelAnimationFrame", (id: number) => pending.delete(id));
    return () => act(() => {
      const callbacks = [...pending.values()];
      pending.clear();
      for (const callback of callbacks) callback(performance.now());
    });
  }

  function wheel(deltaX: number, deltaY: number) {
    act(() => container.querySelector(".tree")!.dispatchEvent(new WheelEvent("wheel", {
      deltaX, deltaY, clientX: 200, clientY: 150, bubbles: true, cancelable: true,
    })));
  }

  it("pans immediately and updates edge controls without refitting or rerendering the cards", () => {
    const nextFrame = frameQueue();
    const ref = draw(null);
    act(() => ref.current!.restoreScene({ camera: { x: 0, y: 0, k: 1 }, expanded: [], mode: "steps" }));
    nextFrame();
    const beforeCards = cards();
    const beforeLines = [...container.querySelectorAll(".hit")];
    const world = container.querySelector<HTMLElement>(".tree__world")!;
    const worldX = () => Number(world.style.transform.match(/translate\(([-\d.e+]+)px/)![1]);
    const beforeX = worldX();
    const card = container.querySelector<HTMLElement>(".card")!;
    const titleQueries = vi.spyOn(card, "querySelector");
    const heights = vi.spyOn(card, "offsetHeight", "get");

    wheel(10000, 0);
    wheel(10000, 0);
    const camera = ref.current!.getScene().camera;
    expect(camera.x).toBeCloseTo(-20000);
    expect(camera.y).toBe(0);
    expect(camera.k).toBe(1);
    expect(worldX()).toBeCloseTo(beforeX - 20000);
    nextFrame();

    // The chip membership changed across the viewport, but its state belongs
    // to the small control layer: the card measurement effect never reruns.
    expect(container.querySelector(".tree__chip--down")).toBeNull();
    expect(titleQueries).not.toHaveBeenCalled();
    expect(heights).not.toHaveBeenCalled();
    expect(cards()).toEqual(beforeCards);
    expect([...container.querySelectorAll(".hit")]).toEqual(beforeLines);
    titleQueries.mockRestore();
    heights.mockRestore();
  });

  it("coalesces same-representation zooms while keeping the latest camera and all semantic zoom forms", () => {
    const nextFrame = frameQueue();
    const ref = draw(null);
    act(() => ref.current!.restoreScene({ camera: { x: 0, y: 0, k: 1 }, expanded: [], mode: "steps" }));
    nextFrame();
    const card = container.querySelector<HTMLElement>(".card")!;
    const titleQueries = vi.spyOn(card, "querySelector");
    wheel(0, -10);
    wheel(0, -10);
    const camera = ref.current!.getScene().camera;
    expect(camera.k).toBeGreaterThan(1);
    expect(titleQueries).not.toHaveBeenCalled();
    nextFrame();
    expect(titleQueries.mock.calls.filter(([selector]) => selector === ".card__ctitle")).toHaveLength(1);
    expect(ref.current!.getScene().camera).toEqual(camera);

    const before = cards();
    for (const [k, representation] of [[0.35, "mark"], [0.65, "compact"], [1, "card"]] as const) {
      act(() => ref.current!.restoreScene({ camera: { x: 10, y: 20, k }, expanded: [], mode: "steps" }));
      nextFrame();
      expect(container.querySelector<HTMLElement>(".tree")!.dataset.rep).toBe(representation);
      expect(cards()).toEqual(before);
      expect(container.querySelectorAll(".card__open").length).toBe(before.length);
      expect(ref.current!.getScene().camera.k).toBe(k);
    }
    titleQueries.mockRestore();
  });
});

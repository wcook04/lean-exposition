// The map beside the paper: which records and main result a passage selects,
// exclusive unfolding (exactly the branches that draw them), and the reader
// taking control (a pan, zoom or unfold pauses following; the toggle resumes).
import { act, createRef } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture, structureFixture } from "./fixtures";
import { chooseGoal, neededExpansion, pathFromGoal, reach, scopedGraph, visibleSet } from "../src/map/treeModel";
import { passageOf, passageRecords } from "../src/reader/page/model";

const graph = graphFixture();
const goal = "full_support";
const scoped = scopedGraph(graph, goal);
const reachOf = (g: string) => reach(scopedGraph(graph, g), g);
const insets = { top: 20, right: 20, bottom: 20, left: 20 };

describe("passage → records → main result", () => {
  const expository = structureFixture("expository");
  it("takes the passage's claims then assumptions, as the inspector lists them", () => {
    const p = passageOf(expository, "contact-and-gap")!;
    expect(passageRecords(p)).toEqual([...p.claim_ids, ...p.assumption_ids]);
  });

  it("chooses the main result whose argument contains most of them", () => {
    const records = passageRecords(passageOf(expository, "contact-and-gap"));
    const candidates = [
      { id: "scalar_value", own: false },
      { id: "full_support", own: true },
      { id: "qaoa_thermodynamic_first", own: false },
    ];
    const counts = candidates.map((c) => records.filter((id) => reachOf(c.id).has(id)).length);
    const best = candidates[counts.indexOf(Math.max(...counts))].id;
    expect(chooseGoal(records, candidates, reachOf, "scalar_value")).toBe(best);
  });

  it("prefers the account's own result on a tie, then the current one, and keeps the current one when nothing is contained", () => {
    const flat = () => new Set(["x"]);
    expect(chooseGoal(["x"], [{ id: "a", own: false }, { id: "b", own: true }], flat, "a")).toBe("b");
    expect(chooseGoal(["x"], [{ id: "a", own: false }, { id: "b", own: false }], flat, "b")).toBe("b");
    expect(chooseGoal(["nothing"], [{ id: "a", own: true }], flat, "c")).toBe("c");
  });
});

describe("exclusive expansion", () => {
  const deep = [...reach(scoped, goal)].filter((id) => (pathFromGoal(scoped, goal, id)?.length ?? 0) >= 4 && graph.nodes.get(id)!.kind !== "assumption");

  it("opens exactly the routes to the records, short of the records themselves", () => {
    const target = deep[0];
    const open = neededExpansion(scoped, goal, [target]);
    const path = pathFromGoal(scoped, goal, target)!;
    expect([...open].sort()).toEqual(path.slice(1, -1).sort());
    expect(visibleSet(scoped, goal, open).has(target)).toBe(true);
    // Nothing fewer draws it.
    for (const id of open) {
      const less = new Set(open);
      less.delete(id);
      expect(visibleSet(scoped, goal, less).has(target)).toBe(false);
    }
  });

  it("draws an assumption through a record that assumes it, without opening that record", () => {
    const assumption = [...reach(scoped, goal)].find((id) => graph.nodes.get(id)!.kind === "assumption" && (pathFromGoal(scoped, goal, id)?.length ?? 0) >= 4)!;
    const path = pathFromGoal(scoped, goal, assumption)!;
    const open = neededExpansion(scoped, goal, [assumption]);
    expect(open.has(path[path.length - 2])).toBe(false);
    expect(visibleSet(scoped, goal, open).has(path[path.length - 2])).toBe(true);
  });
});

// ---- The engine: focusIds and pausing ---------------------------------------------------

let root: Root;
let container: HTMLDivElement;

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

describe("ArgumentTree.focusIds and onUserMove", async () => {
  const { ArgumentTree } = await import("../src/map/ArgumentTree");
  type Handle = import("../src/map/ArgumentTree").MapViewHandle;
  const opened = () => [...container.querySelectorAll<HTMLElement>(".card__inputs[aria-expanded='true']")].map((b) => b.closest<HTMLElement>(".card")!.dataset.record!).sort();
  const draw = (props: Record<string, unknown> = {}, ref = createRef<Handle>()) => {
    act(() => root.render(<ArgumentTree ref={ref} graph={graph} goal={goal} insets={insets} persist={false} onSelect={() => {}} onTrace={() => {}} {...props} />));
    return ref;
  };
  const deep = [...reach(scoped, goal)].filter((id) => (pathFromGoal(scoped, goal, id)?.length ?? 0) >= 4 && graph.nodes.get(id)!.kind !== "assumption");

  it("unfolds exactly what draws the records and folds the rest, lighting them without saving", () => {
    const onUserMove = vi.fn();
    const a = deep[0];
    const b = deep.find((id) => !pathFromGoal(scoped, goal, id)!.some((p) => pathFromGoal(scoped, goal, a)!.slice(1, -1).includes(p)) ) ?? deep[deep.length - 1];
    const ref = draw({ onUserMove, litIds: new Set([a]) });
    act(() => void ref.current!.focusIds([a], { exclusive: true }));
    expect(opened()).toEqual([...neededExpansion(scoped, goal, [a])].sort());
    expect(container.querySelector(`.card[data-record="${a}"]`)!.className).toContain("is-passage");
    act(() => void ref.current!.focusIds([b], { exclusive: true }));
    expect(opened()).toEqual([...neededExpansion(scoped, goal, [b])].sort());
    expect(onUserMove).not.toHaveBeenCalled();
    expect(Object.keys(sessionStorage).filter((k) => k.startsWith("lx-tree-expanded"))).toEqual([]);
  });

  it("reports an unfold or a wheel as the reader taking control", () => {
    const onUserMove = vi.fn();
    draw({ onUserMove });
    const inputs = container.querySelector<HTMLButtonElement>(".card__inputs")!;
    act(() => inputs.click());
    expect(onUserMove).toHaveBeenCalledTimes(1);
    act(() => void container.querySelector(".tree")!.dispatchEvent(new WheelEvent("wheel", { deltaY: 30, bubbles: true, cancelable: true })));
    expect(onUserMove).toHaveBeenCalledTimes(2);
  });
});

// ---- The pane: following, pausing, back into the text -----------------------------------

vi.mock("../src/app/data", () => ({ useEdition: () => ({ graph }) }));
vi.mock("../src/app/router", () => ({ navigate: vi.fn(), routeHref: () => "#" }));
vi.mock("../src/map/TheoremPlate", () => ({
  TheoremBody: () => null,
  mainGoal: () => "full_support",
  startingGoals: () => [
    { id: "full_support", title: "Full support", stages: ["long", "short", "expository"] },
    { id: "scalar_value", title: "Value identities", stages: ["long"] },
  ],
}));

describe("MapPane", async () => {
  const { MapPane } = await import("../src/reader/page/MapPane");
  const structures = { expository: structureFixture("expository") };

  function show(anchor: string | null, onJump = vi.fn()) {
    const records = passageRecords(anchor ? passageOf(structures.expository, anchor) : undefined);
    act(() =>
      root.render(<MapPane stage="expository" structures={structures} anchor={anchor} records={records} onHide={() => {}} onJump={onJump} />),
    );
    return records;
  }
  const toggle = () => container.querySelector<HTMLButtonElement>(".map-pane__follow")!;

  it("follows each passage, pauses when the reader moves the map, and refocuses when turned back on", () => {
    const opened = () => [...container.querySelectorAll<HTMLElement>(".card__inputs[aria-expanded='true']")].map((b) => b.closest<HTMLElement>(".card")!.dataset.record!).sort();
    const needed = (anchor: string) => [...neededExpansion(scoped, goal, passageRecords(passageOf(structures.expository, anchor)))].sort();
    show("contact-and-gap");
    expect(toggle().getAttribute("aria-pressed")).toBe("true");
    expect(opened()).toEqual(needed("contact-and-gap"));
    // A wheel over the map is the reader taking control.
    act(() => void container.querySelector(".map-pane .tree")!.dispatchEvent(new WheelEvent("wheel", { deltaY: 30, bubbles: true, cancelable: true })));
    expect(toggle().getAttribute("aria-pressed")).toBe("false");
    expect(container.querySelector(".map-pane__state")!.textContent).toBe("Paused while you move the map");
    // Paused: the next passage does not move the map.
    show("endpoints");
    expect(opened()).toEqual(needed("contact-and-gap"));
    act(() => toggle().click());
    expect(toggle().getAttribute("aria-pressed")).toBe("true");
    expect(opened()).toEqual(needed("endpoints"));
  });

  it("says when a passage has no linked record", () => {
    show("changed-cases");
    expect(container.querySelector(".map-pane__state")!.textContent).toBe("No record is linked to this passage.");
  });

  it("lights the passage's drawn records", () => {
    const records = show("contact-and-gap");
    const lit = [...container.querySelectorAll<HTMLElement>(".card.is-passage")].map((el) => el.dataset.record);
    for (const id of lit) expect(records).toContain(id);
  });
});

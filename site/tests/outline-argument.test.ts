// The outline lists the same records and relations as the map's projection, and
// a shared record keeps one identity across its occurrences.
import { act, createElement } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { ArgumentOutline, MAX_DEPTH, homeParents, outlineChildren } from "../src/map/ArgumentOutline";
import { reach, usesOf } from "../src/map/treeModel";
import { graphFixture } from "./fixtures";

const graph = graphFixture();
const GOAL = "full_support";

describe("outline projection", () => {
  it("lists exactly the tree's relations under each record, supports first", () => {
    for (const id of reach(graph, GOAL)) {
      const rows = outlineChildren(graph, id);
      expect(new Set(rows.map((e) => e.key))).toEqual(new Set(usesOf(graph, id).map((e) => e.key)));
      const order = rows.map((e) => ["supports", "assumes", "formalizes"].indexOf(e.kind));
      expect(order).toEqual([...order].sort((a, b) => a - b));
    }
  });

  it("respects the account scope like the tree", () => {
    const within = new Set(graph.order.filter((id) => graph.nodes.get(id)!.papers.short));
    for (const e of outlineChildren(graph, GOAL, within)) expect(within.has(e.to)).toBe(true);
  });

  it("gives every record below the goal one home, a consumer that uses it", () => {
    const home = homeParents(graph, GOAL);
    const all = reach(graph, GOAL);
    expect(new Set(home.keys())).toEqual(new Set([...all].filter((id) => id !== GOAL)));
    for (const [id, parent] of home) expect(usesOf(graph, parent).some((e) => e.to === id)).toBe(true);
  });
});

describe("outline rendering", () => {
  let root: Root;
  let container: HTMLDivElement;
  const onSelect = vi.fn();
  const onEdgeSelect = vi.fn();

  beforeEach(() => {
    (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
    if (!(globalThis as { CSS?: unknown }).CSS) vi.stubGlobal("CSS", { escape: (s: string) => s });
    vi.stubGlobal("requestAnimationFrame", (fn: FrameRequestCallback) => {
      fn(0);
      return 0;
    });
    Element.prototype.scrollIntoView = vi.fn();
    container = document.createElement("div");
    document.body.appendChild(container);
    root = createRoot(container);
    act(() =>
      root.render(
        createElement(ArgumentOutline, { graph, goal: GOAL, goalTitle: "Full support", scope: "scope", onSelect, onEdgeSelect }),
      ),
    );
  });

  afterEach(() => {
    act(() => root.unmount());
    container.remove();
    vi.unstubAllGlobals();
  });

  const rowsOf = (id: string) => [...container.querySelectorAll<HTMLElement>(`[data-outline-id="${id}"]`)];

  it("offers the goal's inputs with a count", () => {
    const n = outlineChildren(graph, GOAL).length;
    expect(container.querySelector(".outline__explore")?.textContent).toBe(`Go to the ${n} records it uses`);
    expect(container.querySelectorAll(".outline > .outline__inputs > .outline__list > .orow")).toHaveLength(n);
  });

  it("shows a shared record twice with one id, listing its inputs under its home only", () => {
    // Open every row down to the indentation limit.
    for (let pass = 0; pass < MAX_DEPTH; pass++) {
      const closed = [...container.querySelectorAll<HTMLButtonElement>('.orow__inputs[aria-expanded="false"]')].filter(
        (b) => Number(b.closest<HTMLElement>(".orow")!.dataset.depth) < MAX_DEPTH,
      );
      act(() => closed.forEach((b) => b.click()));
    }
    const home = homeParents(graph, GOAL);
    const shared = [...home.keys()].find((id) => rowsOf(id).length > 1);
    expect(shared, "a record shown more than once").toBeDefined();
    const rows = rowsOf(shared!);
    const withInputs = rows.filter((r) => r.querySelector(":scope > .orow__body .orow__inputs"));
    const also = rows.filter((r) => r.querySelector(":scope > .orow__body .orow__also"));
    expect(withInputs.length + rows.filter((r) => r.querySelector(":scope > .orow__body .orow__leaf")).length).toBe(1);
    expect(also.length).toBe(rows.length - 1);
    expect(also[0].querySelector(".orow__also")!.textContent).toContain("Also used by");
  });

  it("refocuses on a branch below the indentation limit and shows its route", () => {
    for (let pass = 0; pass < MAX_DEPTH; pass++) {
      const closed = [...container.querySelectorAll<HTMLButtonElement>('.orow__inputs[aria-expanded="false"]')].filter(
        (b) => Number(b.closest<HTMLElement>(".orow")!.dataset.depth) < MAX_DEPTH,
      );
      act(() => closed.forEach((b) => b.click()));
    }
    const deep = container.querySelector<HTMLButtonElement>(`.orow[data-depth="${MAX_DEPTH}"] .orow__inputs`);
    if (!deep) return; // the fixture's argument may be shallower than the limit
    const id = deep.closest<HTMLElement>(".orow")!.dataset.outlineId!;
    act(() => deep.click());
    const route = container.querySelector(".outline__route");
    expect(route?.getAttribute("aria-label")).toBe("One recorded route from Full support");
    expect(route?.querySelector('[aria-current="location"]')?.textContent).toBe(graph.nodes.get(id)!.label);
  });

  it("inspects a record and a step without changing the outline", () => {
    const first = container.querySelector<HTMLElement>(".orow")!;
    act(() => first.querySelector<HTMLButtonElement>(".orow__inspect")!.click());
    expect(onSelect).toHaveBeenCalledWith(first.dataset.outlineId);
    act(() => first.querySelector<HTMLButtonElement>(".orow__rel")!.click());
    expect(onEdgeSelect).toHaveBeenCalledWith(outlineChildren(graph, GOAL)[0].key);
  });
});

// A preview (hover or focus on a passage elsewhere) tints drawn cards and
// offers to show folded ones; it never unfolds, moves or saves anything.
import { act, createRef } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture } from "./fixtures";
import { ArgumentTree, type MapViewHandle } from "../src/map/ArgumentTree";
import { reach } from "../src/map/treeModel";

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
  it("tints drawn records and counts folded ones without unfolding or saving", () => {
    draw(null);
    const before = cards();
    const stored = { ...sessionStorage };
    const deep = claimsBelow(before).slice(0, 3);
    const drawn = before.find((id) => id !== goal)!;
    draw(new Set([...deep, drawn]));
    expect(cards()).toEqual(before);
    expect({ ...sessionStorage }).toEqual(stored);
    expect(container.querySelector(`[data-card="${drawn}"]`)!.className).toContain("is-preview");
    expect(container.querySelector(".tree__note")!.textContent).toContain(`${deep.length} linked records are in collapsed branches`);
    draw(null);
    expect(cards()).toEqual(before);
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
    expect(card.querySelector(".card__inputs")!.textContent).toMatch(/Inputs · \d+/);
  });
});

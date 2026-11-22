// A large group of the focus graph opens as a list of its members beside the drawing: the
// drawing gains no node, the list searches and pages the whole group, and Fit leaves it open.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { FocusGraph, type FGCard, type FGEdge } from "../src/map/FocusGraph";

let root: Root;
let container: HTMLDivElement;

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});

afterEach(() => {
  act(() => root.unmount());
  container.remove();
  vi.unstubAllGlobals();
});

// One subject that uses 36 definitions: too many for the column, so they are drawn as one group.
const COUNT = 36;
const cards = new Map<string, FGCard>([["s", { id: "s", title: "The subject", role: "result", kicker: "Theorem 1" }]]);
for (let i = 0; i < COUNT; i++) {
  const id = `d${String(i).padStart(2, "0")}`;
  cards.set(id, {
    id,
    title: i === 30 ? "Unique zebra construction" : `Member number ${i} of the definitions`,
    role: "definition",
    kicker: i === 25 ? "Definition 9.9" : undefined,
    name: i === 33 ? "Paper.fooBarBaz" : `Paper.def${i}`,
  });
}
const edges: FGEdge[] = [...cards.keys()].filter((id) => id !== "s").map((id) => ({ from: "s", to: id, kind: "proof" }));
const card = (id: string) => cards.get(id);

function draw(props: { onSubject?: (id: string) => void; onHover?: (id: string | null) => void; subjects?: string[] } = {}) {
  act(() =>
    root.render(
      <FocusGraph subjects={props.subjects ?? ["s"]} card={card} edges={edges} onSubject={props.onSubject ?? (() => {})} onHover={props.onHover} />,
    ),
  );
}

const $ = <T extends Element = HTMLElement>(sel: string) => container.querySelector<T>(sel);
const $$ = (sel: string) => [...container.querySelectorAll<HTMLElement>(sel)];
const click = (el: Element | null) => act(() => { (el as HTMLElement).click(); });
const head = () => $(".fg__grouphead")!;
const members = () => $$(".fg__list .fg__member").map((b) => b.dataset.card);
const status = () => $(".fg__liststatus")!.textContent;
const button = (text: string) => $$("button").find((b) => b.textContent === text) as HTMLButtonElement;
function type(text: string) {
  const input = $<HTMLInputElement>(".fg__listsearch")!;
  const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value")!.set!;
  act(() => {
    set.call(input, text);
    input.dispatchEvent(new Event("input", { bubbles: true }));
  });
}

describe("a large group opens as a list of its members", () => {
  it("draws the side as one group of all 36", () => {
    draw();
    expect(head().dataset.count).toBe(String(COUNT));
    expect(head().dataset.opens).toBe("list");
    expect(head().getAttribute("aria-expanded")).toBe("false");
  });

  it("lists the members beside the drawing and adds no node to it", () => {
    draw();
    const cardsBefore = $$(".fg__world .fg__card").length;
    click(head());
    const list = $(".fg__list")!;
    expect(list).not.toBeNull();
    expect(list.getAttribute("role")).toBe("region");
    expect(list.getAttribute("aria-label")).toBe(`Members of ${head().querySelector(".fg__groupname")!.textContent}`);
    expect(list.classList.contains("fg__list--uses")).toBe(true);
    // The list is not inside the drawing's world, and the world gains nothing.
    expect(list.closest(".fg__world")).toBeNull();
    expect($$(".fg__world .fg__card").length).toBe(cardsBefore);
    expect($(".fg")!.dataset.opened).toBe("0");
    expect($$(".fg__world .fg__grouphead").length).toBe(1);
    expect(head().getAttribute("aria-expanded")).toBe("true");
    expect($(".fg__listname")!.textContent).toMatch(/, 36$/);
    expect(document.activeElement).toBe($(".fg__listsearch"));
  });

  it("zooms over the drawing and leaves wheel events over the member list and toolbar alone", () => {
    draw();
    const wheel = (el: Element, deltaY: number) => {
      const e = new WheelEvent("wheel", { bubbles: true, cancelable: true, deltaY, clientX: 12, clientY: 8 });
      act(() => { el.dispatchEvent(e); });
      return e.defaultPrevented;
    };
    const scale = () => Number($(".fg__world")!.style.transform.match(/scale\(([^)]+)\)/)?.[1] ?? 1);
    const before = scale();
    expect(wheel($(".fg__scroll")!, -4.5)).toBe(true);
    expect(scale()).toBeGreaterThan(before);
    expect(wheel($(".fg__scroll")!, 4.5)).toBe(true);
    expect(scale()).toBeCloseTo(before);
    click(head());
    expect(wheel($(".fg__list")!, 60)).toBe(false);
    expect(wheel(button("Fit"), 60)).toBe(false);
    expect(scale()).toBeCloseTo(before);
  });

  it("pages twenty members at a time and reaches every one", () => {
    draw();
    click(head());
    expect(members()).toHaveLength(20);
    expect(status()).toBe("1–20 of 36 members");
    expect(button("Previous").disabled).toBe(true);
    const first = members();
    click(button("Next"));
    expect(status()).toBe("21–36 of 36 members");
    expect(button("Next").disabled).toBe(true);
    expect(button("Previous").disabled).toBe(false);
    expect(new Set([...first, ...members()]).size).toBe(COUNT);
    // Each row has its whole title and its kind in words.
    const row = $(".fg__list .fg__member")!;
    expect(row.querySelector(".fg__membertitle")!.textContent).toMatch(/^Member number \d+ of the definitions$/);
    expect(row.querySelector(".fg__memberkind")!.textContent).toBe("Definition");
  });

  it("searches the whole group, not only the page on show", () => {
    draw();
    click(head());
    expect(members()).not.toContain("d30");
    type("ZEBRA");
    expect(members()).toEqual(["d30"]);
    expect(status()).toBe("1 of 36 members match");
    type("definition 9.9");
    expect(members()).toEqual(["d25"]);
    expect($(".fg__list .fg__memberkicker")!.textContent).toBe("Definition 9.9");
    type("barbaz");
    expect(members()).toEqual(["d33"]);
    type("nothing like this");
    expect(members()).toEqual([]);
    expect(status()).toBe("No matches among the 36 members.");
  });

  it("makes a member the subject on a click and previews it on the pointer", () => {
    const onSubject = vi.fn();
    const onHover = vi.fn();
    draw({ onSubject, onHover });
    click(head());
    const row = $$(".fg__list .fg__member")[3];
    act(() => { row.dispatchEvent(new MouseEvent("mouseover", { bubbles: true })); });
    expect(onHover).toHaveBeenLastCalledWith(row.dataset.card);
    act(() => { row.dispatchEvent(new MouseEvent("mouseout", { bubbles: true, relatedTarget: document.body })); });
    expect(onHover).toHaveBeenLastCalledWith(null);
    click(row);
    expect(onSubject).toHaveBeenCalledWith(row.dataset.card);
  });

  it("keeps the list open, with its search and page, when Fit is pressed", () => {
    draw();
    click(head());
    type("member");
    click(button("Next"));
    const before = status();
    click(button("Fit"));
    expect($(".fg__list")).not.toBeNull();
    expect($<HTMLInputElement>(".fg__listsearch")!.value).toBe("member");
    expect(status()).toBe(before);
  });

  it("closes on Escape or Back to the graph, returns focus to the group and remembers the search", () => {
    draw();
    click(head());
    type("zebra");
    act(() => { $(".fg__listsearch")!.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true })); });
    expect($(".fg__list")).toBeNull();
    expect(document.activeElement).toBe(head());
    expect(head().getAttribute("aria-expanded")).toBe("false");
    click(head());
    expect($<HTMLInputElement>(".fg__listsearch")!.value).toBe("zebra");
    expect(members()).toEqual(["d30"]);
    click(button("Back to the graph"));
    expect($(".fg__list")).toBeNull();
    expect(document.activeElement).toBe(head());
  });

  it("forgets the list and its search when the subject changes", () => {
    draw();
    click(head());
    type("zebra");
    draw({ subjects: ["d30"] });
    expect($(".fg__list")).toBeNull();
    draw({ subjects: ["s"] });
    click(head());
    expect($<HTMLInputElement>(".fg__listsearch")!.value).toBe("");
  });
});

describe("the key names the relations drawn", () => {
  it("says which way arrows run and names each kind of line on show", () => {
    draw();
    const key = $(".fg__key")!.textContent!;
    expect(key).toContain("Arrows run from a statement to what it uses.");
    expect(key).toContain("Used in a Lean proof or body");
    expect(key).not.toContain("Used in a Lean statement");
    expect(key).toContain("group, opens its members");
    // Each line carries its relation's name, and a group's line is no heavier than any other.
    const line = $(".fg__lines path.fg__edge")!;
    expect(line.querySelector("title")!.textContent).toBe("Used in a Lean proof or body");
    expect(line.getAttribute("style")).toBeNull();
  });
});

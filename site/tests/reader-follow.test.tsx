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
  StatementExcerpt: () => null,
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

  it("follows each passage without folding, pauses when the reader moves the map, and refocuses when turned back on", () => {
    const opened = () => new Set([...container.querySelectorAll<HTMLElement>(".card__inputs[aria-expanded='true']")].map((b) => b.closest<HTMLElement>(".card")!.dataset.record!));
    const needed = (anchor: string) => [...neededExpansion(scoped, goal, passageRecords(passageOf(structures.expository, anchor)))];
    const holds = (anchor: string) => needed(anchor).every((id) => opened().has(id));
    show("contact-and-gap");
    expect(toggle().getAttribute("aria-pressed")).toBe("true");
    expect(holds("contact-and-gap")).toBe(true);
    // A wheel over the map is the reader taking control.
    act(() => void container.querySelector(".map-pane .tree")!.dispatchEvent(new WheelEvent("wheel", { deltaY: 30, bubbles: true, cancelable: true })));
    expect(toggle().getAttribute("aria-pressed")).toBe("false");
    expect(container.querySelector(".map-pane__state")!.textContent).toBe("Paused while you move the map");
    // Paused: the next passage changes nothing on the map.
    const before = opened();
    show("endpoints");
    expect(opened()).toEqual(before);
    act(() => toggle().click());
    expect(toggle().getAttribute("aria-pressed")).toBe("true");
    // Following again opens what the passage needs and keeps what was open.
    expect(holds("endpoints")).toBe(true);
    for (const id of before) expect(opened().has(id)).toBe(true);
  });

  it("fades records the paper does not discuss, and names the paper that does when one is chosen", () => {
    show("contact-and-gap");
    const covered = new Set(structures.expository.paper.passages.flatMap((p) => [...p.claim_ids, ...p.assumption_ids]));
    const cards = [...container.querySelectorAll<HTMLElement>(".card:not(.card--root)")];
    expect(cards.length).toBeGreaterThan(0);
    for (const el of cards) expect(el.classList.contains("is-elsewhere")).toBe(!covered.has(el.dataset.record!));
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

describe("framing a passage", async () => {
  const { ArgumentTree } = await import("../src/map/ArgumentTree");
  type Handle = import("../src/map/ArgumentTree").MapViewHandle;
  const W = 820;
  const H = 900;
  const pane = { top: 20, right: 20, bottom: 20, left: 20 };

  it("puts every lit record wholly inside the visible canvas", async () => {
    // A sized canvas, measured cards and reduced motion, so the framing lands at once.
    vi.stubGlobal(
      "ResizeObserver",
      class {
        constructor(private cb: (entries: unknown[]) => void) {}
        observe(el: HTMLElement) {
          if (el.classList.contains("tree")) this.cb([{ contentRect: { width: W, height: H }, target: el }]);
        }
        disconnect() {}
      },
    );
    vi.stubGlobal("matchMedia", (q: string) => ({ matches: q.includes("reduce"), media: q, addEventListener() {}, removeEventListener() {} }));
    const height = Object.getOwnPropertyDescriptor(HTMLElement.prototype, "offsetHeight");
    Object.defineProperty(HTMLElement.prototype, "offsetHeight", { configurable: true, get() { return this.dataset?.card ? (this.dataset.card === goal ? 300 : 120) : 0; } });
    try {
      const expository = structureFixture("expository");
      for (const anchor of ["value-and-diffusion", "contact-and-gap", "endpoints", "curvature-transfer"]) {
        const records = passageRecords(passageOf(expository, anchor)).filter((id) => reach(scoped, goal).has(id) && graph.nodes.get(id)!.kind !== "assumption");
        if (!records.length) continue;
        const ref = createRef<Handle>();
        act(() => root.render(<ArgumentTree key={anchor} ref={ref} graph={graph} goal={goal} insets={pane} persist={false} litIds={new Set(records)} onSelect={() => {}} onTrace={() => {}} />));
        act(() => void ref.current!.focusIds(records, { exclusive: true }));
        await act(() => new Promise((r) => setTimeout(r, 1300)));
        const world = container.querySelector<HTMLElement>(".tree__world")!.style.transform;
        const [, tx, ty, k] = world.match(/translate\(([-\d.]+)px, ([-\d.]+)px\) scale\(([-\d.]+)\)/)!.map(Number);
        expect(k).toBeGreaterThanOrEqual(0.5 - 1e-6);
        expect(k).toBeLessThanOrEqual(1 + 1e-6);
        const lit = [...container.querySelectorAll<HTMLElement>(".card.is-passage")];
        expect(lit.length).toBeGreaterThan(0);
        for (const el of lit) {
          const [, x, y] = el.style.transform.match(/translate\(([-\d.]+)px, ([-\d.]+)px\)/)!.map(Number);
          const w = parseFloat(el.style.width);
          const h = el.dataset.card === goal ? 300 : 120;
          const box = { x0: x * k + tx, y0: y * k + ty, x1: (x + w) * k + tx, y1: (y + h) * k + ty };
          expect(box.x0, `${anchor} ${el.dataset.card}`).toBeGreaterThanOrEqual(pane.left - 0.5);
          expect(box.y0, `${anchor} ${el.dataset.card}`).toBeGreaterThanOrEqual(pane.top - 0.5);
          expect(box.x1, `${anchor} ${el.dataset.card}`).toBeLessThanOrEqual(W - pane.right + 0.5);
          expect(box.y1, `${anchor} ${el.dataset.card}`).toBeLessThanOrEqual(H - pane.bottom + 0.5);
        }
      }
    } finally {
      if (height) Object.defineProperty(HTMLElement.prototype, "offsetHeight", height);
    }
  });
});

describe("compact line limits", async () => {
  const { compactLines } = await import("../src/map/canvas/representation");
  it("fits as many title lines as the tile's height on screen holds", () => {
    // 124px card at k = 0.65: 80.6px on screen, less 18px padding and border, 15.86px lines -> 3.
    expect(compactLines(124, 0.65, "card")).toBe(3);
    expect(compactLines(124, 0.79, "card")).toBe(5);
    expect(compactLines(124, 0.52, "card")).toBe(2);
    expect(compactLines(40, 0.5, "card")).toBe(1);
    // The plate keeps a line for "MAIN RESULT"; its title starts at 24px.
    expect(compactLines(300, 0.65, "root")).toBe(5);
    expect(compactLines(200, 1, "card")).toBe(compactLines(200, 1, "lean") - 1);
  });
});

describe("the peek", async () => {
  const { ArgumentTree } = await import("../src/map/ArgumentTree");
  const { lineageOf } = await import("../src/map/treeModel");
  const W = 1400;
  const H = 900;

  it("takes every record below the card, down to records with no inputs", () => {
    const top = [...(scoped.out.get(goal) ?? [])].map((e) => e.to).find((id) => (scoped.out.get(id) ?? []).length > 0)!;
    const lineage = lineageOf(scoped, top, undefined);
    // Closed under uses, and nothing else.
    for (const id of lineage) for (const e of scoped.out.get(id) ?? []) if (["supports", "formalizes", "assumes"].includes(e.kind)) expect(lineage.has(e.to)).toBe(true);
    for (const id of lineage) expect(reach(scoped, top).has(id)).toBe(true);
    expect(lineage.has(top)).toBe(false);
  });

  it("draws the lineage faded with the hovered card held still, and a click keeps it open", async () => {
    vi.stubGlobal(
      "ResizeObserver",
      class {
        constructor(private cb: (entries: unknown[]) => void) {}
        observe(el: HTMLElement) {
          if (el.classList.contains("tree")) this.cb([{ contentRect: { width: W, height: H }, target: el }]);
        }
        disconnect() {}
      },
    );
    vi.stubGlobal("matchMedia", (q: string) => ({ matches: q.includes("reduce"), media: q, addEventListener() {}, removeEventListener() {} }));
    const height = Object.getOwnPropertyDescriptor(HTMLElement.prototype, "offsetHeight");
    Object.defineProperty(HTMLElement.prototype, "offsetHeight", { configurable: true, get() { return this.dataset?.card ? (this.dataset.card === goal ? 300 : 120) : 0; } });
    try {
      const selected: string[] = [];
      act(() => root.render(<ArgumentTree graph={graph} goal={goal} insets={insets} persist={false} onSelect={(id) => id && selected.push(id)} onTrace={() => {}} />));
      await act(() => new Promise((r) => setTimeout(r, 1300)));
      const card = [...container.querySelectorAll<HTMLElement>(".card:not(.card--root)")].find((el) => el.querySelector(".card__inputs[aria-expanded='false']"))!;
      const id = card.dataset.record!;
      const screen = () => {
        const [, tx, ty, k] = container.querySelector<HTMLElement>(".tree__world")!.style.transform.match(/translate\(([-\d.]+)px, ([-\d.]+)px\) scale\(([-\d.]+)\)/)!.map(Number);
        const [, x, y] = card.style.transform.match(/translate\(([-\d.]+)px, ([-\d.]+)px\)/)!.map(Number);
        return { x: x * k + tx, y: y * k + ty };
      };
      const before = screen();
      const drawnBefore = new Set([...container.querySelectorAll<HTMLElement>(".card")].map((el) => el.dataset.record));
      act(() => void card.dispatchEvent(new MouseEvent("pointerover", { bubbles: true })));
      await act(() => new Promise((r) => setTimeout(r, 320)));
      const faded = [...container.querySelectorAll<HTMLElement>(".card.is-peeked")];
      expect(faded.length).toBeGreaterThan(0);
      const lineage = lineageOf(scoped, id, undefined);
      for (const el of faded) {
        expect(lineage.has(el.dataset.record!)).toBe(true);
        expect(drawnBefore.has(el.dataset.record!) && el.dataset.card === el.dataset.record).toBe(false);
        expect(el.getAttribute("aria-hidden")).toBe("true");
        expect([...el.querySelectorAll("button")].every((b) => b.tabIndex === -1)).toBe(true);
      }
      const after = screen();
      expect(Math.abs(after.x - before.x)).toBeLessThan(0.5);
      expect(Math.abs(after.y - before.y)).toBeLessThan(0.5);
      // A click while the peek shows keeps the lineage open and selects.
      const fadedRecords = new Set(faded.map((el) => el.dataset.record));
      act(() => card.click());
      expect(selected).toEqual([id]);
      expect(container.querySelectorAll(".card.is-peeked").length).toBe(0);
      const drawn = new Set([...container.querySelectorAll<HTMLElement>(".card")].map((el) => el.dataset.record));
      for (const r of fadedRecords) expect(drawn.has(r)).toBe(true);
      // Leaving no longer folds anything.
      act(() => void card.dispatchEvent(new MouseEvent("pointerout", { bubbles: true })));
      await act(() => new Promise((r) => setTimeout(r, 300)));
      for (const r of fadedRecords) expect(container.querySelector(`.card[data-record="${r}"]`)).not.toBeNull();
    } finally {
      if (height) Object.defineProperty(HTMLElement.prototype, "offsetHeight", height);
    }
  });
});

describe("shrink to fit", async () => {
  const { fitTitle, wrapLines, titlePieces } = await import("../src/map/canvas/representation");

  it("splits a Lean name after dots and underscores and between camel-case words, never inside a word", () => {
    const pieces = titlePieces("OAI.ZeroTemperatureSK.full_support", true).map((p) => p.text);
    expect(pieces).toEqual(["OAI.", "Zero", "Temperature", "SK.", "full_", "support"]);
    expect(pieces.join("")).toBe("OAI.ZeroTemperatureSK.full_support");
  });
  // Each piece 40px wide at 100px, joined by 25px spaces: about 5.2px and 3.25px at 13px.
  const words = (n: number, w = 40) => ({ pieces: Array.from({ length: n }, (_, i) => ({ w, gap: i ? 25 : 0 })) });

  it("keeps 13px when the whole title fits", () => {
    expect(fitTitle(words(3), 176, 124, 0.7, "card")).toEqual({ size: 13, lines: expect.any(Number), fits: true });
  });

  it("chooses the largest smaller size at which the whole title fits, else clamps at 10px", () => {
    // A tile 176 x 124 at k = 0.55: 80.8px wide and 49.2px tall on screen less padding (two lines at 13px).
    const t = words(14, 130);
    const fit = fitTitle(t, 176, 124, 0.55, "card");
    const width = 176 * 0.55 - 2 - 16;
    if (fit.fits) {
      expect(fit.size).toBeLessThanOrEqual(13);
      expect(wrapLines(t, fit.size, width)).toBeLessThanOrEqual(fit.lines);
      // No larger size would have fitted.
      for (let s = fit.size + 0.5; s <= 13; s += 0.5) {
        const lines = Math.max(1, Math.floor((124 * 0.55 - 19 + 0.5) / (s * 1.22)));
        expect(wrapLines(t, s, width)).toBeGreaterThan(lines);
      }
    } else expect(fit.size).toBe(10);
    expect(fitTitle(words(60, 200), 176, 124, 0.52, "card")).toMatchObject({ size: 10, fits: false });
  });

  it("breaks a Lean name only between its pieces, down to 10px", () => {
    const lean = { pieces: [{ w: 240, gap: 0 }, { w: 1020, gap: 0 }, { w: 300, gap: 0 }] };
    // The longest piece (1020 at 100px) must fit across: 10.2px at 10px in an 88px line.
    expect(fitTitle(lean, 196, 112, 0.55, "lean").fits).toBe(false);
    expect(fitTitle(lean, 196, 112, 0.7, "lean")).toMatchObject({ fits: true });
  });
});

describe("text on marks and the plate", async () => {
  const { fitMark, fitPlate, fitTitle, keptPieces, shortTitle, titlePieces, wrapLines, STATEMENT_W } = await import("../src/map/canvas/representation");
  const words = (n: number, w = 40) => ({ pieces: Array.from({ length: n }, (_, i) => ({ w, gap: i ? 25 : 0 })) });

  it("shows a mark's whole title when it fits at 10px or more on screen", () => {
    // A 176 x 213 card at k = 0.4 is a 70 x 85 mark on screen.
    expect(fitMark(words(3), 176, 213, 0.4, "card")).toMatchObject({ size: 13, fits: true, show: true });
  });

  it("cuts a long title at 10px when two lines fit, every word fits across and half the words stay", () => {
    const t = words(14, 130);
    const fit = fitMark(t, 176, 124, 0.45, "card");
    expect(fit).toMatchObject({ size: 10, fits: false, show: true });
    expect(fit.lines).toBeGreaterThanOrEqual(2);
    expect(wrapLines(t, 10, 176 * 0.45 - 10)).toBeGreaterThan(fit.lines);
    expect(fit.kept! * 2).toBeGreaterThanOrEqual(14);
    // Four words of nine are not enough to name the record: a plain mark instead.
    expect(fitMark(words(9, 280), 176, 90, 0.4, "card")).toMatchObject({ kept: 4, show: false });
  });

  it("cuts after a whole word, with room for the ellipsis, and drops trailing punctuation", () => {
    const t = {
      pieces: ["Existence,", "coupling", "and", "uniqueness", "of", "the", "controlled", "diffusion"].map((text, i) => ({ text, w: text.length * 50, gap: i ? 25 : 0 })),
      ellipsis: 100,
    };
    // At 10px a 60px line holds "Existence," (50px), then "coupling and" (57.5px), but "and…" would overflow.
    const kept = keptPieces(t, 10, 60, 2);
    expect(kept).toBe(2);
    expect(shortTitle(t, kept)).toBe("Existence, coupling…");
    expect(shortTitle(t, 1)).toBe("Existence…");
    expect(shortTitle(t, 4)).toBe("Existence, coupling and uniqueness…");
    expect(fitTitle(t, 176, 40, 0.5, "card")).toMatchObject({ fits: false, short: expect.stringMatching(/…$/) });
  });

  it("keeps hyphenated words whole in the plate's title", () => {
    expect(titlePieces("Full support of zero-temperature SK minimizers", false, true).map((p) => p.text)).toEqual(["Full", "support", "of", "zero-temperature", "SK", "minimizers"]);
    expect(titlePieces("zero-temperature", false).map((p) => p.text)).toEqual(["zero-", "temperature"]);
  });

  it("stays a plain mark when a word is wider than a line or no line fits", () => {
    expect(fitMark(words(3, 900), 176, 124, 0.45, "card").show).toBe(false);
    expect(fitMark(words(1), 176, 122, 0.15, "card").show).toBe(false);
    expect(fitMark(words(3), 176, 122, 0.15, "card").show).toBe(false);
  });

  it("judges each mark by its own size, so the plate keeps its title after the tiles lose theirs", () => {
    const title = words(6, 400);
    expect(fitMark(title, 176, 213, 0.25, "card").show).toBe(false);
    expect(fitMark(title, 800, 427, 0.25, "root")).toMatchObject({ fits: true, show: true });
  });

  it("adds the theorem's first sentence to the plate when it is wide and tall enough", () => {
    const title = words(6, 400);
    // Two lines at 24px, or one line at 19.5px, within a fifth of it: the plate takes one line.
    expect(fitPlate(title, 800, 427, 0.65, 91)).toMatchObject({ size: 19.5, lines: 1, fits: true, statement: true });
    // The 560px measure holds the six words at 21px (25.25 x 21 = 530px).
    expect(fitPlate(title, 800, 427, 0.85, 91)).toMatchObject({ size: 21, lines: 1, statement: true });
    // Unmeasured, too narrow for STATEMENT_W, or too short: the title alone.
    expect(fitPlate(title, 800, 427, 0.65, 0).statement).toBe(false);
    expect(800 * 0.44 - 18).toBeLessThan(STATEMENT_W);
    expect(fitPlate(title, 800, 427, 0.44, 91).statement).toBe(false);
    expect(fitPlate(title, 800, 200, 0.6, 91)).toMatchObject({ statement: false, fits: true });
  });
});

describe("opening a card", async () => {
  const { ArgumentTree } = await import("../src/map/ArgumentTree");
  const { lineageOf } = await import("../src/map/treeModel");
  const W = 1400;
  const H = 700;
  const stub = () => {
    vi.stubGlobal(
      "ResizeObserver",
      class {
        constructor(private cb: (entries: unknown[]) => void) {}
        observe(el: HTMLElement) {
          if (el.classList.contains("tree")) this.cb([{ contentRect: { width: W, height: H }, target: el }]);
        }
        disconnect() {}
      },
    );
    vi.stubGlobal("matchMedia", (q: string) => ({ matches: q.includes("reduce"), media: q, addEventListener() {}, removeEventListener() {} }));
    const height = Object.getOwnPropertyDescriptor(HTMLElement.prototype, "offsetHeight");
    Object.defineProperty(HTMLElement.prototype, "offsetHeight", { configurable: true, get() { return this.dataset?.card ? (this.dataset.card === goal ? 300 : 120) : 0; } });
    return () => {
      if (height) Object.defineProperty(HTMLElement.prototype, "offsetHeight", height);
    };
  };
  const world = () => {
    const [, x, y, k] = container.querySelector<HTMLElement>(".tree__world")!.style.transform.match(/translate\(([-\d.]+)px, ([-\d.]+)px\) scale\(([-\d.]+)\)/)!.map(Number);
    return { x, y, k };
  };
  // The closed card with the largest lineage.
  const biggest = () =>
    [...container.querySelectorAll<HTMLElement>(".card:not(.card--root)")]
      .filter((el) => el.querySelector(".card__inputs[aria-expanded='false']"))
      .sort((a, b) => lineageOf(scoped, b.dataset.record!).size - lineageOf(scoped, a.dataset.record!).size)[0];
  const drawn = () => new Set([...container.querySelectorAll<HTMLElement>(".card")].map((el) => el.dataset.record!));

  it("zooms about the pointer when scrolled up or down, and pans when swiped sideways", async () => {
    const restore = stub();
    try {
      act(() => root.render(<ArgumentTree graph={graph} goal={goal} insets={insets} persist={false} onSelect={() => {}} onTrace={() => {}} />));
      await act(() => new Promise((r) => setTimeout(r, 1300)));
      const tree = container.querySelector<HTMLElement>(".tree")!;
      const home = world();
      // Two fingers on a trackpad: small, fractional steps.
      act(() => void tree.dispatchEvent(new WheelEvent("wheel", { deltaY: 6.5, deltaX: 0.5, clientX: 700, clientY: 350, bubbles: true, cancelable: true })));
      const zoomed = world();
      expect(zoomed.k).toBeLessThan(home.k);
      expect((700 - zoomed.x) / zoomed.k).toBeCloseTo((700 - home.x) / home.k, 3);
      expect((350 - zoomed.y) / zoomed.k).toBeCloseTo((350 - home.y) / home.k, 3);
      act(() => void tree.dispatchEvent(new WheelEvent("wheel", { deltaX: 40, deltaY: 3, bubbles: true, cancelable: true })));
      const panned = world();
      expect(panned.k).toBeCloseTo(zoomed.k, 6);
      expect(panned.x).toBeCloseTo(zoomed.x - 40, 3);
      expect(panned.y).toBeCloseTo(zoomed.y, 3);
    } finally {
      restore();
    }
  });

  it("draws the lineage on hover without moving the camera, and leaves the camera where it was", async () => {
    const restore = stub();
    try {
      act(() => root.render(<ArgumentTree graph={graph} goal={goal} insets={insets} persist={false} onSelect={() => {}} onTrace={() => {}} />));
      await act(() => new Promise((r) => setTimeout(r, 1300)));
      const card = biggest();
      const home = world();
      act(() => void card.dispatchEvent(new MouseEvent("pointerover", { bubbles: true })));
      await act(() => new Promise((r) => setTimeout(r, 400)));
      await act(() => new Promise((r) => setTimeout(r, 900)));
      expect(container.querySelectorAll(".card.is-peeked").length).toBeGreaterThan(0);
      // No zoom, however long the pointer rests.
      expect(world().k).toBeCloseTo(home.k, 4);
      act(() => void card.dispatchEvent(new MouseEvent("pointerout", { bubbles: true })));
      await act(() => new Promise((r) => setTimeout(r, 300)));
      const back = world();
      expect(container.querySelectorAll(".card.is-peeked").length).toBe(0);
      expect(back.k).toBeCloseTo(home.k, 4);
      expect(back.x).toBeCloseTo(home.x, 1);
      expect(back.y).toBeCloseTo(home.y, 1);
    } finally {
      restore();
    }
  });

  it("opens a clicked card's whole lineage and frames it, and a click on the empty map puts the map back", async () => {
    const restore = stub();
    try {
      const selected: (string | null)[] = [];
      act(() => root.render(<ArgumentTree graph={graph} goal={goal} insets={insets} persist={false} onSelect={(id) => selected.push(id)} onTrace={() => {}} />));
      await act(() => new Promise((r) => setTimeout(r, 1300)));
      const card = biggest();
      const id = card.dataset.record!;
      const home = world();
      const before = drawn();
      act(() => card.querySelector<HTMLElement>(".card__open")!.click());
      await act(() => new Promise((r) => setTimeout(r, 500)));
      expect(selected).toEqual([id]);
      // Every record below it that is drawn as a card (assumptions are tags) is on the map, solid...
      const lineage = [...lineageOf(scoped, id)].filter((x) => graph.nodes.get(x)!.kind !== "assumption");
      expect(lineage.length).toBeGreaterThan(1);
      for (const x of lineage) expect(container.querySelector(`.card[data-record="${x}"]`)).not.toBeNull();
      expect(container.querySelectorAll(".card.is-peeked").length).toBe(0);
      // ...and the card and all of it lie inside the canvas.
      const v = world();
      for (const x of [id, ...lineage]) {
        for (const el of container.querySelectorAll<HTMLElement>(`.card[data-record="${x}"]`)) {
          const [, cx, cy] = el.style.transform.match(/translate\(([-\d.]+)px, ([-\d.]+)px\)/)!.map(Number);
          const left = cx * v.k + v.x;
          const top = cy * v.k + v.y;
          expect(left).toBeGreaterThanOrEqual(insets.left - 1);
          expect(top).toBeGreaterThanOrEqual(insets.top - 1);
          expect(left + parseFloat(el.style.width) * v.k).toBeLessThanOrEqual(W - insets.right + 1);
          expect(top + 120 * v.k).toBeLessThanOrEqual(H - insets.bottom + 1);
        }
      }
      // A click on the empty map: the unfolding and camera from before.
      act(() => container.querySelector<HTMLElement>(".tree")!.click());
      await act(() => new Promise((r) => setTimeout(r, 500)));
      expect(drawn()).toEqual(before);
      const back = world();
      expect(back.k).toBeCloseTo(home.k, 4);
      expect(back.x).toBeCloseTo(home.x, 1);
      expect(back.y).toBeCloseTo(home.y, 1);
    } finally {
      restore();
    }
  });
});

describe("a preview's reveal on the map page", async () => {
  const { ArgumentTree } = await import("../src/map/ArgumentTree");
  it("frames the previewed records, and puts the camera back when the preview ends", async () => {
    vi.stubGlobal(
      "ResizeObserver",
      class {
        constructor(private cb: (entries: unknown[]) => void) {}
        observe(el: HTMLElement) {
          if (el.classList.contains("tree")) this.cb([{ contentRect: { width: 1200, height: 700 }, target: el }]);
        }
        disconnect() {}
      },
    );
    vi.stubGlobal("matchMedia", (q: string) => ({ matches: q.includes("reduce"), media: q, addEventListener() {}, removeEventListener() {} }));
    const height = Object.getOwnPropertyDescriptor(HTMLElement.prototype, "offsetHeight");
    Object.defineProperty(HTMLElement.prototype, "offsetHeight", { configurable: true, get() { return this.dataset?.card ? (this.dataset.card === goal ? 300 : 120) : 0; } });
    try {
      const draw = (preview: ReadonlySet<string> | null) =>
        act(() => root.render(<ArgumentTree graph={graph} goal={goal} insets={insets} previewIds={preview} onSelect={() => {}} onTrace={() => {}} />));
      const world = () => container.querySelector<HTMLElement>(".tree__world")!.style.transform;
      draw(null);
      await act(() => new Promise((r) => setTimeout(r, 1300)));
      const home = world();
      const deep = [...reach(scoped, goal)].filter((id) => (pathFromGoal(scoped, goal, id)?.length ?? 0) >= 4 && graph.nodes.get(id)!.kind !== "assumption").slice(0, 2);
      draw(new Set(deep));
      await act(() => new Promise((r) => setTimeout(r, 50)));
      await act(() => new Promise((r) => setTimeout(r, 50)));
      expect(world()).not.toBe(home);
      // Every previewed record inside the canvas.
      const [, tx, ty, k] = world().match(/translate\(([-\d.]+)px, ([-\d.]+)px\) scale\(([-\d.]+)\)/)!.map(Number);
      for (const id of deep) {
        const el = container.querySelector<HTMLElement>(`.card[data-record="${id}"]`)!;
        const [, x, y] = el.style.transform.match(/translate\(([-\d.]+)px, ([-\d.]+)px\)/)!.map(Number);
        expect(x * k + tx).toBeGreaterThanOrEqual(insets.left - 0.5);
        expect((y + 120) * k + ty).toBeLessThanOrEqual(700 - insets.bottom + 0.5);
      }
      draw(null);
      await act(() => new Promise((r) => setTimeout(r, 50)));
      await act(() => new Promise((r) => setTimeout(r, 50)));
      expect(world()).toBe(home);
      expect(container.querySelectorAll(".card__inputs[aria-expanded='true']").length).toBe(0);
    } finally {
      if (height) Object.defineProperty(HTMLElement.prototype, "offsetHeight", height);
    }
  });
});

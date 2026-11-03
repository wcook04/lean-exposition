// The map beside the paper: which records and main result a passage selects,
// exclusive unfolding (exactly the branches that draw them), and the reader
// taking control (a pan, zoom or unfold pauses following; the toggle resumes).
import { act, createRef } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture, structureFixture } from "./fixtures";
import { chooseGoal, neededExpansion, pathFromGoal, reach, scopedGraph, visibleSet } from "../src/map/treeModel";
import { paperTrail, passageOf, passageRecords } from "../src/reader/page/model";
import { Signal } from "../src/reader/page/signal";
import type { Followed, Pointed } from "../src/reader/page/rightPage";
import { tieModel } from "../src/reader/ties";
import type { MapViewHandle } from "../src/map/ArgumentTree";

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

  const signals = {
    heading: new Signal<string | null>(null),
    part: new Signal(0),
    follow: new Signal<Followed>({ tie: null, anchor: null, part: 0 }),
    point: new Signal<Pointed | null>(null),
    caption: new Signal<string | null>(null),
  };
  const trail = paperTrail(structures.expository);
  const ties = tieModel(null);

  function show(anchor: string | null, onJump = vi.fn(), mode: "graph" | "lean" = "graph", onMode: (m: "graph" | "lean") => void = () => {}) {
    act(() => signals.follow.set({ tie: null, anchor, part: 0 }));
    act(() =>
      root.render(<MapPane stage="expository" structures={structures} outline={[]} trail={trail} signals={signals} ties={ties} pin={null} mode={mode} onMode={onMode} onHide={() => {}} onRecord={onJump} onRelease={() => {}} onPoint={() => {}} />),
    );
  }
  const resume = () => container.querySelector<HTMLButtonElement>(".map-pane__follow");

  it("keeps following through initial framing, then yields to wheel and drag input immediately, and says how to resume", async () => {
    vi.stubGlobal("ResizeObserver", class {
      constructor(private cb: (entries: unknown[]) => void) {}
      observe(el: HTMLElement) {
        if (el.classList.contains("tree")) this.cb([{ contentRect: { width: 820, height: 900 }, target: el }]);
      }
      disconnect() {}
    });
    vi.stubGlobal("matchMedia", (q: string) => ({ matches: q.includes("reduce"), media: q, addEventListener() {}, removeEventListener() {} }));
    show("contact-and-gap");
    // Includes expandAll, the delayed initial passage frame, and late first-fit setup.
    await act(() => new Promise((resolve) => setTimeout(resolve, 1300)));
    expect(resume()).toBeNull();
    const tree = container.querySelector<HTMLElement>(".map-pane .tree")!;
    const world = tree.querySelector<HTMLElement>(".tree__world")!;
    const before = world.style.transform;
    act(() => void tree.dispatchEvent(new WheelEvent("wheel", { deltaY: 30, bubbles: true, cancelable: true })));
    expect(world.style.transform).not.toBe(before);
    expect(resume()!.textContent).toBe("Move the graph with the text again");
    act(() => resume()!.click());
    expect(resume()).toBeNull();
    const beforeDrag = world.style.transform;
    const mouse = (type: string, clientX: number, clientY: number) => {
      const event = new MouseEvent(type, { clientX, clientY, bubbles: true });
      // Vitest's Window proxy is rejected by jsdom's UIEvent constructor.
      Object.defineProperty(event, "view", { value: window });
      return event;
    };
    act(() => {
      tree.dispatchEvent(mouse("mousedown", 400, 400));
      window.dispatchEvent(mouse("mousemove", 450, 420));
      window.dispatchEvent(mouse("mouseup", 450, 420));
    });
    expect(world.style.transform).not.toBe(beforeDrag);
    expect(resume()).not.toBeNull();
    // d3 suppresses the click following a drag until the next task; let that
    // capture listener expire before another test clicks in this window.
    await act(() => new Promise((resolve) => setTimeout(resolve, 0)));
  });

  it("follows each passage without folding, pauses when the reader moves the map, and refocuses when turned back on", () => {
    const opened = () => new Set([...container.querySelectorAll<HTMLElement>(".card__inputs[aria-expanded='true']")].map((b) => b.closest<HTMLElement>(".card")!.dataset.record!));
    const needed = (anchor: string) => [...neededExpansion(scoped, goal, passageRecords(passageOf(structures.expository, anchor)))];
    const holds = (anchor: string) => needed(anchor).every((id) => opened().has(id));
    show("contact-and-gap");
    expect(resume()).toBeNull();
    expect(holds("contact-and-gap")).toBe(true);
    // A wheel over the map is the reader taking control.
    act(() => void container.querySelector(".map-pane .tree")!.dispatchEvent(new WheelEvent("wheel", { deltaY: 30, bubbles: true, cancelable: true })));
    expect(resume()).not.toBeNull();
    // Paused: the next passage changes nothing on the map.
    const before = opened();
    show("endpoints");
    expect(opened()).toEqual(before);
    act(() => resume()!.click());
    expect(resume()).toBeNull();
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

  it("says in one line under the graph when nothing in this stretch is tied", () => {
    show("changed-cases");
    expect(container.querySelector(".map-pane__line")!.textContent).toBe("Nothing in this stretch of the paper is tied to the Lean.");
    expect(container.querySelector(".lean-page")).toBeNull();
  });

  it("has one toggle, and the Lean only in Lean mode", () => {
    const onMode = vi.fn();
    show("contact-and-gap", vi.fn(), "graph", onMode);
    expect(container.querySelector(".lean-page")).toBeNull();
    const words = [...container.querySelectorAll<HTMLButtonElement>(".mode-toggle button")];
    expect(words.map((w) => w.textContent)).toEqual(["Graph", "Lean"]);
    expect(words[0].getAttribute("aria-pressed")).toBe("true");
    act(() => words[1].click());
    expect(onMode).toHaveBeenCalledWith("lean");
    show("contact-and-gap", vi.fn(), "lean", onMode);
    expect(container.querySelector<HTMLElement>(".lean-page")!.dataset.via).toBe("follow");
    expect(container.querySelector(".mode-toggle [aria-pressed='true']")!.textContent).toBe("Lean");
  });

  it("lights the passage's drawn records", () => {
    show("contact-and-gap");
    const records = passageRecords(passageOf(structures.expository, "contact-and-gap"));
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

describe("the lineage", async () => {
  const { lineageOf } = await import("../src/map/treeModel");
  it("takes every record below the card, down to records with no inputs", () => {
    const scoped = scopedGraph(graph, goal);
    const top = [...reach(scoped, goal)].find((id) => id !== goal && (scoped.out.get(id) ?? []).length > 0)!;
    const lineage = lineageOf(scoped, top, undefined);
    expect(lineage.size).toBeGreaterThan(0);
    for (const id of lineage) for (const e of scoped.out.get(id) ?? []) if (["supports", "formalizes", "assumes"].includes(e.kind)) expect(lineage.has(e.to)).toBe(true);
    for (const id of lineage) expect(reach(scoped, top).has(id)).toBe(true);
    expect(lineage.has(top)).toBe(false);
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

  it("chooses the largest smaller size at which the whole title fits, else clamps at 11px", () => {
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
    } else expect(fit.size).toBe(11);
    expect(fitTitle(words(60, 200), 176, 124, 0.52, "card")).toMatchObject({ size: 11, fits: false });
  });

  it("breaks a Lean name only between its pieces, down to 11px", () => {
    const lean = { pieces: [{ w: 240, gap: 0 }, { w: 1020, gap: 0 }, { w: 300, gap: 0 }] };
    // The longest piece (1020 at 100px) must fit across: 112px at 11px.
    expect(fitTitle(lean, 196, 112, 0.55, "lean").fits).toBe(false);
    expect(fitTitle(lean, 196, 112, 0.7, "lean")).toMatchObject({ fits: true });
  });
});

describe("every tile shows words, and the plate", async () => {
  const { DENSE_H, DENSE_MIN_K, DENSE_TILE, DENSE_W, MAX_K, MIN_TEXT, STEPS_MIN_K, TILE, fitPlate, fitTitle, floorK, keptPieces, repFor, shortTitle, titlePieces, wrapLines, STATEMENT_W } = await import("../src/map/canvas/representation");
  const { shortTitle: tileTitle } = await import("../src/compare/useAlignment");
  const words = (n: number, w = 40) => ({ pieces: Array.from({ length: n }, (_, i) => ({ w, gap: i ? 25 : 0 })) });
  const measured = (text: string, lean = false) => ({
    pieces: titlePieces(text, lean).map((p, i) => ({ text: p.text, w: p.text.length * 52, gap: i && p.space ? 25 : 0 })),
    ellipsis: 60,
  });

  it("gives every record of the edition words at 11px or more at every scale the camera allows", () => {
    expect(floorK(true, false)).toBeCloseTo(11 / 13);
    for (const node of graph.nodes.values()) {
      const lean = node.kind === "declaration";
      for (const text of [node.label, tileTitle(node.id, node.label)]) {
        const t = measured(text, lean);
        for (let k = DENSE_MIN_K; k <= MAX_K + 1e-9; k += 0.05) {
          const fit = fitTitle(t, DENSE_W, DENSE_H, k, lean ? "lean" : "card", DENSE_TILE);
          expect(fit.size).toBeGreaterThanOrEqual(MIN_TEXT);
          if (!fit.fits) expect(fit.short?.replace("…", "").length).toBeGreaterThan(0);
        }
        for (let k = STEPS_MIN_K; k <= 0.8; k += 0.05) {
          const fit = fitTitle(t, 176, 104, k, lean ? "lean" : "card", TILE);
          expect(fit.size).toBeGreaterThanOrEqual(MIN_TEXT);
          if (!fit.fits) expect(fit.short?.replace("…", "").length).toBeGreaterThan(0);
        }
      }
    }
  });

  it("holds two lines in a dense tile at the floor", () => {
    expect(fitTitle(words(4, 300), DENSE_W, DENSE_H, DENSE_MIN_K, "card", DENSE_TILE)).toMatchObject({ fits: true, lines: 2 });
  });

  it("draws tiles at every scale in the dense layout", () => {
    expect(repFor(1.8, true)).toBe("compact");
    expect(repFor(1.8)).toBe("card");
  });

  it("cuts one word wider than a line rather than leaving the tile empty", () => {
    const fit = fitTitle(measured("Unbreakablelongwordthatcannotfitonanylineofatile"), DENSE_W, DENSE_H, DENSE_MIN_K, "card", DENSE_TILE);
    expect(fit).toMatchObject({ fits: false, kept: 0 });
    expect(fit.short).toMatch(/^Unbreak.*…$/);
    expect(wrapLines(words(3, 900), 11, 90)).toBe(Infinity);
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
  const draw = async () => {
    const restore = stub();
    cleanup = restore;
    const ref = createRef<MapViewHandle>();
    const onSelect = vi.fn();
    act(() => root.render(<ArgumentTree ref={ref} graph={graph} goal={goal} insets={insets} persist={false} onSelect={onSelect} onTrace={() => {}} />));
    await act(() => new Promise((r) => setTimeout(r, 1300)));
    return { ref, onSelect };
  };
  let cleanup: (() => void) | null = null;
  afterEach(() => {
    cleanup?.();
    cleanup = null;
  });

  it("pans when scrolled, and zooms about the pointer on a pinch or with Ctrl or Cmd", async () => {
    const { ref } = await draw();
    const scene = () => ref.current!.getScene().camera;
    const before = scene();
    const tree = container.querySelector(".tree")!;
    const wheel = (init: WheelEventInit) => act(() => tree.dispatchEvent(new WheelEvent("wheel", { bubbles: true, cancelable: true, clientX: 300, clientY: 200, ...init })));
    wheel({ deltaY: 120 });
    expect(scene().k).toBe(before.k);
    expect(scene().y).toBeCloseTo(before.y - 120, 0);
    wheel({ deltaX: 60 });
    expect(scene().x).toBeCloseTo(before.x - 60, 0);
    const k = scene().k;
    wheel({ deltaY: -40, ctrlKey: true });
    expect(scene().k).toBeGreaterThan(k);
    const zoomed = scene().k;
    wheel({ deltaY: 40, metaKey: true });
    expect(scene().k).toBeLessThan(zoomed);
  });

  it("selects on a click without unfolding or zooming, and hover draws nothing new", async () => {
    const { ref, onSelect } = await draw();
    const before = container.querySelectorAll(".card").length;
    const k = ref.current!.getScene().camera.k;
    const el = container.querySelector<HTMLElement>(".card:not(.card--root) .card__open")!;
    const card = el.closest<HTMLElement>(".card")!;
    act(() => card.dispatchEvent(new PointerEvent("pointerenter", { bubbles: false })));
    await act(() => new Promise((r) => setTimeout(r, 420)));
    expect(container.querySelectorAll(".card").length).toBe(before);
    act(() => el.click());
    expect(onSelect).toHaveBeenCalledWith(card.dataset.record);
    await act(() => new Promise((r) => setTimeout(r, 60)));
    expect(container.querySelectorAll(".card").length).toBe(before);
    expect(ref.current!.getScene().camera.k).toBe(k);
  });
});


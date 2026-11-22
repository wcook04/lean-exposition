import { afterEach, describe, expect, it, vi } from "vitest";
import { renderTex } from "../src/reader/math";
import { formulaExtent, joinBracketedPieces, markWideMaths, scaleToFit } from "../src/reader/page/PaperBody";

afterEach(() => vi.unstubAllGlobals());

describe("display fitting notifications", () => {
  it("does not create a resize observer for prose without display maths", () => {
    const observer = vi.fn();
    vi.stubGlobal("ResizeObserver", observer);
    markWideMaths(document.createElement("div"))();
    expect(observer).not.toHaveBeenCalled();
  });

  /** Frames run when the test says so: the fitter reads sizes once a frame, after the frame's changes. */
  const frames = () => {
    const queue: FrameRequestCallback[] = [];
    vi.stubGlobal("requestAnimationFrame", (cb: FrameRequestCallback) => queue.push(cb));
    vi.stubGlobal("cancelAnimationFrame", () => {});
    return () => { while (queue.length) queue.shift()!(0); };
  };

  it("avoids DOM writes on duplicate, height-only and scroll notifications, and refits a changed width", () => {
    const flush = frames();
    let resize: ResizeObserverCallback | undefined;
    vi.stubGlobal("ResizeObserver", class {
      constructor(callback: ResizeObserverCallback) { resize = callback; }
      observe() {} disconnect() {}
    });
    const root = document.createElement("div");
    root.innerHTML = '<div class="math-display"><span class="katex-display"><span class="katex"><span class="katex-html"><span class="katex-base">x = y</span></span></span></span></div>';
    const box = root.firstElementChild as HTMLElement;
    const math = box.querySelector<HTMLElement>(".katex")!;
    let width = 300;
    Object.defineProperty(box, "clientWidth", { get: () => width });
    Object.defineProperty(box, "scrollWidth", { get: () => width });
    Object.defineProperty(math, "scrollWidth", { get: () => 320 });
    const stop = markWideMaths(root);
    const changes = new MutationObserver(() => {});
    changes.observe(root, { attributes: true, subtree: true, childList: true });
    const notify = () => {
      resize!([{
        target: box, contentRect: box.getBoundingClientRect(),
        borderBoxSize: [], contentBoxSize: [], devicePixelContentBoxSize: [],
      }], {} as ResizeObserver);
      flush();
    };
    notify();
    box.dispatchEvent(new Event("scroll"));
    notify();
    expect(changes.takeRecords()).toHaveLength(0);
    expect(box.dataset.fit).toBe("scaled");
    width = 600;
    notify();
    expect(changes.takeRecords().length).toBeGreaterThan(0);
    expect(box.dataset.fit).toBeUndefined();
    expect(math.style.fontSize).toBe("");
    changes.disconnect();
    stop();
  });

  it("keeps its decision when a width flips straight back (a scroll bar its own fit brought and took away)", () => {
    const flush = frames();
    let resize: ResizeObserverCallback | undefined;
    vi.stubGlobal("ResizeObserver", class {
      constructor(callback: ResizeObserverCallback) { resize = callback; }
      observe() {} disconnect() {}
    });
    const root = document.createElement("div");
    root.innerHTML = '<div class="math-display"><span class="katex-display"><span class="katex"><span class="katex-html"><span class="katex-base">x = y</span></span></span></span></div>';
    const box = root.firstElementChild as HTMLElement;
    const math = box.querySelector<HTMLElement>(".katex")!;
    let width = 350;
    Object.defineProperty(box, "clientWidth", { get: () => width });
    Object.defineProperty(box, "scrollWidth", { get: () => width });
    Object.defineProperty(math, "scrollWidth", { get: () => 360 });
    const stop = markWideMaths(root);
    const notify = () => {
      resize!([{ target: box, contentRect: box.getBoundingClientRect(), borderBoxSize: [], contentBoxSize: [], devicePixelContentBoxSize: [] }], {} as ResizeObserver);
      flush();
    };
    notify();
    expect(box.dataset.fit).toBe("scaled");
    // The column gains a scroll bar and narrows, then loses it: the second width is the first again.
    width = 380;
    notify();
    expect(box.dataset.fit).toBeUndefined();
    const changes = new MutationObserver(() => {});
    changes.observe(root, { attributes: true, subtree: true, childList: true });
    width = 350;
    notify();
    width = 380;
    notify();
    expect(changes.takeRecords()).toHaveLength(0);
    changes.disconnect();
    stop();
  });

  it("fits a display reached before the fonts arrive once they have, with their widths", async () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
    let ready!: () => void;
    const previous = Object.getOwnPropertyDescriptor(document, "fonts");
    Object.defineProperty(document, "fonts", { configurable: true, value: {
      status: "loading", ready: new Promise<void>((resolve) => { ready = resolve; }),
    } });
    const root = document.createElement("div");
    root.innerHTML = '<div class="math-display"><span class="katex-display"><span class="katex"><span class="katex-html"><span class="katex-base">x = y</span></span></span></span></div>';
    const box = root.firstElementChild as HTMLElement;
    let formulaWidth = 320;
    Object.defineProperty(box, "clientWidth", { get: () => 300 });
    Object.defineProperty(box, "scrollWidth", { get: () => 300 });
    Object.defineProperty(box.querySelector(".katex"), "scrollWidth", { get: () => formulaWidth });
    const stop = markWideMaths(root);
    try {
      // Nothing is fitted in a fallback font: the display waits for KaTeX's fonts.
      expect(box.dataset.fit).toBeUndefined();
      formulaWidth = 600;
      ready();
      await Promise.resolve();
      // No broken form (the formula has no TeX to break): it shrinks to fit and offers Expand.
      expect(box.dataset.fit).toBe("squeezed");
    } finally {
      stop();
      if (previous) Object.defineProperty(document, "fonts", previous);
      else Reflect.deleteProperty(document, "fonts");
    }
  });
});

// KaTeX's output for "A = B (0 ≤ t_1 < t_2 < 1)." in outline: one piece after each relation sign.
function display(): HTMLElement {
  const math = document.createElement("span");
  math.className = "katex";
  math.innerHTML =
    '<span class="katex-html">' +
    '<span class="katex-base">A =</span>' +
    '<span class="katex-base">B <span class="mopen">(</span>0 ≤</span>' +
    '<span class="katex-base">t1 &lt;</span>' +
    '<span class="katex-base">t2 &lt; 1<span class="mclose">)</span>.</span>' +
    "</span>";
  return math;
}

describe("a breaking display", () => {
  it("keeps a bracketed condition in one piece and leaves the text unchanged", () => {
    const math = display();
    const before = math.textContent;
    joinBracketedPieces(math);
    const pieces = Array.from(math.querySelectorAll(".katex-base")).map((p) => p.textContent);
    expect(pieces).toEqual(["A =", "B (0 ≤t1 <t2 < 1)."]);
    expect(math.textContent).toBe(before);
  });

  it("runs once per formula", () => {
    const math = display();
    joinBracketedPieces(math);
    joinBracketedPieces(math);
    expect(math.querySelectorAll(".katex-base")).toHaveLength(2);
  });

  it("leaves balanced brackets inside a piece alone", () => {
    const math = document.createElement("span");
    math.innerHTML =
      '<span class="katex-html"><span class="katex-base">f<span class="mopen">(</span>x<span class="mclose">)</span> =</span><span class="katex-base">y</span></span>';
    joinBracketedPieces(math);
    expect(math.querySelectorAll(".katex-base")).toHaveLength(2);
  });
});

// A numbered display at 1440px: formula and number fit the 680px column, but KaTeX's 2px strut past
// the number's edge (.vlist-s) made the box report scrollWidth 682, and the display offered to scroll.
describe("a numbered display that fits", () => {
  const rect = (left: number, width: number) => ({ left, right: left + width, width, top: 0, bottom: 20, height: 20, x: left, y: 0 }) as DOMRect;
  function numbered(formula: number, column: number, scrollWidth: number): HTMLElement {
    const root = document.createElement("div");
    root.innerHTML =
      '<div class="math-display"><span class="katex-display"><span class="katex"><span class="katex-html">' +
      '<span class="katex-base">u(t) = v</span><span class="katex-tag"><span class="vlist-t vlist-t2">(1.2)</span></span>' +
      "</span></span></span></div>";
    const box = root.firstElementChild as HTMLElement;
    const tag = box.querySelector<HTMLElement>(".katex-tag")!;
    const piece = box.querySelector<HTMLElement>(".katex-base")!;
    Object.defineProperty(box, "clientWidth", { get: () => column });
    Object.defineProperty(box, "scrollWidth", { get: () => scrollWidth });
    box.getBoundingClientRect = () => rect(0, column);
    piece.getBoundingClientRect = () => rect((column - formula) / 2, formula);
    tag.getBoundingClientRect = () => rect(column - 38.88, 38.88);
    return root;
  }

  it("measures the formula and its number, not the strut past the number's edge", () => {
    const box = numbered(460.47, 680, 682).firstElementChild as HTMLElement;
    expect(formulaExtent(box)).toBe(680);
  });

  it("is left as it is, with no Expand row", () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
    const root = numbered(460.47, 680, 682);
    const box = root.firstElementChild as HTMLElement;
    const stop = markWideMaths(root);
    expect(box.dataset.fit).toBeUndefined();
    expect(root.querySelector(".math-cue")).toBeNull();
    stop();
  });

  it("shrinks a formula with no break to fit, and offers Expand but never a scroll control", () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
    const root = document.createElement("div");
    root.innerHTML = '<div class="math-display"><span class="katex-display"><span class="katex"><span class="katex-html"><span class="katex-base"><span class="mtable">x</span></span></span></span></span></div>';
    const box = root.firstElementChild as HTMLElement;
    const piece = box.querySelector<HTMLElement>(".katex-base")!;
    Object.defineProperty(box, "clientWidth", { get: () => 300 });
    Object.defineProperty(box, "scrollWidth", { get: () => 420 });
    Object.defineProperty(box.querySelector(".katex"), "scrollWidth", { get: () => 420 });
    box.getBoundingClientRect = () => rect(0, 300);
    piece.getBoundingClientRect = () => rect(0, 420);
    const stop = markWideMaths(root);
    expect(box.dataset.fit).toBe("squeezed");
    expect(root.querySelector(".math-cue__expand")).not.toBeNull();
    expect(root.querySelector(".math-cue__scroll")).toBeNull();
    stop();
  });
});

describe("the scale a display fits at", () => {
  it("leaves a fitting formula whole, centred beside its number when there is room", () => {
    expect(scaleToFit({ formula: 400, tag: 40 }, 680)).toEqual({ scale: 1, start: false });
    expect(scaleToFit({ formula: 600, tag: 0 }, 680)).toEqual({ scale: 1, start: false });
  });

  it("sets a numbered formula flush left, then shrinks it, keeping its number at full size", () => {
    expect(scaleToFit({ formula: 600, tag: 40 }, 680)).toEqual({ scale: 1, start: true });
    const { scale, start } = scaleToFit({ formula: 700, tag: 40 }, 680);
    expect(start).toBe(true);
    expect(scale).toBeCloseTo((680 - 40 - 16) / 700);
  });

  it("shrinks an unnumbered formula by the share it overflows", () => {
    expect(scaleToFit({ formula: 750, tag: 0 }, 680).scale).toBeCloseTo(680 / 750);
  });
});

describe("a display with one equation number", () => {
  it("sets the number beside the formula as its own element, and hides KaTeX's", () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
    const root = document.createElement("div");
    root.innerHTML = `<div class="math-display">${renderTex("\\begin{equation} a = b, \\qquad c = d. \\tag{1.2}\\end{equation}", true).html}</div>`;
    const box = root.firstElementChild as HTMLElement;
    Object.defineProperty(box, "clientWidth", { get: () => 600 });
    const stop = markWideMaths(root);
    expect(box.dataset.number).toBe("");
    expect(box.querySelector(":scope > .math-number")?.textContent).toBe("(1.2)");
    expect(box.querySelectorAll(":scope > .katex-display")).toHaveLength(1);
    stop();
  });

  it("leaves a display with several numbers to KaTeX", () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
    const root = document.createElement("div");
    root.innerHTML = `<div class="math-display">${renderTex("\\begin{gather} a = b \\tag{1} \\\\ c = d \\tag{2} \\end{gather}", true).html}</div>`;
    const box = root.firstElementChild as HTMLElement;
    Object.defineProperty(box, "clientWidth", { get: () => 600 });
    const stop = markWideMaths(root);
    expect(box.dataset.number).toBeUndefined();
    expect(box.querySelector(".math-number")).toBeNull();
    stop();
  });
});

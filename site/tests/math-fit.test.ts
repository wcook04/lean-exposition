import { afterEach, describe, expect, it, vi } from "vitest";
import { groupRelationRuns, joinBracketedPieces, markWideMaths } from "../src/reader/page/PaperBody";

afterEach(() => vi.unstubAllGlobals());

describe("display fitting notifications", () => {
  it("does not create a resize observer for prose without display maths", () => {
    const observer = vi.fn();
    vi.stubGlobal("ResizeObserver", observer);
    markWideMaths(document.createElement("div"))();
    expect(observer).not.toHaveBeenCalled();
  });

  it("avoids DOM writes on duplicate, height-only and scroll notifications, and refits a changed width", () => {
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
    Object.defineProperty(math, "scrollWidth", { get: () => 360 });
    const stop = markWideMaths(root);
    const changes = new MutationObserver(() => {});
    changes.observe(root, { attributes: true, subtree: true, childList: true });
    const notify = () => resize!([{
      target: box, contentRect: box.getBoundingClientRect(),
      borderBoxSize: [], contentBoxSize: [], devicePixelContentBoxSize: [],
    }], {} as ResizeObserver);
    notify();
    box.dispatchEvent(new Event("scroll"));
    notify();
    expect(changes.takeRecords()).toHaveLength(0);
    expect(box.dataset.fit).toBe("scaled");
    width = 600;
    notify();
    expect(changes.takeRecords().length).toBeGreaterThan(0);
    expect(box.dataset.fit).toBeUndefined();
    expect(box.style.fontSize).toBe("");
    changes.disconnect();
    stop();
  });

  it("remeasures formula geometry when pending fonts finish loading at the same width", async () => {
    vi.stubGlobal("ResizeObserver", class { observe() {} disconnect() {} });
    let ready!: () => void;
    const previous = Object.getOwnPropertyDescriptor(document, "fonts");
    Object.defineProperty(document, "fonts", { configurable: true, value: {
      status: "loading", ready: new Promise<void>((resolve) => { ready = resolve; }),
    } });
    const root = document.createElement("div");
    root.innerHTML = '<div class="math-display"><span class="katex-display"><span class="katex"><span class="katex-html"><span class="katex-base">x = y</span></span></span></span></div>';
    const box = root.firstElementChild as HTMLElement;
    let formulaWidth = 360;
    Object.defineProperty(box, "clientWidth", { get: () => 300 });
    Object.defineProperty(box, "scrollWidth", { get: () => 300 });
    Object.defineProperty(box.querySelector(".katex"), "scrollWidth", { get: () => formulaWidth });
    const stop = markWideMaths(root);
    try {
      expect(box.dataset.fit).toBe("scaled");
      formulaWidth = 600;
      ready();
      await Promise.resolve();
      expect(box.dataset.fit).toBe("wrap");
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

// KaTeX's pieces for "P(…) ≥ 1 − Ke^{−n/K},  n ≥ 1.": one after each relation sign and each operator.
function bound(): HTMLElement {
  const math = document.createElement("span");
  math.className = "katex";
  const piece = (text: string, last: "mrel" | "mbin" | "mord") =>
    `<span class="katex-base"><span class="katex-strut"></span><span class="mord">${text}</span><span class="${last}">${last === "mord" ? "." : last === "mrel" ? "≥" : "−"}</span>${last === "mord" ? "" : '<span class="mspace"></span>'}</span>`;
  math.innerHTML = `<span class="katex-html">${piece("P(…)", "mrel")}${piece("1", "mbin")}${piece("Ke, n", "mrel")}${piece("1", "mord")}</span>`;
  return math;
}

describe("a breaking display's runs", () => {
  const runs = (math: HTMLElement) =>
    Array.from(math.querySelector(".katex-html")!.children).map((c) => (c.classList.contains("math-seg") ? Array.from(c.children).map((p) => p.textContent) : [c.textContent]));

  it("breaks only after a relation sign: an operator's pieces stay with what follows them", () => {
    const math = bound();
    const before = math.textContent;
    groupRelationRuns(math, 0);
    expect(runs(math)).toEqual([["P(…)≥"], ["1−", "Ke, n≥"], ["1."]]);
    expect(math.textContent).toBe(before);
  });

  it("keeps a short last run with the run before it, and runs once per formula", () => {
    const math = bound();
    // The pieces' widths on the page, 0.8em of an 18px display: "P(…) ≥" 480px, "1 −" 26px, "Ke, n ≥" 118px, "1." 12px.
    const widths = [480, 26, 118, 12];
    math.querySelectorAll<HTMLElement>(".katex-base").forEach((p, i) => {
      p.getBoundingClientRect = () => ({ width: widths[i] }) as DOMRect;
    });
    groupRelationRuns(math, 54);
    groupRelationRuns(math, 54);
    expect(runs(math)).toEqual([["P(…)≥"], ["1−", "Ke, n≥", "1."]]);
  });

  it("never joins across an explicit line break", () => {
    const math = bound();
    const html = math.querySelector(".katex-html")!;
    const br = document.createElement("span");
    br.className = "katex-newline";
    html.children[2].before(br);
    groupRelationRuns(math, 0);
    expect(Array.from(html.children).map((c) => c.className)).toEqual(["katex-base", "katex-base", "katex-newline", "katex-base", "katex-base"]);
  });
});

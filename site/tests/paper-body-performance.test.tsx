import { act, createRef } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { prepareDocument } from "../src/reader/engine";
import { PaperBody, type BodyHandle } from "../src/reader/page/PaperBody";
import { graphFixture } from "./fixtures";

const graph = graphFixture();
const total = 128;
let root: Root;
let container: HTMLDivElement;
let frames: Map<number, FrameRequestCallback>;
let observers: { callback: ResizeObserverCallback; targets: Set<Element> }[];
let extraHeight: number;
let partReads: number;

beforeEach(() => {
  (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
  vi.useFakeTimers();
  frames = new Map();
  observers = [];
  extraHeight = 0;
  partReads = 0;
  let nextFrame = 0;
  vi.stubGlobal("requestAnimationFrame", (callback: FrameRequestCallback) => {
    frames.set(++nextFrame, callback);
    return nextFrame;
  });
  vi.stubGlobal("cancelAnimationFrame", (id: number) => frames.delete(id));
  vi.stubGlobal("scrollY", 5050);
  vi.stubGlobal("scrollBy", vi.fn((options: ScrollToOptions) => vi.stubGlobal("scrollY", window.scrollY + (options.top ?? 0))));
  vi.stubGlobal("IntersectionObserver", class { observe() {} unobserve() {} disconnect() {} });
  vi.stubGlobal("ResizeObserver", class {
    targets = new Set<Element>();
    constructor(callback: ResizeObserverCallback) { observers.push({ callback, targets: this.targets }); }
    observe(target: Element) { this.targets.add(target); }
    unobserve(target: Element) { this.targets.delete(target); }
    disconnect() { this.targets.clear(); }
  });
  vi.spyOn(HTMLElement.prototype, "getBoundingClientRect").mockImplementation(function (this: HTMLElement) {
    const part = this.closest<HTMLElement>("[data-part]");
    const index = Number(part?.dataset.part ?? 0);
    if (this.hasAttribute("data-part")) partReads++;
    const top = index * 100 + (index > 0 ? extraHeight : 0) - window.scrollY;
    const height = 100 + (index === 0 ? extraHeight : 0);
    return { top, bottom: top + height, left: 0, right: 680, width: 680, height, x: 0, y: top, toJSON() {} };
  });
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});

afterEach(() => {
  act(() => root.unmount());
  container.remove();
  vi.useRealTimers();
  vi.restoreAllMocks();
  vi.unstubAllGlobals();
});

function show() {
  const text = "A paragraph.\n\n";
  const length = new TextEncoder().encode(text).length;
  const doc = prepareDocument({
    stage: "long", bytes: new TextEncoder().encode(text.repeat(total)),
    parts: Array.from({ length: total }, (_, i) => ({ kind: "unmapped_text", span: { start_byte: i * length, end_byte: (i + 1) * length } })),
    documentPath: "long/reasoning-record.md", documentPaths: {},
  });
  const ref = createRef<BodyHandle>();
  act(() => root.render(<PaperBody ref={ref} stage="long" doc={doc} structures={{}} graph={graph}
    initial={doc.parts.map((p) => p.index)} topInset={56} inspected={null} onInspect={() => {}} onSameTopic={() => {}} />));
  const observer = observers.find((o) => [...o.targets].some((el) => el.hasAttribute("data-part")))!;
  const notify = (targets: Element[]) => act(() => observer.callback(targets.map((target) => ({ target }) as ResizeObserverEntry), {} as ResizeObserver));
  notify([...observer.targets]);
  return { ref, observer, notify };
}

function flushFrames() {
  const pending = [...frames.values()];
  frames.clear();
  act(() => pending.forEach((callback) => callback(0)));
}

describe("paper layout work", () => {
  it("compensates a changed part above the reader without remeasuring every other part", () => {
    const { observer, notify } = show();
    partReads = 0;
    extraHeight = 25;
    notify([[...observer.targets][0]]);
    expect(window.scrollBy).toHaveBeenCalledWith({ top: 25, behavior: "instant" });
    expect(partReads).toBeLessThan(20);
  });

  it("keeps a deliberately held target fixed when earlier text changes height", () => {
    const { ref, observer, notify } = show();
    const target = container.querySelector<HTMLElement>('[data-part="70"] .part__text p')!;
    act(() => ref.current!.hold(target));
    const before = target.getBoundingClientRect().top;
    extraHeight = 45;
    partReads = 0;
    notify([[...observer.targets][0]]);
    expect(target.getBoundingClientRect().top).toBe(before);
    expect(partReads).toBeLessThan(20);
  });

  it("keeps the prior anchor when a scroll arrives before a changed height is observed", () => {
    const { observer, notify } = show();
    extraHeight = 30;
    act(() => window.dispatchEvent(new Event("scroll")));
    flushFrames();
    notify([[...observer.targets][0]]);
    expect(window.scrollBy).toHaveBeenCalledWith({ top: 30, behavior: "instant" });
  });

  it("measures one anchor for a burst of scroll events and cancels pending work on unmount", () => {
    show();
    partReads = 0;
    act(() => { for (let i = 0; i < 8; i++) window.dispatchEvent(new Event("scroll")); });
    expect(partReads).toBe(0);
    expect(frames.size).toBe(1);
    flushFrames();
    expect(partReads).toBeGreaterThan(0);
    expect(partReads).toBeLessThan(total + 20);
    act(() => window.dispatchEvent(new Event("scroll")));
    expect(frames.size).toBe(1);
    act(() => root.render(null));
    expect(frames.size).toBe(0);
  });
});

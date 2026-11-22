// The statements on the page: attributes, never state, and the reading line's choice.
import { beforeEach, describe, expect, it, vi } from "vitest";
import type { TieIndex } from "../src/api/lean";
import type { PreparedPart } from "../src/reader/engine";
import { isBlock, Statements } from "../src/reader/page/statements";
import { tieModel } from "../src/reader/ties";

const index: TieIndex = {
  meaning: "",
  segments: [[0, 5, [0]], [6, 9, [0, 1]], [100, 110, [1]]],
  ties: [
    { record: "a", role: "statement", lean: true, name: "A", module: "M", lines: [1, 2], anchor: "p", at: "b0-9" },
    { record: "b", role: "mention", lean: false, name: null, module: null, lines: null, anchor: "q", at: "b6-110" },
  ],
  passages: [],
};
const parts = [
  { span: { start: 0, end: 50 } },
  { span: { start: 50, end: 200 } },
] as PreparedPart[];

function section(part: number, spans: [segment: number, top: number, bottom: number][]) {
  const el = document.createElement("section");
  el.dataset.part = String(part);
  const text = document.createElement("div");
  text.className = "part__text";
  for (const [segment, top, bottom] of spans) {
    const span = document.createElement("span");
    span.className = "tie";
    span.dataset.t = String(segment);
    vi.spyOn(span, "getBoundingClientRect").mockReturnValue({ top, bottom, height: bottom - top, left: 0, right: 10, width: 10, x: 0, y: top, toJSON() {} });
    text.append(span);
  }
  el.append(text);
  return el;
}

describe("statements on the page", () => {
  let statements: Statements;
  let first: HTMLElement;
  beforeEach(() => {
    vi.stubGlobal("IntersectionObserver", class { observe() {} unobserve() {} disconnect() {} });
    vi.stubGlobal("ResizeObserver", class { observe() {} unobserve() {} disconnect() {} });
    statements = new Statements(tieModel(index), parts);
    first = section(0, [[0, 100, 120], [1, 130, 150]]);
    statements.adopt(0, first);
    statements.adopt(1, section(1, [[2, 400, 420]]));
  });

  it("lights every span of a statement, across parts, and puts out the last", () => {
    statements.light("on", 1);
    expect(first.querySelectorAll("[data-on]").length).toBe(1);
    statements.light("on", 0);
    expect(first.querySelectorAll("[data-on]").length).toBe(2);
    statements.light("on", null);
    expect(first.querySelectorAll("[data-on]").length).toBe(0);
  });

  it("keeps one tab stop, with a role and a name, which moves and stays between statements", () => {
    statements.light("on", 0);
    const stop = () => first.querySelector<HTMLElement>("[tabindex='0']")!;
    expect(first.querySelectorAll("[tabindex='0']").length).toBe(1);
    expect(stop().getAttribute("role")).toBe("button");
    expect(stop().getAttribute("aria-label")).toBeTruthy();
    statements.light("on", null);
    expect(first.querySelectorAll("[tabindex='0']").length).toBe(1);
    statements.light("on", 1);
    expect(stop().dataset.t).toBe("1");
    expect(first.querySelectorAll("[role='button']").length).toBe(1);
  });

  it("puts a note under a statement's last words, and takes it away", () => {
    const off = statements.noteUnder(0, "Not in the Lean.");
    expect(first.querySelector(".tie-note")).toBeNull();
    const para = document.createElement("p");
    first.querySelector(".part__text")!.append(para);
    para.append(...first.querySelectorAll(".tie"));
    const remove = statements.noteUnder(0, "Not in the Lean.");
    expect(para.nextElementSibling?.textContent).toBe("Not in the Lean.");
    remove();
    off();
    expect(first.querySelector(".tie-note")).toBeNull();
  });

  it("keeps what is lit when a part renders after it was lit", () => {
    statements.light("pin", 1);
    const late = section(1, [[2, 400, 420]]);
    statements.adopt(1, late);
    expect(late.querySelector("[data-pin]")).not.toBeNull();
  });

  it("colours existing margin ticks from their own linked words", () => {
    const model = tieModel({ ...index, ties: [{ ...index.ties[0], tone: 0 }, { ...index.ties[1], tone: 7 }] });
    const reader = new Statements(model, parts);
    const page = section(0, [[0, 100, 120], [1, 130, 150], [2, 155, 175]]);
    reader.adopt(0, page);
    (reader as unknown as { drawTicks(part: number): void }).drawTicks(0);
    const topics = (selector: string) => [...page.querySelectorAll<HTMLElement>(selector)].map(el => el.dataset.tone);
    expect(topics(".tick")).toEqual(["0", "0", "7"]);
    expect(topics(".tick")).toEqual(topics(".tie"));
    reader.dispose();
  });

  it("marks a selection across paragraphs as a block, with one margin rule, and clears both", () => {
    const text = first.querySelector(".part__text")!;
    const [a, b] = [...first.querySelectorAll<HTMLElement>(".tie")];
    const p1 = document.createElement("p");
    const p2 = document.createElement("p");
    p1.append(a);
    p2.append(b);
    text.append(p1, p2);
    (statements as unknown as { drawTicks(part: number): void }).drawTicks(0);
    statements.light("pin", 0);
    expect(first.querySelectorAll("[data-pin-block]").length).toBe(2);
    const run = first.querySelectorAll<HTMLElement>(".part__ticks .tick-run");
    expect(run.length).toBe(1);
    expect([run[0].style.top, run[0].style.height]).toEqual(["100px", "50px"]);
    statements.light("pin", null);
    expect(first.querySelectorAll("[data-pin-block]").length).toBe(0);
    expect(first.querySelectorAll(".tick-run").length).toBe(0);
  });

  it("tells a block from a phrase", () => {
    const para = (words: string) => Object.assign(document.createElement("p"), { textContent: words });
    const long = para("x".repeat(300));
    const phrase = document.createElement("span");
    phrase.textContent = "x".repeat(40);
    long.append(phrase);
    expect(isBlock([phrase])).toBe(false);
    const whole = para("");
    const all = document.createElement("span");
    all.textContent = "x".repeat(300);
    whole.append(all);
    expect(isBlock([all])).toBe(true);
    const display = document.createElement("span");
    display.className = "math-display";
    display.textContent = "y".repeat(300);
    expect(isBlock([display])).toBe(false);
    expect(isBlock([phrase, display])).toBe(true);
  });

  it("picks the words under the line, else the nearest, the one above winning a near tie", () => {
    expect(statements.atLine(110, 50, 0)).toBe(0);
    expect(statements.atLine(125, 50, 0)).toBe(0);
    expect(statements.atLine(160, 50, 0)).toBe(1);
    expect(statements.atLine(300, 50, 0)).toBeNull();
  });

  it("says where a statement stands, and that a statement in an unrendered part stands nowhere", () => {
    expect(statements.extent(0)).toEqual({ top: 100, bottom: 150 });
    statements.adopt(0, null);
    expect(statements.extent(0)).toBeNull();
  });

  it("finds a statement's part from its first segment", () => {
    expect(statements.partOf(0)).toBe(0);
    expect(new Statements(tieModel({ ...index, ties: index.ties, segments: [[100, 110, [0]]] }), parts).partOf(0)).toBe(1);
  });
});

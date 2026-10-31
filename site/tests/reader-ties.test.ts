// Ties reach the text without changing it: with every segment marked, a paper's
// HTML is the same HTML with spans in it, on all three papers.
import { describe, expect, it } from "vitest";
import type { TieIndex } from "../src/api/lean";
import type { PaperStructure, Stage } from "../src/api/types";
import { prepareDocument } from "../src/reader/engine";
import { markSource, passageTopics, sameWords, segmentsIn, statementFor, statementOf, stepFrom, tieCounts, tieModel, wrapTies, openMark, closeMark } from "../src/reader/ties";
import { documentFixture, fixture, structureFixture } from "./fixtures";

const PATHS: Record<Stage, string> = { long: "long/reasoning-record.md", short: "short/paper.md", expository: "expository/main.md" };
const STAGES: Stage[] = ["short", "expository", "long"];

function prepare(stage: Stage, ties?: TieIndex) {
  const structure: PaperStructure = structureFixture(stage);
  const anchors = new Map(structure.paper.passages.map((p) => [p.ref, p.anchor]));
  return prepareDocument({
    stage,
    bytes: documentFixture(stage),
    parts: structure.paper.document_parts.map((p) => ({ kind: p.kind, span: p.span, passageAnchor: p.passage_ref ? anchors.get(p.passage_ref) : undefined })),
    documentPath: PATHS[stage],
    documentPaths: PATHS,
    ties: ties?.segments,
  });
}

/** One paragraph's source through the whole pipeline, with these byte slices marked. */
function render(source: string, slices: [string, string][]) {
  const bytes = new TextEncoder().encode(source);
  const at = (text: string, from = 0) => {
    const i = source.indexOf(text, from);
    expect(i).toBeGreaterThanOrEqual(0);
    return new TextEncoder().encode(source.slice(0, i)).length;
  };
  const ties = slices.map(([from, to], n): [number, number, number[]] => {
    const start = at(from);
    return [start, at(to, source.indexOf(from)) + new TextEncoder().encode(to).length, [n]];
  });
  const plain = prepareDocument({ stage: "short", bytes, documentPath: "short/paper.md", documentPaths: PATHS }).render(0).html;
  const tied = prepareDocument({ stage: "short", bytes, documentPath: "short/paper.md", documentPaths: PATHS, ties }).render(0).html;
  const box = document.createElement("div");
  box.innerHTML = tied;
  return { box, plain, tied };
}

function unwrap(html: string): string {
  const box = document.createElement("div");
  box.innerHTML = html;
  box.querySelectorAll("span.tie:not(.math-display)").forEach((span) => span.replaceWith(...span.childNodes));
  box.querySelectorAll(".tie").forEach((el) => {
    el.classList.remove("tie");
    el.removeAttribute("data-t");
  });
  box.normalize();
  return box.innerHTML;
}

const text = (box: Element, t: number) => [...box.querySelectorAll(`[data-t="${t}"]`)].map((el) => el.textContent).join("");

describe("a segment in the rendered text", () => {
  it("wraps plain words and leaves the rest", () => {
    const { box } = render("One two three four.\n", [["two", "three"]]);
    expect(text(box, 0)).toBe("two three");
    expect(box.textContent).toContain("One two three four.");
  });

  it("starts before a bold label and keeps it a run-in label", () => {
    const { box, plain } = render("**Theorem 1.** Every word here counts.\n", [["**Theorem", "word"]]);
    expect(plain).toContain("run-in");
    expect(box.querySelector("p")!.className).toContain("run-in");
    expect(box.querySelector("p strong .tie")!.textContent).toBe("Theorem 1.");
    expect(text(box, 0)).toBe("Theorem 1. Every word");
  });

  it("holds inline math whole", () => {
    const { box } = render("Let $x_1<y$ be real, and $z$ too.\n", [["$x_1", "real"]]);
    expect(box.querySelector(".tie .katex")).not.toBeNull();
    expect(box.querySelector(".tie")!.textContent).toContain("be real");
    expect(box.textContent).not.toMatch(/[\uE000-\uF8FF]/);
  });

  it("keeps a closing formula joined to its full stop", () => {
    const { box, plain, tied } = render("Then $x$. And more.\n", [["Then", "$x$"]]);
    expect(plain).toContain("math-nobreak");
    expect(unwrap(tied)).toBe(plain);
    expect(box.querySelector(".math-nobreak .tie")).not.toBeNull();
  });

  it("marks a display itself, so the code that fits it still finds it", () => {
    const { box, plain, tied } = render("Before.\n\n$$a=b \\tag{1}$$\n\nAfter.\n", [["$$a", "}$$"]]);
    const display = box.querySelector(".math-display")!;
    expect(display.classList.contains("tie")).toBe(true);
    expect(display.querySelector(":scope > .katex-display")).not.toBeNull();
    expect(unwrap(tied)).toBe(plain);
  });

  it("marks a display set inside a paragraph, and the words around it", () => {
    const { box, plain, tied } = render("Take\n$$a=b$$\nso on.\n", [["Take", "so on"]]);
    expect(box.querySelector(".math-display")!.classList.contains("tie")).toBe(true);
    expect(text(box, 0)).toContain("Take");
    expect(text(box, 0)).toContain("so on");
    expect(unwrap(tied)).toBe(plain);
  });

  it("spans several sentences and inline nesting", () => {
    const { box, plain, tied } = render("One. *Two and **three** then.* Four. Five.\n", [["Two", "Four."]]);
    expect(text(box, 0)).toBe("Two and three then. Four.");
    expect(box.querySelectorAll("[data-t='0']").length).toBeGreaterThan(1);
    expect(unwrap(tied)).toBe(plain);
  });

  it("keeps quotes and dashes as they were", () => {
    const { plain, tied } = render('He said "yes" -- and left.\n', [['"yes"', "left"]]);
    expect(plain).toContain("“yes”");
    expect(unwrap(tied)).toBe(plain);
  });

  it("keeps block syntax first on its line", () => {
    for (const source of ["## A heading here\n", "- item one\n- item two\n", "1. first item\n", "> quoted words\n", "| a | b |\n|---|---|\n| c | d |\n"]) {
      const word = source.replace(/^[#\-\d.>| ]+/, "").split(/\s/)[0];
      const { plain, tied } = render(source, [[source.slice(0, 1), word]]);
      expect(unwrap(tied)).toBe(plain);
    }
  });

  it("gives overlapping ranges a span each and drops nothing", () => {
    const html = wrapTies(`a ${openMark(0)}b ${openMark(1)}c${closeMark(0)} d${closeMark(1)} e`, document);
    const box = document.createElement("div");
    box.innerHTML = html;
    expect(box.textContent).toBe("a b c d e");
    expect(box.querySelectorAll(".tie").length).toBeGreaterThanOrEqual(2);
  });

  it("ends an unclosed mark with the part, and never leaves a mark behind", () => {
    const html = wrapTies(`<p>a ${openMark(4)}b</p>`, document);
    expect(html).toBe('<p>a <span class="tie" data-t="4">b</span></p>');
  });

  it("does not wrap the white space between blocks", () => {
    const html = wrapTies(`<ul>${openMark(2)}\n<li>x</li>\n${closeMark(2)}</ul>`, document);
    expect(html).toBe('<ul>\n<li><span class="tie" data-t="2">x</span></li>\n</ul>');
  });

  it("marks bytes, so words after a non-ASCII character land exactly", () => {
    const source = "Erdős wrote “this”.";
    const bytes = new TextEncoder().encode(source);
    const start = new TextEncoder().encode("Erdős wrote “").length;
    const out = markSource(bytes, { start: 0, end: bytes.length }, [{ segment: 0, start, end: start + 4 }], (b) => new TextDecoder().decode(b));
    expect(out).toBe(`Erdős wrote “${openMark(0)}this${closeMark(0)}”.`);
  });
});

describe.each(STAGES)("the %s paper with all its ties", (stage) => {
  const index = fixture<TieIndex>(`ties-${stage}.json`);
  const plain = prepare(stage);
  const tied = prepare(stage, index);

  it("is the same paper: same parts, ids, headings and lines", () => {
    expect(tied.parts).toEqual(plain.parts);
    expect([...tied.anchorIndex]).toEqual([...plain.anchorIndex]);
    expect(tied.mathCount).toBe(plain.mathCount);
  });

  it("renders the same HTML with spans in it, and no mark", () => {
    plain.parts.forEach((part) => {
      const a = plain.render(part.index);
      const b = tied.render(part.index);
      expect(b.mathErrors).toEqual(a.mathErrors);
      expect(b.html).not.toMatch(/[\uE100-\uF4FF]/);
      const box = document.createElement("div");
      box.innerHTML = a.html;
      const got = unwrap(b.html);
      const want = box.innerHTML;
      if (got !== want) {
        let i = 0;
        while (got[i] === want[i]) i++;
        expect.fail(`part ${part.index} differs at ${i}:\n got  ${got.slice(Math.max(0, i - 60), i + 120)}\n want ${want.slice(Math.max(0, i - 60), i + 120)}`);
      }
    });
  });

  it("marks every segment outside the figures", () => {
    const html = plain.parts.map((part) => tied.render(part.index).html).join("");
    const seen = new Set([...html.matchAll(/data-t="(\d+)"/g)].map((m) => Number(m[1])));
    const missing = index.segments.map((_, i) => i).filter((i) => !seen.has(i));
    expect(missing).toEqual([]);
  });

  it("gives every statement a place in reading order", () => {
    const model = tieModel(index);
    expect(model.order.length).toBe(index.ties.length);
    expect(new Set(model.stops.map((t) => model.segmentsOf[t][0])).size).toBe(model.stops.length);
    const starts = model.order.map((t) => index.segments[model.segmentsOf[t][0]][0]);
    expect(starts).toEqual([...starts].sort((a, b) => a - b));
  });
});

describe("the model", () => {
  const index: TieIndex = {
    meaning: "",
    segments: [[0, 5, [0]], [6, 9, [0, 1]], [10, 12, [1]]],
    ties: [
      { record: "a", role: "statement", lean: true, name: "A", module: "M", lines: [1, 2], anchor: "p", at: "b0-9" },
      { record: "b", role: "mention", lean: false, name: null, module: null, lines: null, anchor: "p", at: "b6-12" },
    ],
    passages: [[0, 20, ["a", "b", "c"], "p"]],
  };
  const model = tieModel(index);

  it("takes a segment's first tie, and names the others on the same words", () => {
    expect(statementOf(model, 1)).toBe(0);
    expect(statementOf(model, 2)).toBe(1);
    expect(sameWords(model, 1)).toEqual([0]);
    expect(sameWords(model, 0)).toEqual([]);
  });

  it("finds a record's statement by slice, else by Lean", () => {
    expect(statementFor(model, "b", "b6-12")).toBe(1);
    expect(statementFor(model, "a")).toBe(0);
    expect(statementFor(model, "nothing")).toBeNull();
  });

  it("steps in reading order and stops at the ends", () => {
    expect(stepFrom(model, null, 1)).toBe(0);
    expect(stepFrom(model, 0, 1)).toBe(1);
    expect(stepFrom(model, 1, 1)).toBeNull();
    expect(stepFrom(model, null, -1)).toBe(1);
    expect(stepFrom(model, 1, -1)).toBe(0);
  });

  it("stops once where several statements open on the same words, so a step always moves", () => {
    const same = tieModel({ ...index, segments: [[0, 5, [0, 1]], [6, 9, [1]]] });
    expect(same.stops).toEqual([0]);
    expect(same.place).toEqual([0, 0]);
  });

  it("answers for a paragraph with no slice from its passage", () => {
    expect(passageTopics(model, "p")).toEqual(["a", "b", "c"]);
    expect(passageTopics(model, null)).toEqual([]);
  });

  it("counts a section's statements with those of its subsections", () => {
    const counts = tieCounts(model, [{ id: "s1", start: 0, parent: null }, { id: "s1.1", start: 3, parent: "s1" }, { id: "s2", start: 8, parent: null }]);
    expect(counts.get("s1")).toEqual({ lean: 1, all: 2 });
    expect(counts.get("s1.1")).toEqual({ lean: 0, all: 1 });
    expect(counts.get("s2")).toEqual({ lean: 0, all: 0 });
  });

  it("copes with an edition that has no index", () => {
    const empty = tieModel(null);
    expect(empty.order).toEqual([]);
    expect(segmentsIn([], 0, 10)).toEqual([]);
  });
});

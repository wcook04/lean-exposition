// The reading trail, slices of a paper, and the Lean page.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture, structureFixture } from "./fixtures";
import { bestSlice, linkedCount, paperTrail, passageRecords, resolveAt, statementHref, trailAt, trailWords, type OutlineEntry } from "../src/reader/page/model";
import type { Alignment, AlignedStatement } from "../src/api/lean";

const expository = structureFixture("expository");
const ordered = [...expository.paper.passages].sort((a, b) => a.block_span.start_byte - b.block_span.start_byte).filter((p) => passageRecords(p).length);

describe("the reading trail", () => {
  const trail = paperTrail(expository);
  const total = new Set(ordered.flatMap(passageRecords)).size;

  it("has passed nothing before the first passage", () => {
    expect(trailAt(trail, null, [])).toMatchObject({ seen: 0, total });
    expect(trailAt(trail, null, []).passed.size).toBe(0);
  });

  it("splits records into passed, current and ahead by the paper's order", () => {
    const mid = ordered[Math.floor(ordered.length / 2)];
    const current = passageRecords(mid);
    const place = trailAt(trail, mid.anchor, current);
    const before = new Set(ordered.slice(0, ordered.indexOf(mid)).flatMap(passageRecords));
    for (const id of current) expect(place.passed.has(id)).toBe(false);
    for (const id of before) if (!current.includes(id)) expect(place.passed.has(id)).toBe(true);
    expect(place.seen).toBe(new Set([...before, ...current]).size);
  });

  it("never falls back as the reader moves forward, and reaches every record at the end", () => {
    let last = 0;
    for (const p of ordered) {
      const { seen } = trailAt(trail, p.anchor, passageRecords(p));
      expect(seen).toBeGreaterThanOrEqual(last);
      last = seen;
    }
    expect(last).toBe(total);
  });

  it("says where the reader is in words", () => {
    const entry = (title: string, part: number, parent: string | null = null): OutlineEntry => ({ id: title, title, level: parent ? 3 : 2, part, parent });
    const outline = [entry("Abstract", 0), entry("1 One", 2), entry("2 Two", 6), entry("2.1 Inner", 7, "2 Two"), entry("3 Three", 9), entry("References", 12)];
    const place = { seen: 14, total: 37 };
    expect(trailWords(outline, 7, place)).toBe("Section 2 of 3. You have reached 14 of this paper’s 37 steps.");
    expect(trailWords(outline, 0, place)).toBe("Abstract. You have reached 14 of this paper’s 37 steps.");
    expect(trailWords(outline, 13, place)).toBe("References. You have reached 14 of this paper’s 37 steps.");
    expect(trailWords([], 0, { seen: 0, total: 0 })).toBe("");
  });
});

describe("a passage's quiet line", () => {
  it("counts what the Linked passages chooser offers", () => {
    const structures = { expository, long: structureFixture("long"), short: structureFixture("short") };
    expect(linkedCount(structures, { stage: "expository", anchor: ordered[0].anchor })).toBeGreaterThanOrEqual(0);
    expect(linkedCount({}, { stage: "expository", anchor: "nothing" })).toBe(0);
  });
});

const slice = (over: Partial<AlignedStatement>): AlignedStatement => ({ paper: "short", role: "mention", markdown: "", start_byte: 0, end_byte: 1, at: "b0-1", lean: [], lean_source: "record", anchor: null, section: "", heading_id: null, ...over });

describe("a slice of a paper", () => {
  const aligned = (statements: AlignedStatement[]): Alignment => ({ dictionary: [], records: { r: { short: "x", lean: [], statements } } });
  const doc = { lineOfByte: (byte: number) => Math.floor(byte / 10) + 1 };

  it("takes the best slice by role, then position, in this paper only", () => {
    const a = aligned([
      slice({ role: "mention", start_byte: 1 }),
      slice({ role: "derivation", start_byte: 90 }),
      slice({ role: "derivation", start_byte: 70 }),
      slice({ role: "statement", paper: "long", start_byte: 5 }),
    ]);
    expect(bestSlice(a, "short", "r")?.start_byte).toBe(70);
    expect(bestSlice(a, "expository", "r")).toBeNull();
    expect(bestSlice(null, "short", "r")).toBeNull();
  });

  it("orders roles as statement, definition, derivation, explanation, example, mention", () => {
    const roles: AlignedStatement["role"][] = ["mention", "example", "explanation", "derivation", "definition", "statement"];
    const a = aligned(roles.map((role) => slice({ role })));
    expect(bestSlice(a, "short", "r")?.role).toBe("statement");
    expect(bestSlice(aligned(roles.slice(0, 4).map((role) => slice({ role }))), "short", "r")?.role).toBe("derivation");
  });

  it("builds a link in context and resolves it to source lines", () => {
    const href = statementHref(slice({ paper: "short", anchor: "main-result", start_byte: 100, end_byte: 251 }));
    expect(href).toContain("/read/short/?l=b100-251#main-result");
    expect(resolveAt(doc, "b100-251")).toEqual({ start: 11, end: 26 });
    expect(resolveAt(doc, "120")).toEqual({ start: 120, end: 120 });
    expect(resolveAt(doc, "120-134")).toEqual({ start: 120, end: 134 });
    expect(resolveAt(doc, "x")).toBeNull();
  });
});

// ---- The Lean page ----------------------------------------------------------------------

const graph = graphFixture();
const record = [...graph.nodes.keys()][3];
vi.mock("../src/app/data", () => ({ useEdition: () => ({ graph }) }));
vi.mock("../src/app/router", async (load) => {
  const real = await load<typeof import("../src/app/router")>();
  return { ...real, navigate: vi.fn() };
});
vi.mock("../src/panels/RecordPanel", () => ({ RecordPanel: ({ nodeId }: { nodeId: string }) => <p data-testid="panel">{nodeId}</p> }));
vi.mock("../src/lean/lazy", () => ({ LazyLeanBlock: ({ name, lines }: { name: string; lines?: number[] }) => <p data-testid="lean">{`${name} ${lines?.join("-")}`}</p> }));

describe("the Lean page", async () => {
  const { LeanDock, clampDock, DOCK_MAX, DOCK_MIN, plainName, readDockShare, readKeepLean, recordOfDecl, saveDockShare, saveKeepLean } = await import("../src/reader/page/RecordDock");
  const { tieModel } = await import("../src/reader/ties");
  type Open = import("../src/reader/page/RecordDock").LeanOpen;
  let root: Root;
  let container: HTMLDivElement;

  const lean = { name: "OAI.a.full_support", module: "OAI.a", line: 4, end_line: 9, relation: "states" as const, note: "", lines: [5, 6] as [number, number] };
  const other = { ...lean, name: "OAI.b.full_support" };
  const alignment: Alignment = {
    dictionary: [],
    records: {
      [record]: { short: "x", lean: [lean], statements: [slice({ at: "b0-5", role: "statement", section: "2 The result", lean: [lean, other], lean_source: "statement" }), slice({ paper: "long", at: "b9-12", role: "statement", section: "5.3 The step" })] },
      none: { short: "y", lean: [], statements: [slice({ at: "b6-9" })] },
    },
  };
  const ties = tieModel({
    meaning: "",
    segments: [[0, 5, [0]], [6, 9, [1]]],
    ties: [
      { record, role: "statement", lean: true, name: lean.name, module: lean.module, lines: lean.lines, anchor: "p", at: "b0-5" },
      { record: "none", role: "mention", lean: false, name: null, module: null, lines: null, anchor: "p", at: "b6-9" },
    ],
    passages: [[0, 20, [record], "p"]],
  });

  beforeEach(() => {
    (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
    localStorage.clear();
    container = document.createElement("div");
    document.body.appendChild(container);
    root = createRoot(container);
  });
  afterEach(() => {
    act(() => root.unmount());
    container.remove();
  });

  const show = (open: Partial<Open>, props: Record<string, unknown> = {}) =>
    act(() => root.render(<LeanDock open={{ via: "pin", record: null, tie: null, decl: null, ...open }} ties={ties} stage="short" alignment={alignment} onRelease={() => {}} onPick={() => {}} onPoint={() => {}} passageHref={() => "#"} {...props} />));
  const button = (words: string) => [...container.querySelectorAll("button")].find((b) => b.textContent === words);

  it("heads the Lean with the step in plain words and its raw name small beside it", () => {
    show({ record, tie: 0 });
    expect(container.querySelector(".lean-page__title")!.textContent).not.toContain("OAI.");
    expect(container.querySelector(".lean-page__raw")!.textContent).toBe("full_support");
    expect(container.querySelector("[data-testid=lean]")!.textContent).toBe("OAI.a.full_support 5-6");
  });

  it("says where each paper states the step, each a link with the exact landing, then Compare", () => {
    show({ record, tie: 0 });
    const crumbs = [...container.querySelectorAll<HTMLAnchorElement>(".lean-crumbs a")];
    expect(crumbs.map((a) => a.textContent)).toEqual(["Short paper §2", "Long record §5.3, same step", "Compare"]);
    expect(crumbs[1].getAttribute("href")).toContain("l=");
    expect(crumbs[2].getAttribute("href")).toContain("/compare");
  });

  it("sends a reader to the slice that names the open declaration, not just the step's best", async () => {
    const { paperTarget } = await import("../src/reader/page/model");
    const named = slice({ paper: "long", at: "b50-60", role: "explanation", lean: [lean], lean_source: "statement", start_byte: 50 });
    const wide = slice({ paper: "long", at: "b9-12", role: "statement", lean: [lean], lean_source: "record", start_byte: 9 });
    const elsewhere = slice({ paper: "expository", at: "b70-80", role: "mention", lean: [lean], lean_source: "statement", start_byte: 70 });
    const data: Alignment = { dictionary: [], records: { a: { short: "", lean: [lean], statements: [wide, named] }, b: { short: "", lean: [], statements: [elsewhere] } } };
    expect(paperTarget(data, "long", "a", lean.name)).toMatchObject({ record: "a", near: false, slice: { at: "b50-60" } });
    expect(paperTarget(data, "expository", "a", lean.name)).toMatchObject({ record: "b", near: false, slice: { at: "b70-80" } });
    const other: Alignment = { ...data, records: { a: data.records.a } };
    expect(paperTarget(other, "long", "a", "OAI.not.named")).toMatchObject({ near: true, slice: { at: "b9-12" } });
    expect(paperTarget(other, "expository", "a", lean.name)).toBeNull();
    expect(paperTarget(other, "long", "a", null)).toMatchObject({ near: false, slice: { at: "b9-12" } });
  });

  it("offers each declaration of a step, one at a time", () => {
    show({ record, tie: 0 });
    expect(container.querySelectorAll(".lean-page__rows button").length).toBe(2);
  });

  it("says plainly when a step has no Lean", () => {
    show({ record: "none", tie: 1 });
    expect(container.textContent).toContain("No Lean linked.");
  });

  it("closes with one control, and opens the whole record only from a pin", () => {
    const onRelease = vi.fn();
    show({ record, tie: 0 }, { onRelease });
    act(() => button("Close")!.click());
    expect(onRelease).toHaveBeenCalledOnce();
    act(() => button("Everything on this step")!.click());
    expect(container.querySelector("[data-testid=panel]")!.textContent).toBe(record);
    show({ via: "follow", record, tie: 0 });
    expect(button("Everything on this step")).toBeUndefined();
    expect(button("Follow the text")).toBeUndefined();
  });

  it("walks to a declaration by name, in words where it can", () => {
    show({ record, decl: "OAI.a.full_support" });
    expect(container.querySelector("[data-testid=lean]")!.textContent).toContain("OAI.a.full_support");
    expect(recordOfDecl(alignment, "OAI.a.full_support")).toBe(record);
    expect(plainName(alignment, "OAI.c.some_helper_lemma")).toBe("some helper lemma");
    expect(plainName({ ...alignment, names: { "OAI.c.x": "The heat identity" } } as Alignment, "OAI.c.x")).toBe("The heat identity");
  });

  it("kept open, says it is following, and answers between statements", () => {
    show({ via: "follow", record, tie: 0 });
    expect(container.querySelector(".lean-page__state")!.textContent).toBe("Changes as you scroll");
    show({ via: "follow", topics: [record] });
    expect(container.textContent).toContain("Steps in this passage");
    expect(container.querySelectorAll(".lean-page__topics button").length).toBe(1);
    show({ via: "follow" });
    expect(container.textContent).toContain("Nothing in this stretch of the paper is tied to the Lean.");
  });

  it("lets a preview stand in", () => {
    show({ record, tie: 0 }, { slot: <p data-testid="slot">Theorem 1</p> });
    expect(container.querySelector("[data-testid=slot]")).not.toBeNull();
    expect(container.querySelector("[data-testid=lean]")).toBeNull();
  });

  it("has the whole pane until a reader draws the graph back, and remembers", () => {
    expect(clampDock(0.1)).toBe(DOCK_MIN);
    expect(clampDock(1.2)).toBe(DOCK_MAX);
    expect(readDockShare()).toBe(1);
    saveDockShare(0.61);
    expect(readDockShare()).toBe(0.61);
    expect(readDockShare(true)).toBe(1);
  });

  it("following a statement with no Lean says so, even where its step has Lean elsewhere", () => {
    const told = tieModel({
      meaning: "",
      segments: [[0, 5, [0]]],
      ties: [{ record, role: "statement", lean: false, note: "Illustration only.", name: null, module: null, lines: null, anchor: "p", at: "b0-5" }],
      passages: [],
    });
    show({ via: "follow", record, tie: 0 }, { ties: told });
    expect(container.querySelector("[data-testid=lean]")).toBeNull();
    expect(container.textContent).toContain("Illustration only.");
  });

  it("is in Graph mode unless this reader chose Lean", () => {
    expect(readKeepLean()).toBe(false);
    saveKeepLean(true);
    expect(readKeepLean()).toBe(true);
    saveKeepLean(false);
    expect(readKeepLean()).toBe(false);
  });
});

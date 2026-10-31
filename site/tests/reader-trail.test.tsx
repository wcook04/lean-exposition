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
    expect(trailWords(outline, 7, place)).toBe("§2 of 3, 14 of 37 records so far");
    expect(trailWords(outline, 0, place)).toBe("Abstract, 14 of 37 records so far");
    expect(trailWords(outline, 13, place)).toBe("References, 14 of 37 records so far");
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
    expect(href).toContain("/read/short?l=b100-251#main-result");
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
  const { LeanDock, clampDock, DOCK_MAX, DOCK_MIN, readDockShare, readPanes, savePanes } = await import("../src/reader/page/RecordDock");
  const { tieModel } = await import("../src/reader/ties");
  type View = import("../src/reader/page/RecordDock").LeanView;
  let root: Root;
  let container: HTMLDivElement;

  const lean = { name: "OAI.a.full", module: "OAI.a", line: 4, end_line: 9, relation: "states" as const, note: "", lines: [5, 6] as [number, number] };
  const other = { ...lean, name: "OAI.b.full" };
  const alignment: Alignment = {
    dictionary: [],
    records: {
      [record]: { short: "x", lean: [lean], statements: [slice({ at: "b0-5", lean: [lean, other], lean_source: "statement" }), slice({ paper: "long", at: "b9-12", role: "statement", section: "2.3 The step" })] },
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

  const show = (view: View, props: Record<string, unknown> = {}) =>
    act(() => root.render(<LeanDock view={view} ties={ties} stage="short" alignment={alignment} onRelease={() => {}} onPick={() => {}} onPoint={() => {}} passageHref={() => "#"} {...props} />));
  const state = () => container.querySelector(".lean-page__state")!;

  it("shows a statement's own Lean at its exact lines, and says it is following", () => {
    show({ via: "follow", kind: "statement", tie: 0, record });
    expect(state().textContent).toContain("Following the text");
    expect(container.querySelector("[data-testid=lean]")!.textContent).toBe("OAI.a.full 5-6");
    expect(container.querySelectorAll(".lean-page__rows button").length).toBe(2);
    expect(container.querySelector(".lean-page__places a")!.textContent).toContain("Long paper".slice(0, 4));
  });

  it("says plainly when a step has no Lean, and offers the papers it has", () => {
    show({ via: "pin", kind: "statement", tie: 1, record: "none" });
    expect(container.textContent).toContain("No Lean declaration is linked to this step.");
    expect(container.textContent).toContain("No paper states it apart from here.");
  });

  it("says which state it is in, and pinned has a way out", () => {
    const onRelease = vi.fn();
    show({ via: "pin", kind: "statement", tie: 0, record }, { onRelease });
    expect(state().textContent).toContain("Pinned:");
    const release = [...container.querySelectorAll("button")].find((b) => b.textContent === "Follow the text")!;
    act(() => release.click());
    expect(onRelease).toHaveBeenCalledOnce();
  });

  it("opens the whole record only from a pin", () => {
    show({ via: "follow", kind: "statement", tie: 0, record });
    expect([...container.querySelectorAll("button")].some((b) => b.textContent === "Whole record")).toBe(false);
    show({ via: "pin", kind: "statement", tie: 0, record });
    act(() => [...container.querySelectorAll("button")].find((b) => b.textContent === "Whole record")!.click());
    expect(container.querySelector("[data-testid=panel]")!.textContent).toBe(record);
  });

  it("answers for a passage with no exact statement, and for a stretch with no ties", () => {
    show({ via: "follow", kind: "passage", anchor: "p", records: [record] });
    expect(container.textContent).toContain("This passage discusses");
    expect(container.querySelectorAll(".lean-page__topics button").length).toBe(1);
    show({ via: "follow", kind: "nothing" });
    expect(container.textContent).toContain("Nothing in this stretch of the paper is tied to the Lean.");
  });

  it("lets a preview stand in, and says nothing has moved", () => {
    show({ via: "follow", kind: "statement", tie: 0, record }, { slot: <p data-testid="slot">Theorem 1</p> });
    expect(container.querySelector("[data-testid=slot]")).not.toBeNull();
    expect(container.querySelector("[data-testid=lean]")).toBeNull();
  });

  it("keeps the split within its limits and gives the Lean more of a short page", () => {
    expect(clampDock(0.1)).toBe(DOCK_MIN);
    expect(clampDock(0.95)).toBe(DOCK_MAX);
    expect(readDockShare(800)).toBe(0.5);
    expect(readDockShare(600)).toBeGreaterThan(0.5);
    localStorage.setItem("lx-reader-sheet", "0.41");
    expect(readDockShare(600)).toBe(0.41);
  });

  it("remembers which side is closed, and never remembers both closed", () => {
    savePanes({ graph: false, lean: true });
    expect(readPanes({ graph: true, lean: true })).toEqual({ graph: false, lean: true });
    savePanes({ graph: false, lean: false });
    expect(readPanes({ graph: true, lean: true })).toEqual({ graph: true, lean: true });
  });
});

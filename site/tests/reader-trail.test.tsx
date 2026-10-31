// The reading trail, the passage bar's helpers and the docked record sheet.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { graphFixture, structureFixture } from "./fixtures";
import { bestSlice, chipSplit, chipTitle, leanRecord, linkedCount, paperTrail, passageRecords, recordsCovering, resolveAt, sliceRows, statementHref, trailAt, trailWords, type OutlineEntry } from "../src/reader/page/model";
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

describe("the passage bar", () => {
  it("names the first few records and counts the rest, never saying 'and 1 more'", () => {
    expect(chipSplit(["a", "b", "c"])).toEqual({ shown: ["a", "b", "c"], more: 0 });
    expect(chipSplit(["a", "b", "c", "d"])).toEqual({ shown: ["a", "b", "c", "d"], more: 0 });
    expect(chipSplit(["a", "b", "c", "d", "e"])).toEqual({ shown: ["a", "b", "c"], more: 2 });
  });

  it("cuts a long title after a whole word", () => {
    expect(chipTitle("Short title")).toBe("Short title");
    expect(chipTitle("Monotonicity of the derivative across every interval of the parameter")).toBe("Monotonicity of the derivative across…");
  });

  it("marks Lean from the graph and from the alignment's count", () => {
    const graph = { nodes: new Map([["a", { kind: "claim" }], ["b", { kind: "claim" }], ["d", { kind: "declaration" }]]), out: new Map([["b", [{ kind: "formalizes" }]]]) };
    expect(leanRecord(["a"], graph, () => false)).toBeNull();
    expect(leanRecord(["a", "b"], graph, () => false)).toBe("b");
    expect(leanRecord(["a", "d"], graph, () => false)).toBe("d");
    expect(leanRecord(["a"], graph, (id) => id === "a")).toBe("a");
  });

  it("counts what the Linked passages chooser offers", () => {
    const structures = { expository, long: structureFixture("long"), short: structureFixture("short") };
    expect(linkedCount(structures, { stage: "expository", anchor: ordered[0].anchor })).toBeGreaterThanOrEqual(0);
    expect(linkedCount({}, { stage: "expository", anchor: "nothing" })).toBe(0);
  });
});

describe("a slice of a paper", () => {
  const slice = (over: Partial<AlignedStatement>): AlignedStatement => ({ paper: "short", role: "mention", markdown: "", start_byte: 0, end_byte: 1, anchor: null, section: "", heading_id: null, ...over });
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

  it("follows the records whose slices cover a block, and lets a statement outrank a mention", () => {
    const rows = sliceRows({ dictionary: [], records: {
      a: { short: "", lean: [], statements: [slice({ role: "statement", start_byte: 100, end_byte: 200 })] },
      b: { short: "", lean: [], statements: [slice({ role: "mention", start_byte: 100, end_byte: 500 })] },
    } }, doc, "short");
    expect(recordsCovering(rows, { start: 12, end: 13 })).toEqual(["a"]);
    expect(recordsCovering(rows, { start: 30, end: 31 })).toEqual(["b"]);
    expect(recordsCovering(rows, { start: 90, end: 91 })).toEqual([]);
  });
});

// ---- The docked sheet -------------------------------------------------------------------

const graph = graphFixture();
const record = [...graph.nodes.keys()][3];
vi.mock("../src/app/data", () => ({ useEdition: () => ({ graph }) }));
vi.mock("../src/app/router", async (load) => {
  const real = await load<typeof import("../src/app/router")>();
  return { ...real, navigate: vi.fn() };
});
vi.mock("../src/panels/RecordPanel", () => ({ RecordPanel: ({ nodeId }: { nodeId: string }) => <p data-testid="panel">{nodeId}</p> }));

describe("RecordDock", async () => {
  const { RecordDock, clampDock, DOCK_MAX, DOCK_MIN, readDockShare } = await import("../src/reader/page/RecordDock");
  let root: Root;
  let container: HTMLDivElement;

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

  const show = (props: Record<string, unknown> = {}) =>
    act(() => root.render(<RecordDock record={{ id: record }} onClose={() => {}} onSelect={() => {}} passageHref={() => "#"} {...props} />));

  it("mounts the record's panel with a close control, a handle and a link to the full map", () => {
    const onClose = vi.fn();
    show({ onClose });
    expect(container.querySelector("[data-testid=panel]")!.textContent).toBe(record);
    expect(container.querySelector<HTMLAnchorElement>(".record-dock__map")!.getAttribute("href")).toContain(`/map?n=${encodeURIComponent(record)}`);
    act(() => container.querySelector<HTMLButtonElement>(".record-dock__close")!.click());
    expect(onClose).toHaveBeenCalledOnce();
    expect(container.querySelector("[role=separator]")).not.toBeNull();
  });

  it("has neither handle nor close in a modal, which has its own", () => {
    show({ docked: false });
    expect(container.querySelector("[role=separator]")).toBeNull();
    expect(container.querySelector(".record-dock__close")).toBeNull();
  });

  it("resizes from the keyboard within its limits and remembers the height", () => {
    const onShare = vi.fn();
    show({ share: 0.5, onShare });
    const handle = container.querySelector<HTMLElement>("[role=separator]")!;
    act(() => void handle.dispatchEvent(new KeyboardEvent("keydown", { key: "ArrowUp", bubbles: true })));
    expect(onShare).toHaveBeenCalledWith(0.55);
    expect(readDockShare()).toBe(0.55);
    expect(clampDock(2)).toBe(DOCK_MAX);
    expect(clampDock(0)).toBe(DOCK_MIN);
  });
});

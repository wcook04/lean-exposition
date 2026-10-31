// The reviewed reference tables and the marks that turn them into links. Every row is
// checked against the paper's bytes and against the page it renders.

import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { Stage } from "../src/api/types";
import { prepareDocument, type PreparedDocument } from "../src/reader/engine";
import {
  equationId,
  labelIds,
  leanModuleOf,
  linkReferences,
  MARK_CAPACITY,
  markReferences,
  opensInPlace,
  recordOver,
  referenceIndex,
  refView,
  stripRefMarks,
  type RefRow,
  type ReferenceTable,
} from "../src/reader/references";
import { documentFixture, structureFixture } from "./fixtures";

const here = path.dirname(fileURLToPath(import.meta.url));
const STAGES: Stage[] = ["short", "long", "expository"];
const PATHS: Record<Stage, string> = { long: "long/reasoning-record.md", short: "short/paper.md", expository: "expository/main.md" };

interface Row extends RefRow {
  before: string;
  reason?: string;
}
type File = Omit<ReferenceTable, "references"> & { references: Row[] };

const file = (stage: Stage): File => JSON.parse(readFileSync(path.join(here, `../../examples/qaoa-sk/alignment/references-${stage}.json`), "utf8"));
const paper = (stage: Stage) => new Uint8Array(readFileSync(path.join(here, `../../papers/qaoa-sk/${PATHS[stage]}`)));
const liveTable = (stage: Stage): ReferenceTable => {
  const table = file(stage);
  return { ...table, references: table.references.filter((row) => (row.kind as string) !== "plain") };
};

function prepare(stage: Stage, withTable = true): PreparedDocument {
  const structure = structureFixture(stage);
  const passages = new Map(structure.paper.passages.map((p) => [p.ref, p.anchor]));
  return prepareDocument({
    stage,
    bytes: documentFixture(stage),
    parts: structure.paper.document_parts.map((p) => ({ kind: p.kind, span: p.span, passageAnchor: p.passage_ref ? passages.get(p.passage_ref) : undefined })),
    documentPath: PATHS[stage],
    documentPaths: PATHS,
    referenceTable: withTable ? liveTable(stage) : null,
  });
}

const dom = (doc: PreparedDocument) => {
  const box = document.createElement("div");
  box.innerHTML = doc.renderAll().map((part) => part.html).join("");
  return box;
};

/** Outside KaTeX: the reader's words of an element. */
const words = (el: Element) => {
  const copy = el.cloneNode(true) as Element;
  copy.querySelectorAll(".katex-mathml").forEach((node) => node.remove());
  return (copy.textContent ?? "").replace(/\s+/g, " ").trim();
};

const NUMBER = String.raw`(?:[A-Z]\.)?\d+(?:\.\d+)*`;
const CANDIDATE = new RegExp(
  String.raw`\b(?:Theorems?|Lemmas?|Propositions?|Corollar(?:y|ies)|Assumptions?|Figures?)[\s~]+${NUMBER}|§§?\s?\d+(?:\.\d+)*|\bSections?[\s~]+\d+(?:\.\d+)*|\b[Aa]ppendix\b`,
  "g",
);

/** Bytes that hold no prose: comments, formulas, code, reference definitions and raw TeX. */
function blank(text: string): string {
  const spaces = (m: string) => m.replace(/[^\n]/g, " ");
  return text
    .replace(/<!--[\s\S]*?-->/g, spaces)
    .replace(/^\[[^\]\n]+\]:.*$/gm, spaces)
    .replace(/^(`{3,})[^\n]*\n[\s\S]*?^\1[ \t]*$/gm, spaces)
    .replace(/\\begin\{figure\*?\}[\s\S]*?\\end\{figure\*?\}/g, spaces)
    .replace(/\$\$[\s\S]*?\$\$/g, spaces)
    .replace(/(?<!\\)\$(?!\s)(?:[^$\\]|\\.)*?(?<![\s\\])\$(?!\d)/g, spaces);
}

describe.each(STAGES)("the table of the %s paper", (stage) => {
  const table = file(stage);
  const bytes = paper(stage);
  const decoder = new TextDecoder();
  const at = (start: number, end: number) => decoder.decode(bytes.subarray(start, end));

  it("was reviewed against these bytes", () => {
    expect(documentFixture(stage)).toEqual(bytes);
    for (const row of table.references) {
      expect(at(row.start_byte, row.end_byte), row.quote).toBe(row.quote);
      expect(at(Math.max(0, row.start_byte - 60), row.start_byte).endsWith(row.before), row.quote).toBe(true);
    }
  });

  it("has no two references over the same words", () => {
    table.references.reduce((previous, row) => {
      expect(row.start_byte, row.quote).toBeGreaterThanOrEqual(previous);
      return row.end_byte;
    }, 0);
  });

  it("lands each own reference on what it names", () => {
    for (const row of table.references) {
      const number = /\d+(?:\.\d+)*/.exec(row.quote)?.[0] ?? "";
      if (row.kind === "equation") {
        expect(row.target).toBe(`eq-${row.quote.slice(1, -1)}`);
        const target = table.targets[row.target!];
        expect(at(target.start_byte, target.end_byte)).toContain(`\\tag{${row.quote.slice(1, -1)}}`);
      } else if (row.kind === "label" && !row.quote.startsWith("[")) {
        const target = table.targets[row.target!];
        expect(target.label).toBe(row.quote);
        expect(at(target.start_byte, target.end_byte).startsWith(`**${row.quote}`)).toBe(true);
      } else if (row.kind === "section" && /\d/.test(row.quote) && !row.quote.startsWith("[")) {
        const target = table.targets[row.target!];
        expect(target.label, row.quote).toBe(`§${number}`);
        expect(target.title?.startsWith(number), row.quote).toBe(true);
      } else if (row.kind === "figure") {
        expect(table.targets[row.target!].label).toBe(row.quote);
      }
    }
  });

  it("gives every source an address, a name and a place in the list where the list has it", () => {
    const used = new Set(table.references.flatMap((row) => (row.source ? [row.source] : [])));
    for (const key of used) {
      const source = table.sources[key];
      expect(source?.name, key).toBeTruthy();
      expect(source.href).toMatch(/^https:\/\//);
      if (source.entry) expect(at(source.entry[0], source.entry[1]).length).toBeGreaterThan(20);
    }
  });

  it("leaves no candidate undecided", () => {
    const text = decoder.decode(bytes);
    const prose = blank(text);
    const covered = new Set<number>();
    const encoder = new TextEncoder();
    let byte = 0;
    let char = 0;
    const toChar = new Map<number, number>();
    for (const c of text) {
      toChar.set(byte, char);
      byte += encoder.encode(c).length;
      char += c.length;
    }
    toChar.set(byte, char);
    for (const row of table.references) {
      const end = toChar.get(row.end_byte)!;
      for (let i = toChar.get(row.start_byte)!; i < end; i++) covered.add(i);
    }
    // Links the table leaves to the paper's own companion links.
    const companion = [...text.matchAll(/\]\(\.\.\/[^)]*\)/g)].map((m) => m.index);
    const inCompanion = (i: number) => companion.some((close) => close > i && text.slice(i, close).length < 400 && !text.slice(i, close).includes("["));
    const missing = [...prose.matchAll(CANDIDATE)].filter((m) => !covered.has(m.index) && !inCompanion(m.index)).map((m) => text.slice(Math.max(0, m.index - 30), m.index + m[0].length + 10));
    expect(missing).toEqual([]);
  });

  it("never reads another manuscript's numbering as this paper's", () => {
    const rows = table.references.filter((row) => row.kind === "manuscript");
    for (const row of rows) expect(table.sources[row.source!].href, row.quote).not.toContain("lean-exposition");
  });
});

describe.each(STAGES)("the %s paper as rendered", (stage) => {
  const doc = prepare(stage);
  const box = dom(doc);
  const links = Array.from(box.querySelectorAll<HTMLAnchorElement>("a[data-ref]"));

  it("links every row once, around its own words", () => {
    const rows = doc.refs!.rows;
    expect(rows.length).toBeLessThanOrEqual(MARK_CAPACITY);
    expect(links.map((a) => Number(a.dataset.ref))).toEqual(rows.map((_, i) => i));
    for (const a of links) {
      const row = rows[Number(a.dataset.ref)];
      if (row.quote.startsWith("[")) continue;
      expect(words(a)).toBe(row.quote.replace(/\s+/g, " "));
    }
  });

  it("changes no word of the paper", () => {
    expect(words(box)).toBe(words(dom(prepare(stage, false))));
    expect(box.innerHTML).not.toMatch(/[-]/);
  });

  it("gives each target an element to land on", () => {
    for (const row of doc.refs!.rows) {
      if (row.kind === "manuscript" || row.kind === "citation" || row.kind === "other_paper") continue;
      expect(doc.anchorIndex.has(row.target!), row.target).toBe(true);
      expect(box.querySelector(`[id="${row.target}"]`), row.target).not.toBeNull();
    }
  });

  it("keeps the anchors it had", () => {
    const before = prepare(stage, false).anchorIndex;
    for (const [id, part] of before) expect(doc.anchorIndex.get(id), id).toBe(part);
  });
});

describe("the anchors", () => {
  it("names each labelled block and proof", () => {
    const short = prepare("short");
    const box = dom(short);
    for (const id of ["thm-1", "lem-2", "prop-3", "cor-4", "prop-5", "cor-6", "proof-thm-1", "proof-cor-4", "proof-cor-6"]) expect(box.querySelector(`p[id="${id}"]`), id).not.toBeNull();
    const long = dom(prepare("long"));
    for (const id of ["prop-2.1", "thm-5.1", "cor-10.2", "proof-prop-4.1", "proof-prop-6.2"]) expect(long.querySelector(`p[id="${id}"]`), id).not.toBeNull();
    expect(long.querySelector('[id="eq-4.1"]')).not.toBeNull();
    const expository = dom(prepare("expository"));
    for (const id of ["source-theorem", "strict-curvature-input", "fig-1", "fig-2", "question-1"]) expect(expository.querySelector(`[id="${id}"]`), id).not.toBeNull();
  });

  it("tells a proof which result it proves", () => {
    const id = labelIds();
    expect(id("Lemma 2 (constant-interval curvature; …).")).toBe("lem-2");
    expect(id("Proof of Theorem 1, assuming Lemma 2.")).toBe("proof-thm-1");
    expect(id("Proof.")).toBe("proof-lem-2");
    expect(id("Why the adjacent pairing is the energy.")).toBeNull();
    expect(id("Question 1: allowed changes.")).toBeNull();
  });

  it("numbers equations by their tag", () => {
    expect(equationId("x=1\\tag{4.1}")).toBe("eq-4.1");
    expect(equationId("x=1")).toBeNull();
  });
});

describe("marks", () => {
  const rows = [
    { start_byte: 3, end_byte: 10, quote: "Lemma 2", kind: "label", target: "lem-2" },
    { start_byte: 18, end_byte: 21, quote: "(5)", kind: "equation", target: "eq-5" },
  ] as RefRow[];
  const table = { paper: "short", targets: {}, sources: {}, references: rows } as ReferenceTable;
  const text = "By Lemma 2 and § (5) we are done";
  const index = referenceIndex(table, new TextEncoder().encode(text));

  it("count bytes, not characters", () => {
    expect(index.rows).toHaveLength(2);
    const marked = markReferences(text, 0, index);
    expect(stripRefMarks(marked)).toBe(text);
    expect(linkReferences(marked, index)).toContain('<a href="#eq-5" data-in="short" data-ref="1">(5)</a>');
  });

  it("step over the marks of ties, which stand for no bytes", () => {
    const tied = `By Lemma 2 and § (5) we are done`;
    const linked = linkReferences(markReferences(tied, 0, index), index);
    expect(linked).toContain(`${"\uE100"}<a href="#lem-2" data-in="short" data-ref="0">Lemma 2</a>${"\uEB00"}`);
  });

  it("drop a row whose words have moved", () => {
    const moved = referenceIndex(table, new TextEncoder().encode(`X${text}`));
    expect(moved.rows).toHaveLength(0);
  });

  it("add the row to a link the Markdown already made", () => {
    const row = { start_byte: 0, end_byte: 8, quote: "[a][KEY]", kind: "citation", source: "KEY" } as RefRow;
    const own = { paper: "short", targets: {}, sources: {}, references: [row] } as unknown as ReferenceTable;
    const at = { stage: "short", table: own, rows: [row], text: () => "" };
    expect(linkReferences('<a href="https://x.org">a</a>', at)).toBe('<a data-ref="0" href="https://x.org">a</a>');
  });
});

describe("what a reference shows", () => {
  const index = (stage: Stage) => referenceIndex(liveTable(stage), paper(stage));
  const find = (stage: Stage, quote: string, nth = 0) => {
    const at = index(stage);
    return { at, row: at.rows.filter((row) => row.quote === quote)[nth] };
  };

  it("types a label's whole statement and offers a jump", () => {
    const { at, row } = find("short", "Lemma 2", 1);
    const view = refView(at, row);
    expect(view.title).toBe("Lemma 2");
    expect(view.go).toBe("lem-2");
    expect(view.body).toContain("\\tag{3}");
    expect(view.body).toContain("If $c=0$");
  });

  it("says which manuscript a colliding number belongs to", () => {
    const { at, row } = find("long", "(6.1)", 2);
    expect(row.kind).toBe("manuscript");
    const view = refView(at, row);
    expect(view.note).toContain("Basso");
    expect(view.href).toContain("2110.14206");
    expect(view.go).toBeNull();
  });

  it("opens a citation with its entry and its locator", () => {
    const at = index("short");
    const row = at.rows.find((r) => r.kind === "citation" && r.locator?.includes("Lemmas 2.1–2.2"))!;
    const view = refView(at, row);
    expect(view.body).toContain("OpenAI (2026a)");
    expect(view.href).toContain("main.pdf");
    expect(opensInPlace(row)).toBe(true);
  });

  it("jumps for a section and opens the other paper beside this one", () => {
    const at = index("short");
    expect(opensInPlace(at.rows.find((r) => r.kind === "section")!)).toBe(false);
    const other = at.rows.find((r) => r.kind === "other_paper")!;
    expect(other.target).toBe("rooted-energy");
    expect(refView(at, other).note).toContain("§8.1");
  });

  it("finds a statement's record by its slice", () => {
    const records = {
      a: { lean: [{}], statements: [{ paper: "short", role: "statement", start_byte: 100, end_byte: 150 }] },
      b: { lean: [{}], statements: [{ paper: "short", role: "statement", start_byte: 90, end_byte: 300 }] },
      c: { lean: [], statements: [{ paper: "short", role: "statement", start_byte: 90, end_byte: 400 }] },
      d: { lean: [{}], statements: [{ paper: "long", role: "statement", start_byte: 90, end_byte: 400 }] },
    };
    expect(recordOver([95, 305], "short", records)).toBe("b");
    expect(recordOver([0, 50], "short", records)).toBeNull();
  });

  it("reads a Lean module from a pinned GitHub link", () => {
    expect(leanModuleOf("https://github.com/openai/math/blob/abc/lean/OAI/Probability/SKSupport/Main.lean#L35")).toBe("OAI.Probability.SKSupport.Main");
    expect(leanModuleOf("https://arxiv.org/abs/1606.05335v2")).toBeNull();
  });
});

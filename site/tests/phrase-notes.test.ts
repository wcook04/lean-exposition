// Every reading note and fidelity note of the phrase layer typesets without a KaTeX error, and
// the reader's words for a comparison name all four outcomes, "different" included.
import { readdirSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import { describe, expect, it } from "vitest";
import { isFidelity, phraseVerdict } from "../src/compare/fidelityWords";
import { noteHtml } from "../src/reader/math";
import { tieModel, topicOf, isPhraseRecord, partAt } from "../src/reader/ties";
import type { TieIndex } from "../src/api/lean";

const EXAMPLES = resolve(__dirname, "../../examples");

function phraseFiles(): { path: string; data: { parts: { notes: Record<string, string> }[]; ties: { lean: { fidelity: string; fidelity_note?: string }[] }[] } }[] {
  const out = [];
  for (const example of readdirSync(EXAMPLES)) {
    let names: string[] = [];
    try {
      names = readdirSync(resolve(EXAMPLES, example, "alignment"));
    } catch {
      continue;
    }
    for (const name of names.filter((n) => /^phrases-.*\.json$/.test(n))) {
      const path = resolve(EXAMPLES, example, "alignment", name);
      out.push({ path, data: JSON.parse(readFileSync(path, "utf8")) });
    }
  }
  return out;
}

describe("phrase notes", () => {
  it("sets mathematics with KaTeX, names as code, and escapes the rest", () => {
    const { html, errors } = noteHtml("If $x<1$, then `foo` holds; a \\$ sign <b>.");
    expect(errors).toEqual([]);
    expect(html).toContain("katex");
    expect(html).toContain("<code>foo</code>");
    expect(html).toContain("&lt;b&gt;");
    expect(html).toContain("$ sign");
    expect(noteHtml("$\\frac{1$").errors).toHaveLength(1);
  });

  it("links the reviewed PDF destination and escapes its label", () => {
    const { html, errors } = noteHtml("See [Statement 2.2 <here>](pdf#theorem.2.2).");
    expect(errors).toEqual([]);
    expect(html).toContain('href="/pdf/paper.pdf#nameddest=theorem.2.2"');
    expect(html).toContain('target="_blank" rel="noopener">Statement 2.2 &lt;here&gt;</a>');
    expect(noteHtml("[Unsafe](pdf#../elsewhere)").html).not.toContain("<a ");
  });

  it("reports broken math delimiters without dropping the prose", () => {
    const { html, errors } = noteHtml("The bound is $x < 1");
    expect(html).toBe("The bound is $x &lt; 1");
    expect(errors).toHaveLength(1);
    expect(noteHtml("Use `$x` as code.").errors).toEqual([]);
  });

  it("typesets every note of every phrase file", () => {
    const files = phraseFiles();
    expect(files.length).toBeGreaterThan(0);
    for (const { path, data } of files) {
      for (const part of data.parts) {
        for (const [name, note] of Object.entries(part.notes)) {
          const { errors } = noteHtml(note);
          expect(errors, `${path}: ${name}`).toEqual([]);
        }
      }
      for (const tie of data.ties) {
        for (const row of tie.lean) {
          expect(isFidelity(row.fidelity), path).toBe(true);
          if (row.fidelity_note) expect(noteHtml(row.fidelity_note).errors).toEqual([]);
        }
      }
    }
  });

  it("says each comparison in words", () => {
    expect(phraseVerdict("weaker")).toBe("Lean states less");
    expect(phraseVerdict("stronger")).toBe("Lean states more");
    expect(phraseVerdict("different")).toBe("Lean states it differently");
    expect(phraseVerdict("same")).toBe("Lean states the same as this phrase");
  });

  it("gives a phrase with no step on the map a record of its own, and says its topic", () => {
    const index: TieIndex = {
      layer: "phrases",
      topics: [{ id: "t", name: "Topic one", description: "", part: 0, tone: 0 }],
      parts: [{ name: "", start_byte: 0, end_byte: 100 }, { name: "Part two", start_byte: 100, end_byte: 200 }],
      segments: [[0, 5, [0]]],
      ties: [{ record: null as unknown as string, phrase: "p", topic: "t", tone: 0, role: "statement", lean: true, name: "A.b", module: "A", lines: [1, 1], anchor: null, at: "b0-5",
        rows: [{ name: "A.b", module: "A", line: 1, end_line: 1, lines: [1, 1], relation: "states", note: "", plain: "The b" }] }],
      passages: [],
      meaning: "",
    };
    const model = tieModel(index);
    expect(isPhraseRecord(model.index.ties[0].record)).toBe(true);
    expect(topicOf(model, 0)?.name).toBe("Topic one");
    expect(partAt(model, 150)).toBe(1);
  });
});

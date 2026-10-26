import { describe, expect, it } from "vitest";
import { jsonField, marked, matchRanges, plainMarkdown, prepareExcerpt, segments, utf16IndexOf } from "../src/search/excerpt";

const markedText = (m: { text: string; marks: boolean[] }) => m.text.split("").filter((_, i) => m.marks[i]).join("");

describe("search excerpt offsets", () => {
  it("converts code points to UTF-16 indices past astral characters", () => {
    const text = "𝔼[X] curvature";
    // 𝔼 is one code point but two UTF-16 units.
    expect(utf16IndexOf(text, 1)).toBe(2);
    expect(utf16IndexOf(text, 5)).toBe(6);
    expect(utf16IndexOf(text, 99)).toBe(text.length);
  });

  it("places matches relative to the excerpt start", () => {
    const excerpt = "𝔼 𝟙 a curvature b";
    // The excerpt starts at code point 100 of the indexed text; "curvature" is code points 6–15 within it.
    const ranges = matchRanges(excerpt, 100, [{ start_character: 106, end_character: 115 }]);
    expect(ranges).toHaveLength(1);
    expect(excerpt.slice(...ranges[0])).toBe("curvature");
  });

  it("clips matches cut by the excerpt's edges and drops those outside it", () => {
    const excerpt = "vature and more";
    const ranges = matchRanges(excerpt, 10, [
      { start_character: 7, end_character: 16 },
      { start_character: 400, end_character: 409 },
    ]);
    expect(ranges.map((r) => excerpt.slice(...r))).toEqual(["vature"]);
  });

  it("handles BMP characters outside ASCII as single units", () => {
    const excerpt = "Sherrington–Kirkpatrick gap";
    const ranges = matchRanges(excerpt, 0, [{ start_character: 24, end_character: 27 }]);
    expect(excerpt.slice(...ranges[0])).toBe("gap");
  });
});

describe("readable excerpts", () => {
  it("finds the JSON field holding a record match and unescapes it", () => {
    const excerpt = '"id": "x", "statement": "If \\"gap\\" then curvature fails", "kind": "claim"';
    const start = excerpt.indexOf("curvature");
    const field = jsonField(marked(excerpt, [[start, start + 9]]))!;
    expect(field.key).toBe("statement");
    expect(field.value.text).toBe('If "gap" then curvature fails');
    expect(markedText(field.value)).toBe("curvature");
  });

  it("keeps highlights through Markdown clean-up", () => {
    const text = "## 5.3 Strict curvature\n\nSee [the **curvature** bound][ref] and `code`.";
    const ranges: [number, number][] = [];
    for (const m of text.matchAll(/curvature/g)) ranges.push([m.index!, m.index! + 9]);
    const plain = plainMarkdown(marked(text, ranges));
    expect(plain.text).toBe("5.3 Strict curvature. See the curvature bound and code.");
    expect(markedText(plain)).toBe("curvaturecurvature");
  });

  it("splits TeX into math segments and drops a formula cut at the start", () => {
    const source = "q'(0)\\le1$. The gap $(\\ell,r)$ closes.";
    const at = source.indexOf("gap");
    const m = marked(source, [[at, at + 3]]);
    const segs = segments(m, true, false);
    expect(segs[0]).toEqual({ kind: "text", text: ". The ", mark: false });
    expect(segs.find((s) => s.kind === "math")).toMatchObject({ tex: "(\\ell,r)" });
    expect(segs.some((s) => s.kind === "text" && s.mark && s.text === "gap")).toBe(true);
  });

  it("prepares an API passage result end to end", () => {
    const excerpt = "\nzero.\n\n### 5.3 Strict curvature creates an impossible integral\n\nThe support";
    const start = 2539;
    const at = [...excerpt].length - [...excerpt.slice(excerpt.indexOf("curvature"))].length;
    const prepared = prepareExcerpt({
      table: "passages",
      excerpt,
      excerpt_start_character: start,
      excerpt_truncated: true,
      matches: [{ start_character: start + at, end_character: start + at + 9 }],
    })!;
    const text = prepared.segments.map((s) => (s.kind === "text" ? s.text : "")).join("");
    expect(text).toBe("zero. 5.3 Strict curvature creates an impossible integral. The support");
    expect(prepared.segments.filter((s) => s.mark).map((s) => s.kind === "text" && s.text)).toEqual(["curvature"]);
    expect(prepared.cutStart).toBe(true);
  });
});

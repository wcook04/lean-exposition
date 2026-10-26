// Fragment identifiers for rendered manuscripts.
//
// Heading ids follow Pandoc 3's `auto_identifiers` algorithm, so links written
// against the PDF/HTML editions produced by Pandoc keep working:
//   1. take the heading's plain text (formatting and links removed; inline math
//      contributes its TeX source, as Pandoc's `stringify` does),
//   2. lowercase it,
//   3. keep only alphanumerics (Unicode-aware), whitespace, `_`, `-` and `.`,
//   4. split on whitespace and join the words with `-`,
//   5. drop everything before the first letter,
//   6. use `section` when nothing is left,
//   7. deduplicate in document order with `-1`, `-2`, ...
//
// GitHub-style slugs (`## 2. What a gap means` -> `2-what-a-gap-means`) are
// registered as alias anchors when they differ, because some companion
// documents link to that form.

const ALNUM = /[\p{L}\p{N}]/u;
const LETTER = /\p{L}/u;

export function pandocIdentifier(text: string): string {
  let kept = "";
  for (const ch of text.toLowerCase()) {
    if (/\s/u.test(ch) || ALNUM.test(ch) || ch === "_" || ch === "-" || ch === ".") kept += ch;
  }
  const joined = kept.split(/\s+/u).filter(Boolean).join("-");
  let start = 0;
  const chars = Array.from(joined);
  while (start < chars.length && !LETTER.test(chars[start])) start++;
  const id = chars.slice(start).join("");
  return id === "" ? "section" : id;
}

/** GitHub's heading slug: lowercase, drop punctuation except `-`/`_`, each space to `-`. */
export function githubSlug(text: string): string {
  return text
    .trim()
    .toLowerCase()
    .replace(/[^\p{L}\p{M}\p{N}\p{Pc}\- ]/gu, "")
    .replace(/ /g, "-");
}

/** Tracks used ids across a whole document (all parts, in order). */
export class AnchorRegistry {
  private readonly used = new Map<string, number>();
  readonly duplicates: { id: string; parts: [number, number] }[] = [];

  has(id: string): boolean {
    return this.used.has(id);
  }

  partOf(id: string): number | undefined {
    return this.used.get(id);
  }

  /** Register an explicit id (`<a id>`). Duplicates are recorded, first wins. */
  claimExplicit(id: string, part: number): boolean {
    const prior = this.used.get(id);
    if (prior !== undefined) {
      this.duplicates.push({ id, parts: [prior, part] });
      return false;
    }
    this.used.set(id, part);
    return true;
  }

  /** Pandoc-style unique heading id: base, then base-1, base-2, ... */
  claimHeading(base: string, part: number): string {
    let id = base;
    for (let n = 1; this.used.has(id); n++) id = `${base}-${n}`;
    this.used.set(id, part);
    return id;
  }

  /** Alias anchors are only registered when free; they never displace a real id. */
  claimAlias(id: string, part: number): boolean {
    if (id === "" || this.used.has(id)) return false;
    this.used.set(id, part);
    return true;
  }

  entries(): Map<string, number> {
    return new Map(this.used);
  }
}

/** UTF-8 byte length of `text.slice(0, utf16Index)`. */
export function byteOffsetOf(text: string, utf16Index: number): number {
  let bytes = 0;
  const end = Math.max(0, Math.min(utf16Index, text.length));
  for (let i = 0; i < end; i++) {
    const c = text.charCodeAt(i);
    if (c < 0x80) bytes += 1;
    else if (c < 0x800) bytes += 2;
    else if (c >= 0xd800 && c <= 0xdbff && i + 1 < end) {
      const d = text.charCodeAt(i + 1);
      if (d >= 0xdc00 && d <= 0xdfff) {
        bytes += 4;
        i++;
      } else bytes += 3;
    } else bytes += 3;
  }
  return bytes;
}

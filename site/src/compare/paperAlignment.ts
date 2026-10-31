// Two papers read side by side, like a diff of two documents that share a graph.
// A sequence alignment over their passages: a pair scores by the records it shares,
// a rare record counting for more, with a bonus where the authors wrote a reading link
// between the two. Gaps are free, the alignment is monotone, and every part of both
// papers lands in exactly one row, in reading order.

export interface AlignUnit {
  /** The document part this unit is. */
  part: number;
  /** The records its passage is mapped to; none for unmapped text. */
  records: readonly string[];
  /** Its length in bytes, so a heading between passages can travel with what it heads. */
  size: number;
}

export interface AlignPair {
  /** Index into `left`. */
  left: number;
  /** Index into `right`. */
  right: number;
}

export interface AlsoLinked {
  side: "left" | "right";
  /** The unit on the other side. */
  unit: number;
  /** The row that holds it. */
  row: number;
}

export interface AlignedRow {
  /** Unit indices, in reading order. */
  left: number[];
  right: number[];
  /** Records both cells are mapped to, rarest first. */
  shared: string[];
  /** Linked passages the monotone order put in another row. */
  also: AlsoLinked[];
}

/** An authored reading link is worth about one rare shared record. */
export const LINK_BONUS = 3;
/** A piece of unmapped text this short is a heading or a bridge, and stays with its neighbour. */
export const SMALL_TEXT = 320;
/** "Also linked" jumps per side of a row. */
const ALSO_LIMIT = 1;

/** How much each record counts: more for a record few passages carry. */
export function recordWeights(left: readonly AlignUnit[], right: readonly AlignUnit[]): Map<string, number> {
  const counts = new Map<string, number>();
  for (const unit of [...left, ...right]) for (const id of new Set(unit.records)) counts.set(id, (counts.get(id) ?? 0) + 1);
  const total = left.length + right.length;
  return new Map([...counts].map(([id, n]) => [id, Math.log(1 + total / n)]));
}

function sharedOf(a: readonly string[], b: readonly string[], weights: Map<string, number>): string[] {
  const other = new Set(b);
  return [...new Set(a)].filter((id) => other.has(id)).sort((x, y) => (weights.get(y) ?? 0) - (weights.get(x) ?? 0) || x.localeCompare(y));
}

export function alignPapers(left: readonly AlignUnit[], right: readonly AlignUnit[], links: readonly AlignPair[] = []): AlignedRow[] {
  const weights = recordWeights(left, right);
  const linked = new Set(links.map((l) => `${l.left}:${l.right}`));
  const score = (i: number, j: number) => {
    const shared = sharedOf(left[i].records, right[j].records, weights).reduce((n, id) => n + (weights.get(id) ?? 0), 0);
    return shared + (linked.has(`${i}:${j}`) ? LINK_BONUS : 0);
  };

  // Needleman-Wunsch with free gaps, over what remains of each paper from (i, j).
  const n = left.length;
  const m = right.length;
  const best = new Float64Array((n + 1) * (m + 1));
  const at = (i: number, j: number) => i * (m + 1) + j;
  const scores = new Float64Array(n * m);
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      const s = score(i, j);
      scores[i * m + j] = s;
      const match = s > 0 ? s + best[at(i + 1, j + 1)] : -1;
      best[at(i, j)] = Math.max(match, best[at(i + 1, j)], best[at(i, j + 1)]);
    }
  }

  const rows: AlignedRow[] = [];
  const row = (l: number[], r: number[]): AlignedRow => ({ left: l, right: r, shared: [], also: [] });
  let i = 0;
  let j = 0;
  while (i < n || j < m) {
    if (i < n && j < m && scores[i * m + j] > 0 && best[at(i, j)] === scores[i * m + j] + best[at(i + 1, j + 1)]) rows.push(row([i++], [j++]));
    else if (i < n && (j === m || best[at(i, j)] === best[at(i + 1, j)])) rows.push(row([i++], []));
    else rows.push(row([], [j++]));
  }

  const merged = attachSmallText(mergeGaps(rows, left, right), left, right);
  for (const r of merged) {
    r.shared = sharedOf(r.left.flatMap((u) => [...left[u].records]), r.right.flatMap((u) => [...right[u].records]), weights);
  }
  markAlsoLinked(merged, left, right, scores);
  return merged;
}

const carries = (units: readonly AlignUnit[], cell: number[], records: ReadonlySet<string>) => cell.some((u) => units[u].records.some((id) => records.has(id)));

/** A passage left alone moves into the nearest paired row when it shares a record with that row's other cell. */
function mergeGaps(rows: AlignedRow[], left: readonly AlignUnit[], right: readonly AlignUnit[]): AlignedRow[] {
  const out = rows.map((r) => ({ ...r, left: [...r.left], right: [...r.right] }));
  const pull = (side: "left" | "right", other: "left" | "right", direction: 1 | -1) => {
    const mine = side === "left" ? left : right;
    const theirs = side === "left" ? right : left;
    const from = direction === 1 ? 0 : out.length - 1;
    for (let k = from; k >= 0 && k < out.length; k += direction) {
      const r = out[k];
      if (r[side].length !== 1 || r[other].length) continue;
      const records = new Set(mine[r[side][0]].records);
      if (!records.size) continue;
      // The nearest row with this side's content or a paired row; other-side gaps may be crossed.
      let p = k - direction;
      while (p >= 0 && p < out.length && !out[p][side].length) p -= direction;
      if (p < 0 || p >= out.length || !out[p][other].length) continue;
      if (!carries(theirs, out[p][other], records)) continue;
      if (direction === 1) out[p][side].push(r[side].pop()!);
      else out[p][side].unshift(r[side].pop()!);
    }
  };
  pull("left", "right", 1);
  pull("right", "left", 1);
  pull("left", "right", -1);
  pull("right", "left", -1);
  return out.filter((r) => r.left.length || r.right.length);
}

/** A heading or short bridge joins the next row on its side, or the last one at the end of the paper. */
function attachSmallText(rows: AlignedRow[], left: readonly AlignUnit[], right: readonly AlignUnit[]): AlignedRow[] {
  const small = (units: readonly AlignUnit[], cell: number[]) => cell.length > 0 && cell.every((u) => !units[u].records.length && units[u].size <= SMALL_TEXT);
  const out = rows.map((r) => ({ ...r, left: [...r.left], right: [...r.right] }));
  const lift = (side: "left" | "right", units: readonly AlignUnit[], other: "left" | "right") => {
    for (let k = out.length - 1; k >= 0; k--) {
      const r = out[k];
      if (r[other].length || !small(units, r[side])) continue;
      let p = k + 1;
      while (p < out.length && !out[p][side].length) p++;
      if (p < out.length) {
        out[p][side].unshift(...r[side]);
      } else {
        p = k - 1;
        while (p >= 0 && !out[p][side].length) p--;
        if (p < 0) continue;
        out[p][side].push(...r[side]);
      }
      r[side] = [];
    }
  };
  lift("left", left, "right");
  lift("right", right, "left");
  return out.filter((r) => r.left.length || r.right.length);
}

/** For each row, the strongest pairs its passages have with passages in other rows. */
function markAlsoLinked(rows: AlignedRow[], left: readonly AlignUnit[], right: readonly AlignUnit[], scores: Float64Array): void {
  const m = right.length;
  const rowOfRight = new Map<number, number>();
  const rowOfLeft = new Map<number, number>();
  rows.forEach((r, k) => {
    r.left.forEach((u) => rowOfLeft.set(u, k));
    r.right.forEach((u) => rowOfRight.set(u, k));
  });
  rows.forEach((r, k) => {
    const pick = (cell: number[], others: number, side: "left" | "right", value: (mine: number, theirs: number) => number, rowOf: Map<number, number>) => {
      const found = new Map<number, number>();
      for (const mine of cell) {
        for (let theirs = 0; theirs < others; theirs++) {
          const s = value(mine, theirs);
          if (s > 0 && rowOf.get(theirs) !== k) found.set(theirs, Math.max(found.get(theirs) ?? 0, s));
        }
      }
      return [...found]
        .sort((a, b) => b[1] - a[1] || a[0] - b[0])
        .slice(0, ALSO_LIMIT)
        .map(([unit]) => ({ side, unit, row: rowOf.get(unit)! }));
    };
    r.also = [
      ...pick(r.left, m, "left", (a, b) => scores[a * m + b], rowOfRight),
      ...pick(r.right, left.length, "right", (b, a) => scores[a * m + b], rowOfLeft),
    ];
  });
}

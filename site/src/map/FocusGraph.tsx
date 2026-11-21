// The focus graph: one subject (a step, a declaration, or the steps of one paragraph) in the
// middle, the cards that use it on the left and the cards it uses on the right, each joined to
// it by a curved line. It fits its pane when it opens: nodes are one compact line of plain
// words, and a side with more neighbours than fit is drawn as named groups, each with its
// count, that open in place. Nothing is left out and nothing is replaced by a bare count.
// The same file serves the Quartic Reader, the SK and Erdős #257 readers and Proof Reader:
// docs/graph-pane.md is its specification, and a change here should be copied to the other two.
//
// Layout is the browser's own (columns of wrapped titles); the lines are measured from the
// nodes after layout, so a title of any length, or one with typeset mathematics, is never cut.

import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import "./focus-graph.css";

/** What a card is, for the reader: this decides its look and, on a crowded side, its group. */
export type FGRole = "result" | "step" | "definition" | "helper" | "library" | "cited" | "open";

export interface FGCard {
  id: string;
  /** Plain words, shown whole. */
  title: string;
  /** The raw Lean name, shown on the subject and in the dock. */
  name?: string;
  role: FGRole;
  /** A short tag before the title: "Theorem 2.1", "Lemma 4.5". */
  kicker?: string;
  /** The topic colour this card shares with its phrases in the paper (any CSS colour). */
  tone?: string;
  /** The name of that topic: a crowded side is grouped by it. */
  topic?: string;
  /** The Lean file or the section of the paper it belongs to: a large group is divided by it. */
  section?: string;
  /** Where the paper states it, against the reading position. */
  seen?: "before" | "here" | "later";
}

/** `from` uses `to`. `statement`: only the statement of `from` names `to`; `proof`: its proof or body does;
 *  `argument`: the paper's own argument, as authored. */
export interface FGEdge { from: string; to: string; kind?: "proof" | "statement" | "argument" }

export interface FGRoleWords { order: number; one: string; many: string; uses: string; usedBy: string }

export const FG_ROLES: Record<FGRole, FGRoleWords> = {
  result: { order: 0, one: "Paper result", many: "Results of the paper", uses: "Results of the paper it uses", usedBy: "Results of the paper that use it" },
  step: { order: 1, one: "Step", many: "Steps of the argument", uses: "Steps of the argument it uses", usedBy: "Steps of the argument that use it" },
  definition: { order: 2, one: "Definition", many: "Definitions", uses: "Definitions it uses", usedBy: "Definitions that use it" },
  cited: { order: 3, one: "Cited result", many: "Cited results", uses: "Cited results it uses", usedBy: "Cited results that use it" },
  open: { order: 4, one: "Open question", many: "Open questions", uses: "Open questions it rests on", usedBy: "Open questions that use it" },
  helper: { order: 5, one: "Lean helper", many: "Lean helper lemmas", uses: "Lean helper lemmas it uses", usedBy: "Lean helper lemmas that use it" },
  library: { order: 6, one: "Library fact", many: "Library facts", uses: "Library facts it uses", usedBy: "Library facts that use it" },
};

export interface FocusGraphProps {
  /** The card or cards in the middle. */
  subjects: readonly string[];
  card(id: string): FGCard | undefined;
  /** Every edge with a subject at one end (others are ignored). */
  edges: readonly FGEdge[];
  /** From the subject to the main result: each card is used by the next. Empty when the subject is the main result. */
  route?: readonly string[] | null;
  /** Said when there is no route to draw. */
  routeNote?: ReactNode;
  /** One line over the drawing: what this view is, and a way back if it is a view of its own. */
  label?: ReactNode;
  /** Cards lit from outside: the phrase or sentence under the pointer. */
  lit?: readonly string[];
  /** The card whose detail is docked below, if it is not the subject. */
  held?: string | null;
  onSubject(id: string): void;
  onHover?(id: string | null): void;
  renderTitle?(card: FGCard): ReactNode;
  roles?: Partial<Record<FGRole, Partial<FGRoleWords>>>;
  /** Words for the subject frame when a paragraph has several steps. */
  manyLabel?: string;
}

interface Box { x: number; y: number; w: number; h: number }
interface Seg { d: string; cls: string; edge?: string; width?: number }
interface Drawn { w: number; h: number; segs: Seg[]; paths: Record<string, string>; boxes: { id: string; box: Box; band: string }[] }
type Side = "users" | "uses";
interface Rel { kind: string; of: Set<string> }
/** One thing in a side's column: a card, or a named group of cards that opens in place. */
type Item =
  | { type: "node"; id: string }
  | { type: "group"; key: string; name: string; tone?: string; role?: FGRole; said?: string; ids: string[]; open: boolean; children: Item[] };
/** How one side is divided when it does not fit: named parts, some of them drawn out as their own nodes. */
interface Part { key: string; name: string; list: string[]; depth: number }
type Plan = { flat: true } | { flat: false; parts: Part[]; out: ReadonlySet<string> };

const ZOOMS = [0.93, 1, 1.15, 1.3, 1.5];
const PAD_X = 16;
const PAD_Y = 14;
const ITEM_GAP = 6;
/** A group with more members than this, from several files or sections, opens into those first. */
const DIVIDE_ABOVE = 18;
/** A kind's words inside a sentence: "Definitions" becomes "definitions"; "Lean helper lemmas" keeps its capital. */
const inSentence = (words: string) => (words.startsWith("Lean ") ? words : words.charAt(0).toLowerCase() + words.slice(1));
const MINI_W = 150;
const MINI_H = 58;
const MINI_MIN_W = 64;

export function FocusGraph(props: FocusGraphProps) {
  const { subjects, card, edges, route, routeNote, label, lit, held, onSubject, onHover, renderTitle } = props;
  const scroller = useRef<HTMLDivElement>(null);
  const world = useRef<HTMLDivElement>(null);
  const [size, setSize] = useState({ w: 0, h: 0 });
  const [zoomAt, setZoomAt] = useState(1);
  const zoom = ZOOMS[zoomAt];
  const [drawn, setDrawn] = useState<Drawn | null>(null);
  const [hot, setHot] = useState<string | null>(null);
  const [view, setView] = useState<Box>({ x: 0, y: 0, w: 0, h: 0 });
  /** Groups the reader opened, by side and key. */
  const [opened, setOpened] = useState<ReadonlySet<string>>(new Set());
  /** How many times the first estimate of what fits has been tightened for this subject. */
  const [tight, setTight] = useState(0);
  const moved = useRef(false);
  const openedNow = useRef(false);
  openedNow.current = opened.size > 0;

  const words = useCallback((role: FGRole): FGRoleWords => ({ ...FG_ROLES[role], ...(props.roles?.[role] ?? {}) }), [props.roles]);

  // What is drawn: the subjects, in ranks when they use one another; on the left the cards that
  // use a subject; on the right the cards a subject uses. A card that both uses and is used is on the left.
  const model = useMemo(() => {
    const subj = subjects.filter((id, i) => card(id) && subjects.indexOf(id) === i);
    const isSubject = new Set(subj);
    const users = new Map<string, Rel>();
    const uses = new Map<string, Rel>();
    const inner: FGEdge[] = [];
    const add = (into: Map<string, Rel>, id: string, subject: string, kind = "proof") => {
      if (!card(id)) return;
      const row = into.get(id) ?? { kind, of: new Set<string>() };
      // A statement-only use is said so only if no proof or body also uses it; the paper's argument outranks both.
      if (kind === "argument" || (kind !== "statement" && row.kind !== "argument")) row.kind = kind;
      row.of.add(subject);
      into.set(id, row);
    };
    for (const e of edges) {
      const f = isSubject.has(e.from), t = isSubject.has(e.to);
      if (f && t) { if (e.from !== e.to) inner.push(e); }
      else if (f) add(uses, e.to, e.from, e.kind);
      else if (t) add(users, e.from, e.to, e.kind);
    }
    for (const id of users.keys()) uses.delete(id);
    // The subjects of one paragraph, in an order in which a step comes after every step that uses it.
    const rank = new Map(subj.map((id) => [id, 0]));
    for (let pass = 0; pass < subj.length; pass++) {
      let changed = false;
      for (const e of inner) {
        const want = (rank.get(e.from) ?? 0) + 1;
        if ((rank.get(e.to) ?? 0) < want && want <= subj.length) { rank.set(e.to, want); changed = true; }
      }
      if (!changed) break;
    }
    const ordered = [...subj].sort((a, b) => (rank.get(a) ?? 0) - (rank.get(b) ?? 0));
    const sorted = (side: Map<string, Rel>) =>
      [...side.keys()].sort((a, b) => {
        const A = card(a)!, B = card(b)!;
        return words(A.role).order - words(B.role).order || (A.topic ?? "~").localeCompare(B.topic ?? "~") || A.title.localeCompare(B.title);
      });
    return { subj: ordered, inner, users, uses, left: sorted(users), right: sorted(uses) };
  }, [subjects, card, edges, words]);

  const key = model.subj.join("|");
  const many = model.subj.length > 1;
  useLayoutEffect(() => { setOpened(new Set()); setTight(0); setHot(null); }, [key]);
  // A new size is fitted afresh, unless the reader has a group open.
  useLayoutEffect(() => { if (!openedNow.current) setTight(0); }, [size.w, size.h, zoom]);

  // The widths of the three columns, for the room there is.
  const W = (size.w || 640) / zoom;
  const H = (size.h || 420) / zoom;
  const both = model.left.length > 0 && model.right.length > 0;
  const gap = Math.round(Math.max(30, Math.min(96, W * 0.07)));
  const subjectW = Math.round(Math.max(190, Math.min(280, W * (both ? 0.27 : 0.3))));
  /** The width of the note that stands where a side has nothing. */
  const NOTE_W = 132;
  // Too narrow for three columns (a phone): the sides stand over and under the subject, at the pane's width.
  const stacked = W < 520;
  const sideW = stacked ? Math.floor(W - 2 * PAD_X - 18) : Math.floor(Math.max(150, Math.min(both ? 380 : 460, both ? (W - subjectW - 2 * PAD_X - 2 * gap) / 2 : W - subjectW - 2 * PAD_X - 2 * gap - NOTE_W)));

  // A column fits when its nodes' heights, estimated from the length of each title, come to no more
  // than the height of the area. A side that does not fit starts from its kinds and divides the largest
  // group that can be divided (by topic, then by file or section), largest pieces first, for as long as
  // the column still fits; the smallest groups are then drawn out as their own nodes while there is room.
  const narrow = stacked;
  const plan = useCallback((ids: string[]): Plan => {
    const lines = (text: string, tag = "") => Math.max(1, Math.ceil(((text.length + (tag ? tag.length + 1 : 0)) * 6.9) / (sideW - 24)));
    const nodeH = (id: string) => { const c = card(id)!; return 10 + lines(c.title, c.kicker) * 17.5 + ITEM_GAP; };
    const headH = (name: string) => 15 + lines(name + " 00000") * 17.5 + ITEM_GAP;
    const room = (narrow ? Math.max(H, 520) * 0.5 : H - 2 * PAD_Y - 30) * Math.pow(0.86, tight);
    if (ids.reduce((sum, id) => sum + nodeH(id), 0) <= room) return { flat: true };
    const by = (list: string[], pick: (c: FGCard) => string) => {
      const groups = new Map<string, string[]>();
      for (const id of list) { const k = pick(card(id)!); groups.set(k, [...(groups.get(k) ?? []), id]); }
      return [...groups.entries()];
    };
    let parts: Part[] = by(ids, (c) => c.role).map(([role, list]) => ({ key: role, name: words(role as FGRole).many, list, depth: 0 }));
    const total = (ps: Part[]) => ps.reduce((sum, p) => sum + headH(p.name), 0);
    // The pieces a part divides into, largest first: by topic, and a part that is one topic by file or section.
    const pieces = (p: Part): Part[] | null => {
      for (const depth of [1, 2]) {
        if (p.depth >= depth || (depth === 2 && p.list.length < 8)) continue;
        const found = by(p.list, (c) => (depth === 1 ? c.topic : c.section) ?? "").sort((x, y) => y[1].length - x[1].length);
        if (found.length < 2) continue;
        return found.map(([k, list]) => ({ key: `${p.key}/${depth}:${k}`, list, depth, name: k ? (depth === 2 && p.depth === 1 ? `${p.name} · ${k}` : k) : `Other ${inSentence(p.name)}` }));
      }
      return null;
    };
    for (let guard = 0; guard < 60; guard++) {
      const order = parts.map((_, i) => i).sort((a, b) => parts[b].list.length - parts[a].list.length);
      let done = false;
      for (const i of order) {
        if (parts[i].list.length < 4 || parts[i].key.endsWith("/rest")) continue;
        const all = pieces(parts[i]);
        if (!all) continue;
        // As many of the largest pieces as fit; what is left stays together under the part's own name.
        for (let take = all.length; take >= 1 && !done; take--) {
          const rest = all.slice(take).flatMap((x) => x.list);
          if (take < all.length && rest.length === 0) continue;
          const kept: Part[] = take === all.length ? all : [...all.slice(0, take), { key: `${parts[i].key}/rest`, name: parts[i].name.startsWith("Other ") ? parts[i].name : `Other ${inSentence(parts[i].name)}`, list: rest, depth: parts[i].depth }];
          // Pieces of one name (the cards with no topic, and what was left over) stand as one group.
          const merged: Part[] = [];
          for (const k of kept) { const same = merged.find((m) => m.name === k.name); if (same) same.list = [...same.list, ...k.list]; else merged.push({ ...k }); }
          const next = [...parts.slice(0, i), ...merged, ...parts.slice(i + 1)];
          if (total(next) <= room) { parts = next; done = true; }
        }
        if (done) break;
      }
      if (!done) break;
    }
    let left = room - total(parts);
    const out = new Set<string>();
    for (const p of [...parts].sort((a, b) => a.list.length - b.list.length)) {
      const cost = p.list.reduce((sum, id) => sum + nodeH(id), 0) - headH(p.name);
      if (p.list.length === 1 || cost <= left) { out.add(p.key); left -= Math.max(0, cost); }
    }
    return { flat: false, parts, out };
  }, [card, words, sideW, H, tight, narrow]);

  // While the reader has a group open the division is kept as it was, so that the group stays where it is.
  const kept = useRef<{ key: string; users: Plan; uses: Plan } | null>(null);
  const plans = useMemo(() => {
    if (opened.size && kept.current?.key === key) return kept.current;
    kept.current = { key, users: plan(model.left), uses: plan(model.right) };
    return kept.current;
  }, [plan, model.left, model.right, opened, key]);

  const column = useCallback((side: Side, ids: string[], how: Plan): Item[] => {
    const node = (id: string): Item => ({ type: "node", id });
    if (how.flat) return ids.map(node);
    const open = (path: string) => opened.has(`${side}:${path}`);
    const group = (path: string, name: string, list: string[], divide: boolean): Item => {
      const tones = new Set(list.map((id) => card(id)!.tone));
      const kinds = new Set(list.map((id) => card(id)!.role));
      const isOpen = open(path);
      let children: Item[] = [];
      if (isOpen) {
        const sections = new Map<string, string[]>();
        if (divide && list.length > DIVIDE_ABOVE) for (const id of list) { const k = card(id)!.section ?? ""; sections.set(k, [...(sections.get(k) ?? []), id]); }
        children = sections.size > 1 && sections.size < list.length
          ? [...sections.entries()].map(([sec, part]) => (part.length === 1 ? node(part[0]) : group(`${path}/s:${sec}`, sec || "Elsewhere", part, false)))
          : list.map(node);
      }
      return { type: "group", key: path, name, tone: tones.size === 1 ? [...tones][0] : undefined, role: kinds.size === 1 ? [...kinds][0] : undefined, ids: list, open: isOpen, children };
    };
    const items = how.parts.flatMap((p) => (how.out.has(p.key) && !open(p.key) ? p.list.map(node) : [group(p.key, p.name, p.list, p.depth < 2)]));
    // Two groups of one name (one topic among the definitions and again among the lemmas) each say their kind.
    const names = new Map<string, number>();
    for (const it of items) if (it.type === "group") names.set(it.name, (names.get(it.name) ?? 0) + 1);
    for (const it of items) if (it.type === "group" && it.role && (names.get(it.name) ?? 0) > 1) it.said = inSentence(words(it.role).many);
    return items;
  }, [card, opened, words]);

  const leftItems = useMemo(() => column("users", model.left, plans.users), [column, model.left, plans]);
  const rightItems = useMemo(() => column("uses", model.right, plans.uses), [column, model.right, plans]);

  useLayoutEffect(() => {
    const el = scroller.current;
    if (!el) return;
    const read = () => setSize((s) => (s.w === el.clientWidth && s.h === el.clientHeight ? s : { w: el.clientWidth, h: el.clientHeight }));
    read();
    const ro = new ResizeObserver(read);
    ro.observe(el);
    return () => ro.disconnect();
  }, []);

  // The lines, measured from the nodes as the browser laid them out.
  const measure = useCallback(() => {
    const w = world.current;
    if (!w) return;
    const origin = w.getBoundingClientRect();
    const box = (el: Element): Box => {
      const r = el.getBoundingClientRect();
      return { x: (r.left - origin.left) / zoom, y: (r.top - origin.top) / zoom, w: r.width / zoom, h: r.height / zoom };
    };
    const frame = w.querySelector(".fg__subjects");
    if (!frame) { setDrawn(null); return; }
    const F = box(frame);
    const stackedNow = w.classList.contains("fg__world--narrow");
    const segs: Seg[] = [];
    const paths: Record<string, string> = {};
    const boxes: Drawn["boxes"] = [];
    const subjectBox = new Map<string, Box>();
    for (const el of w.querySelectorAll<HTMLElement>(".fg__card, .fg__grouphead")) {
      const b = box(el);
      boxes.push({ id: el.dataset.card ?? `group:${el.dataset.group}`, box: b, band: el.dataset.band ?? "group" });
      if (el.dataset.band === "subject") subjectBox.set(el.dataset.card!, b);
    }
    const curve = (x1: number, y1: number, x2: number, y2: number) => {
      const mx = (x1 + x2) / 2;
      return `M${x1.toFixed(1)} ${y1.toFixed(1)} C${mx.toFixed(1)} ${y1.toFixed(1)}, ${mx.toFixed(1)} ${y2.toFixed(1)}, ${x2.toFixed(1)} ${y2.toFixed(1)}`;
    };
    for (const side of ["users", "uses"] as const) {
      const col = w.querySelector(`.fg__side[data-band="${side}"]`);
      if (!col) continue;
      const rels = side === "users" ? model.users : model.uses;
      // Where lines meet a subject: spread along its edge, in the order of the nodes they come from.
      const tops = [...col.querySelectorAll<HTMLElement>(":scope > .fg__card, :scope > .fg__group > .fg__grouphead")];
      const perSubject = new Map<string, number>();
      const ends: { el: HTMLElement; b: Box; to: Box; id: string }[] = [];
      for (const el of tops) {
        const b = box(el);
        const id = el.dataset.card;
        const of = id ? [...(rels.get(id)?.of ?? [])] : [];
        // A group's line goes to the frame of the subjects; a card's to each subject it is related to.
        const targets = many && of.length ? of.map((s) => subjectBox.get(s)).filter((x): x is Box => !!x) : [F];
        for (const to of targets) {
          const k = `${to.x},${to.y}`;
          perSubject.set(k, (perSubject.get(k) ?? 0) + 1);
          ends.push({ el, b, to, id: id ?? `group:${el.dataset.group}` });
        }
      }
      const seenAt = new Map<string, number>();
      for (const e of ends) {
        const k = `${e.to.x},${e.to.y}`;
        const n = perSubject.get(k)!;
        const i = seenAt.get(k) ?? 0;
        seenAt.set(k, i + 1);
        const spread = Math.min(e.to.h - 12, (n - 1) * 5);
        const ty = e.to.y + e.to.h / 2 + (n > 1 ? -spread / 2 + (spread * i) / (n - 1) : 0);
        const ny = e.b.y + e.b.h / 2;
        // Stacked, every line runs in the left margin, from the left edge of one to the left edge of the other.
        const loop = (x1: number, y1: number, x2: number, y2: number) => { const m = Math.min(x1, x2) - 16; return `M${x1.toFixed(1)} ${y1.toFixed(1)} C${m.toFixed(1)} ${y1.toFixed(1)}, ${m.toFixed(1)} ${y2.toFixed(1)}, ${(x2 - 5).toFixed(1)} ${y2.toFixed(1)}`; };
        const d = stackedNow
          ? (side === "users" ? loop(e.b.x, ny, e.to.x, ty) : loop(e.to.x, ty, e.b.x, ny))
          : side === "users" ? curve(e.b.x + e.b.w, ny, e.to.x - 5, ty) : curve(e.to.x + e.to.w, ty, e.b.x - 5, ny);
        const isGroup = !e.el.dataset.card;
        const count = Number(e.el.dataset.count ?? 1);
        const kind = isGroup ? (e.el.dataset.kind ?? "proof") : (rels.get(e.id)?.kind ?? "proof");
        segs.push({ d, cls: `fg__wire fg__edge fg__edge--${kind}${isGroup ? " fg__edge--group" : ""}`, edge: side === "users" ? `${e.id}>` : `>${e.id}`, width: isGroup ? 1.6 + Math.min(4.4, Math.log2(count) * 0.8) : undefined });
        paths[e.id] = paths[e.id] ? `${paths[e.id]} ${d}` : d;
        // A card inside an open group lights the group's own line.
        if (isGroup) for (const m of e.el.parentElement!.querySelectorAll<HTMLElement>(".fg__card")) paths[m.dataset.card!] = paths[e.id];
      }
    }
    // Between the subjects of one paragraph: each line runs down from a step to one it uses.
    model.inner.forEach((e, i) => {
      const a = subjectBox.get(e.from), b = subjectBox.get(e.to);
      if (!a || !b) return;
      const bulge = 14 + (i % 3) * 9;
      const x = a.x + a.w - 14 - (i % 4) * 12;
      const d = b.y > a.y + a.h + 30 || b.y < a.y
        ? `M${x} ${a.y + a.h} C${x + bulge * 3} ${a.y + a.h + 20}, ${x + bulge * 3} ${b.y - 20}, ${x} ${b.y - 5}`
        : `M${x} ${a.y + a.h} L${x} ${b.y - 5}`;
      segs.push({ d, cls: `fg__wire fg__edge fg__edge--${e.kind ?? "proof"} fg__inner`, edge: `${e.from}>${e.to}` });
    });
    setDrawn({ w: Math.ceil(origin.width / zoom), h: Math.ceil(origin.height / zoom), segs, paths, boxes });
  }, [zoom, model, many]);

  useLayoutEffect(() => {
    measure();
    const w = world.current;
    if (!w) return;
    // Fonts and typeset titles can arrive after the first layout.
    const ro = new ResizeObserver(() => measure());
    ro.observe(w);
    for (const c of w.querySelectorAll(".fg__card, .fg__grouphead")) ro.observe(c);
    return () => ro.disconnect();
  }, [measure, key, leftItems, rightItems, sideW, subjectW]);

  // If the estimate let through more than fits, group more. The reader's own opened groups may overflow: they scroll.
  useLayoutEffect(() => {
    const el = scroller.current, w = world.current;
    if (!el || !w || opened.size || tight >= 6) return;
    const grouped = (items: Item[]) => items.every((it) => it.type === "group");
    if (w.getBoundingClientRect().height > el.clientHeight + 2 && !(grouped(leftItems) && grouped(rightItems))) setTight((t) => t + 1);
  }, [drawn, opened, tight, leftItems, rightItems]);

  // The subject is in the middle whenever it changes; a reader's own scrolling is kept until then.
  const centre = useCallback(() => {
    const el = scroller.current, w = world.current;
    const frame = w?.querySelector<HTMLElement>(".fg__subjects");
    if (!el || !w || !frame) return;
    const o = w.getBoundingClientRect(), r = frame.getBoundingClientRect();
    const cx = r.left - o.left + r.width / 2, cy = r.top - o.top + r.height / 2;
    // Stacked on a phone the drawing reads from its top: what uses the subject, the subject, what it uses.
    const y = w.classList.contains("fg__world--narrow") ? 0 : r.height > el.clientHeight - 24 ? r.top - o.top - 12 : cy - el.clientHeight / 2;
    el.scrollTo({ left: Math.max(0, cx - el.clientWidth / 2), top: Math.max(0, y) });
    moved.current = false;
  }, []);
  useLayoutEffect(() => { centre(); }, [key, centre]);
  useLayoutEffect(() => { if (!moved.current && !opened.size) centre(); }, [drawn?.h, drawn?.w, size.w, size.h, centre, opened]);

  const readView = useCallback(() => {
    const el = scroller.current;
    if (el) setView({ x: el.scrollLeft, y: el.scrollTop, w: el.clientWidth, h: el.clientHeight });
  }, []);
  useLayoutEffect(readView, [readView, drawn, size]);

  // Drag to pan. A drag that starts on a card and moves is a pan, not a click.
  const drag = useRef<{ x: number; y: number; left: number; top: number; far: boolean } | null>(null);
  const onPointerDown = (e: React.PointerEvent) => {
    if (e.button !== 0 || (e.target as HTMLElement).closest(".fg__mini, .fg__tools")) return;
    const el = scroller.current!;
    drag.current = { x: e.clientX, y: e.clientY, left: el.scrollLeft, top: el.scrollTop, far: false };
  };
  const onPointerMove = (e: React.PointerEvent) => {
    const d = drag.current;
    if (!d) return;
    const dx = e.clientX - d.x, dy = e.clientY - d.y;
    if (!d.far && Math.hypot(dx, dy) < 5) return;
    if (!d.far) { d.far = true; scroller.current!.setPointerCapture(e.pointerId); scroller.current!.classList.add("is-panning"); }
    moved.current = true;
    scroller.current!.scrollTo({ left: d.left - dx, top: d.top - dy });
  };
  const suppressClick = useRef(false);
  const onPointerUp = (e: React.PointerEvent) => {
    const d = drag.current;
    drag.current = null;
    if (d?.far) {
      suppressClick.current = true;
      window.setTimeout(() => { suppressClick.current = false; }, 0);
      scroller.current!.releasePointerCapture(e.pointerId);
      scroller.current!.classList.remove("is-panning");
    }
  };
  // Ctrl or ⌘ with the wheel zooms; the wheel alone scrolls, as everywhere.
  useEffect(() => {
    const el = scroller.current;
    if (!el) return;
    const wheel = (e: WheelEvent) => {
      moved.current = true;
      if (!(e.ctrlKey || e.metaKey)) return;
      e.preventDefault();
      setZoomAt((z) => Math.max(0, Math.min(ZOOMS.length - 1, z + (e.deltaY < 0 ? 1 : -1))));
    };
    const keyed = (e: KeyboardEvent) => { if (e.key.startsWith("Arrow") || e.key.startsWith("Page") || e.key === "Home" || e.key === "End" || e.key === " ") moved.current = true; };
    el.addEventListener("wheel", wheel, { passive: false });
    el.addEventListener("keydown", keyed);
    return () => { el.removeEventListener("wheel", wheel); el.removeEventListener("keydown", keyed); };
  }, []);

  const hover = (id: string | null) => { setHot(id); onHover?.(id); };
  const choose = (id: string) => { if (!suppressClick.current) onSubject(id); };
  // Opening a group keeps it in view: the drawing may now be taller than its area, and scrolls.
  const toggle = (side: Side, path: string) => {
    if (suppressClick.current) return;
    const k = `${side}:${path}`;
    setOpened((was) => {
      const next = new Set(was);
      if (next.has(k)) { for (const o of was) if (o === k || o.startsWith(`${k}/`)) next.delete(o); } else next.add(k);
      return next;
    });
    moved.current = true;
    requestAnimationFrame(() => requestAnimationFrame(() => {
      const sc = scroller.current;
      const el = world.current?.querySelector<HTMLElement>(`.fg__side[data-band="${side}"] .fg__group[data-group="${CSS.escape(path)}"]`);
      if (!sc || !el) return;
      // Only the graph's own area moves: the page and the paper stay where they are.
      const v = sc.getBoundingClientRect(), r = el.getBoundingClientRect();
      if (r.height > v.height - 16 || r.top < v.top + 8) sc.scrollTop += r.top - v.top - 8;
      else if (r.bottom > v.bottom - 8) sc.scrollTop += r.bottom - v.bottom + 8;
    }));
  };

  const litSet = useMemo(() => new Set(lit ?? []), [lit]);
  const hotOf = hot ? (model.users.get(hot)?.of ?? model.uses.get(hot)?.of) : null;

  const renderCard = (id: string, band: Side | "subject", kind?: string) => {
    const c = card(id)!;
    const subject = band === "subject";
    const cls = ["fg__card", `fg__card--${c.role}`, subject ? "is-subject" : "", litSet.has(id) ? "is-lit" : "", held === id ? "is-held" : "", hot === id ? "is-hot" : "", subject && hotOf?.has(id) ? "is-related" : ""].filter(Boolean).join(" ");
    const said = `${c.kicker ?? words(c.role).one}${c.seen === "later" ? ", stated later in the paper" : c.seen === "before" ? ", already read" : ""}`;
    return (
      <button
        key={id}
        type="button"
        className={cls}
        data-card={id}
        data-band={band}
        data-role={c.role}
        data-kind={kind}
        data-seen={c.seen}
        aria-current={subject ? "true" : undefined}
        title={subject ? undefined : said}
        style={c.tone ? ({ "--fg-tone": c.tone } as React.CSSProperties) : undefined}
        onClick={() => choose(id)}
        onMouseEnter={() => hover(id)}
        onMouseLeave={() => hover(null)}
        onFocus={() => hover(id)}
        onBlur={() => hover(null)}
      >
        {subject && <span className="fg__kicker">{c.kicker ?? words(c.role).one}</span>}
        <span className="fg__title">
          {!subject && c.kicker && <span className="fg__tag">{c.kicker}</span>}
          {renderTitle ? renderTitle(c) : c.title}
        </span>
        {subject && !many && c.name && <code className="fg__name">{c.name.replace(/([._])/g, "$1\u200b")}</code>}
      </button>
    );
  };

  const renderItems = (side: Side, items: Item[], rels: Map<string, Rel>): ReactNode =>
    items.map((it) => {
      if (it.type === "node") return renderCard(it.id, side, rels.get(it.id)?.kind);
      const kinds = new Set(it.ids.map((id) => rels.get(id)?.kind ?? "proof"));
      const kind = kinds.has("argument") ? "argument" : kinds.size === 1 && kinds.has("statement") ? "statement" : "proof";
      return (
        <div key={`g:${it.key}`} className={`fg__group${it.open ? " is-open" : ""}`} data-group={it.key} style={it.tone ? ({ "--fg-tone": it.tone } as React.CSSProperties) : undefined}>
          <button
            type="button"
            className={`fg__grouphead${it.role ? ` fg__grouphead--${it.role}` : ""}`}
            data-group={it.key}
            data-count={it.ids.length}
            data-kind={kind}
            aria-expanded={it.open}
            title={it.open ? "Fold these back into one group" : `Show these ${it.ids.length} cards here`}
            onClick={() => toggle(side, it.key)}
          >
            <span className="fg__groupname">{it.name}{it.said && <span className="fg__groupkind"> {it.said}</span>}</span>
            <span className="fg__count">{it.ids.length}</span>
            <span className="fg__sign" aria-hidden="true">{it.open ? "−" : "+"}</span>
          </button>
          {it.open && <div className="fg__members">{renderItems(side, it.children, rels)}</div>}
        </div>
      );
    });

  const renderSide = (side: Side, items: Item[], ids: string[], rels: Map<string, Rel>) => (
    <div className="fg__side" data-band={side} data-total={ids.length} style={{ width: ids.length || stacked ? sideW : NOTE_W }}>
      {ids.length > 0
        ? <>
          <h4 className="fg__sidehead">{side === "users" ? (many ? "Use these" : "Use this") : (many ? "These use" : "This uses")} <span>{ids.length}</span></h4>
          {renderItems(side, items, rels)}
        </>
        : <p className="fg__edge-note" data-band-note={side}>{side === "users" ? `Nothing drawn here uses ${many ? "these" : "this"}.` : `${many ? "These use" : "This uses"} nothing else drawn here.`}</p>}
    </div>
  );

  const overflow = !!drawn && (drawn.h * zoom > view.h + 4 || drawn.w * zoom > view.w + 4);
  const mini = drawn ? Math.min(MINI_W / drawn.w, MINI_H / drawn.h) : 0;
  // A very tall drawing keeps an overview wide enough to read: its width is stretched to at least MINI_MIN_W.
  const miniX = drawn ? Math.max(mini, Math.min(MINI_W, MINI_MIN_W) / drawn.w) : 0;
  const miniMove = (e: React.PointerEvent<HTMLDivElement>) => {
    if (!drawn || !(e.buttons & 1)) return;
    const r = e.currentTarget.getBoundingClientRect();
    const el = scroller.current!;
    moved.current = true;
    el.scrollTo({ left: ((e.clientX - r.left) / miniX) * zoom - el.clientWidth / 2, top: ((e.clientY - r.top) / mini) * zoom - el.clientHeight / 2 });
  };
  const kinds = new Set([...model.users.values(), ...model.uses.values(), ...model.inner.map((e) => ({ kind: e.kind ?? "proof" }))].map((r) => r.kind));
  const groups = (items: Item[]) => items.filter((it) => it.type === "group").length;
  const roles = new Set([...model.left, ...model.right].map((id) => card(id)!.role));

  return (
    <div
      className="fg"
      data-subjects={key}
      data-users={model.left.length}
      data-uses={model.right.length}
      data-groups={groups(leftItems) + groups(rightItems)}
      data-opened={opened.size}
      data-cards={drawn?.boxes.filter((b) => b.band !== "group").length ?? 0}
      data-lines={drawn?.segs.filter((s) => s.edge).length ?? 0}
      data-overflow={overflow ? "true" : "false"}
    >
      {label && <p className="fg__label">{label}</p>}
      {(route || routeNote) && (
        <nav className="fg__route" aria-label="From this step to the main result">
          {route && route.length > 0
            ? <>
              <span className="fg__routeword">{route.length === 1 ? "The main result uses this directly:" : `${route.length} steps to the main result:`}</span>
              {route.map((id, i) => (
                <span key={id} className="fg__crumb">
                  <span aria-hidden="true">→</span>
                  <button type="button" onClick={() => onSubject(id)} className={i === route.length - 1 ? "is-main" : undefined}>{card(id) ? (renderTitle ? renderTitle(card(id)!) : card(id)!.title) : id}</button>
                </span>
              ))}
            </>
            : <span className="fg__routeword">{routeNote}</span>}
        </nav>
      )}
      <div
        className="fg__scroll"
        ref={scroller}
        tabIndex={0}
        role="group"
        aria-label="Graph: what uses this step, on the left, and what it uses, on the right. Scroll or drag to move."
        onScroll={readView}
        onPointerDown={onPointerDown}
        onPointerMove={onPointerMove}
        onPointerUp={onPointerUp}
        onPointerCancel={onPointerUp}
      >
        <div className={`fg__world${narrow ? " fg__world--narrow" : ""}`} ref={world} style={{ zoom, columnGap: gap }}>
          {drawn && (
            <svg className="fg__lines" width={drawn.w} height={drawn.h} aria-hidden="true">
              <defs>
                <marker id="fg-arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" markerUnits="userSpaceOnUse" orient="auto"><path d="M0 0.6 L7.4 4 L0 7.4 z" className="fg__arrow" /></marker>
                <marker id="fg-arrow-hot" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="8" markerHeight="8" markerUnits="userSpaceOnUse" orient="auto"><path d="M0 0.6 L7.4 4 L0 7.4 z" className="fg__arrow fg__arrow--hot" /></marker>
              </defs>
              {drawn.segs.map((s, i) => <path key={i} d={s.d} className={s.cls} data-edge={s.edge} markerEnd="url(#fg-arrow)" style={s.width ? { strokeWidth: s.width } : undefined} />)}
              {hot && drawn.paths[hot] && <path d={drawn.paths[hot]} className="fg__hotline" markerEnd="url(#fg-arrow-hot)" />}
            </svg>
          )}
          {model.subj.length === 0
            ? <p className="fg__none">Nothing is drawn for this place in the paper.</p>
            : <>
              {renderSide("users", leftItems, model.left, model.users)}
              <div className={`fg__subjects${many ? " fg__subjects--many" : ""}`} data-count={model.subj.length} style={{ width: stacked ? sideW : subjectW }}>
                {many && <h4 className="fg__sidehead">{props.manyLabel ?? "Stated in this paragraph"} <span>{model.subj.length}</span></h4>}
                {model.subj.map((id) => renderCard(id, "subject"))}
              </div>
              {renderSide("uses", rightItems, model.right, model.uses)}
            </>}
        </div>
      </div>
      <div className="fg__tools" role="group" aria-label="Move the graph">
        <button type="button" onClick={() => setZoomAt((z) => Math.max(0, z - 1))} disabled={zoomAt === 0} aria-label="Smaller">−</button>
        <button type="button" onClick={() => setZoomAt((z) => Math.min(ZOOMS.length - 1, z + 1))} disabled={zoomAt === ZOOMS.length - 1} aria-label="Larger">+</button>
        <button type="button" onClick={() => { setZoomAt(1); setOpened(new Set()); requestAnimationFrame(centre); }} title="Fold every group and bring the subject back to the middle">Fit</button>
      </div>
      {overflow && drawn && (
        <div
          className="fg__mini"
          style={{ width: drawn.w * miniX, height: drawn.h * mini }}
          role="img"
          aria-label="Overview of the whole drawing; drag to move the view"
          onPointerDown={(e) => { e.currentTarget.setPointerCapture(e.pointerId); miniMove(e); }}
          onPointerMove={miniMove}
        >
          {drawn.boxes.map((b) => (
            <i key={b.band + b.id} className={b.band === "subject" ? "is-subject" : hot === b.id ? "is-hot" : undefined} style={{ left: b.box.x * miniX, top: b.box.y * mini, width: Math.max(2, b.box.w * miniX), height: Math.max(2, b.box.h * mini) }} />
          ))}
          <b style={{ left: (view.x / zoom) * miniX, top: (view.y / zoom) * mini, width: Math.min(drawn.w, view.w / zoom) * miniX, height: Math.min(drawn.h, view.h / zoom) * mini }} />
        </div>
      )}
      {model.subj.length > 0 && (
        <p className={`fg__key${overflow ? " fg__key--mini" : ""}`}>
          <span><i className="fg__keyline" /> uses, left to right</span>
          {kinds.has("argument") && kinds.size > 1 && <span><i className="fg__keyline fg__keyline--argument" /> the paper's argument</span>}
          {kinds.has("statement") && kinds.size > 1 && <span><i className="fg__keyline fg__keyline--statement" /> statement only</span>}
          {(roles.has("helper") || roles.has("library")) && <span><i className="fg__keybox fg__keybox--helper" /> Lean helper</span>}
          {roles.has("definition") && <span><i className="fg__keybox fg__keybox--definition" /> definition</span>}
          {groups(leftItems) + groups(rightItems) > 0 && <span><i className="fg__keybox fg__keybox--group" /> group, opens here</span>}
        </p>
      )}
    </div>
  );
}

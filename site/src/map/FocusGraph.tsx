// The focus graph: one subject (a step, a declaration, or the steps of one paragraph) with
// everything that uses it above and everything it uses below. Every direct neighbour is drawn
// with its line; neighbours are grouped by what they are; the drawing scrolls when it is larger
// than its pane, and a small overview shows where the view is. The same file serves the
// Quartic Reader, the SK and Erdős #257 readers and Proof Reader: docs/graph-pane.md is its
// specification, and a change here should be copied to the other two.
//
// Layout is the browser's own (grids of whole, wrapped titles); the lines are measured from
// the cards after layout, so a title of any length, or one with typeset mathematics, is never
// cut and never estimated.

import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type ReactNode } from "react";
import "./focus-graph.css";

/** What a card is, for the reader: this decides its group and its look. */
export type FGRole = "result" | "step" | "definition" | "helper" | "library" | "cited" | "open";

export interface FGCard {
  id: string;
  /** Plain words, shown whole. */
  title: string;
  /** The raw Lean name, small under the title. */
  name?: string;
  role: FGRole;
  /** A short line over the title: "Theorem 2.1", "Lean helper", "Definition". */
  kicker?: string;
  /** The topic colour this card shares with its phrases in the paper (any CSS colour). */
  tone?: string;
  /** Where the paper states it, against the reading position. */
  seen?: "before" | "here" | "later";
}

/** `from` uses `to`. `statement`: only the statement of `from` names `to`; `proof`: its proof or body does;
 *  `argument`: the paper's own argument, as authored. */
export interface FGEdge { from: string; to: string; kind?: "proof" | "statement" | "argument" }

export interface FGRoleWords { order: number; one: string; uses: string; usedBy: string }

export const FG_ROLES: Record<FGRole, FGRoleWords> = {
  result: { order: 0, one: "Paper result", uses: "Results of the paper it uses", usedBy: "Results of the paper that use it" },
  step: { order: 1, one: "Step", uses: "Steps of the argument it uses", usedBy: "Steps of the argument that use it" },
  definition: { order: 2, one: "Definition", uses: "Definitions it uses", usedBy: "Definitions that use it" },
  cited: { order: 3, one: "Cited result", uses: "Cited results it uses", usedBy: "Cited results that use it" },
  open: { order: 4, one: "Open question", uses: "Open questions it rests on", usedBy: "Open questions that use it" },
  helper: { order: 5, one: "Lean helper", uses: "Lean helper lemmas it uses", usedBy: "Lean helper lemmas that use it" },
  library: { order: 6, one: "Library fact", uses: "Library facts it uses", usedBy: "Library facts that use it" },
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
interface Seg { d: string; cls: string; edge?: string }
interface Drawn { w: number; h: number; segs: Seg[]; paths: Record<string, string>; boxes: { id: string; box: Box; band: string }[] }

const ZOOMS = [0.93, 1, 1.15, 1.3, 1.5];
const CARD_MIN = 178;
const CARD_MAX = 248;
const GAP = 12;
const PAD = 22;
/** A group's frame: its padding and border. */
const FRAME = 40;
/** The frame and the extra left padding of the drawing, where the lines run. */
const GROUP_CHROME = FRAME + 12;
const MINI_W = 132;
const MINI_H = 150;
const MINI_MIN_W = 72;


export function FocusGraph(props: FocusGraphProps) {
  const { subjects, card, edges, route, routeNote, label, lit, held, onSubject, onHover, renderTitle } = props;
  const scroller = useRef<HTMLDivElement>(null);
  const world = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(0);
  const [zoomAt, setZoomAt] = useState(1);
  const zoom = ZOOMS[zoomAt];
  const [drawn, setDrawn] = useState<Drawn | null>(null);
  const [hot, setHot] = useState<string | null>(null);
  const [view, setView] = useState<Box>({ x: 0, y: 0, w: 0, h: 0 });
  const moved = useRef(false);

  const words = useCallback((role: FGRole): FGRoleWords => ({ ...FG_ROLES[role], ...(props.roles?.[role] ?? {}) }), [props.roles]);

  // What is drawn: the subjects, in ranks when they use one another; above, the cards that use
  // a subject; below, the cards a subject uses. A card that both uses and is used is drawn above.
  const model = useMemo(() => {
    const subj = subjects.filter((id, i) => card(id) && subjects.indexOf(id) === i);
    const isSubject = new Set(subj);
    const users = new Map<string, { kind: string; of: Set<string> }>();
    const uses = new Map<string, { kind: string; of: Set<string> }>();
    const inner: FGEdge[] = [];
    const add = (into: typeof users, id: string, subject: string, kind = "proof") => {
      if (!card(id)) return;
      const row = into.get(id) ?? { kind, of: new Set<string>() };
      // A statement-only use is said so only if no proof or body also uses it.
      if (kind !== "statement") row.kind = kind;
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
    // Ranks of the subjects: a subject sits under every subject that uses it.
    const rank = new Map(subj.map((id) => [id, 0]));
    for (let pass = 0; pass < subj.length; pass++) {
      let changed = false;
      for (const e of inner) {
        const want = (rank.get(e.from) ?? 0) + 1;
        if ((rank.get(e.to) ?? 0) < want && want <= subj.length) { rank.set(e.to, want); changed = true; }
      }
      if (!changed) break;
    }
    const ranks: string[][] = [];
    for (const id of subj) (ranks[rank.get(id) ?? 0] ??= []).push(id);
    const group = (side: Map<string, { kind: string; of: Set<string> }>) => {
      const by = new Map<FGRole, string[]>();
      for (const id of side.keys()) {
        const role = card(id)!.role;
        by.set(role, [...(by.get(role) ?? []), id]);
      }
      return [...by.entries()].sort((a, b) => words(a[0]).order - words(b[0]).order).map(([role, ids]) => ({ role, ids }));
    };
    return { subj, ranks: ranks.filter(Boolean), inner, users, uses, above: group(users), below: group(uses) };
  }, [subjects, card, edges, words]);

  const key = model.subj.join("|");
  const many = model.subj.length > 1;

  // How many cards a row holds, and how wide each is, for the room there is.
  // A drawing taller than its area keeps a column on the right for the overview, so no card lies under it.
  const tall = !!drawn && drawn.h * zoom > view.h + 4;
  const reserve = tall ? MINI_W + 18 : 0;
  const room = Math.max(CARD_MIN, ((width || 600) - reserve) / zoom - 2 * PAD - GROUP_CHROME);
  const cols = Math.max(1, Math.floor((room + GAP) / (CARD_MIN + GAP)));
  const biggest = Math.max(1, ...model.above.map((g) => g.ids.length), ...model.below.map((g) => g.ids.length), ...model.ranks.map((r) => r.length));
  const used = Math.min(cols, biggest);
  const cardW = Math.floor(Math.min(CARD_MAX, (room - (used - 1) * GAP) / used));

  useLayoutEffect(() => {
    const el = scroller.current;
    if (!el) return;
    const read = () => setWidth(el.clientWidth);
    read();
    const ro = new ResizeObserver(read);
    ro.observe(el);
    return () => ro.disconnect();
  }, []);

  // The lines, measured from the cards as the browser laid them out.
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
    const S = box(frame);
    const sx = Math.round(S.x + S.w / 2);
    const segs: Seg[] = [];
    const paths: Record<string, string> = {};
    const boxes: Drawn["boxes"] = [];
    const line = (pts: [number, number][]) => pts.map(([x, y], i) => `${i ? "L" : "M"}${Math.round(x)} ${Math.round(y)}`).join(" ");
    for (const el of w.querySelectorAll<HTMLElement>(".fg__card")) boxes.push({ id: el.dataset.card!, box: box(el), band: el.dataset.band! });

    for (const side of ["users", "uses"] as const) {
      const band = w.querySelector(`.fg__band[data-band="${side}"]`);
      if (!band) continue;
      const B = box(band);
      const up = side === "users";
      const mx = B.x - 12;
      const busY = up ? (B.y + B.h + S.y) / 2 : (S.y + S.h + B.y) / 2;
      const stubs: number[] = [];
      const row = (band as HTMLElement).dataset.flow === "row";
      const spines: number[] = [];
      for (const g of band.querySelectorAll<HTMLElement>(".fg__group")) {
        const G = box(g);
        const spine = G.x + 12;
        // Side by side, each group's own line meets the bus; stacked, a stub joins it to the shared line on the left.
        const stubY = row ? busY : up ? G.y + G.h - 12 : G.y + 17;
        if (row) spines.push(spine);
        else {
          stubs.push(stubY);
          segs.push({ d: line([[mx, stubY], [spine, stubY]]), cls: "fg__wire" });
        }
        const rows = new Map<number, { el: HTMLElement; b: Box }[]>();
        for (const c of g.querySelectorAll<HTMLElement>(".fg__card")) {
          const b = box(c);
          const at = Math.round(b.y);
          rows.set(at, [...(rows.get(at) ?? []), { el: c, b }]);
        }
        let far = stubY;
        for (const [, cards] of rows) {
          const top = Math.min(...cards.map((c) => c.b.y));
          const bottom = Math.max(...cards.map((c) => c.b.y + c.b.h));
          const railY = up ? bottom + 9 : top - 9;
          far = up ? Math.min(far, railY) : Math.max(far, railY);
          const last = Math.max(...cards.map((c) => c.b.x + c.b.w / 2));
          segs.push({ d: line([[spine, railY], [last, railY]]), cls: "fg__wire" });
          for (const c of cards) {
            const cx = c.b.x + c.b.w / 2;
            const id = c.el.dataset.card!;
            const kind = c.el.dataset.kind ?? "proof";
            const edge = up ? `${id}>` : `>${id}`;
            segs.push({ d: line(up ? [[cx, c.b.y + c.b.h], [cx, railY]] : [[cx, railY], [cx, c.b.y]]), cls: `fg__wire fg__tick fg__tick--${kind}`, edge });
            const join: [number, number][] = row ? [[spine, busY]] : [[spine, stubY], [mx, stubY], [mx, busY]];
            const whole: [number, number][] = up
              ? [[cx, c.b.y + c.b.h], [cx, railY], [spine, railY], ...join, [sx, busY], [sx, S.y]]
              : [[sx, S.y + S.h], [sx, busY], ...[...join].reverse(), [spine, railY], [cx, railY], [cx, c.b.y]];
            paths[id] = line(whole);
          }
        }
        segs.push({ d: line([[spine, stubY], [spine, far]]), cls: "fg__wire" });
      }
      if (spines.length) {
        segs.push({ d: line([[Math.min(sx, ...spines), busY], [Math.max(sx, ...spines), busY]]), cls: "fg__wire fg__trunk" });
        segs.push({ d: line([[sx, busY], [sx, up ? S.y : S.y + S.h]]), cls: "fg__wire fg__trunk" });
      }
      if (stubs.length) {
        const end = up ? Math.min(...stubs) : Math.max(...stubs);
        segs.push({ d: line([[mx, end], [mx, busY], [sx, busY], [sx, up ? S.y : S.y + S.h]]), cls: "fg__wire fg__trunk" });
      }
    }
    // Between the subjects of one paragraph: each line drops from a step to one it uses.
    const at = new Map(boxes.filter((b) => b.band === "subject").map((b) => [b.id, b.box]));
    model.inner.forEach((e, i) => {
      const a = at.get(e.from), b = at.get(e.to);
      if (!a || !b) return;
      const lane = 8 + (i % 4) * 4;
      const ax = a.x + a.w / 2 + ((i % 3) - 1) * 10, bx = b.x + b.w / 2 + ((i % 3) - 1) * 10;
      const d = line([[ax, a.y + a.h], [ax, b.y - lane], [bx, b.y - lane], [bx, b.y]]);
      segs.push({ d, cls: `fg__wire fg__tick fg__tick--${e.kind ?? "proof"} fg__inner`, edge: `${e.from}>${e.to}` });
    });
    setDrawn({ w: Math.ceil(origin.width / zoom), h: Math.ceil(origin.height / zoom), segs, paths, boxes });
  }, [zoom, model]);

  useLayoutEffect(() => {
    measure();
    const w = world.current;
    if (!w) return;
    // Fonts and typeset titles can arrive after the first layout.
    const ro = new ResizeObserver(() => measure());
    ro.observe(w);
    for (const c of w.querySelectorAll(".fg__card")) ro.observe(c);
    return () => ro.disconnect();
  }, [measure, key, cardW, used]);

  // The subject comes to the middle whenever it changes; a reader's own scrolling is kept until then.
  const centre = useCallback(() => {
    const el = scroller.current, w = world.current;
    const frame = w?.querySelector<HTMLElement>(".fg__subjects");
    if (!el || !w || !frame) return;
    const o = w.getBoundingClientRect(), r = frame.getBoundingClientRect();
    const cx = r.left - o.left + r.width / 2, top = r.top - o.top, cy = top + r.height / 2;
    // Parents above, as many neighbours as fit below: the subject sits a little above the middle,
    // and wholly in view when it is taller than that leaves room for.
    let y = cy - el.clientHeight * 0.42;
    // Nothing drawn below: the room goes to what uses it, above.
    if (!w.querySelector('.fg__band[data-band="uses"]')) y = Math.max(top + r.height + 64 - el.clientHeight, Math.min(y, top - 12));
    if (r.height > el.clientHeight * 0.8) y = top - 12;
    el.scrollTo({ left: Math.max(0, cx - el.clientWidth / 2), top: Math.max(0, y) });
    moved.current = false;
  }, []);
  useLayoutEffect(() => { centre(); }, [key, centre]);
  useLayoutEffect(() => { if (!moved.current) centre(); }, [drawn?.h, drawn?.w, width, centre]);

  const readView = useCallback(() => {
    const el = scroller.current;
    if (el) setView({ x: el.scrollLeft, y: el.scrollTop, w: el.clientWidth, h: el.clientHeight });
  }, []);
  useLayoutEffect(readView, [readView, drawn, width]);

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

  const litSet = useMemo(() => new Set(lit ?? []), [lit]);
  const hotOf = hot ? (model.users.get(hot)?.of ?? model.uses.get(hot)?.of) : null;

  const renderCard = (id: string, band: "users" | "subject" | "uses", kind?: string) => {
    const c = card(id)!;
    const w = words(c.role);
    const cls = ["fg__card", `fg__card--${c.role}`, band === "subject" ? "is-subject" : "", litSet.has(id) ? "is-lit" : "", held === id ? "is-held" : "", hot === id ? "is-hot" : "", band === "subject" && hotOf?.has(id) ? "is-related" : ""].filter(Boolean).join(" ");
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
        aria-current={band === "subject" ? "true" : undefined}
        style={{ width: cardW, ...(c.tone ? ({ "--fg-tone": c.tone } as React.CSSProperties) : {}) }}
        onClick={() => choose(id)}
        onMouseEnter={() => hover(id)}
        onMouseLeave={() => hover(null)}
        onFocus={() => hover(id)}
        onBlur={() => hover(null)}
      >
        <span className="fg__kicker">
          <span>{c.kicker ?? w.one}</span>
          {c.seen === "later" && <span className="fg__seen">stated later</span>}
          {c.seen === "before" && <span className="fg__seen">read</span>}
        </span>
        <span className="fg__title">{renderTitle ? renderTitle(c) : c.title}</span>
        {c.name && <code className="fg__name">{c.name}</code>}
      </button>
    );
  };

  // Groups stand side by side when they all fit in one row; otherwise they stack on one left edge.
  const sideBySide = (groups: { ids: string[] }[]) =>
    groups.length > 1 && groups.reduce((sum, g) => sum + Math.min(used, g.ids.length) * (cardW + GAP) - GAP + 40, (groups.length - 1) * 16) <= room + FRAME;

  const renderBand = (side: "users" | "uses", groups: { role: FGRole; ids: string[] }[], rows: Map<string, { kind: string }>) =>
    groups.length > 0 && (
      <div className="fg__band" data-band={side} data-flow={sideBySide(groups) ? "row" : "column"}>
        {groups.map((g) => {
          const w = words(g.role);
          const text = side === "uses" ? w.uses : w.usedBy;
          return (
            <section key={g.role} className={`fg__group fg__group--${g.role}`} data-group={g.role} aria-label={text}>
              <h4 className="fg__grouphead">{many ? text.replace(/\bit uses\b/, "these use").replace(/\buse it\b/, "use these").replace(/\bit rests on\b/, "these rest on") : text} <span>{g.ids.length}</span></h4>
              <div className="fg__grid" style={{ gridTemplateColumns: `repeat(${Math.min(used, g.ids.length)}, ${cardW}px)` }}>
                {g.ids.map((id) => renderCard(id, side, rows.get(id)?.kind))}
              </div>
            </section>
          );
        })}
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
  const kinds = new Set([...model.users.values(), ...model.uses.values()].map((r) => r.kind));

  return (
    <div className="fg" data-subjects={key} data-cards={(drawn?.boxes.length ?? 0)} data-lines={drawn?.segs.filter((s) => s.edge).length ?? 0} data-overflow={overflow ? "true" : "false"}>
      {label && <p className="fg__label">{label}</p>}
      {(route || routeNote) && (
        <nav className="fg__route" aria-label="From this step to the main result">
          {route && route.length > 0
            ? <>
              <span className="fg__routeword">{route.length === 1 ? "The main result uses this directly:" : `${route.length} steps to the main result:`}</span>
              {route.map((id, i) => (
                <span key={id} className="fg__crumb">
                  <span aria-hidden="true">↑</span>
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
        aria-label="Graph: what uses this step, above, and what it uses, below. Scroll or drag to move."
        onScroll={readView}
        onPointerDown={onPointerDown}
        onPointerMove={onPointerMove}
        onPointerUp={onPointerUp}
        onPointerCancel={onPointerUp}
      >
        <div className="fg__world" ref={world} style={{ zoom, paddingRight: PAD + reserve / zoom }}>
          {drawn && (
            <svg className="fg__lines" width={drawn.w} height={drawn.h} aria-hidden="true">
              {drawn.segs.map((s, i) => <path key={i} d={s.d} className={s.cls} data-edge={s.edge} />)}
              {hot && drawn.paths[hot] && <path d={drawn.paths[hot]} className="fg__hotline" />}
            </svg>
          )}
          {model.subj.length === 0
            ? <p className="fg__none">Nothing is drawn for this place in the paper.</p>
            : <>
              {renderBand("users", model.above, model.users)}
              {model.above.length === 0 && <p className="fg__edge-note" data-band-note="users">Nothing drawn here uses {many ? "these" : "this"}.</p>}
              <div className={`fg__subjects${many ? " fg__subjects--many" : ""}`} data-count={model.subj.length}>
                {many && <h4 className="fg__grouphead">{props.manyLabel ?? "Stated in this paragraph"} <span>{model.subj.length}</span></h4>}
                {model.ranks.map((ids, i) => <div key={i} className="fg__rank" style={{ maxWidth: used * (cardW + GAP) - GAP }}>{ids.map((id) => renderCard(id, "subject"))}</div>)}
              </div>
              {renderBand("uses", model.below, model.uses)}
              {model.below.length === 0 && <p className="fg__edge-note" data-band-note="uses">{many ? "These use" : "This uses"} nothing else drawn here.</p>}
            </>}
        </div>
      </div>
      <div className="fg__tools" role="group" aria-label="Move the graph">
        <button type="button" onClick={() => setZoomAt((z) => Math.max(0, z - 1))} disabled={zoomAt === 0} aria-label="Smaller">−</button>
        <button type="button" onClick={() => setZoomAt((z) => Math.min(ZOOMS.length - 1, z + 1))} disabled={zoomAt === ZOOMS.length - 1} aria-label="Larger">+</button>
        <button type="button" onClick={() => { setZoomAt(1); requestAnimationFrame(centre); }} title="Bring the subject back to the middle">Centre</button>
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
        <p className="fg__key">
          A line runs down from a card to one it uses.
          {kinds.has("statement") && kinds.size > 1 && <> <i className="fg__keyline fg__keyline--statement" /> used in the statement only <i className="fg__keyline" /> used in the proof or definition.</>}
          {" "}Click a card to put it in the middle.
        </p>
      )}
    </div>
  );
}

// The declaration among its neighbours: what uses it on the left, what it uses on the
// right, with real lines. An arrow runs from a name into the declaration that uses it,
// as lines run on the argument map. Walking opens the chosen declaration at its head;
// Back walks home.

import { useLayoutEffect, useMemo, useRef, useState } from "react";
import type { LeanDeclaration } from "../api/lean";
import { navigate, routeHref } from "../app/router";
import { dependencyWords, fetchModule, kindWord, type LeanShell } from "./data";
import { Breakable } from "./ReadingStrip";
import { findDecl, type DeclRow } from "./resolve";

const SIDE_LIMIT = 12;

interface Walk {
  to: string;
  from: string;
  toRect: DOMRect;
  fromRect: DOMRect;
  at: number;
}

/** The step in progress, read once by the picture that the step opens. */
let walking: Walk | null = null;

const reduced = () => typeof window.matchMedia === "function" && window.matchMedia("(prefers-reduced-motion: reduce)").matches;

function moveFrom(element: HTMLElement, rect: DOMRect): void {
  const now = element.getBoundingClientRect();
  element.animate([{ transform: `translate(${rect.left - now.left}px, ${rect.top - now.top}px)` }, { transform: "none" }], { duration: 320, easing: "cubic-bezier(0.45, 0, 0.2, 1)" });
}

/** An element's place inside `host`, unaffected by a move in progress. */
function place(element: HTMLElement, host: HTMLElement) {
  let left = 0;
  let top = 0;
  for (let at: HTMLElement | null = element; at && at !== host; at = at.offsetParent as HTMLElement | null) {
    left += at.offsetLeft;
    top += at.offsetTop;
  }
  return { left, top, width: element.offsetWidth, height: element.offsetHeight };
}

interface Line {
  id: string;
  d: string;
  /** Where the arrow ends, and which way it points. */
  tip: string;
}

function Tile({ row, record, side, onWalk, onHover }: { row: DeclRow; record?: string; side: string; onWalk(row: DeclRow, element: HTMLElement): void; onHover(id: string | null): void }) {
  const id = `${side}:${row.name}`;
  return (
    <a
      className="lean-tile"
      data-tile={id}
      data-name={row.name}
      href={routeHref({ view: "lean", module: row.module, decl: row.name })}
      onPointerEnter={() => {
        onHover(id);
        void fetchModule(row.module).catch(() => undefined);
      }}
      onPointerLeave={() => onHover(null)}
      onFocus={() => onHover(id)}
      onBlur={() => onHover(null)}
      onClick={(event) => {
        if (event.metaKey || event.ctrlKey || event.shiftKey) return;
        event.preventDefault();
        onWalk(row, event.currentTarget);
      }}
    >
      <Breakable name={row.short} />
      <span className={record ? "lean-tile__record" : "lean-tile__kind"}>{record ?? kindWord(row.kind)}</span>
    </a>
  );
}

function Side({ title, side, rows, shell, empty, onWalk, onHover }: { title: string; side: "by" | "uses"; rows: DeclRow[]; shell: LeanShell; empty: string; onWalk(row: DeclRow, element: HTMLElement): void; onHover(id: string | null): void }) {
  const [all, setAll] = useState(false);
  const shown = all ? rows : rows.slice(0, SIDE_LIMIT);
  const more = rows.length - shown.length;
  return (
    <section className={`lean-hood__side lean-hood__side--${side}`} aria-label={title}>
      <p className="lean-hood__title">
        {title} <span>{rows.length.toLocaleString("en-GB")}</span>
      </p>
      {rows.length === 0 && <p className="lean-hood__none">{empty}</p>}
      {shown.map((row) => (
        <Tile key={`${row.module}:${row.name}`} row={row} side={side} record={shell.linked.get(row.name)?.[0]?.title} onWalk={onWalk} onHover={onHover} />
      ))}
      {more > 0 && (
        <button type="button" className="lean-action" onClick={() => setAll(true)}>
          and {more.toLocaleString("en-GB")} more
        </button>
      )}
    </section>
  );
}

export function Neighbourhood({ decl, module, shell }: { decl: LeanDeclaration; module: string; shell: LeanShell }) {
  const root = useRef<HTMLDivElement>(null);
  const centre = useRef<HTMLDivElement>(null);
  const [lines, setLines] = useState<Line[]>([]);
  const [size, setSize] = useState({ w: 0, h: 0 });
  const [hot, setHot] = useState<string | null>(null);

  const sides = useMemo(() => {
    const rowsOf = (names: readonly string[]) => {
      const rows = names.flatMap((name) => {
        const row = name === decl.name ? undefined : findDecl(shell.index, name, module);
        return row ? [row] : [];
      });
      const rank = (row: DeclRow) => (shell.linked.has(row.name) ? 0 : shell.terms.has(row.name) ? 1 : 2);
      return rows.sort((a, b) => rank(a) - rank(b) || a.short.localeCompare(b.short));
    };
    return { by: rowsOf(decl.used_by), uses: rowsOf(decl.uses) };
  }, [decl, module, shell]);

  // Lines follow the tiles as they stand, including after a side opens in full.
  useLayoutEffect(() => {
    const host = root.current;
    const middle = centre.current;
    if (!host || !middle) return;
    const draw = () => {
      const box = host.getBoundingClientRect();
      const mid = place(middle, host);
      const y = mid.top + mid.height / 2;
      const inner = { l: mid.left, r: mid.left + mid.width };
      const next: Line[] = [];
      if (getComputedStyle(host).getPropertyValue("--hood-lines").trim() !== "off") {
        host.querySelectorAll<HTMLElement>("[data-tile]").forEach((tile) => {
          const id = tile.dataset.tile as string;
          const t = place(tile, host);
          const ty = t.top + t.height / 2;
          if (id.startsWith("by:")) {
            const x1 = inner.l;
            const x2 = t.left + t.width + 7;
            const c = (x1 + x2) / 2;
            next.push({ id, d: `M${x1} ${y}C${c} ${y} ${c} ${ty} ${x2} ${ty}`, tip: `M${x2} ${ty - 4}L${x2 - 7} ${ty}L${x2} ${ty + 4}Z` });
          } else {
            const x1 = t.left;
            const x2 = inner.r + 7;
            const c = (x1 + x2) / 2;
            next.push({ id, d: `M${x1} ${ty}C${c} ${ty} ${c} ${y} ${x2} ${y}`, tip: `M${x2} ${y - 4}L${x2 - 7} ${y}L${x2} ${y + 4}Z` });
          }
        });
      }
      setSize({ w: box.width, h: box.height });
      setLines(next);
    };
    draw();
    const watcher = new ResizeObserver(draw);
    watcher.observe(host);
    void document.fonts?.ready.then(draw);
    return () => watcher.disconnect();
  }, [sides]);

  // A step arrives: the declaration just opened is what the reader came for, so show its head.
  useLayoutEffect(() => {
    const step = walking;
    const host = root.current;
    const middle = centre.current;
    if (!step || !host || !middle || step.to !== decl.name) return;
    walking = null;
    if (performance.now() - step.at > 4000) return;
    const head = host.closest<HTMLElement>("[data-decl]");
    head?.scrollIntoView({ block: "start" });
    (head?.querySelector<HTMLElement>(".lean-block__name a") ?? middle).focus({ preventScroll: true });
    if (reduced()) return;
    moveFrom(middle, step.toRect);
    const before = host.querySelector<HTMLElement>(`[data-name="${CSS.escape(step.from)}"]`);
    if (before) moveFrom(before, step.fromRect);
    host.querySelectorAll<HTMLElement>(".lean-tile, .lean-hood__lines").forEach((element) => {
      if (element !== before) element.animate([{ opacity: 0 }, { opacity: 1 }], { duration: 180, delay: 140, fill: "backwards" });
    });
  }, [decl.name]);

  const walk = (row: DeclRow, element: HTMLElement) => {
    if (!centre.current) return;
    const step: Walk = { to: row.name, from: decl.name, toRect: element.getBoundingClientRect(), fromRect: centre.current.getBoundingClientRect(), at: performance.now() };
    const href = routeHref({ view: "lean", module: row.module, decl: row.name });
    // The next module arrives first, so the step never shows a loading state.
    void fetchModule(row.module)
      .catch(() => undefined)
      .then(() => {
        walking = step;
        navigate(href);
      });
  };

  const record = shell.linked.get(decl.name)?.[0]?.title;
  const source = decl.dependency_source ?? shell.modules.dependency_source;
  return (
    <section className="lean-hood" aria-label={`What uses ${decl.short} and what it uses`}>
      <p className="lean-terms__title">How {decl.short} connects</p>
      <div className="lean-hood__picture" ref={root}>
        <svg className="lean-hood__lines" width={size.w} height={size.h} aria-hidden="true">
          {lines.map((line) => (
            <g key={line.id} className={line.id === hot ? "is-hot" : undefined}>
              <path d={line.d} />
              <path d={line.tip} className="lean-hood__tip" />
            </g>
          ))}
        </svg>
        <Side title="Used by" side="by" rows={sides.by} shell={shell} empty="Nothing in OpenAI's source names it." onWalk={walk} onHover={setHot} />
        <div className="lean-hood__centre" ref={centre} tabIndex={-1} aria-current="true">
          <span className="lean-hood__kind">{kindWord(decl.kind)}</span>
          <Breakable name={decl.short} />
          {record && <span className="lean-tile__record">{record}</span>}
        </div>
        <Side title="Uses" side="uses" rows={sides.uses} shell={shell} empty="It names nothing else in OpenAI's source." onWalk={walk} onHover={setHot} />
      </div>
      <p className="lean-hood__note">
        {source === "elaborated" ? `${dependencyWords(source)}.` : (shell.modules.dependency_note ?? `${dependencyWords(source)}.`)} Each arrow runs from a name into the declaration that uses it. Click a name to move to it; Back returns.
      </p>
    </section>
  );
}

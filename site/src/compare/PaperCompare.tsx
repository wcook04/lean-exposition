// Two papers read together, one scroller of aligned rows like a side-by-side diff.
// Each row holds the passages of both papers that share records; the gutter names
// those records. Text with no partner keeps its place, so nothing is dropped and
// both papers can be read from start to end down their own column.

import { Suspense, lazy, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { describeError, useEdition } from "../app/data";
import { PAPER_NAMES } from "../app/papers";
import { navigate, routeHref } from "../app/router";
import { useDocument, type LoadedDocument } from "../reader/documents";
import { mountFigures } from "../reader/mount";
import { freshSlots, markWideMaths } from "../reader/page/PaperBody";
import { estimateHeight, passageOf, passageRecords, sectionNumber, sectionTitleIn, withoutIds } from "../reader/page/model";
import "../reader/reader-content.css";
import "../reader/reader-page.css";
import { ModeSwitch } from "./ModeSwitch";
import { alignPapers, type AlignPair, type AlignUnit, type AlignedRow } from "./paperAlignment";
import { shortTitle } from "./useAlignment";

const MapBeside = lazy(() => import("./MapBeside").then((m) => ({ default: m.MapBeside })));

const STAGES: Stage[] = ["long", "short", "expository"];
const NEAR = "900px 0px";

function unitsOf({ doc, paper }: LoadedDocument): AlignUnit[] {
  return doc.parts
    .filter((part) => !part.blank)
    .map((part) => ({
      part: part.index,
      records: part.anchor ? passageRecords(passageOf(paper.structure, part.anchor)) : [],
      size: part.span.end - part.span.start,
    }));
}

function linksBetween(a: LoadedDocument, b: LoadedDocument, left: AlignUnit[], right: AlignUnit[]): AlignPair[] {
  const index = (loaded: LoadedDocument, units: AlignUnit[]) => {
    const byAnchor = new Map<string, number>();
    units.forEach((unit, i) => {
      const anchor = loaded.doc.parts[unit.part].anchor;
      if (anchor) byAnchor.set(anchor, i);
    });
    return byAnchor;
  };
  const ai = index(a, left);
  const bi = index(b, right);
  const pairs: AlignPair[] = [];
  const push = (l: number | undefined, r: number | undefined) => {
    if (l !== undefined && r !== undefined) pairs.push({ left: l, right: r });
  };
  for (const link of a.paper.structure.reading_links) if (link.to_stage === b.paper.stage) push(ai.get(link.from_anchor), bi.get(link.to_anchor));
  for (const link of b.paper.structure.reading_links) if (link.to_stage === a.paper.stage) push(ai.get(link.to_anchor), bi.get(link.from_anchor));
  return pairs;
}

export function PaperCompare({ a, b, node }: { a: Stage; b: Stage; node?: string }) {
  const { graph } = useEdition();
  const left = useDocument(a);
  const right = useDocument(b);
  const [mapOpen, setMapOpen] = useState(false);
  const scroller = useRef<HTMLDivElement>(null);

  const aligned = useMemo(() => {
    if (left.status !== "ready" || right.status !== "ready" || left.value.paper.stage !== a || right.value.paper.stage !== b) return null;
    const l = unitsOf(left.value);
    const r = unitsOf(right.value);
    return { left: l, right: r, rows: alignPapers(l, r, linksBetween(left.value, right.value, l, r)) };
  }, [left, right, a, b]);

  const choose = (side: "a" | "b", stage: Stage) => {
    // Picking the other side's paper trades places, so the two sides always differ.
    const papers = side === "a" ? { a: stage, b: stage === b ? a : b } : { a: stage === a ? b : a, b: stage };
    navigate({ view: "compare", papers, node });
  };

  // A row jumped to from "Also linked", or from a record in the address.
  const [marked, setMarked] = useState<number | null>(null);
  const jump = (row: number) => {
    setMarked(row);
    scroller.current?.querySelector(`[data-row="${row}"]`)?.scrollIntoView({ block: "start" });
  };
  useLayoutEffect(() => {
    if (!aligned || !node) return;
    const at = aligned.rows.findIndex((row) => row.shared.includes(node));
    const fallback = at >= 0 ? at : aligned.rows.findIndex((row) => [...row.left.map((u) => aligned.left[u]), ...row.right.map((u) => aligned.right[u])].some((u) => u.records.includes(node)));
    if (fallback >= 0) jump(fallback);
    // Only on arrival: scrolling afterwards belongs to the reader.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [aligned]);

  // The row under the reading line, watched only while the map needs it.
  const [reading, setReading] = useState(0);
  useEffect(() => {
    const root = scroller.current;
    if (!mapOpen || !root || !aligned) return;
    const observer = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) if (entry.isIntersecting) setReading(Number((entry.target as HTMLElement).dataset.row));
      },
      { root, rootMargin: "-32% 0px -67% 0px" },
    );
    root.querySelectorAll("[data-row]").forEach((el) => observer.observe(el));
    return () => observer.disconnect();
  }, [mapOpen, aligned]);

  const nameA = PAPER_NAMES[a].short;
  const nameB = PAPER_NAMES[b].short;
  const failed = left.status === "error" ? left.error : right.status === "error" ? right.error : null;
  const litRow = aligned?.rows[reading];
  const litRecords = useMemo(() => {
    if (!aligned || !litRow) return [];
    return [...new Set([...litRow.left.flatMap((u) => [...aligned.left[u].records]), ...litRow.right.flatMap((u) => [...aligned.right[u].records])])];
  }, [aligned, litRow]);

  return (
    <div className={`papers${mapOpen ? " papers--map" : ""}`}>
      <header className="papers-head">
        <ModeSwitch mode="papers" papers={{ a, b }} node={node} />
        <h1 className="papers-head__title">
          The {nameA.toLowerCase()} and the {nameB.toLowerCase()}, aligned by the records they share
        </h1>
        <div className="papers-head__tools">
          <PaperPicker label="Left paper" value={a} onChange={(stage) => choose("a", stage)} />
          <button type="button" className="control" onClick={() => navigate({ view: "compare", papers: { a: b, b: a }, node })}>
            Swap
          </button>
          <PaperPicker label="Right paper" value={b} onChange={(stage) => choose("b", stage)} />
          <button type="button" className="bench-toggle papers-head__map" aria-pressed={mapOpen} onClick={() => setMapOpen((v) => !v)}>
            Map beside
          </button>
        </div>
      </header>
      <div className="papers-body">
        <div className="papers-scroll" ref={scroller} tabIndex={0} aria-label={`The ${nameA.toLowerCase()} and the ${nameB.toLowerCase()} in aligned rows`}>
          <div className="papers-names" aria-hidden="true">
            <span>{nameA}</span>
            <span>Records both link to</span>
            <span>{nameB}</span>
          </div>
          {failed != null && <p className="bench-note">{describeError(failed).title}</p>}
          {!aligned && failed == null && <p className="bench-note">Aligning the {nameA.toLowerCase()} and the {nameB.toLowerCase()}…</p>}
          {aligned && left.status === "ready" && right.status === "ready" && (
            <>
              <p className="papers-note">
                Two passages share a row when they are linked to the same records, so each paper still reads from start to end down its own column. A shared record says where to look. The two passages may make different arguments.
              </p>
              {aligned.rows.map((row, i) => (
                <Row
                  key={`${a}:${b}:${row.left[0] ?? "-"}:${row.right[0] ?? "-"}`}
                  index={i}
                  row={row}
                  marked={marked === i}
                  lit={mapOpen && reading === i}
                  left={{ loaded: left.value, units: aligned.left }}
                  right={{ loaded: right.value, units: aligned.right }}
                  titleOf={(id) => shortTitle(id, graph.nodes.get(id)?.label ?? id)}
                  onJump={jump}
                  root={scroller}
                />
              ))}
            </>
          )}
        </div>
        {mapOpen && (
          <aside className="papers-map" aria-label="The argument map beside the papers">
            <Suspense fallback={null}>
              <MapBeside records={litRecords} />
            </Suspense>
          </aside>
        )}
      </div>
    </div>
  );
}

function PaperPicker({ label, value, onChange }: { label: string; value: Stage; onChange(stage: Stage): void }) {
  return (
    <label className="bench-field bench-field--inline">
      <span>{label}</span>
      <select value={value} onChange={(e) => onChange(e.target.value as Stage)}>
        {STAGES.map((stage) => (
          <option key={stage} value={stage}>
            {PAPER_NAMES[stage].short}
          </option>
        ))}
      </select>
    </label>
  );
}

interface Side {
  loaded: LoadedDocument;
  units: AlignUnit[];
}

interface RowProps {
  index: number;
  row: AlignedRow;
  marked: boolean;
  lit: boolean;
  left: Side;
  right: Side;
  titleOf(id: string): string;
  onJump(row: number): void;
  root: React.RefObject<HTMLDivElement | null>;
}

function placeOf(side: Side, unit: number): string {
  const { doc, paper } = side.loaded;
  const part = doc.parts[side.units[unit].part];
  const title = part.anchor ? sectionTitleIn(paper.structure, part.anchor) : part.headings[0]?.title;
  const name = PAPER_NAMES[paper.stage].short;
  return title ? `${name} ${sectionNumber(title)}` : name;
}

function Row({ index, row, marked, lit, left, right, titleOf, onJump, root }: RowProps) {
  const ref = useRef<HTMLDivElement>(null);
  const [near, setNear] = useState(false);
  useEffect(() => {
    const el = ref.current;
    if (!el || near) return;
    const observer = new IntersectionObserver((entries) => entries.some((e) => e.isIntersecting) && setNear(true), { root: root.current, rootMargin: NEAR });
    observer.observe(el);
    return () => observer.disconnect();
  }, [near, root]);

  // A shorter cell travels with its neighbour, so a row never shows text beside nothing.
  useLayoutEffect(() => {
    const el = ref.current;
    const scrollerEl = root.current;
    if (!el || !scrollerEl || !near) return;
    const inners = [...el.querySelectorAll<HTMLElement>(".papers-cell__in")];
    const fit = () => {
      const tallest = Math.max(...inners.map((inner) => inner.offsetHeight));
      const room = scrollerEl.clientHeight - 48;
      inners.forEach((inner) => {
        const height = inner.offsetHeight;
        const travels = height < tallest - 40;
        inner.classList.toggle("is-travelling", travels);
        // A cell taller than the window is read through first, then rests with its end in view.
        inner.style.top = travels ? `${Math.min(48, room - height + 32)}px` : "";
      });
    };
    const observer = new ResizeObserver(fit);
    inners.forEach((inner) => observer.observe(inner));
    return () => observer.disconnect();
  }, [near, root]);

  const paired = row.left.length > 0 && row.right.length > 0;
  return (
    <div ref={ref} className={`papers-row${paired ? " papers-row--paired" : ""}${marked ? " is-marked" : ""}${lit ? " is-reading" : ""}`} data-row={index}>
      <Cell side={left} cell={row.left} near={near} />
      <Gutter row={row} left={left} right={right} titleOf={titleOf} onJump={onJump} />
      <Cell side={right} cell={row.right} near={near} />
    </div>
  );
}

function Cell({ side, cell, near }: { side: Side; cell: number[]; near: boolean }) {
  if (!cell.length) {
    return (
      <div className="papers-cell papers-cell--none">
        <p>The {PAPER_NAMES[side.loaded.paper.stage].short.toLowerCase()} has no passage for this.</p>
      </div>
    );
  }
  return (
    <div className="papers-cell">
      <div className="papers-cell__in">
        <span className="papers-cell__name">{PAPER_NAMES[side.loaded.paper.stage].short}</span>
        {cell.map((unit) => (near ? <PartText key={unit} loaded={side.loaded} part={side.units[unit].part} /> : <PartHold key={unit} loaded={side.loaded} part={side.units[unit].part} />))}
      </div>
    </div>
  );
}

function PartHold({ loaded, part }: { loaded: LoadedDocument; part: number }) {
  return <div style={{ minHeight: estimateHeight(loaded.doc.parts[part]) }} />;
}

function PartText({ loaded, part }: { loaded: LoadedDocument; part: number }) {
  const html = useMemo(() => withoutIds(loaded.doc.render(part).html), [loaded, part]);
  const ref = useRef<HTMLDivElement>(null);
  useLayoutEffect(() => {
    const body = ref.current;
    if (!body) return;
    const unmount = mountFigures(freshSlots(body));
    const unmark = markWideMaths(body);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);
  return <div ref={ref} className="slice prose papers-text" dangerouslySetInnerHTML={{ __html: html }} />;
}

function Gutter({ row, left, right, titleOf, onJump }: { row: AlignedRow; left: Side; right: Side; titleOf(id: string): string; onJump(row: number): void }) {
  const [open, setOpen] = useState(false);
  const limit = 4;
  const shown = open ? row.shared : row.shared.slice(0, limit);
  return (
    <div className="papers-gutter">
      <div className="papers-gutter__in">
        {shown.map((id) => (
        <a key={id} className="bench-chip" href={routeHref({ view: "compare", node: id })}>
          {titleOf(id)}
        </a>
      ))}
      {!open && row.shared.length > limit && (
        <button type="button" className="bench-chip bench-chip--more" onClick={() => setOpen(true)}>
          and {row.shared.length - limit} more
        </button>
      )}
      {row.also.map((also) => (
        <button key={`${also.side}:${also.unit}`} type="button" className="papers-also" onClick={() => onJump(also.row)}>
          Also linked: {also.side === "left" ? placeOf(right, also.unit) : placeOf(left, also.unit)}
        </button>
      ))}
      </div>
    </div>
  );
}

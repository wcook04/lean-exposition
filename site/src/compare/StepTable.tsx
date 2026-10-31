// Compare's first view: the proof as a table. A row is one step and a cell is that step's
// exact statement at one level, so the words side by side are about the same thing. The
// papers' surrounding text stays in the reader, one link away from each statement. A row's
// title opens that step in full.

import { Fragment, memo, useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type CSSProperties, type RefObject } from "react";
import type { RecordAlignment } from "../api/lean";
import { useEdition } from "../app/data";
import { LEVELS, navigate, routeHref, type Level, type Route } from "../app/router";
import { LINK_CAVEAT } from "../lean/data";
import { LazyLeanBlock } from "../lean/lazy";
import { sectionLabel, mainGoal } from "../map/TheoremPlate";
import { statementHref } from "../reader/links";
import { onIdle } from "./idle";
import { LazyStatementSlice, primeSlices } from "./lazy";
import { ModeSwitch } from "./ModeSwitch";
import { LEVEL_NAMES, STACK_BELOW, absentWords, filterOutline, roleWords, storeLevels, storedLevels, toggleLevel } from "./model";
import { defaultLevels, holdHeight, orderWords, rowFor, rowsSentence, sayings, tableRows, type TableRow as Row } from "./table";
import { alignmentResource, shortTitle, useAlignment } from "./useAlignment";
import { useWidth } from "./useWidth";

/** How far from the window a row is typeset, and how many rows ahead are prepared when idle. */
const NEAR = "900px 0px";
const AHEAD = 8;
/** The band where a row counts as being read: a thin slice near the top of the table. */
const READING_LINE = "-26% 0px -73% 0px";
/** Rows above a landing typeset and their Lean arrives, so the landing is held until they settle. */
const SETTLE_MS = [300, 800, 1600];

type CompareRoute = Extract<Route, { view: "compare" }>;

export function StepTable({ route }: { route: CompareRoute }) {
  const edition = useEdition();
  const { graph } = edition;
  const alignment = useAlignment();
  const width = useWidth();
  const records = alignment?.records;
  // The Lean's own records are what its column shows, so a row is always a step of the argument.
  const steps = useMemo(() => (records ? Object.fromEntries(Object.entries(records).filter(([id]) => graph.nodes.get(id)?.kind !== "declaration")) : undefined), [records, graph]);
  const main = useMemo(() => mainGoal(edition), [edition]);

  const [stored] = useState(storedLevels);
  const chosen = route.levels ?? stored ?? defaultLevels(width);
  const levels = useMemo(() => LEVELS.filter((level) => chosen.includes(level)), [chosen]);
  const levelsKey = levels.join(",");

  const every = useMemo(() => (steps ? tableRows(steps, levels, false, main) : []), [steps, levelsKey, main]);
  const anyRows = useMemo(() => (steps ? tableRows(steps, levels, true, main) : []), [steps, levelsKey, main]);
  // A step asked for by name is always listed, even when only some of the levels have it.
  const wide = route.any || (!!route.at && !rowFor(every, route.at) && !!rowFor(anyRows, route.at));
  const listed = wide ? anyRows : every;

  const titleOf = useCallback((id: string) => shortTitle(id, graph.nodes.get(id)?.label ?? id), [graph]);
  const rowTitle = useCallback((row: Row) => [row.id, ...row.also].map(titleOf).join(" "), [titleOf]);
  const [query, setQuery] = useState("");
  const rows = useMemo(() => filterOutline(listed, query, (id) => rowTitle(rowFor(listed, id)!)), [listed, query, rowTitle]);

  const scroller = useRef<HTMLDivElement>(null);
  const top = useRef<HTMLDivElement>(null);
  const [marked, setMarked] = useState<string | null>(null);
  const [reading, setReading] = useState<string | null>(null);

  // The band at the top of the table can wrap, so the row titles that stick under it follow its height.
  useLayoutEffect(() => {
    const band = top.current;
    if (!band) return;
    const place = () => scroller.current?.style.setProperty("--top-h", `${band.offsetHeight}px`);
    place();
    const observer = new ResizeObserver(place);
    observer.observe(band);
    return () => observer.disconnect();
  }, []);

  // A row is held at the top until the rows around it have settled, or the reader moves.
  const unpin = useRef(() => {});
  const pin = useCallback((id: string) => {
    const root = scroller.current;
    if (!root) return;
    const place = () => root.querySelector(`[data-row="${CSS.escape(id)}"]`)?.scrollIntoView({ block: "start" });
    unpin.current();
    place();
    const timers = SETTLE_MS.map((ms) => window.setTimeout(place, ms));
    const moves = ["wheel", "touchstart", "pointerdown"];
    const release = () => {
      timers.forEach((timer) => window.clearTimeout(timer));
      moves.forEach((move) => root.removeEventListener(move, release));
      window.removeEventListener("keydown", release);
    };
    moves.forEach((move) => root.addEventListener(move, release, { passive: true }));
    window.addEventListener("keydown", release);
    unpin.current = release;
  }, []);
  useEffect(() => () => unpin.current(), []);
  const jump = useCallback(
    (id: string) => {
      setMarked(id);
      pin(id);
    },
    [pin],
  );

  const target = route.at ? rowFor(rows, route.at)?.id : undefined;
  useLayoutEffect(() => {
    if (target) jump(target);
  }, [target, jump]);

  // The row under the reading line: where "One step" goes, and the row to keep in view when the columns change.
  useEffect(() => {
    const root = scroller.current;
    if (!root || !rows.length || typeof IntersectionObserver === "undefined") return;
    const observer = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) if (entry.isIntersecting) setReading((entry.target as HTMLElement).dataset.row ?? null);
      },
      { root, rootMargin: READING_LINE },
    );
    root.querySelectorAll("[data-row]").forEach((el) => observer.observe(el));
    return () => observer.disconnect();
  }, [rows]);
  const current = (reading ? rows.find((row) => row.id === reading) : undefined)?.id ?? rows[0]?.id ?? null;

  const keep = useRef<string | null>(null);
  const toggle = (level: Level) => {
    const next = toggleLevel(levels, level);
    keep.current = current;
    storeLevels(next);
    navigate({ view: "compare", levels: next, any: route.any }, { replace: true });
  };
  useLayoutEffect(() => {
    if (keep.current) pin(keep.current);
    keep.current = null;
  }, [levelsKey, pin]);

  // The rows ahead of the reader are typeset when the page is idle.
  useEffect(() => {
    if (!records || !current) return;
    const at = rows.findIndex((row) => row.id === current);
    const ahead = rows.slice(at + 1, at + 1 + AHEAD).flatMap((row) => records[row.id].statements.filter((s) => s.role !== "mention"));
    return onIdle(() => primeSlices(ahead), 800);
  }, [records, rows, current]);

  // j and k move between rows; the arrow keys go on scrolling as they would anywhere.
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.defaultPrevented || event.metaKey || event.ctrlKey || event.altKey) return;
      const step = event.key === "j" ? 1 : event.key === "k" ? -1 : 0;
      if (!step || (event.target as HTMLElement).matches?.("input, textarea, select, [contenteditable]")) return;
      const next = rows[rows.findIndex((row) => row.id === current) + step];
      if (!next) return;
      event.preventDefault();
      jump(next.id);
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [rows, current, jump]);

  const [loaded, setLoaded] = useState(false);
  useEffect(() => {
    void alignmentResource().then(() => setLoaded(true));
  }, []);

  const columns = { "--cols": levels.length } as CSSProperties;
  const columnWidth = width / (width < STACK_BELOW ? 1 : levels.length);
  const stepHref = useCallback((id: string) => routeHref({ view: "compare", node: id, levels: route.levels }), [route.levels]);
  const someHave = levels.length > 1 && anyRows.length > every.length;

  return (
    <div className="table">
      <div className="table-scroll" ref={scroller} tabIndex={0} aria-label="The steps of the proof at each level" style={columns}>
        <div className="table-top" ref={top}>
          <header className="table-head">
            <ModeSwitch mode="table" step={current ?? main} levels={route.levels} />
            <h1 className="table-head__title">Every step, side by side</h1>
            <div className="table-head__tools">
              <label className="bench-search table-head__find">
                <span className="visually-hidden">Filter the steps</span>
                <input type="search" placeholder="Filter the steps" value={query} onChange={(e) => setQuery(e.target.value)} />
              </label>
              <div className="compare-words" role="group" aria-label="Levels shown">
                {LEVELS.map((level) => (
                  <button key={level} type="button" aria-pressed={levels.includes(level)} onClick={() => toggle(level)}>
                    {LEVEL_NAMES[level]}
                  </button>
                ))}
              </div>
            </div>
          </header>
          {records && (
            <p className="table-line">
              {rowsSentence(levels, listed.length, wide)} {orderWords(levels)}{" "}
              {someHave &&
                (wide ? (
                  <a href={routeHref({ view: "compare", levels: route.levels })}>Only the {every.length} at every level shown</a>
                ) : (
                  <a href={routeHref({ view: "compare", levels: route.levels, any: true })}>Add the {anyRows.length - every.length} at only some of them</a>
                ))}
              {levels.includes("lean") && <span className="table-line__caveat">{LINK_CAVEAT}</span>}
            </p>
          )}
          <div className="table-names" aria-hidden="true">
            {levels.map((level) => (
              <span key={level}>{LEVEL_NAMES[level]}</span>
            ))}
          </div>
        </div>
        {!records && <p className="bench-note">{loaded ? "This edition does not say where each level states each step." : "Loading where each level states each step…"}</p>}
        {records && !rows.length && <p className="bench-note">{query ? "No step has those words in its title." : "No step appears at every level shown."}</p>}
        {records &&
          rows.map((row) => (
            <TableRow key={row.id} id={row.id} titles={[row.id, ...row.also].map((id) => ({ id, title: titleOf(id), href: stepHref(id) }))} record={records[row.id]} levels={levels} href={stepHref(row.id)} root={scroller} hold={holdHeight(records[row.id], levels, columnWidth)} marked={marked === row.id} />
          ))}
      </div>
    </div>
  );
}

interface RowProps {
  id: string;
  /** Usually one; two when two steps say the same words at these levels. */
  titles: { id: string; title: string; href: string }[];
  record: RecordAlignment;
  levels: readonly Level[];
  href: string;
  root: RefObject<HTMLDivElement | null>;
  hold: number;
  marked: boolean;
}

const TableRow = memo(function TableRow({ id, titles, record, levels, href, root, hold, marked }: RowProps) {
  const ref = useRef<HTMLElement>(null);
  const [near, setNear] = useState(() => typeof IntersectionObserver === "undefined");
  useEffect(() => {
    const el = ref.current;
    if (!el || near) return;
    const observer = new IntersectionObserver((entries) => entries.some((e) => e.isIntersecting) && setNear(true), { root: root.current, rootMargin: NEAR });
    observer.observe(el);
    return () => observer.disconnect();
  }, [near, root]);
  return (
    <article ref={ref} className={`trow${marked ? " is-marked" : ""}`} data-row={id}>
      <div className="trow__band">
        <h2 className="trow__title">
          {titles.map((title, i) => (
            <Fragment key={title.id}>
              {i > 0 && <span className="trow__and"> and </span>}
              <a href={title.href}>{title.title}</a>
            </Fragment>
          ))}
        </h2>
        <a className="trow__map" href={routeHref({ view: "map", node: id })}>
          On the map
        </a>
      </div>
      <div className="trow__cells" style={near ? undefined : { minHeight: hold }}>
        {near && levels.map((level) => <Cell key={level} level={level} record={record} href={href} />)}
      </div>
    </article>
  );
});

function Cell({ level, record, href }: { level: Level; record: RecordAlignment; href: string }) {
  const name = LEVEL_NAMES[level];
  if (level === "lean") {
    const first = record.lean[0];
    if (!first) return <Absent level={level} />;
    return (
      <section className="tcell" aria-label={name}>
        <p className="tcell__name">{name}</p>
        <LazyLeanBlock name={first.name} module={first.module} relation={first.relation} note={first.note} clause={first.clause} compact bare />
        <p className="tcell__foot">
          <a href={routeHref({ view: "lean", module: first.module, decl: first.name })}>Read in context</a>
          <More count={record.lean.length - 1} href={href} />
        </p>
      </section>
    );
  }
  const [first, ...others] = sayings(record, level);
  if (!first) return <Absent level={level} />;
  return (
    <section className="tcell" aria-label={name}>
      <p className="tcell__name">{name}</p>
      <header className="bench-slice__head">
        <span className="bench-slice__role">{roleWords(first.role)}</span>
        <span className="bench-slice__section">{sectionLabel(first.section)}</span>
      </header>
      <LazyStatementSlice statement={first} />
      {first.note && <p className="bench-slice__note">{first.note}</p>}
      <p className="tcell__foot">
        <a href={statementHref(first)}>Read in context</a>
        <More count={others.length} href={href} />
      </p>
    </section>
  );
}

function More({ count, href }: { count: number; href: string }) {
  return count > 0 ? <a href={href}>and {count} more</a> : null;
}

function Absent({ level }: { level: Level }) {
  return (
    <div className="tcell tcell--none">
      <p>{absentWords(level)}</p>
    </div>
  );
}

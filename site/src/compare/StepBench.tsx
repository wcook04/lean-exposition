// One step of the argument, read across every level. The rail is the argument as an
// outline; the main area shows what the Lean, the long record, the short paper and
// the exposition each do with the chosen record, with what it uses and is used by,
// so the reader can walk the argument in either direction.

import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { AlignedStatement, RecordAlignment } from "../api/lean";
import { useEdition } from "../app/data";
import { LEVELS, navigate, routeHref, type Level, type Route } from "../app/router";
import { kindName } from "../map/labels";
import { mainGoal, sectionLabel, startingGoals } from "../map/TheoremPlate";
import { goalFor, reach, scopedGraph, usesOf } from "../map/treeModel";
import type { ArgGraph } from "../model/graph";
import { fetchModule } from "../lean/data";
import { LazyLeanBlock } from "../lean/lazy";
import { statementHref } from "../reader/links";
import { onIdle } from "./idle";
import { LazyStatementSlice, primeSlices } from "./lazy";
import { ModeSwitch } from "./ModeSwitch";
import {
  LEVEL_NAMES,
  LEVEL_FILTERS,
  STACK_BELOW,
  absentWords,
  argumentOutline,
  arrangeLevels,
  filterByLevel,
  filterOutline,
  leanAbsence,
  levelVerb,
  roleWords,
  statementsOf,
  storeLevels,
  storedLevels,
  toggleLevel,
  walkListed,
  type LevelFilter,
  type OutlineRow,
  type Slot,
} from "./model";
import { recordLine, shortTitle, useAlignment } from "./useAlignment";

type CompareRoute = Extract<Route, { view: "compare" }>;

/** The window's width, followed live. */
function useWidth(): number {
  const [width, setWidth] = useState(() => window.innerWidth);
  useEffect(() => {
    const onResize = () => setWidth(window.innerWidth);
    window.addEventListener("resize", onResize);
    return () => window.removeEventListener("resize", onResize);
  }, []);
  return width;
}

export function StepBench({ route }: { route: CompareRoute }) {
  const edition = useEdition();
  const { graph } = edition;
  const alignment = useAlignment();
  const width = useWidth();
  const stacked = width < STACK_BELOW;

  const main = useMemo(() => mainGoal(edition), [edition]);
  const goals = useMemo(() => startingGoals(edition), [edition]);
  const asked = route.node && graph.nodes.has(route.node) ? route.node : undefined;

  // The goal stays while the reader walks. It changes when they pick another, or
  // arrive at a record its argument does not reach.
  const [picked, setPicked] = useState<string>(() => main);
  const goal = useMemo(() => {
    if (!asked || reach(graph, picked).has(asked)) return picked;
    return goalFor(graph, asked, goals.map((g) => g.id)) ?? picked;
  }, [asked, graph, picked, goals]);
  useEffect(() => setPicked(goal), [goal]);

  const scoped = useMemo(() => scopedGraph(graph, goal), [graph, goal]);
  const outline = useMemo(() => argumentOutline(scoped, goal), [scoped, goal]);
  const node = asked ?? goal;
  const [levelFilter, setLevelFilter] = useState<LevelFilter>("all");
  const listed = useMemo(() => filterByLevel(outline, levelFilter, scoped), [outline, levelFilter, scoped]);
  const stepAt = listed.findIndex((row) => row.id === node);

  const titleOf = useCallback((id: string) => shortTitle(id, graph.nodes.get(id)?.label ?? id), [graph]);

  const [query, setQuery] = useState("");
  const visible = useMemo(() => filterOutline(listed, query, (id) => `${titleOf(id)} ${graph.nodes.get(id)?.label ?? ""}`), [listed, query, titleOf, graph]);

  // The levels the reader chose: the address first, then what they chose last time.
  const [stored] = useState(storedLevels);
  const chosen = route.levels ?? stored;
  const go = useCallback(
    (id: string, options?: { replace?: boolean; levels?: Level[] }) => {
      navigate({ view: "compare", node: id, levels: options?.levels ?? route.levels }, { replace: options?.replace });
    },
    [route.levels],
  );

  const record = alignment?.records[node] ?? null;
  const slots = useMemo(() => (record ? arrangeLevels(record, width, chosen) : []), [record, width, chosen]);
  const shownLevels = slots.filter((s) => s.state !== "folded").map((s) => s.level);

  const chooseLevels = (levels: Level[]) => {
    storeLevels(levels);
    navigate({ view: "compare", node, levels }, { replace: true });
  };
  const toggle = (level: Level) => chooseLevels(toggleLevel(chosen ?? slots.filter((s) => s.state === "column").map((s) => s.level), level));
  const unfold = (level: Level) => chooseLevels(toggleLevel(slots.filter((s) => s.state === "column").map((s) => s.level), level));

  // Walking: arrows, or j and k. Inside a column the arrows scroll it, as they would anywhere.
  const railRef = useRef<HTMLOListElement>(null);
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.defaultPrevented || event.metaKey || event.ctrlKey || event.altKey) return;
      const step = event.key === "ArrowDown" || event.key === "j" ? 1 : event.key === "ArrowUp" || event.key === "k" ? -1 : 0;
      if (!step) return;
      const target = event.target as HTMLElement;
      const typing = target.matches?.("input, textarea, select, [contenteditable]");
      const letter = event.key === "j" || event.key === "k";
      if (typing && (letter || !target.matches('input[type="search"]'))) return;
      if (!letter && target.closest?.("[data-scrolls]")) return;
      const next = walkListed(outline, visible, node, step);
      if (!next) return;
      event.preventDefault();
      go(next.id, { replace: true });
      if (target.closest?.(".bench-rail__list")) requestAnimationFrame(() => railRef.current?.querySelector<HTMLElement>('[aria-current="step"]')?.focus());
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [outline, visible, node, go]);

  // The current row stays in view.
  useLayoutEffect(() => {
    railRef.current?.querySelector('[aria-current="step"]')?.scrollIntoView({ block: "nearest" });
  }, [node, visible]);

  // Neighbours arrive before the reader does: their Lean modules and their typeset slices.
  useEffect(() => {
    if (!alignment || stepAt < 0) return;
    const near = [listed[stepAt - 1], listed[stepAt + 1], listed[stepAt + 2]].flatMap((row) => (row ? [alignment.records[row.id]] : [])).filter(Boolean) as RecordAlignment[];
    const prefetch = () => {
      new Set(near.flatMap((r) => r.lean.map((l) => l.module))).forEach((module) => void fetchModule(module).catch(() => undefined));
      primeSlices(near.flatMap((r) => r.statements));
    };
    return onIdle(prefetch, 800);
  }, [alignment, listed, stepAt]);

  const previous = walkListed(outline, listed, node, -1);
  const next = walkListed(outline, listed, node, 1);
  const filterName = LEVEL_FILTERS.find((f) => f.id === levelFilter)!.label.toLowerCase();
  const filters = <LevelFilters outline={outline} graph={scoped} value={levelFilter} onChange={setLevelFilter} />;
  const href = (id: string) => routeHref({ view: "compare", node: id, levels: route.levels });

  return (
    <div className={`bench${stacked ? " bench--stacked" : ""}`}>
      {stacked ? (
        <div className="bench-pick">
          <ModeSwitch mode="steps" node={route.node} />
          <GoalMenu goals={goals} goal={goal} onPick={(id) => { setPicked(id); go(id); }} />
          {filters}
          <label className="bench-field">
            <span>Step</span>
            <select value={stepAt >= 0 ? node : ""} onChange={(e) => go(e.target.value)}>
              {stepAt < 0 && <option value="">Outside this argument</option>}
              {listed.map((row, i) => (
                <option key={row.id} value={row.id}>
                  {i + 1}. {titleOf(row.id)}
                </option>
              ))}
            </select>
          </label>
        </div>
      ) : (
        <nav className="bench-rail" aria-label="The steps of the argument">
          <ModeSwitch mode="steps" node={route.node} />
          <GoalMenu goals={goals} goal={goal} onPick={(id) => { setPicked(id); go(id); }} />
          {filters}
          <label className="bench-field">
            <span className="visually-hidden">Filter the steps</span>
            <input type="search" placeholder="Filter the steps" value={query} onChange={(e) => setQuery(e.target.value)} />
          </label>
          <ol className="bench-rail__list" ref={railRef}>
            {visible.map((row) => (
              <RailRow key={row.id} row={row} title={titleOf(row.id)} current={row.id === node} href={href(row.id)} filtered={!!query} />
            ))}
            {!visible.length && <li className="bench-rail__none">{query ? "No step has those words in its title." : `The ${filterName} discusses no step of this argument.`}</li>}
          </ol>
        </nav>
      )}

      <section className="bench-main" aria-label="This step at each level">
        <StepHead graph={graph} node={node} title={graph.nodes.get(node)?.label ?? node} titleOf={titleOf} href={href} shown={shownLevels} onToggle={toggle} hasRecord={!!record} stacked={stacked} />
        {!alignment && <p className="bench-note">Loading where each level states this step…</p>}
        {alignment && !record && (
          <p className="bench-note">
            No level is linked to this record in this edition. <a href={routeHref({ view: "map", node })}>See it on the map</a>.
          </p>
        )}
        {record && (stacked ? <StackedLevels key={node} id={node} record={record} slots={slots} /> : <Columns key={node} id={node} record={record} slots={slots} onUnfold={unfold} />)}
        <footer className="bench-foot">
          <a className="bench-foot__link" href={previous ? href(previous.id) : undefined} aria-disabled={!previous} rel="prev">
            {previous ? <><span aria-hidden="true">↑ </span><span className="bench-foot__word">Previous: </span>{titleOf(previous.id)}</> : "First step"}
          </a>
          <p className="bench-foot__count">{stepAt >= 0 ? `Step ${stepAt + 1} of ${listed.length}${levelFilter === "all" ? "" : ` in the ${filterName}`}` : levelFilter === "all" ? "Outside this argument" : `Not in the ${filterName}`}</p>
          <a className="bench-foot__link bench-foot__link--next" href={next ? href(next.id) : undefined} aria-disabled={!next} rel="next">
            {next ? <><span className="bench-foot__word">Next: </span>{titleOf(next.id)}<span aria-hidden="true"> ↓</span></> : "Last step"}
          </a>
        </footer>
      </section>
    </div>
  );
}

function GoalMenu({ goals, goal, onPick }: { goals: { id: string; title: string }[]; goal: string; onPick(id: string): void }) {
  return (
    <label className="bench-field">
      <span>Argument for</span>
      <select value={goal} onChange={(e) => onPick(e.target.value)}>
        {goals.map((g) => (
          <option key={g.id} value={g.id}>
            {g.title}
          </option>
        ))}
      </select>
    </label>
  );
}

/** The whole argument or one paper's part of it, each with how many steps that is. */
function LevelFilters({ outline, graph, value, onChange }: { outline: OutlineRow[]; graph: ArgGraph; value: LevelFilter; onChange(filter: LevelFilter): void }) {
  return (
    <div className="bench-filters" role="group" aria-label="Show the steps each level discusses">
      {LEVEL_FILTERS.map((filter) => (
        <button key={filter.id} type="button" className="bench-filter" aria-pressed={value === filter.id} onClick={() => onChange(filter.id)}>
          {filter.label} <span className="bench-filter__count">{filterByLevel(outline, filter.id, graph).length}</span>
        </button>
      ))}
    </div>
  );
}

function RailRow({ row, title, current, href, filtered }: { row: OutlineRow; title: string; current: boolean; href: string; filtered: boolean }) {
  return (
    <li>
      <a className="bench-row" href={href} aria-current={current ? "step" : undefined} style={{ paddingLeft: `${8 + (filtered ? 0 : Math.min(row.depth, 5)) * 8}px` }}>
        <span className="bench-row__title">{title}</span>
        {!!recordLine(row.id)?.lean && <span className="bench-row__lean">Lean</span>}
      </a>
    </li>
  );
}

function neighbours(graph: ArgGraph, id: string) {
  const usedBy = [...new Set((graph.in.get(id) ?? []).filter((e) => e.kind === "supports").map((e) => e.from))];
  const uses = [...new Set(usesOf(graph, id).filter((e) => e.kind === "supports").map((e) => e.to))];
  const assumes = [...new Set(usesOf(graph, id).filter((e) => e.kind === "assumes").map((e) => e.to))];
  return { usedBy, uses, assumes };
}

interface HeadProps {
  graph: ArgGraph;
  node: string;
  title: string;
  titleOf(id: string): string;
  href(id: string): string;
  shown: Level[];
  onToggle(level: Level): void;
  hasRecord: boolean;
  stacked: boolean;
}

function StepHead({ graph, node, title, titleOf, href, shown, onToggle, hasRecord, stacked }: HeadProps) {
  const { usedBy, uses, assumes } = useMemo(() => neighbours(graph, node), [graph, node]);
  const kind = graph.nodes.get(node)?.kind ?? "claim";
  return (
    <header className="bench-head">
      <div className="bench-head__top">
        <div className="bench-head__kind">
          <p className="caps">{kindName(kind)}</p>
          {assumes.length > 0 && <ChipRow label="Assumes" ids={assumes} titleOf={titleOf} href={href} tags />}
        </div>
        <div className="bench-head__tools">
          {hasRecord && !stacked && (
            <div className="bench-toggles" role="group" aria-label="Levels shown">
              {LEVELS.map((level) => (
                <button key={level} type="button" className="bench-toggle" aria-pressed={shown.includes(level)} onClick={() => onToggle(level)}>
                  {LEVEL_NAMES[level]}
                </button>
              ))}
            </div>
          )}
          <a className="control" href={routeHref({ view: "map", node })}>
            Show on the map
          </a>
        </div>
      </div>
      <h1 className="bench-head__title">{title}</h1>
      <ChipRow label="Used by" empty="Nothing in the record uses this step." ids={usedBy} titleOf={titleOf} href={href} limit={stacked ? 2 : 5} />
      <ChipRow label="Uses" empty="No recorded inputs." ids={uses} titleOf={titleOf} href={href} limit={stacked ? 2 : 5} />
    </header>
  );
}

/** A row of chips. What does not fit on the row is one press away, and the row says how many. */
function ChipRow({ label, empty, ids, titleOf, href, tags, limit = 5 }: { label: string; empty?: string; ids: string[]; titleOf(id: string): string; href(id: string): string; tags?: boolean; limit?: number }) {
  const [open, setOpen] = useState(false);
  useEffect(() => setOpen(false), [ids]);
  const cut = !open && ids.length > limit + 1;
  const shown = cut ? ids.slice(0, limit) : ids;
  return (
    <div className="bench-chips">
      <span className="bench-chips__label">{label}</span>
      {!ids.length && <span className="bench-chips__empty">{empty}</span>}
      {shown.map((id) => (
        <a key={id} className={tags ? "bench-chip bench-chip--tag" : "bench-chip"} href={href(id)}>
          {titleOf(id)}
        </a>
      ))}
      {cut && (
        <button type="button" className="bench-chip bench-chip--more" onClick={() => setOpen(true)}>
          and {ids.length - limit} more
        </button>
      )}
    </div>
  );
}

function Columns({ id, record, slots, onUnfold }: { id: string; record: RecordAlignment; slots: Slot[]; onUnfold(level: Level): void }) {
  return (
    <div className="bench-levels">
      {slots.map((slot) => {
        if (slot.state === "column") {
          return (
            <section key={slot.level} className="bench-col" style={{ flexGrow: slot.weight }} aria-label={LEVEL_NAMES[slot.level]}>
              <ColumnHead record={record} level={slot.level} />
              <div className="bench-col__scroll" tabIndex={0} data-scrolls="" aria-label={`${LEVEL_NAMES[slot.level]}, its text for this step`}>
                <LevelBody record={record} level={slot.level} />
              </div>
            </section>
          );
        }
        if (slot.state === "folded") {
          return (
            <button key={slot.level} type="button" className="bench-strip bench-strip--folded" onClick={() => onUnfold(slot.level)}>
              <span>Show the {LEVEL_NAMES[slot.level].toLowerCase()}</span>
            </button>
          );
        }
        if (slot.level === "lean") {
          return (
            <div key={slot.level} className="bench-absent">
              <p className="bench-absent__title">{absentWords("lean")}</p>
              <p>{leanAbsence(id)}</p>
            </div>
          );
        }
        return (
          <div key={slot.level} className="bench-strip">
            <span>{absentWords(slot.level)}</span>
          </div>
        );
      })}
    </div>
  );
}

function ColumnHead({ record, level }: { record: RecordAlignment; level: Level }) {
  return (
    <header className="bench-col__head">
      <h2>{LEVEL_NAMES[level]}</h2>
      <p>{levelVerb(record, level)}</p>
    </header>
  );
}

function LevelBody({ record, level }: { record: RecordAlignment; level: Level }) {
  if (level === "lean") {
    return (
      <>
        {record.lean.map((row) => (
          <article key={row.name} className="bench-decl">
            <LazyLeanBlock name={row.name} relation={row.relation} note={row.note} clause={row.clause} compact />
          </article>
        ))}
      </>
    );
  }
  return (
    <>
      {statementsOf(record, level).map((s) => (
        <SliceRow key={`${s.start_byte}:${s.end_byte}`} statement={s} />
      ))}
    </>
  );
}

function SliceRow({ statement }: { statement: AlignedStatement }) {
  return (
    <article className="bench-slice">
      <header className="bench-slice__head">
        <span className="bench-slice__role">{roleWords(statement.role)}</span>
        <span className="bench-slice__section">{sectionLabel(statement.section)}</span>
      </header>
      <LazyStatementSlice statement={statement} />
      {statement.note && <p className="bench-slice__note">{statement.note}</p>}
      <a className="bench-slice__read" href={statementHref(statement)}>
        Read in context
      </a>
    </article>
  );
}

/** Below 1000px the levels stack in reading order, and tabs jump between them. */
function StackedLevels({ id, record, slots }: { id: string; record: RecordAlignment; slots: Slot[] }) {
  const has = (level: Level) => slots.some((s) => s.level === level && s.state !== "empty");
  const [active, setActive] = useState<Level>(() => LEVELS.find(has) ?? "lean");
  const root = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const scroller = root.current?.closest<HTMLElement>(".bench-main");
    if (!scroller || !root.current) return;
    const observer = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) if (entry.isIntersecting) setActive((entry.target as HTMLElement).dataset.level as Level);
      },
      { root: scroller, rootMargin: "-20% 0px -70% 0px" },
    );
    root.current.querySelectorAll("[data-level]").forEach((el) => observer.observe(el));
    return () => observer.disconnect();
  }, []);
  const jump = (level: Level) => {
    setActive(level);
    root.current?.querySelector(`[data-level="${level}"]`)?.scrollIntoView({ block: "start" });
  };
  return (
    <div className="bench-stack" ref={root}>
      <div className="bench-tabs" role="group" aria-label="Jump to a level">
        {LEVELS.map((level) => (
          <button key={level} type="button" className="bench-tab" aria-current={active === level ? "true" : undefined} disabled={!has(level)} onClick={() => jump(level)}>
            {LEVEL_NAMES[level]}
          </button>
        ))}
      </div>
      {LEVELS.map((level) =>
        has(level) ? (
          <section key={level} className="bench-stack__level" data-level={level} aria-label={LEVEL_NAMES[level]}>
            <ColumnHead record={record} level={level} />
            <LevelBody record={record} level={level} />
          </section>
        ) : (
          <p key={level} className="bench-stack__absent">
            {level === "lean" ? leanAbsence(id) : `${absentWords(level)}.`}
          </p>
        ),
      )}
    </div>
  );
}

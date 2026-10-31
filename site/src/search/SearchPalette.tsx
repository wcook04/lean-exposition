// Search across the edition: records on the map, paper headings, mapped passages
// and Lean declaration names. Every word typed is required, as a whole word or the
// start of one; each group is ordered by title matches and by how close together
// the words occur (rank.ts). Follows the WAI-ARIA combobox pattern with a grouped listbox.
// The palette shows the first few of each kind; a truncated group ends in
// "See all N matching …", which opens the full results page for the query.

import { useCallback, useEffect, useId, useLayoutEffect, useMemo, useRef, useState, type KeyboardEvent, type ReactNode } from "react";
import "katex/dist/katex.min.css";
import type { SearchItem } from "../api/types";
import { describeError, useEdition } from "../app/data";
import { navigate, routeHref, type SearchType } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { destination, LeanResultBody, nounFor, ResultBody, SEARCH_HELP, typeOfTable } from "./results";
import { rankedSearch } from "./rank";
import { leanNames, searchLean, type LeanHit } from "./leanNames";
import "./search.css";

const DEBOUNCE = 180;
const MAX_TOKENS = 16;
const MAX_CHARS = 256;

const TABLES: { table: string; limit: number }[] = [
  { table: "nodes", limit: 4 },
  { table: "sections", limit: 4 },
  { table: "passages", limit: 4 },
  { table: "citations", limit: 3 },
  { table: "sources", limit: 2 },
  { table: "evidence", limit: 3 },
];

const LEAN_LIMIT = 4;

type GroupId = "start" | "map" | "sections" | "passages" | "lean" | "other";

const GROUP_TABLES: Record<Exclude<GroupId, "start" | "lean">, string[]> = {
  map: ["nodes"],
  sections: ["sections"],
  passages: ["passages"],
  other: ["citations", "sources", "evidence"],
};

const GROUP_TITLES: Record<GroupId, string> = {
  start: "Places to start",
  map: "Records on the argument map",
  sections: "Sections",
  passages: "Passages",
  lean: "Lean declarations",
  other: "Citations, sources and check records",
};

interface Option {
  key: string;
  group: GroupId;
  item?: SearchItem;
  leanHit?: LeanHit;
  /** Fixed content for starting points. */
  title?: string;
  meta?: string;
  lean?: boolean;
  href?: string;
  /** A "See all N matching …" row at the end of a truncated group. */
  more?: boolean;
}

interface Results {
  q: string;
  byTable: Map<string, { items: SearchItem[]; total: number }>;
  lean: LeanHit[];
}

type Phase = { status: "idle" } | { status: "loading" } | { status: "ready" } | { status: "error"; message: string };

export function SearchPalette({ onClose }: { onClose: () => void }) {
  const edition = useEdition();
  const { graph, overview } = edition;
  const uid = useId();
  const inputRef = useRef<HTMLInputElement>(null);
  const dialogRef = useRef<HTMLDivElement>(null);
  const listRef = useRef<HTMLDivElement>(null);
  const [text, setText] = useState("");
  const [results, setResults] = useState<Results | null>(null);
  const [phase, setPhase] = useState<Phase>({ status: "idle" });
  const [active, setActive] = useState(0);
  const [opening, setOpening] = useState<string | null>(null);

  // Focus: into the input on open, back to where it was on close.
  useLayoutEffect(() => {
    const previous = document.activeElement as HTMLElement | null;
    inputRef.current?.focus();
    const root = document.documentElement;
    const overflow = root.style.overflow;
    root.style.overflow = "hidden";
    return () => {
      root.style.overflow = overflow;
      if (previous && previous.isConnected) previous.focus({ preventScroll: true });
    };
  }, []);

  const tokens = text.trim() ? text.trim().split(/\s+/) : [];
  const tooLong = tokens.length > MAX_TOKENS || text.length > MAX_CHARS;

  useEffect(() => {
    const q = text.trim();
    if (!q || tooLong) {
      setResults(null);
      setPhase({ status: "idle" });
      return;
    }
    const controller = new AbortController();
    setPhase({ status: "loading" });
    const timer = window.setTimeout(() => {
      Promise.all([rankedSearch(q, TABLES.map((t) => t.table), controller.signal), leanNames()]).then(
        ([ranked, names]) => {
          if (controller.signal.aborted) return;
          const byTable = new Map(TABLES.map(({ table, limit }) => {
            const all = ranked.get(table) ?? [];
            return [table, { items: all.slice(0, limit), total: all.length }] as const;
          }));
          setResults({ q, byTable, lean: names ? searchLean(names, q) : [] });
          setPhase({ status: "ready" });
          setActive(0);
        },
        (error: unknown) => {
          if (controller.signal.aborted) return;
          setPhase({ status: "error", message: describeError(error).detail || describeError(error).title });
        },
      );
    }, DEBOUNCE);
    return () => {
      controller.abort();
      window.clearTimeout(timer);
    };
  }, [text, tooLong]);

  const starts = useMemo<Option[]>(() => {
    const out: Option[] = [];
    const long = overview.papers.find((p) => p.stage === "long");
    const main = (long?.paper_scope.selected_goal_ids ?? graph.goals).find((g) => graph.nodes.has(g));
    if (main) {
      out.push({ key: "start:main", group: "start", title: graph.nodes.get(main)!.label, meta: "Opens the main result on the argument map", href: routeHref({ view: "map", node: main }) });
    }
    for (const stage of STAGE_ORDER) {
      out.push({ key: `start:${stage}`, group: "start", title: PAPER_NAMES[stage].short, meta: PAPER_NAMES[stage].job, href: routeHref({ view: "read", stage }) });
    }
    const formal = graph.edges.filter((e) => e.kind === "formalizes" && graph.nodes.get(e.from)?.kind === "goal");
    for (const e of formal) {
      out.push({
        key: `start:${e.to}`,
        group: "start",
        title: graph.nodes.get(e.to)!.label,
        lean: true,
        meta: `The Lean statement recorded as corresponding to ${graph.nodes.get(e.from)!.label}, with its check records`,
        href: routeHref({ view: "checks", node: e.to }),
      });
    }
    return out;
  }, [graph, overview]);

  const options = useMemo<Option[]>(() => {
    if (!results) return text.trim() ? [] : starts;
    const out: Option[] = [];
    const lean = () => {
      for (const hit of results.lean.slice(0, LEAN_LIMIT)) {
        out.push({ key: `lean:${hit.module}:${hit.name}`, group: "lean", leanHit: hit, href: routeHref({ view: "lean", module: hit.module, decl: hit.name }) });
      }
      if (results.lean.length > LEAN_LIMIT) {
        out.push({ key: "more:lean", group: "lean", more: true, title: `See all ${results.lean.length} matching Lean declarations`, href: routeHref({ view: "search", q: results.q }) });
      }
    };
    for (const [group, tables] of Object.entries(GROUP_TABLES) as [Exclude<GroupId, "start" | "lean">, string[]][]) {
      if (group === "other") lean();
      let shown = 0;
      let total = 0;
      let first: SearchType | null = null;
      for (const table of tables) {
        const page = results.byTable.get(table);
        for (const item of page?.items ?? []) out.push({ key: `${table}:${item.ref}`, group, item });
        shown += page?.items.length ?? 0;
        total += page?.total ?? 0;
        if (!first && page?.total) first = typeOfTable(table);
      }
      if (total > shown && first) {
        const noun = tables.length === 1 ? nounFor(first, total) : "citations, sources and check records";
        out.push({
          key: `more:${group}`,
          group,
          more: true,
          title: `See all ${total} matching ${noun}`,
          href: routeHref({ view: "search", q: results.q, type: first }),
        });
      }
    }
    return out;
  }, [results, starts, text]);

  const groups = useMemo(() => {
    const order: GroupId[] = ["start", "map", "sections", "passages", "lean", "other"];
    return order
      .map((id) => ({ id, options: options.filter((o) => o.group === id) }))
      .filter((g) => g.options.length > 0);
  }, [options]);

  const totals = useMemo(() => {
    const t: Partial<Record<GroupId, { shown: number; total: number }>> = {};
    if (!results) return t;
    const sum = (tables: string[]) =>
      tables.reduce(
        (acc, table) => {
          const page = results.byTable.get(table);
          return { shown: acc.shown + (page?.items.length ?? 0), total: acc.total + (page?.total ?? 0) };
        },
        { shown: 0, total: 0 },
      );
    t.map = sum(["nodes"]);
    t.sections = sum(["sections"]);
    t.passages = sum(["passages"]);
    t.other = sum(["citations", "sources", "evidence"]);
    t.lean = { shown: Math.min(LEAN_LIMIT, results.lean.length), total: results.lean.length };
    return t;
  }, [results]);

  const optionId = (index: number) => `${uid}-option-${index}`;
  const activeIndex = Math.min(active, Math.max(0, options.length - 1));

  useEffect(() => {
    const el = document.getElementById(optionId(activeIndex));
    el?.scrollIntoView({ block: "nearest" });
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [activeIndex, options]);

  const open = useCallback(
    async (option: Option) => {
      setOpening(option.key);
      try {
        const target = option.href ?? (option.item ? await destination(option.item, graph) : null);
        if (!target) {
          setOpening(null);
          return;
        }
        if (/^https?:\/\//.test(target)) window.open(target, "_blank", "noopener,noreferrer");
        else navigate(target);
        onClose();
      } catch (error) {
        setOpening(null);
        setPhase({ status: "error", message: describeError(error).title });
      }
    },
    [graph, onClose],
  );

  const onKeyDown = (event: KeyboardEvent<HTMLDivElement>) => {
    if (event.key === "Escape") {
      event.preventDefault();
      event.stopPropagation();
      onClose();
      return;
    }
    if (event.key === "Tab") {
      const focusables = [...(dialogRef.current?.querySelectorAll<HTMLElement>("input, button, a[href]") ?? [])];
      if (focusables.length === 0) return;
      const index = focusables.indexOf(document.activeElement as HTMLElement);
      const next = event.shiftKey ? (index <= 0 ? focusables.length - 1 : index - 1) : index === focusables.length - 1 ? 0 : index + 1;
      event.preventDefault();
      focusables[next].focus();
      return;
    }
    if (event.target !== inputRef.current) return;
    if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      event.preventDefault();
      if (options.length === 0) return;
      const delta = event.key === "ArrowDown" ? 1 : -1;
      setActive((activeIndex + delta + options.length) % options.length);
    } else if (event.key === "Home" && event.ctrlKey) {
      event.preventDefault();
      setActive(0);
    } else if (event.key === "End" && event.ctrlKey) {
      event.preventDefault();
      setActive(options.length - 1);
    } else if (event.key === "Enter") {
      event.preventDefault();
      const option = options[activeIndex];
      if (option) void open(option);
    }
  };

  let status: ReactNode;
  if (tooLong) status = `Search takes at most ${MAX_TOKENS} words and ${MAX_CHARS} characters. Remove some words.`;
  else if (phase.status === "error") status = phase.message;
  else if (!text.trim()) status = null;
  else if (phase.status === "loading" && !results) status = "Searching…";
  else if (results && options.length === 0)
    status = (
      <>
        No record, section heading, linked passage or Lean name contains all of the words <q>{results.q}</q>, as whole
        words or the starts of words. Other text in the papers is not searched. Try fewer words, or another spelling.
      </>
    );
  else if (results) {
    const total = [...results.byTable.values()].reduce((s, p) => s + p.total, results.lean.length);
    status = (
      <>
        {total} {total === 1 ? "match" : "matches"} in all.{" "}
        <a href={routeHref({ view: "search", q: results.q })} onClick={() => onClose()}>
          List every result
        </a>
        {phase.status === "loading" ? " Updating…" : ""}
      </>
    );
  }

  let index = -1;
  return (
    <div className="palette-scrim" onMouseDown={(e) => e.target === e.currentTarget && onClose()}>
      <div
        ref={dialogRef}
        className="palette"
        role="dialog"
        aria-modal="true"
        aria-labelledby={`${uid}-title`}
        data-modal-open=""
        onKeyDown={onKeyDown}
      >
        <h2 id={`${uid}-title`} className="visually-hidden">
          Search records and passages
        </h2>
        <div className="palette__field">
          <svg className="palette__icon" viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
            <circle cx="7" cy="7" r="4.6" fill="none" stroke="currentColor" strokeWidth="1.5" />
            <path d="M10.5 10.5L14 14" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
          </svg>
          <input
            ref={inputRef}
            className="palette__input"
            type="text"
            role="combobox"
            aria-expanded={options.length > 0}
            aria-controls={`${uid}-listbox`}
            aria-activedescendant={options.length > 0 ? optionId(activeIndex) : undefined}
            aria-autocomplete="list"
            aria-describedby={`${uid}-hint`}
            aria-label="Search records and passages"
            placeholder="Words to find"
            autoComplete="off"
            autoCorrect="off"
            autoCapitalize="off"
            spellCheck={false}
            value={text}
            maxLength={MAX_CHARS + 40}
            onChange={(e) => setText(e.target.value)}
          />
          <button type="button" className="palette__close" aria-label="Close search" onClick={onClose}>
            <span className="kbd palette__esc" aria-hidden="true">
              Esc
            </span>
            <span className="palette__close-word">Close</span>
          </button>
        </div>
        <p id={`${uid}-hint`} className="palette__hint" hidden={!!text.trim()}>
          {SEARCH_HELP}
        </p>

        <div ref={listRef} id={`${uid}-listbox`} role="listbox" aria-label="Results" className="palette__list">
          {groups.map((group) => {
            const count = totals[group.id];
            return (
              <div key={group.id} role="group" aria-labelledby={`${uid}-group-${group.id}`} className="palette__group">
                <div id={`${uid}-group-${group.id}`} role="presentation" className="palette__group-head">
                  <span>{GROUP_TITLES[group.id]}</span>
                  {count && (
                    <span className="palette__count num">
                      {count.shown === count.total ? `${count.total} found` : `first ${count.shown} of ${count.total}`}
                    </span>
                  )}
                </div>
                {group.options.map((option) => {
                  index += 1;
                  const i = index;
                  return (
                    <div
                      key={option.key}
                      id={optionId(i)}
                      role="option"
                      aria-selected={i === activeIndex}
                      className={`palette__option${option.more ? " palette__more" : ""}${i === activeIndex ? " is-active" : ""}`}
                      onMouseMove={() => i !== activeIndex && setActive(i)}
                      onMouseDown={(e) => e.preventDefault()}
                      onClick={() => void open(option)}
                    >
                      {option.more ? (
                        <span className="palette__more-text">
                          {option.title}
                          <span aria-hidden="true"> →</span>
                        </span>
                      ) : option.leanHit ? (
                        <LeanResultBody hit={option.leanHit} />
                      ) : option.item ? (
                        <ResultBody item={option.item} opening={opening === option.key} />
                      ) : (
                        <>
                          <span className={`palette__title${option.lean ? " lean" : ""}`}>{option.title}</span>
                          {option.meta && <span className="palette__meta">{option.meta}</span>}
                        </>
                      )}
                    </div>
                  );
                })}
              </div>
            );
          })}
        </div>

        <div className="palette__foot">
          <p className="palette__status" role="status" aria-live="polite">
            {status}
          </p>
          <p className="palette__keys" aria-hidden="true" hidden={options.length === 0}>
            <span className="kbd">↑</span>
            <span className="kbd">↓</span> to move, <span className="kbd">Enter</span> to open
          </p>
        </div>
      </div>
    </div>
  );
}


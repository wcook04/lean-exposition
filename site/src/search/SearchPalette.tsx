// Search across the edition: records on the map, paper headings and mapped
// passages. The server matches the exact words typed (case-folded, every
// word required); results are grouped by what they open, not ranked by
// meaning. Follows the WAI-ARIA combobox pattern with a grouped listbox.

import { useCallback, useEffect, useId, useLayoutEffect, useMemo, useRef, useState, type KeyboardEvent, type ReactNode } from "react";
import "katex/dist/katex.min.css";
import { query } from "../api/client";
import type { Page, RecordDetail, SearchItem, Stage } from "../api/types";
import { describeError, useEdition, useRecord } from "../app/data";
import { navigate, routeHref } from "../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { kindName } from "../map/labels";
import { CHECK_KINDS, OUTCOME_NAMES } from "../checks/summary";
import { loadDocument, sectionTitleOf, useDocument } from "../reader/documents";
import { renderTex } from "../reader/math";
import { get } from "../api/client";
import { prepareExcerpt, type PreparedExcerpt } from "./excerpt";
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

type GroupId = "start" | "map" | "sections" | "passages" | "other";

const GROUP_TITLES: Record<GroupId, string> = {
  start: "Places to start",
  map: "Results on the map",
  sections: "Sections",
  passages: "Passages",
  other: "Citations, sources and check records",
};

interface Option {
  key: string;
  group: GroupId;
  item?: SearchItem;
  /** Fixed content for starting points. */
  title?: string;
  meta?: string;
  lean?: boolean;
  href?: string;
}

interface Results {
  q: string;
  byTable: Map<string, Page<SearchItem>>;
}

type Phase = { status: "idle" } | { status: "loading" } | { status: "ready" } | { status: "error"; message: string };

const FIELD_NAMES: Record<string, string> = {
  statement: "Statement",
  boundary: "Scope",
  locator: "Where in the source",
  id: "Identifier",
  declaration: "Lean name",
  title: "Title",
  details: "Record",
  tool: "Tool",
  url: "Address",
  path: "File",
  kind: "Kind",
  rationale: "Reason",
  citation_ids: "Citations",
  subject_ids: "Concerns",
  source_ids: "Sources",
  source_id: "Source",
  evidence_ids: "Checks",
  assumption_ids: "Assumptions",
  note: "Note",
};

function stageOf(item: SearchItem): Stage | null {
  const fromPapers = (item.papers as string[] | undefined)?.[0];
  const fromHref = /[?&]paper=([a-z]+)/.exec(item.href ?? "")?.[1];
  const value = fromHref ?? fromPapers;
  return value === "long" || value === "short" || value === "expository" ? value : null;
}

function idFromRef(ref: string, table: string): string {
  const marker = `/${table}/`;
  const at = ref.lastIndexOf(marker);
  return at >= 0 ? ref.slice(at + marker.length) : ref;
}

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
      Promise.all(
        TABLES.map(({ table, limit }) =>
          query<Page<SearchItem>>("/search", { q, table, limit }, controller.signal).then((r) => [table, r.data] as const),
        ),
      ).then(
        (pairs) => {
          if (controller.signal.aborted) return;
          setResults({ q, byTable: new Map(pairs) });
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
      out.push({ key: "start:main", group: "start", title: graph.nodes.get(main)!.label, meta: "The main result, on the argument map", href: routeHref({ view: "map", node: main }) });
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
        meta: `Lean statement of ${graph.nodes.get(e.from)!.label}, with its recorded checks`,
        href: routeHref({ view: "checks", node: e.to }),
      });
    }
    return out;
  }, [graph, overview]);

  const options = useMemo<Option[]>(() => {
    if (!results) return text.trim() ? [] : starts;
    const out: Option[] = [];
    const add = (table: string, group: GroupId) => {
      for (const item of results.byTable.get(table)?.items ?? []) out.push({ key: `${table}:${item.ref}`, group, item });
    };
    add("nodes", "map");
    add("sections", "sections");
    add("passages", "passages");
    add("citations", "other");
    add("sources", "other");
    add("evidence", "other");
    return out;
  }, [results, starts, text]);

  const groups = useMemo(() => {
    const order: GroupId[] = ["start", "map", "sections", "passages", "other"];
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
      const focusables = [...(dialogRef.current?.querySelectorAll<HTMLElement>("input, button") ?? [])];
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
        Nothing in this edition contains every one of these words: <q>{results.q}</q>. Try fewer words, or a different
        spelling of one.
      </>
    );
  else if (results) {
    const total = [...results.byTable.values()].reduce((s, p) => s + p.total, 0);
    status = `${total} ${total === 1 ? "match" : "matches"} in all. ${phase.status === "loading" ? "Updating…" : ""}`;
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
          Search this edition
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
            aria-label="Search words"
            placeholder="Search for words"
            autoComplete="off"
            autoCorrect="off"
            autoCapitalize="off"
            spellCheck={false}
            value={text}
            maxLength={MAX_CHARS + 40}
            onChange={(e) => setText(e.target.value)}
          />
          <button type="button" className="palette__close" onClick={onClose}>
            <span className="kbd palette__esc" aria-hidden="true">
              Esc
            </span>
            <span className="palette__close-word">Close</span>
          </button>
        </div>
        <p id={`${uid}-hint`} className="palette__hint">
          Finds the exact words you type, all of them, in records, headings and mapped passages. It does not search for
          meanings or related terms.
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
                      className={`palette__option${i === activeIndex ? " is-active" : ""}`}
                      onMouseMove={() => i !== activeIndex && setActive(i)}
                      onMouseDown={(e) => e.preventDefault()}
                      onClick={() => void open(option)}
                    >
                      {option.item ? (
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

// ---------------------------------------------------------------- one result

function ResultBody({ item, opening }: { item: SearchItem; opening: boolean }) {
  const excerpt = useMemo(() => prepareExcerpt(item), [item]);
  switch (item.table) {
    case "nodes":
      return <NodeResult item={item} excerpt={excerpt} opening={opening} />;
    case "sections":
      return <SectionResult item={item} excerpt={excerpt} opening={opening} />;
    case "passages":
      return <PassageResult item={item} excerpt={excerpt} opening={opening} />;
    default:
      return <RecordResult item={item} excerpt={excerpt} opening={opening} />;
  }
}

function NodeResult({ item, excerpt, opening }: { item: SearchItem; excerpt: PreparedExcerpt | null; opening: boolean }) {
  const { graph } = useEdition();
  const id = idFromRef(item.ref, "nodes");
  const node = graph.nodes.get(id);
  const label = node?.label ?? item.label ?? id;
  const inLabel = excerpt?.field === "label";
  return (
    <>
      <span className={`palette__title${node?.kind === "declaration" ? " lean" : ""}`} data-region={node?.region}>
        {node && <span className="region-dot" aria-hidden="true" />}
        {inLabel && excerpt ? <Excerpt excerpt={{ ...excerpt, cutStart: false, cutEnd: false }} /> : label}
      </span>
      <span className="palette__meta">
        {node ? kindName(node.kind) : "Record"}
        {node && graph.regions.find((r) => r.id === node.region) && <> in {graph.regions.find((r) => r.id === node.region)!.title}</>}
        {opening && <span className="palette__opening"> Opening…</span>}
      </span>
      {excerpt && !inLabel && <ExcerptLine excerpt={excerpt} />}
    </>
  );
}

function SectionResult({ item, excerpt, opening }: { item: SearchItem; excerpt: PreparedExcerpt | null; opening: boolean }) {
  const stage = stageOf(item);
  return (
    <>
      <span className="palette__title palette__title--serif">{excerpt ? <Excerpt excerpt={excerpt} /> : sectionLabel(item.label ?? "")}</span>
      <span className="palette__meta">
        Heading in the {stage ? PAPER_NAMES[stage].short.toLowerCase() : "papers"}
        {opening && <span className="palette__opening"> Opening…</span>}
      </span>
    </>
  );
}

function PassageResult({ item, excerpt, opening }: { item: SearchItem; excerpt: PreparedExcerpt | null; opening: boolean }) {
  const stage = stageOf(item);
  const doc = useDocument(stage);
  const anchor = item.label ?? idFromRef(item.ref, "passages");
  const section = doc.status === "ready" ? sectionTitleOf(doc.value.paper, anchor) : null;
  return (
    <>
      <span className="palette__title palette__title--serif">{section ? sectionLabel(section) : humanAnchor(anchor)}</span>
      <span className="palette__meta">
        Passage in the {stage ? PAPER_NAMES[stage].short.toLowerCase() : "papers"}
        {opening && <span className="palette__opening"> Opening…</span>}
      </span>
      {excerpt && <ExcerptLine excerpt={excerpt} />}
    </>
  );
}

function RecordResult({ item, excerpt, opening }: { item: SearchItem; excerpt: PreparedExcerpt | null; opening: boolean }) {
  const { graph } = useEdition();
  const detail = useRecord(item.ref);
  const record = detail.status === "ready" ? detail.value.record : null;
  let title = item.label ?? idFromRef(item.ref, item.table);
  let meta = "";
  if (item.table === "citations") {
    title = (record?.title as string | undefined) ?? title;
    const owner = detail.status === "ready" ? ownerNode(detail.value, graph) : null;
    const ownerLabel = owner ? graph.nodes.get(owner)!.label : null;
    meta = !ownerLabel ? "Citation" : ownerLabel === title ? "Citation for the record of the same name" : `Citation for ${ownerLabel}`;
  } else if (item.table === "sources") {
    const path = record?.path as string | undefined;
    title = path ? path.slice(path.lastIndexOf("/") + 1) : title;
    meta = `Source ${record?.kind === "file" ? "file" : "publication"}`;
  } else if (item.table === "evidence") {
    title = (record?.tool as string | undefined) ?? title;
    const kind = CHECK_KINDS[String(record?.kind ?? "")]?.title;
    const status = OUTCOME_NAMES[String(record?.status ?? "")];
    meta = ["Check record", kind, status?.toLowerCase()].filter(Boolean).join(", ");
  } else if (item.table === "edges") {
    meta = "Recorded relation";
  }
  return (
    <>
      <span className="palette__title">{title}</span>
      <span className="palette__meta">
        {meta}
        {opening && <span className="palette__opening"> Opening…</span>}
      </span>
      {excerpt && <ExcerptLine excerpt={excerpt} />}
    </>
  );
}

/** "5.3 Strict curvature" as "§5.3 Strict curvature", as the record panel names sections. */
function sectionLabel(title: string): string {
  const match = title.match(/^(\d+(?:\.\d+)*)\.?\s+(.*)$/);
  return match ? `§${match[1]} ${match[2]}` : title;
}

function humanAnchor(anchor: string): string {
  const words = anchor.replace(/[-_]+/g, " ").trim();
  return words.charAt(0).toUpperCase() + words.slice(1);
}

function ExcerptLine({ excerpt }: { excerpt: PreparedExcerpt }) {
  const field = excerpt.field && excerpt.field !== "label" ? FIELD_NAMES[excerpt.field] ?? humanAnchor(excerpt.field) : null;
  return (
    <span className="palette__excerpt">
      {field && <span className="palette__field-name">{field}: </span>}
      <Excerpt excerpt={excerpt} />
    </span>
  );
}

function Excerpt({ excerpt }: { excerpt: PreparedExcerpt }) {
  return (
    <>
      {excerpt.cutStart && "…"}
      {excerpt.segments.map((s, i) => {
        if (s.kind === "math") {
          const html = renderTex(s.tex, false).html;
          const inner = <span className="palette__math" dangerouslySetInnerHTML={{ __html: html }} />;
          return s.mark ? <mark key={i}>{inner}</mark> : <span key={i}>{inner}</span>;
        }
        return s.mark ? <mark key={i}>{s.text}</mark> : <span key={i}>{s.text}</span>;
      })}
      {excerpt.cutEnd && "…"}
    </>
  );
}

// ------------------------------------------------------------- destinations

function ownerNode(detail: RecordDetail, graph: ReturnType<typeof useEdition>["graph"]): string | null {
  for (const relation of detail.relations) {
    if (relation.to !== detail.ref) continue;
    if (!relation.from.includes("/nodes/")) continue;
    const id = idFromRef(relation.from, "nodes");
    if (graph.nodes.has(id)) return id;
  }
  return null;
}

/** Where a result opens. Records on the map open the map; others their nearest reading place. */
async function destination(item: SearchItem, graph: ReturnType<typeof useEdition>["graph"]): Promise<string | null> {
  const stage = stageOf(item);
  switch (item.table) {
    case "nodes":
      return routeHref({ view: "map", node: idFromRef(item.ref, "nodes") });
    case "passages": {
      const anchor = item.label ?? idFromRef(item.ref, "passages");
      return stage ? routeHref({ view: "read", stage, anchor }) : null;
    }
    case "sections": {
      if (!stage) return null;
      const { doc } = await loadDocument(stage);
      const start = (item.span as { start_byte?: number } | undefined)?.start_byte ?? -1;
      const title = (item.label ?? "").replace(/\s+/g, " ").trim();
      const part = doc.parts.find((p) => p.span.start <= start && start < p.span.end);
      const same = (h: { title: string }) => h.title.replace(/\s+/g, " ").trim() === title;
      const heading = part?.headings.find(same) ?? doc.parts.flatMap((p) => p.headings).find(same);
      return routeHref({ view: "read", stage, anchor: heading?.id });
    }
    case "evidence":
      return routeHref({ view: "checks", node: idFromRef(item.ref, "evidence") });
    case "edges": {
      const detail = (await get<RecordDetail>("/record", { ref: item.ref })).data;
      const from = detail.record.from as string | undefined;
      return from && graph.nodes.has(from) ? routeHref({ view: "map", node: from }) : null;
    }
    default: {
      const detail = (await get<RecordDetail>("/record", { ref: item.ref })).data;
      const owner = ownerNode(detail, graph);
      if (owner) return routeHref({ view: "map", node: owner });
      const check = detail.relations.find((r) => r.to === detail.ref && r.from.includes("/evidence/"));
      if (check) return routeHref({ view: "checks", node: idFromRef(check.from, "evidence") });
      const passage = detail.usage?.direct_passages?.[0];
      if (passage) return routeHref({ view: "read", stage: passage.stage, anchor: passage.anchor });
      const url = detail.record.url as string | undefined;
      return url && /^https?:\/\//.test(url) ? url : null;
    }
  }
}

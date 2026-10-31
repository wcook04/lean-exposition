// How one search result is shown and where it opens, shared by the palette
// and the full results page. The kind of result is always said in words.

import { useMemo } from "react";
import type { Overview, RecordDetail, SearchItem, Stage } from "../api/types";
import { get } from "../api/client";
import { useEdition, useRecord } from "../app/data";
import { routeHref, type SearchType } from "../app/router";
import { PAPER_NAMES } from "../app/papers";
import { kindName } from "../map/labels";
import { shortTitle } from "../compare/useAlignment";
import { CHECK_KINDS, OUTCOME_NAMES } from "../checks/summary";
import { loadDocument, sectionTitleOf, useDocument } from "../reader/documents";
import { renderTex } from "../reader/math";
import type { ArgGraph } from "../model/graph";
import { prepareExcerpt, type PreparedExcerpt } from "./excerpt";
import type { StepTitles } from "./order";
import { markedPieces, type LeanHit } from "./leanNames";
import { kindWord } from "../lean/data";
import { isChallengeCopy } from "../lean/find";
import { hasLeanHost } from "../lean/walk";

/** The API table behind each kind of result, in the order results are listed. */
export const SEARCH_TABLES: { type: SearchType; table: string; noun: [string, string] }[] = [
  { type: "statements", table: "statements", noun: ["statement in the papers", "statements in the papers"] },
  { type: "records", table: "nodes", noun: ["step on the map", "steps on the map"] },
  { type: "sections", table: "sections", noun: ["section heading", "section headings"] },
  { type: "text", table: "paper", noun: ["place in the papers' text", "places in the papers' text"] },
  { type: "passages", table: "passages", noun: ["linked passage", "linked passages"] },
  { type: "citations", table: "citations", noun: ["citation", "citations"] },
  { type: "sources", table: "sources", noun: ["source", "sources"] },
  { type: "checks", table: "evidence", noun: ["check record", "check records"] },
];

export function tableOf(type: SearchType): string {
  return SEARCH_TABLES.find((t) => t.type === type)!.table;
}

export function typeOfTable(table: string): SearchType | null {
  return SEARCH_TABLES.find((t) => t.table === table)?.type ?? null;
}

export function nounFor(type: SearchType, n: number): string {
  const noun = SEARCH_TABLES.find((t) => t.type === type)!.noun;
  return n === 1 ? noun[0] : noun[1];
}

/** What search does, said the same way in the palette and on the results page. */
export const SEARCH_HELP =
  "Search finds Lean names and what the papers call them, the records of the argument, the exact statements in the papers, section headings and the full text of the three papers. Every word you type must appear, as a whole word or the start of one. It does not look for words with related meanings.";

/** A Lean declaration as a result: the name, what the papers call it, and what and where it is. */
export function LeanResultBody({ hit, beside }: { hit: LeanHit; beside?: boolean }) {
  const fromShort = hit.name.length - hit.short.length;
  const marks = hit.marks.flatMap(([a, b]): [number, number][] => (b <= fromShort ? [] : [[Math.max(a, fromShort) - fromShort, b - fromShort]]));
  const file = hit.module.split(".").slice(-2).join("/");
  const notation = hit.term?.tex ? renderTex(hit.term.tex, false).html : null;
  return (
    <>
      <span className="palette__title lean" translate="no">
        {markedPieces(hit.short, marks).map((piece, i) => (piece.mark ? <mark key={i}>{piece.text}</mark> : <span key={i}>{piece.text}</span>))}
        {notation && <span className="palette__notation" dangerouslySetInnerHTML={{ __html: notation }} />}
      </span>
      <span className="palette__meta">
        Lean {kindWord(hit.kind).toLowerCase()} in {isChallengeCopy(hit.module) ? `the Comparator challenge file ${hit.module.split(".").pop()}` : file}
        {beside ? ". Opens beside the paper" : ""}
      </span>
      {hit.term?.words && <span className="palette__excerpt">{hit.term.words.replace(/`/g, "")}</span>}
    </>
  );
}

/** How search knows the steps of the argument, from the edition's graph. */
export function stepTitles(graph: ArgGraph, main: string | null): StepTitles {
  return {
    main,
    titles(id) {
      const node = graph.nodes.get(id);
      return node ? [node.label, shortTitle(id, node.label)] : [];
    },
    idOf: (item) => idFromRef(item.ref, "nodes"),
    isDeclaration: (id) => graph.nodes.get(id)?.kind === "declaration",
  };
}

/** The main result the long record names, as the search's first place. */
export function mainStep(overview: Overview, graph: ArgGraph): string | null {
  const long = overview.papers.find((paper) => paper.stage === "long");
  return (long?.paper_scope.selected_goal_ids ?? graph.goals).find((goal) => graph.nodes.has(goal)) ?? null;
}

/** Whether a Lean result would open beside what is being read. */
export const opensBeside = hasLeanHost;

/** Where a result will open, in words, before it is opened. */
export function destinationWords(item: SearchItem): string {
  const stage = stageOf(item);
  const paper = stage ? PAPER_NAMES[stage].short : "the papers";
  switch (item.table) {
    case "nodes":
      return "Opens on the argument map";
    case "sections":
      return `Opens the ${paper.toLowerCase()} at this heading`;
    case "passages":
      return `Opens the ${paper.toLowerCase()} at this passage`;
    case "evidence":
      return "Opens on the checks page";
    case "edges":
      return "Opens the record that uses it on the argument map";
    case "statements":
      return `Opens the ${paper.toLowerCase()} at this statement`;
    case "paper":
      return `Opens the ${paper.toLowerCase()} at this paragraph`;
    default:
      return "Opens the record that uses it";
  }
}

/** The address a result opens without asking the server, when one is known. */
export function directHref(item: SearchItem): string | null {
  const stage = stageOf(item);
  switch (item.table) {
    case "nodes":
      return routeHref({ view: "map", node: idFromRef(item.ref, "nodes") });
    case "passages": {
      const anchor = item.label ?? idFromRef(item.ref, "passages");
      return stage ? routeHref({ view: "read", stage, anchor }) : null;
    }
    case "evidence":
      return routeHref({ view: "checks", node: idFromRef(item.ref, "evidence") });
    case "statements":
    case "paper":
      return item.href ?? null;
    default:
      return null;
  }
}

const FIELD_NAMES: Record<string, string> = {
  statement: "Statement",
  boundary: "Scope",
  locator: "Where in the source",
  id: "Identifier",
  declaration: "Lean name",
  title: "Title",
  details: "Step",
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

export function stageOf(item: SearchItem): Stage | null {
  const fromPapers = (item.papers as string[] | undefined)?.[0];
  const fromHref = /[?&]paper=([a-z]+)/.exec(item.href ?? "")?.[1];
  const value = fromHref ?? fromPapers;
  return value === "long" || value === "short" || value === "expository" ? value : null;
}

export function idFromRef(ref: string, table: string): string {
  const marker = `/${table}/`;
  const at = ref.lastIndexOf(marker);
  return at >= 0 ? ref.slice(at + marker.length) : ref;
}

// ---------------------------------------------------------------- one result

export function ResultBody({ item, opening }: { item: SearchItem; opening: boolean }) {
  const excerpt = useMemo(() => prepareExcerpt(item), [item]);
  switch (item.table) {
    case "nodes":
      return <NodeResult item={item} excerpt={excerpt} opening={opening} />;
    case "sections":
      return <SectionResult item={item} excerpt={excerpt} opening={opening} />;
    case "passages":
      return <PassageResult item={item} excerpt={excerpt} opening={opening} />;
    case "statements":
    case "paper":
      return <PaperResult item={item} excerpt={excerpt} />;
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
  const short = shortTitle(id, label);
  const marked = inLabel && excerpt ? <Excerpt excerpt={{ ...excerpt, cutStart: false, cutEnd: false }} /> : label;
  return (
    <>
      <span className={`palette__title${node?.kind === "declaration" && short === label ? " lean" : ""}`} data-region={node?.region}>
        {node && <span className="region-dot" aria-hidden="true" />}
        {short === label ? marked : short}
      </span>
      {short !== label && <span className={`palette__full${node?.kind === "declaration" ? " lean" : ""}`}>{marked}</span>}
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

const ROLE_NOUNS: Record<string, string> = { statement: "Statement", definition: "Definition", derivation: "Derivation", explanation: "Explanation", example: "Worked example" };

/** A statement or a paragraph of a paper, by where it stands there. */
function PaperResult({ item, excerpt }: { item: SearchItem; excerpt: PreparedExcerpt | null }) {
  const stage = stageOf(item);
  const paper = stage ? PAPER_NAMES[stage].short.toLowerCase() : "papers";
  const section = String(item.section ?? "");
  const statement = item.table === "statements";
  return (
    <>
      <span className="palette__title palette__title--serif">{statement ? item.label : section ? sectionLabel(section) : "Opening of the paper"}</span>
      <span className="palette__meta">
        {statement ? `${ROLE_NOUNS[String(item.role)] ?? "Statement"} in the ${paper}${section ? `, ${sectionLabel(section)}` : ""}` : `Text of the ${paper}`}
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
    meta = "Recorded link";
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

function ownerNode(detail: RecordDetail, graph: ArgGraph): string | null {
  for (const relation of detail.relations) {
    if (relation.to !== detail.ref) continue;
    if (!relation.from.includes("/nodes/")) continue;
    const id = idFromRef(relation.from, "nodes");
    if (graph.nodes.has(id)) return id;
  }
  return null;
}

/** Where a result opens. Records on the map open the map; others their nearest reading place. */
export async function destination(item: SearchItem, graph: ArgGraph): Promise<string | null> {
  const stage = stageOf(item);
  switch (item.table) {
    case "nodes":
      return routeHref({ view: "map", node: idFromRef(item.ref, "nodes") });
    case "passages": {
      const anchor = item.label ?? idFromRef(item.ref, "passages");
      return stage ? routeHref({ view: "read", stage, anchor }) : null;
    }
    case "statements":
    case "paper":
      return item.href ?? null;
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

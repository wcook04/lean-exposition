// The reading column for one record. Its first screen answers why the reader
// chose it: what it is and where it comes from, its title, a passage from the
// chosen account, then the recorded statement and scope, every direct
// relation (drawn on the map or not), and its sources and checks. Everything
// shown is the record as captured; the panel adds wording, not facts.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { routeHref, type Trace } from "../app/router";
import { kindLead } from "../checks/summary";
import { statedDate } from "../checks/summary";
import { closure, type ArgEdge } from "../model/graph";
import { transitiveReduction } from "../map/engine/skeleton";
import { Accounts } from "./Accounts";
import { LeanCode } from "./LeanCode";
import { flyTitle, installCardCapture, sourceFor } from "./flight";
import {
  announcement,
  firstSentence,
  groupPassages,
  kindWord,
  outcomeParts,
  relationName,
  routeView,
  shortRevision,
  statusWords,
  stepVerb,
  webUrl,
} from "./model";
import { CloseButton, CopyButton, Jumps, Pane, type PaneSpec } from "./parts";
import { useSheet } from "./sheet";
import { useProvenance } from "./sources";
import { failureKind, useRecordDetail, useStored } from "./stored";
import "./panel.css";

export type EchoHandler = (ids: ReadonlySet<string> | null) => void;

interface Props {
  nodeId: string;
  /**
   * One recorded route from the goal on screen down to this record, the goal
   * first and this record last. `null` says no route is recorded within the
   * current account; omitted, no route line is shown.
   */
  path?: string[] | null;
  trace?: Trace;
  onClose(): void;
  onSelect(id: string): void;
  onTrace(trace: Trace | undefined): void;
  /** Where passage links should open; the map opens the reader, the reader opens beside. */
  passageHref?: (stage: Stage, anchor: string) => string;
  compact?: boolean;
  /** Light these cards on the map while a list item is pointed at or focused. */
  onEcho?: EchoHandler;
  /** Open the view of one step (an edge key); "Inspect step" appears only when given. */
  onEdge?(key: string): void;
  /** The panel is sliding out. */
  leaving?: boolean;
  /** Open scrolled to this section ("explanation", "statement", "argument", "sources"). */
  section?: "explanation" | "statement" | "argument" | "sources";
  /** Mark the panel's root element, e.g. for the page to restore focus or measure it. */
  panelRef?: React.Ref<HTMLElement>;
}

const PANES: PaneSpec[] = [
  { id: "explanation", title: "Passages" },
  { id: "statement", title: "Statement" },
  { id: "argument", title: "Argument" },
  { id: "sources", title: "Sources & checks" },
];

export function RecordPanel({ nodeId, path, trace, onClose, onSelect, onTrace, passageHref, compact, onEcho, onEdge, leaving, section, panelRef }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const node = graph.nodes.get(nodeId)!;
  const { state: detail, retry } = useRecordDetail(node.ref);
  const rootRef = useRef<HTMLElement | null>(null);
  const headingRef = useRef<HTMLHeadingElement>(null);
  const bodyRef = useRef<HTMLDivElement>(null);
  const sheet = useSheet({ panel: rootRef, title: headingRef, enabled: !compact });

  useEffect(() => installCardCapture(), []);

  // A new selection: back to the top (or the asked-for section), focus the
  // title, and fly the clicked card's title in.
  useLayoutEffect(() => {
    const body = bodyRef.current;
    if (body) body.scrollTop = 0;
    const target = section ? rootRef.current?.querySelector<HTMLElement>(`[data-section="${section}"]`) : null;
    if (target && body && !compact) body.scrollTop = target.offsetTop - 48;
    const heading = headingRef.current;
    if (!heading) return;
    heading.focus({ preventScroll: true });
    if (compact) return;
    const from = sourceFor(nodeId, false);
    if (!from) return;
    return flyTitle(heading, from);
  }, [nodeId, compact, section]);

  // Clear any echo this panel set when it changes record or closes.
  useEffect(() => () => onEcho?.(null), [nodeId, onEcho]);

  const record = detail.status === "ready" ? detail.value.record : null;
  const grouped = useMemo(() => (detail.status === "ready" ? groupPassages(detail.value.aligned_passages ?? []) : null), [detail]);
  const memberships = useMemo(() => {
    const m: Partial<Record<Stage, string[]>> = {};
    if (detail.status === "ready") for (const p of detail.value.usage.paper_memberships) m[p.stage] = p.roles;
    else for (const [s, v] of Object.entries(node.papers)) m[s as Stage] = v!.roles;
    return m;
  }, [detail, node]);
  const href = passageHref ?? ((stage: Stage, anchor: string) => routeHref({ view: "read", stage, anchor, node: nodeId }));
  const origin = node.origin;
  const echo = (ids: Iterable<string> | null) => onEcho?.(ids ? new Set(ids) : null);
  const setRoot = (el: HTMLElement | null) => {
    rootRef.current = el;
    if (typeof panelRef === "function") panelRef(el);
    else if (panelRef) (panelRef as React.MutableRefObject<HTMLElement | null>).current = el;
  };
  const failed = detail.status === "error" ? failureKind(detail.error) : null;
  const peek = sheet.phone && sheet.state === "peek";

  return (
    <aside
      ref={setRoot}
      className={`panel${compact ? " panel--compact" : ""}${leaving ? " panel--leaving" : ""}${sheet.dragging ? " panel--dragging" : ""}`}
      aria-labelledby="panel-title"
      data-region={node.region}
      style={sheet.style}
      {...sheet.attrs}
    >
      {sheet.handle}
      <header className="panel__head">
        <div className="panel__id">
          <span className="caps">{kindWord(node.kind)}</span>
          <span className="panel__src" data-slot={origin.slot} title={origin.locator ?? undefined}>
            <span className="src-sq" aria-hidden="true" />
            <span className="panel__src-name">
              {origin.label}
              {origin.place && `, ${origin.place}`}
            </span>
          </span>
          <span className={`panel__status panel__status--${node.status}`}>{statusWords(node.status, "record")}</span>
          {!compact && <CloseButton onClose={onClose} />}
        </div>
        {sheet.modal && (
          <button type="button" className="panel__back" onClick={sheet.toPeek}>
            <span aria-hidden="true">↓ </span>Show the map
          </button>
        )}
        <h2 id="panel-title" ref={headingRef} tabIndex={-1} className={`panel__title${node.kind === "declaration" ? " lean" : ""}`}>
          {node.kind === "declaration" ? breakable(node.label) : node.label}
        </h2>
        {path !== undefined && <Route path={path} nodeId={nodeId} onSelect={onSelect} onEcho={echo} />}
        {peek && (
          <div className="panel__peek">
            <button ref={sheet.readRef} type="button" className="panel__action panel__action--primary" onClick={() => sheet.open()}>
              Read the record
            </button>
            <button type="button" className="panel__action" onClick={() => sheet.open("sources")}>
              Sources &amp; checks
            </button>
          </div>
        )}
      </header>

      <div className="panel__body" ref={bodyRef} hidden={peek || undefined}>
        <Jumps panes={PANES} root={rootRef} resetKey={nodeId} />
        <div className="panel__content" key={`b:${nodeId}`}>
          {failed === "missing" ? (
            <p className="panel__error" role="alert">
              This site has no record with this identifier.
            </p>
          ) : null}
          <Pane id="explanation" title="Passages">
            <Accounts
              nodeId={nodeId}
              grouped={grouped}
              memberships={memberships}
              status={detail.status}
              onRetry={retry}
              href={href}
            />
          </Pane>

          <Pane id="statement" title="Statement">
            <Statement
              kind={node.kind}
              status={node.status}
              statement={record?.statement ? String(record.statement) : null}
              boundary={record?.boundary ? String(record.boundary) : null}
              state={detail.status}
              onRetry={retry}
            />
          </Pane>

          <Pane id="argument" title="Argument">
            <Argument nodeId={nodeId} trace={trace} onTrace={onTrace} onSelect={onSelect} onEcho={echo} onEdge={onEdge} />
          </Pane>

          <Pane id="sources" title="Sources & checks">
            <Provenance
              nodeId={nodeId}
              sourceId={record?.source_id}
              citationIds={record?.citation_ids}
              declaration={record?.declaration}
            />
            <Checks nodeId={nodeId} evidenceIds={(record?.evidence_ids as string[] | undefined) ?? node.evidenceIds ?? []} />
          </Pane>
        </div>
      </div>
      <p className="visually-hidden" aria-live="polite">
        {leaving ? "" : announcement(node.label, kindWord(node.kind))}
      </p>
    </aside>
  );
}

// ------------------------------------------------------------------ route

function Route({
  path,
  nodeId,
  onSelect,
  onEcho,
}: {
  path: string[] | null;
  nodeId: string;
  onSelect(id: string): void;
  onEcho(ids: Iterable<string> | null): void;
}) {
  const { graph } = useEdition();
  const [open, setOpen] = useState(false);
  const [whole, setWhole] = useState(false);
  useEffect(() => {
    setOpen(false);
    setWhole(false);
  }, [nodeId]);
  if (path === null) return <p className="panel__route">No recorded route from the main result in this account</p>;
  if (path.length < 2) return null;
  const goal = path[0];
  const goalName = graph.regions.find((r) => r.goal === goal)?.title ?? graph.nodes.get(goal)?.label ?? goal;
  const steps = path.length - 1;
  const view = routeView(path, whole);
  const listId = `route-${nodeId.replace(/[^\w-]/g, "_")}`;
  return (
    <div className="panel__route">
      <button type="button" className="panel__route-toggle" aria-expanded={open} aria-controls={listId} onClick={() => setOpen((o) => !o)}>
        <span>
          One recorded route from <strong>{goalName}</strong>, in {steps} {steps === 1 ? "step" : "steps"}
        </span>
        <span className="panel__route-chev" aria-hidden="true" />
      </button>
      {open && (
        <ol className="panel__route-list" id={listId}>
          {view.items.map((id, i) => (
            <RouteItem key={id} id={id} current={id === nodeId} onSelect={onSelect} onEcho={onEcho}>
              {i === view.hiddenAt - 1 && view.hidden > 0 && (
                <button type="button" className="linklike panel__route-more" onClick={() => setWhole(true)}>
                  Show {view.hidden} intermediate {view.hidden === 1 ? "step" : "steps"}
                </button>
              )}
            </RouteItem>
          ))}
        </ol>
      )}
    </div>
  );
}

function RouteItem({
  id,
  current,
  onSelect,
  onEcho,
  children,
}: {
  id: string;
  current: boolean;
  onSelect(id: string): void;
  onEcho(ids: Iterable<string> | null): void;
  children?: React.ReactNode;
}) {
  const { graph } = useEdition();
  const label = graph.nodes.get(id)?.label ?? id;
  return (
    <li aria-current={current ? "location" : undefined}>
      {current ? (
        <span>{label}</span>
      ) : (
        <button type="button" className="linklike" onClick={() => onSelect(id)} onPointerEnter={() => onEcho([id])} onPointerLeave={() => onEcho(null)}>
          {label}
        </button>
      )}
      {children && <div className="panel__route-gap">{children}</div>}
    </li>
  );
}

// -------------------------------------------------------------- statement

function Statement({
  kind,
  status,
  statement,
  boundary,
  state,
  onRetry,
}: {
  kind: string;
  status: string;
  statement: string | null;
  boundary: string | null;
  state: "loading" | "error" | "ready";
  onRetry(): void;
}) {
  if (state === "loading") return <p className="panel__state faint">Loading the record…</p>;
  if (state === "error")
    return (
      <p className="panel__state" role="alert">
        The record could not be loaded.{" "}
        <button type="button" className="control panel__retry" onClick={onRetry}>
          Retry
        </button>
      </p>
    );
  const summary = boundary ? firstSentence(boundary) : null;
  return (
    <>
      <p className="panel__lead caps">Recorded statement</p>
      {statement ? (
        kind === "declaration" ? (
          <>
            <LeanCode source={statement} />
            <p className="panel__note">{statusWords(status, kind)}</p>
          </>
        ) : (
          <p className="panel__statement">{statement}</p>
        )
      ) : (
        <p className="panel__note">No statement is recorded for this record.</p>
      )}
      {summary && (
        <p className="panel__scope">
          <span className="panel__scope-lead">Scope</span> {summary}
        </p>
      )}
      {boundary && summary !== boundary.trim() && (
        <details className="panel__more-scope">
          <summary>Full recorded scope</summary>
          <p>{boundary}</p>
        </details>
      )}
    </>
  );
}

// --------------------------------------------------------------- argument

function Argument({
  nodeId,
  trace,
  onTrace,
  onSelect,
  onEcho,
  onEdge,
}: {
  nodeId: string;
  trace?: Trace;
  onTrace(trace: Trace | undefined): void;
  onSelect(id: string): void;
  onEcho(ids: Iterable<string> | null): void;
  onEdge?(key: string): void;
}) {
  const { graph } = useEdition();
  const restsOn = useMemo(() => closure(graph, nodeId, "prerequisites"), [graph, nodeId]);
  const feeds = useMemo(() => closure(graph, nodeId, "consumers"), [graph, nodeId]);
  // Relations the simplified map leaves out because a longer drawn route implies them.
  const implied = useMemo(() => transitiveReduction(graph.order, graph.edges).implied, [graph]);
  const prerequisites = graph.out.get(nodeId) ?? [];
  const uses = graph.in.get(nodeId) ?? [];
  const cites = useMemo(() => {
    const to = new Set<string>();
    const from = new Set<string>();
    for (const c of graph.cites) {
      if (c.from === nodeId && c.to !== nodeId && graph.nodes.has(c.to)) to.add(c.to);
      if (c.to === nodeId && c.from !== nodeId && graph.nodes.has(c.from)) from.add(c.from);
    }
    return { to: [...to], from: [...from] };
  }, [graph, nodeId]);
  const boundary = graph.boundaries.get(nodeId);

  return (
    <>
      <Relations
        title="Records it uses directly"
        edges={prerequisites}
        end="to"
        implied={implied}
        empty="No recorded inputs."
        onSelect={onSelect}
        onEcho={onEcho}
        onEdge={onEdge}
      />
      <Relations title="Records that use it directly" edges={uses} end="from" implied={implied} empty="No record is recorded as using it directly." onSelect={onSelect} onEcho={onEcho} onEdge={onEdge} />
      <div className="panel__trace" role="group" aria-label="Highlight on the map">
        <button
          type="button"
          className="control"
          aria-pressed={trace === "rests"}
          onClick={() => onTrace(trace === "rests" ? undefined : "rests")}
          onPointerEnter={() => onEcho(restsOn)}
          onPointerLeave={() => onEcho(null)}
          disabled={restsOn.size <= 1}
        >
          All records it uses (<span className="num">{restsOn.size - 1}</span>)
        </button>
        <button
          type="button"
          className="control"
          aria-pressed={trace === "uses"}
          onClick={() => onTrace(trace === "uses" ? undefined : "uses")}
          onPointerEnter={() => onEcho(feeds)}
          onPointerLeave={() => onEcho(null)}
          disabled={feeds.size <= 1}
        >
          All records that use it (<span className="num">{feeds.size - 1}</span>)
        </button>
      </div>
      <p className="panel__note">
        Each button highlights on the map every record reached through recorded links, directly or through other records.
      </p>
      {(cites.to.length > 0 || cites.from.length > 0) && (
        <div className="panel__cites">
          <p className="panel__group">
            Citations <span className="faint">(links for navigation, not part of the argument)</span>
          </p>
          <CiteList title="Cites" ids={cites.to} onSelect={onSelect} onEcho={onEcho} />
          <CiteList title="Cited by" ids={cites.from} onSelect={onSelect} onEcho={onEcho} />
        </div>
      )}
      {boundary && <p className="panel__note">{boundary}</p>}
    </>
  );
}

function Relations({
  title,
  edges,
  end,
  implied,
  empty,
  onSelect,
  onEcho,
  onEdge,
}: {
  title: string;
  edges: ArgEdge[];
  end: "from" | "to";
  implied: ReadonlySet<string>;
  empty: string;
  onSelect(id: string): void;
  onEcho(ids: Iterable<string> | null): void;
  onEdge?(key: string): void;
}) {
  const { graph } = useEdition();
  return (
    <div className="panel__rels">
      <p className="panel__group">
        {title} (<span className="num">{edges.length}</span>)
      </p>
      {edges.length === 0 ? (
        <p className="panel__note">{empty}</p>
      ) : (
        <ul className="rels">
          {edges.map((edge) => {
            const id = edge[end];
            const n = graph.nodes.get(id)!;
            return (
              <li key={edge.key} onPointerEnter={() => onEcho([id])} onPointerLeave={() => onEcho(null)}>
                <span className={`rel-sample rel-sample--${edge.kind}`} aria-hidden="true" />
                <span className="rels__word">{relationName(edge.kind)}</span>
                <span className="rels__what">
                  <button
                    type="button"
                    className={`rels__name${n.kind === "declaration" ? " lean" : ""}`}
                    onClick={() => onSelect(id)}
                    onFocus={() => onEcho([id])}
                    onBlur={() => onEcho(null)}
                  >
                    {n.label}
                  </button>
                  <span className="rels__meta">
                    {implied.has(edge.key) && <span className="faint">Not drawn on the map</span>}
                    {onEdge && (
                      <button
                        type="button"
                        className="linklike rels__inspect"
                        aria-label={`Open the step: ${graph.nodes.get(edge.from)?.label} ${stepVerb(edge.kind)} ${graph.nodes.get(edge.to)?.label}`}
                        onClick={() => onEdge(edge.key)}
                      >
                        Open step
                      </button>
                    )}
                  </span>
                </span>
              </li>
            );
          })}
        </ul>
      )}
    </div>
  );
}

function CiteList({ title, ids, onSelect, onEcho }: { title: string; ids: string[]; onSelect(id: string): void; onEcho(ids: Iterable<string> | null): void }) {
  const { graph } = useEdition();
  if (!ids.length) return null;
  return (
    <ul className="rels rels--cites" aria-label={title}>
      {ids.map((id) => (
        <li key={id} onPointerEnter={() => onEcho([id])} onPointerLeave={() => onEcho(null)}>
          <span className="rels__cite-mark" aria-hidden="true">↗</span>
          <span className="rels__word">{title}</span>
          <span className="rels__what">
            <button type="button" className="rels__name" onClick={() => onSelect(id)}>
              {graph.nodes.get(id)!.label}
            </button>
          </span>
        </li>
      ))}
    </ul>
  );
}

// ------------------------------------------------------- sources and checks

function Provenance({ nodeId, sourceId, citationIds, declaration }: { nodeId: string; sourceId?: string; citationIds?: string[]; declaration?: string }) {
  const { graph } = useEdition();
  const node = graph.nodes.get(nodeId)!;
  const origin = node.origin;
  const provenance = useProvenance();
  const source = provenance.status === "ready" && sourceId ? provenance.value.sources.get(sourceId) : undefined;
  const citations = provenance.status === "ready" ? (citationIds ?? []).map((id) => provenance.value.citations.get(id) ?? { id }) : [];
  const sourceUrl = webUrl(source?.url ?? origin.url);
  const revision = source?.revision ?? null;
  return (
    <div className="prov">
      <p className="prov__source" data-slot={origin.slot}>
        <span className="src-sq" aria-hidden="true" />
        <span>
          {origin.label}
          {origin.place && <span className="muted">, {origin.place}</span>}
        </span>
      </p>
      {origin.locator && <p className="prov__locator">{origin.locator}</p>}
      {sourceUrl && (
        <p className="prov__open">
          <a href={sourceUrl} data-external rel="noopener" target="_blank">
            Open the source at the recorded revision <span aria-hidden="true">↗</span>
          </a>
        </p>
      )}
      <details className="prov__exact">
        <summary>File, revision and identifiers</summary>
        <dl>
          {source?.path && (
            <>
              <dt>File</dt>
              <dd>
                <code>{source.path}</code> <CopyButton text={source.path} what="file path" />
              </dd>
            </>
          )}
          {revision && (
            <>
              <dt>Revision</dt>
              <dd>
                <code title={revision}>{shortRevision(revision)}</code> <CopyButton text={revision} what="revision" />
              </dd>
            </>
          )}
          <dt>Record</dt>
          <dd>
            <code>{nodeId}</code> <CopyButton text={nodeId} what="record id" />
          </dd>
          {declaration && (
            <>
              <dt>Declaration</dt>
              <dd>
                <code className="lean">{declaration}</code> <CopyButton text={declaration} what="declaration name" />
              </dd>
            </>
          )}
        </dl>
      </details>
      {citations.length > 0 && (
        <>
          <p className="panel__group">Cited sources</p>
          <ul className="prov__cites">
            {citations.map((c) => {
              const url = webUrl(c.url);
              const label = c.title ?? c.id.replace(/_/g, " ");
              return (
                <li key={c.id}>
                  {url ? (
                    <a href={url} data-external rel="noopener" target="_blank">
                      {label} <span aria-hidden="true">↗</span>
                    </a>
                  ) : (
                    label
                  )}
                  {c.locator && <span className="faint">, {c.locator}</span>}
                </li>
              );
            })}
          </ul>
        </>
      )}
    </div>
  );
}

const CHECK_ORDER = ["source_hash", "lean_build", "comparator", "extraction", "semantic_review", "platform"];
const CHECK_TITLES: Record<string, string> = {
  source_hash: "Source file hashes",
  lean_build: "Lean build",
  comparator: "Comparator",
  extraction: "Dependency extraction",
  semantic_review: "Correspondence review",
  platform: "Platform label",
};
const OUTCOME_NAMES: Record<string, string> = { passed: "Passed", failed: "Failed", unavailable: "Unavailable", not_run: "Not run" };

/** One row per kind of check, each outcome in its own words; history in place. */
function Checks({ nodeId, evidenceIds }: { nodeId: string; evidenceIds: readonly string[] }) {
  const edition = useEdition();
  const stored = useStored();
  const [open, setOpen] = useState<string | null>(null);
  useEffect(() => setOpen(null), [nodeId]);
  const rows = useMemo(() => {
    const cards = new Map(edition.map.records.evidence.map((e) => [e.id, e]));
    const by = new Map<string, { id: string; label: string; status: string }[]>();
    for (const id of evidenceIds) {
      const c = cards.get(id);
      if (!c) continue;
      if (!by.has(c.kind)) by.set(c.kind, []);
      by.get(c.kind)!.push({ id, label: c.label, status: c.status });
    }
    const kinds = [...by.keys()].sort((a, b) => ((CHECK_ORDER.indexOf(a) + 99) % 99) - ((CHECK_ORDER.indexOf(b) + 99) % 99));
    return kinds.map((kind) => {
      const records = by.get(kind)!;
      const counts: Record<string, number> = {};
      for (const r of records) counts[r.status] = (counts[r.status] ?? 0) + 1;
      return { kind, records, counts };
    });
  }, [edition, evidenceIds]);

  return (
    <div className="checks">
      <p className="panel__group">Recorded checks</p>
      {rows.length === 0 ? (
        <p className="panel__note">No check is recorded for this record.</p>
      ) : (
        <ul className="checks__rows">
          {rows.map((row) => {
            const passedReview = row.kind === "semantic_review" && (row.counts.passed ?? 0) > 0;
            const lead = passedReview ? "Review record: passed" : kindLead(row.kind, row.counts);
            const title = CHECK_TITLES[row.kind] ?? row.kind.replace(/_/g, " ");
            const isOpen = open === row.kind;
            const histId = `hist-${nodeId.replace(/[^\w-]/g, "_")}-${row.kind}`;
            return (
              <li key={row.kind} className="checks__row">
                <div className="checks__line">
                  <span className="checks__kind">{title}</span>
                  <span className="checks__outcomes">
                    {outcomeParts(row.counts).map((p, i) => (
                      <span key={p.status}>
                        {i > 0 && <span className="faint">, </span>}
                        <span className={`outcome outcome--${p.status}`}>
                          {p.n} {p.word}
                        </span>
                      </span>
                    ))}
                  </span>
                </div>
                {lead !== title && <p className="checks__lead">{lead}</p>}
                <button type="button" className="linklike checks__toggle" aria-expanded={isOpen} aria-controls={histId} onClick={() => setOpen(isOpen ? null : row.kind)}>
                  {isOpen ? "Hide the check records" : row.records.length === 1 ? "Show the check record" : `Show the ${row.records.length} check records`}
                </button>
                {isOpen && (
                  <ol className="checks__history" id={histId}>
                    {row.records.map((r) => {
                      const details = stored.status === "ready" ? stored.value.evidence.get(r.id)?.details : undefined;
                      const date = statedDate(details);
                      return (
                        <li key={r.id}>
                          <span className={`outcome outcome--${r.status}`}>{OUTCOME_NAMES[r.status] ?? r.status.replace(/_/g, " ")}</span>
                          <span className="checks__label">{r.label}</span>
                          {date && <span className="faint">{date.text}</span>}
                        </li>
                      );
                    })}
                  </ol>
                )}
              </li>
            );
          })}
        </ul>
      )}
      <p className="panel__more">
        <a href={routeHref({ view: "checks", node: nodeId })}>
          What each check examined <span aria-hidden="true">→</span>
        </a>
      </p>
    </div>
  );
}

/** A Lean name may wrap after each dot rather than inside a word. */
function breakable(name: string) {
  const parts = name.split(".");
  return parts.map((p, i) => (
    <span key={i}>
      {p}
      {i < parts.length - 1 && (
        <>
          .<wbr />
        </>
      )}
    </span>
  ));
}

// The place where one result opens up: what it says, how each account says
// it in its own rendered text, where it sits in the argument, where it comes
// from and what has been checked. Everything shown is the record as captured;
// the panel adds wording, not facts.

import { useEffect, useLayoutEffect, useMemo, useRef, type CSSProperties, type ReactNode } from "react";
import type { Stage } from "../api/types";
import { useEdition, useRecord } from "../app/data";
import { routeHref, type Trace } from "../app/router";
import { kindName } from "../map/labels";
import { checkSummary } from "../checks/summary";
import { closure, type ArgEdge } from "../model/graph";
import { Accounts } from "./Accounts";
import { LeanCode } from "./LeanCode";
import { flyTitle, installCardCapture, sourceFor } from "./flight";
import { announcement, collapsePath, firstSentence, groupPassages, shortRevision, statusWords, unusedBy, webUrl } from "./model";
import { useSheet } from "./sheet";
import { useProvenance } from "./sources";
import "./panel.css";

export type EchoHandler = (ids: ReadonlySet<string> | null) => void;

interface Props {
  nodeId: string;
  /** The chain of uses from the goal on screen down to this record. */
  path?: string[];
  trace?: Trace;
  onClose(): void;
  onSelect(id: string): void;
  onTrace(trace: Trace | undefined): void;
  /** Where passage links should open; the map opens the reader, the reader opens beside. */
  passageHref?: (stage: Stage, anchor: string) => string;
  compact?: boolean;
  /** Light these cards on the map while a list item is pointed at or focused. */
  onEcho?: EchoHandler;
  /** Open the view of one step (an edge key); the "Why" buttons appear only when given. */
  onEdge?(key: string): void;
  /** The panel is sliding out. */
  leaving?: boolean;
}

const SITE_TITLE = "Lean Exposition";

export function RecordPanel({ nodeId, path, trace, onClose, onSelect, onTrace, passageHref, compact, onEcho, onEdge, leaving }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const node = graph.nodes.get(nodeId)!;
  const detail = useRecord(node.ref);
  const headingRef = useRef<HTMLHeadingElement>(null);
  const bodyRef = useRef<HTMLDivElement>(null);
  const mounted = useRef(false);
  const sheet = useSheet();

  useEffect(() => installCardCapture(), []);

  // A new selection: back to the top, focus the title, fly the card's title in.
  useLayoutEffect(() => {
    const first = !mounted.current;
    mounted.current = true;
    if (bodyRef.current) bodyRef.current.scrollTop = 0;
    const heading = headingRef.current;
    if (!heading) return;
    heading.focus({ preventScroll: true });
    if (compact) return;
    const from = sourceFor(nodeId, !first);
    if (!from) return;
    return flyTitle(heading, from);
  }, [nodeId, compact]);

  // The browser tab names the selected record while the map panel is open.
  useEffect(() => {
    if (compact || leaving) return;
    const before = document.title;
    document.title = `${node.label} · ${SITE_TITLE}`;
    return () => {
      document.title = before.includes(" · ") && before.endsWith(SITE_TITLE) ? SITE_TITLE : before;
    };
  }, [node.label, compact, leaving]);

  // Clear any echo this panel set when it changes record or closes.
  useEffect(() => () => onEcho?.(null), [nodeId, onEcho]);

  const out = graph.out.get(nodeId) ?? [];
  const inc = graph.in.get(nodeId) ?? [];
  const uses = out.filter((e) => e.kind !== "assumes");
  const assumes = out.filter((e) => e.kind === "assumes");
  const usedBy = inc.filter((e) => e.kind !== "assumes");
  const assumedBy = inc.filter((e) => e.kind === "assumes");
  const restsOn = useMemo(() => closure(graph, nodeId, "prerequisites"), [graph, nodeId]);
  const feeds = useMemo(() => closure(graph, nodeId, "consumers"), [graph, nodeId]);
  const seeAlso = useMemo(() => {
    const ids = new Set<string>();
    for (const c of graph.cites) {
      if (c.from === nodeId) ids.add(c.to);
      if (c.to === nodeId) ids.add(c.from);
    }
    ids.delete(nodeId);
    return [...ids].filter((id) => graph.nodes.has(id));
  }, [graph, nodeId]);

  const record = detail.status === "ready" ? detail.value.record : null;
  const grouped = useMemo(
    () => (detail.status === "ready" ? groupPassages(detail.value.aligned_passages ?? []) : null),
    [detail],
  );
  const memberships = useMemo(() => {
    const m: Partial<Record<Stage, string[]>> = {};
    if (detail.status === "ready") for (const p of detail.value.usage.paper_memberships) m[p.stage] = p.roles;
    else for (const [s, v] of Object.entries(node.papers)) m[s as Stage] = v!.roles;
    return m;
  }, [detail, node]);
  const unused = useMemo(() => {
    const u: Partial<Record<Stage, boolean>> = {};
    for (const p of edition.overview.papers) u[p.stage] = unusedBy(graph, nodeId, p.paper_scope.selected_goal_ids);
    return u;
  }, [edition, graph, nodeId]);
  const checks = record ? checkSummary(edition, (record.evidence_ids as string[] | undefined) ?? []) : [];
  const boundary = graph.boundaries.get(nodeId);
  const href = passageHref ?? ((stage: Stage, anchor: string) => routeHref({ view: "read", stage, anchor, node: nodeId }));
  const crumbs = collapsePath(path && path.length > 1 ? path.slice(0, -1) : []);
  const origin = node.origin;
  const echo = (ids: Iterable<string> | null) => onEcho?.(ids ? new Set(ids) : null);

  let section = 0;
  const rise = (): CSSProperties => ({ ["--i" as string]: Math.min(section++, 5) });

  return (
    <aside
      className={`panel${compact ? " panel--compact" : ""}${leaving ? " panel--leaving" : ""}${sheet.dragging ? " panel--dragging" : ""}`}
      aria-labelledby="panel-title"
      data-region={node.region}
      data-sheet={compact ? undefined : sheet.state}
      style={sheet.style}
    >
      {!compact && sheet.handle}
      <header className="panel__head" key={`h:${nodeId}`}>
        <div className="panel__chips panel__rise">
          <span className="chip chip--kind">
            <span className="region-dot" aria-hidden="true" />
            {kindName(node.kind)}
          </span>
          <span className="chip chip--source" data-slot={origin.slot} title={origin.locator ?? undefined}>
            <span className="swatch" aria-hidden="true" />
            <span className="chip__text">
              {origin.label}
              {origin.place && <span className="chip__place"> · {origin.place}</span>}
            </span>
          </span>
        </div>
        <button type="button" className="control control--plain panel__close" aria-label="Close" onClick={onClose}>
          <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
            <path d="M2 2l8 8M10 2l-8 8" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
          </svg>
        </button>
        {crumbs.length > 0 && (
          <ol className="panel__path panel__rise" aria-label="From the goal to this result">
            {crumbs.map((id, i) =>
              id === null ? (
                <li key={`gap${i}`} className="panel__gap" aria-label="Steps between">
                  …
                </li>
              ) : (
                <li key={id}>
                  <button type="button" onClick={() => onSelect(id)} onPointerEnter={() => echo([id])} onPointerLeave={() => echo(null)}>
                    {graph.nodes.get(id)?.label ?? id}
                  </button>
                </li>
              ),
            )}
          </ol>
        )}
        <h2 id="panel-title" ref={headingRef} tabIndex={-1} className={`panel__title${node.kind === "declaration" ? " lean" : ""}`}>
          {node.label}
        </h2>
        <p className={`panel__status panel__status--${node.status} panel__rise`}>{statusWords(node.status, node.kind)}</p>
      </header>

      <div className="panel__body" ref={bodyRef}>
        <div className="panel__content" key={`b:${nodeId}`}>
          {(record?.statement || detail.status === "loading") && (
            <Section title="What it says" style={rise()}>
              {detail.status === "loading" && <p className="faint">Opening the record…</p>}
              {record?.statement &&
                (node.kind === "declaration" ? (
                  <LeanCode source={String(record.statement)} />
                ) : (
                  <p className="panel__statement">{String(record.statement)}</p>
                ))}
              {record?.boundary && (
                <p className="panel__boundary">
                  <span className="panel__lead">Scope</span> {String(record.boundary)}
                </p>
              )}
            </Section>
          )}

          <Section title="How each account says it" style={rise()}>
            <Accounts nodeId={nodeId} grouped={grouped} memberships={memberships} unused={unused} href={href} />
          </Section>

          <Section title="In the argument" style={rise()}>
            <div className="panel__trace" role="group" aria-label="Trace on the map">
              <button
                type="button"
                className="control"
                aria-pressed={trace === "rests"}
                onClick={() => onTrace(trace === "rests" ? undefined : "rests")}
                onPointerEnter={() => echo(restsOn)}
                onPointerLeave={() => echo(null)}
                disabled={restsOn.size <= 1}
              >
                Rests on <span className="num">{restsOn.size - 1}</span>
              </button>
              <button
                type="button"
                className="control"
                aria-pressed={trace === "uses"}
                onClick={() => onTrace(trace === "uses" ? undefined : "uses")}
                onPointerEnter={() => echo(feeds)}
                onPointerLeave={() => echo(null)}
                disabled={feeds.size <= 1}
              >
                Feeds <span className="num">{feeds.size - 1}</span>
              </button>
            </div>
            <NodeList title="Uses" edges={uses} end="to" onSelect={onSelect} onEcho={echo} onEdge={onEdge} empty="Uses nothing else recorded here." />
            <NodeList title="Used by" edges={usedBy} end="from" onSelect={onSelect} onEcho={echo} onEdge={onEdge} empty="Nothing recorded here uses it." />
            <NodeList title="Assumes" edges={assumes} end="to" onSelect={onSelect} onEcho={echo} onEdge={onEdge} />
            <NodeList title="Assumed by" edges={assumedBy} end="from" onSelect={onSelect} onEcho={echo} onEdge={onEdge} />
            {seeAlso.length > 0 && <SeeAlso ids={seeAlso} onSelect={onSelect} onEcho={echo} />}
            {boundary && <p className="panel__note">{boundary}</p>}
          </Section>

          <Section title="Where it comes from" style={rise()}>
            <Provenance nodeId={nodeId} sourceId={record?.source_id} citationIds={record?.citation_ids} declaration={record?.declaration} />
          </Section>

          {checks.length > 0 && (
            <Section title="What has been checked" style={rise()}>
              <ul className="plate__checks">
                {checks.map((row) => (
                  <li key={row.kind} className={`check check--${row.tone}`}>
                    <span className="check__mark" aria-hidden="true" />
                    <span className="check__kind">{row.title}</span>
                    <span className="check__outcome">{row.outcome}</span>
                  </li>
                ))}
              </ul>
              <p className="panel__more">
                <a href={routeHref({ view: "checks", node: nodeId })}>What each check examined</a>
              </p>
            </Section>
          )}
        </div>
      </div>
      <p className="visually-hidden" aria-live="polite">
        {leaving ? "" : announcement(node.label, kindName(node.kind))}
      </p>
    </aside>
  );
}

export function Section({ title, style, children }: { title: string; style?: CSSProperties; children: ReactNode }) {
  return (
    <section className="panel__section panel__rise" style={style}>
      <h3 className="panel__label">{title}</h3>
      {children}
    </section>
  );
}

function NodeList({
  title,
  edges,
  end,
  onSelect,
  onEcho,
  onEdge,
  empty,
}: {
  title: string;
  edges: ArgEdge[];
  end: "from" | "to";
  onSelect(id: string): void;
  onEcho(ids: Iterable<string> | null): void;
  onEdge?(key: string): void;
  empty?: string;
}) {
  const { graph } = useEdition();
  if (edges.length === 0) return empty ? <p className="panel__empty faint">{empty}</p> : null;
  return (
    <div className="panel__nodes">
      <p className="panel__nodes-title">
        {title} <span className="num">{edges.length}</span>
      </p>
      <ul>
        {edges.map((edge) => {
          const id = edge[end];
          const n = graph.nodes.get(id)!;
          const gist = edge.warrant?.text ? firstSentence(edge.warrant.text) : null;
          return (
            <li key={edge.key} className="panel__item" onPointerEnter={() => onEcho([id])} onPointerLeave={() => onEcho(null)}>
              <button type="button" className="panel__node" onClick={() => onSelect(id)} onFocus={() => onEcho([id])} onBlur={() => onEcho(null)}>
                <span className="swatch" data-slot={n.origin.slot} aria-hidden="true" />
                <span className="panel__node-label">
                  <span className={n.kind === "declaration" ? "lean" : undefined}>{n.label}</span>
                  {edge.kind === "formalizes" && <span className="faint"> · Lean statement</span>}
                  <span className="panel__node-origin">{n.origin.label}</span>
                </span>
              </button>
              {gist && <p className="panel__gist">{gist}</p>}
              {onEdge && (edge.warrant || edge.application) && (
                <button
                  type="button"
                  className="panel__why"
                  aria-label={`Why: how ${graph.nodes.get(edge.to)?.label} is used for ${graph.nodes.get(edge.from)?.label}`}
                  onClick={() => onEdge(edge.key)}
                >
                  Why
                </button>
              )}
            </li>
          );
        })}
      </ul>
    </div>
  );
}

function SeeAlso({ ids, onSelect, onEcho }: { ids: string[]; onSelect(id: string): void; onEcho(ids: Iterable<string> | null): void }) {
  const { graph } = useEdition();
  return (
    <div className="panel__nodes">
      <p className="panel__nodes-title">
        See also <span className="faint">· citation links, not dependencies</span>
      </p>
      <ul>
        {ids.map((id) => {
          const n = graph.nodes.get(id)!;
          return (
            <li key={id} className="panel__item" onPointerEnter={() => onEcho([id])} onPointerLeave={() => onEcho(null)}>
              <button type="button" className="panel__node" onClick={() => onSelect(id)} onFocus={() => onEcho([id])} onBlur={() => onEcho(null)}>
                <span className="swatch" data-slot={n.origin.slot} aria-hidden="true" />
                <span className="panel__node-label">
                  <span className={n.kind === "declaration" ? "lean" : undefined}>{n.label}</span>
                </span>
              </button>
            </li>
          );
        })}
      </ul>
    </div>
  );
}

function Provenance({
  nodeId,
  sourceId,
  citationIds,
  declaration,
}: {
  nodeId: string;
  sourceId?: string;
  citationIds?: string[];
  declaration?: string;
}) {
  const { graph } = useEdition();
  const node = graph.nodes.get(nodeId)!;
  const origin = node.origin;
  const provenance = useProvenance();
  const source = provenance.status === "ready" && sourceId ? provenance.value.sources.get(sourceId) : undefined;
  const citations =
    provenance.status === "ready" ? (citationIds ?? []).map((id) => provenance.value.citations.get(id) ?? { id }) : [];
  const sourceUrl = webUrl(source?.url ?? origin.url);
  const revision = shortRevision(source?.revision);
  return (
    <dl className="prov">
      <dt>Source</dt>
      <dd>
        <span className="prov__family" data-slot={origin.slot}>
          <span className="swatch" aria-hidden="true" />
          {origin.label}
          {origin.place && <span className="muted"> · {origin.place}</span>}
        </span>
      </dd>
      {source?.path && (
        <>
          <dt>File</dt>
          <dd>
            <code className="prov__path">{source.path}</code>
            {revision && <span className="prov__rev"> at {revision}</span>}
          </dd>
        </>
      )}
      {!source?.path && revision && (
        <>
          <dt>Edition</dt>
          <dd>{revision}</dd>
        </>
      )}
      {origin.locator && (
        <>
          <dt>Where in it</dt>
          <dd>{origin.locator}</dd>
        </>
      )}
      {declaration && (
        <>
          <dt>Declaration</dt>
          <dd>
            <code className="lean prov__decl">{declaration}</code>
          </dd>
        </>
      )}
      {sourceUrl && (
        <>
          <dt>Online</dt>
          <dd>
            <a href={sourceUrl} data-external rel="noopener" target="_blank" className="prov__url">
              {sourceUrl.replace(/^https?:\/\//, "")}
            </a>
          </dd>
        </>
      )}
      {citations.length > 0 && (
        <>
          <dt>Cites</dt>
          <dd>
            <ul className="prov__cites">
              {citations.map((c) => {
                const url = webUrl(c.url);
                const label = c.title ?? c.id.replace(/_/g, " ");
                return (
                  <li key={c.id} title={c.locator}>
                    {url ? (
                      <a href={url} data-external rel="noopener" target="_blank">
                        {label}
                      </a>
                    ) : (
                      label
                    )}
                  </li>
                );
              })}
            </ul>
          </dd>
        </>
      )}
    </dl>
  );
}

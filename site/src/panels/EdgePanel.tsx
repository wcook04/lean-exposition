// One step of the argument: how a prerequisite is used for the result that
// rests on it, as the recorded warrant says, where the sources make the step,
// which premises an applied theorem has supplied, and where the accounts make
// the step. The panel adds wording, not facts.

import { useEffect, useLayoutEffect, useMemo, useRef, type CSSProperties } from "react";
import type { AlignedPassage, Stage } from "../api/types";
import { useEdition, useRecord } from "../app/data";
import { routeHref } from "../app/router";
import { Accounts } from "./Accounts";
import { Section, type EchoHandler } from "./RecordPanel";
import { accountName, groupPassages, stepVerb, warrantStatus } from "./model";
import { useSheet } from "./sheet";
import "./panel.css";

interface Props {
  edgeKey: string;
  onClose(): void;
  onSelect(id: string): void;
  onEcho?: EchoHandler;
  passageHref?: (stage: Stage, anchor: string) => string;
  leaving?: boolean;
}

export function EdgePanel({ edgeKey, onClose, onSelect, onEcho, passageHref, leaving }: Props) {
  const { graph } = useEdition();
  const edge = graph.edges.find((e) => e.key === edgeKey);
  const sheet = useSheet();
  const headingRef = useRef<HTMLHeadingElement>(null);
  const bodyRef = useRef<HTMLDivElement>(null);

  useLayoutEffect(() => {
    if (bodyRef.current) bodyRef.current.scrollTop = 0;
    headingRef.current?.focus({ preventScroll: true });
  }, [edgeKey]);

  // Light both ends on the map while the step is open.
  useEffect(() => {
    if (!edge || leaving) return;
    onEcho?.(new Set([edge.from, edge.to]));
    return () => onEcho?.(null);
  }, [edge, onEcho, leaving]);

  const consumer = edge ? graph.nodes.get(edge.from) : undefined;
  const prerequisite = edge ? graph.nodes.get(edge.to) : undefined;
  const a = useRecord(consumer?.ref ?? null);
  const b = useRecord(prerequisite?.ref ?? null);

  const step = useMemo(() => {
    if (a.status !== "ready" || b.status !== "ready") return null;
    const theirs = new Set((b.value.aligned_passages ?? []).map((p) => `${p.stage}:${p.anchor}`));
    const shared: AlignedPassage[] = (a.value.aligned_passages ?? []).filter((p) => theirs.has(`${p.stage}:${p.anchor}`));
    const fallback = shared.length === 0;
    return { grouped: groupPassages(fallback ? (a.value.aligned_passages ?? []) : shared), fallback };
  }, [a, b]);

  const memberships = useMemo(() => {
    const m: Partial<Record<Stage, string[]>> = {};
    if (a.status === "ready") for (const p of a.value.usage.paper_memberships) m[p.stage] = p.roles;
    return m;
  }, [a]);

  if (!edge || !consumer || !prerequisite) {
    return (
      <aside className="panel" aria-label="Step">
        <header className="panel__head">
          <p className="panel__status">This step is not recorded in this edition.</p>
          <button type="button" className="control control--plain panel__close" aria-label="Close" onClick={onClose}>
            ×
          </button>
        </header>
      </aside>
    );
  }

  const w = edge.warrant;
  const href = passageHref ?? ((stage: Stage, anchor: string) => routeHref({ view: "read", stage, anchor, node: consumer.id }));
  let n = 0;
  const rise = (): CSSProperties => ({ ["--i" as string]: Math.min(n++, 5) });
  const chip = (id: string) => {
    const node = graph.nodes.get(id)!;
    return (
      <button
        type="button"
        className="step-chip"
        data-slot={node.origin.slot}
        onClick={() => onSelect(id)}
        onPointerEnter={() => onEcho?.(new Set([id]))}
        onPointerLeave={() => onEcho?.(new Set([edge.from, edge.to]))}
      >
        <span className="swatch" aria-hidden="true" />
        <span className={node.kind === "declaration" ? "lean" : undefined}>{node.label}</span>
      </button>
    );
  };

  return (
    <aside
      className={`panel panel--step${leaving ? " panel--leaving" : ""}${sheet.dragging ? " panel--dragging" : ""}`}
      aria-labelledby="step-title"
      data-sheet={sheet.state}
      style={sheet.style}
    >
      {sheet.handle}
      <header className="panel__head" key={`h:${edgeKey}`}>
        <div className="panel__chips panel__rise">
          <span className="chip chip--kind">One step of the argument</span>
        </div>
        <button type="button" className="control control--plain panel__close" aria-label="Close" onClick={onClose}>
          <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
            <path d="M2 2l8 8M10 2l-8 8" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
          </svg>
        </button>
        <h2 id="step-title" ref={headingRef} tabIndex={-1} className="step__title">
          {chip(edge.to)}
          <span className="step__verb">{stepVerb(edge.kind)}</span>
          {chip(edge.from)}
        </h2>
        {w && <p className="panel__status panel__rise">{warrantStatus(w.status, w.tool)}</p>}
      </header>

      <div className="panel__body" ref={bodyRef}>
        <div className="panel__content" key={`b:${edgeKey}`}>
          <Section title="How it is used" style={rise()}>
            {w ? <p className="panel__statement step__warrant">{w.text}</p> : <p className="muted">No account of this step is recorded.</p>}
            {w?.shared && <p className="panel__note">This account is shared with neighbouring steps; it is not written for this step alone.</p>}
          </Section>

          {w?.sources && (
            <Section title="Where in the sources" style={rise()}>
              <p className="step__sources">{w.sources}</p>
              {w.scope && <p className="panel__note">{w.scope}</p>}
            </Section>
          )}
          {!w?.sources && w?.scope && (
            <Section title="Scope" style={rise()}>
              <p className="panel__note">{w.scope}</p>
            </Section>
          )}

          {edge.application && (
            <Section title="Premises this use supplies" style={rise()}>
              {edge.application.rationale && <p className="panel__note">{edge.application.rationale}</p>}
              <ul className="step__bindings">
                {edge.application.bindings.map((bnd) => (
                  <li key={`${bnd.assumption}:${bnd.supplier}`}>
                    <p>
                      Supplies <strong>{graph.nodes.get(bnd.assumption)?.label ?? bnd.assumption}</strong>
                      {bnd.names.length > 0 && <code className="lean"> ({bnd.names.join(", ")})</code>}
                      {bnd.rationale ? `: ${bnd.rationale}` : ""}
                    </p>
                    {graph.nodes.has(bnd.supplier) && <p className="step__from">from {chip(bnd.supplier)}</p>}
                  </li>
                ))}
              </ul>
              {edge.application.remaining.length > 0 && (
                <p className="panel__note">
                  Still assumed: {edge.application.remaining.map((id) => graph.nodes.get(id)?.label ?? id).join("; ")}.
                </p>
              )}
            </Section>
          )}

          <Section title="Where the accounts make this step" style={rise()}>
            <Accounts
              nodeId={consumer.id}
              grouped={step?.grouped ?? null}
              memberships={memberships}
              href={href}
              note={step?.fallback ? `No passage discusses both; these are the passages for ${consumer.label}.` : undefined}
              empty={(stage) =>
                step?.fallback
                  ? `${capital(accountName(stage))} has no passage for ${consumer.label}.`
                  : `${capital(accountName(stage))} has no passage that discusses both.`
              }
            />
          </Section>
        </div>
      </div>
      <p className="visually-hidden" aria-live="polite">
        {leaving ? "" : `Selected step: ${prerequisite.label} ${stepVerb(edge.kind)} ${consumer.label}.`}
      </p>
    </aside>
  );
}

function capital(s: string): string {
  return s[0].toUpperCase() + s.slice(1);
}

// One step of the argument: which relation it is, in words, between which two
// records; for an applied theorem, what this use holds fixed, which premise
// each recorded supplier provides and what is still assumed; then the
// recorded explanation and the related passages in each account. The panel
// adds wording, not facts.

import { useEffect, useLayoutEffect, useMemo, useRef } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { recordLine } from "../compare/useAlignment";
import { routeHref } from "../app/router";
import { Accounts } from "./Accounts";
import type { LeanStep } from "./model";
import { LeanRoute } from "./LeanRoute";
import type { EchoHandler } from "./RecordPanel";
import { NO_REMAINING, applicationView, relationName, stepBasisLabel, stepPassages, stepVerb, warrantStatus } from "./model";
import { CloseButton, Jumps, Pane, type PaneSpec } from "./parts";
import { useSheet } from "./sheet";
import { useRecordDetail } from "./stored";
import "./panel.css";

interface Props {
  edgeKey: string;
  onClose(): void;
  onSelect(id: string): void;
  onEcho?: EchoHandler;
  /** Walk to a Lean name in the sheet, as one history entry. */
  onWalk?(walk: LeanStep): void;
  passageHref?: (stage: Stage, anchor: string) => string;
  leaving?: boolean;
  /** Mark the panel's root element, e.g. for the page to restore focus or measure it. */
  panelRef?: React.Ref<HTMLElement>;
}

export function EdgePanel({ edgeKey, onClose, onSelect, onEcho, onWalk, passageHref, leaving, panelRef }: Props) {
  const { graph } = useEdition();
  const edge = graph.edges.find((e) => e.key === edgeKey);
  const rootRef = useRef<HTMLElement | null>(null);
  const headingRef = useRef<HTMLHeadingElement>(null);
  const bodyRef = useRef<HTMLDivElement>(null);
  const sheet = useSheet({ panel: rootRef, title: headingRef });

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
  const a = useRecordDetail(consumer?.ref ?? null);
  const b = useRecordDetail(prerequisite?.ref ?? null);

  const step = useMemo(() => {
    if (a.state.status !== "ready" || b.state.status !== "ready") return null;
    return stepPassages(a.state.value.aligned_passages ?? [], b.state.value.aligned_passages ?? []);
  }, [a.state, b.state]);
  const request = a.state.status === "error" || b.state.status === "error" ? "error" : step ? "ready" : "loading";

  const memberships = useMemo(() => {
    const m: Partial<Record<Stage, string[]>> = {};
    if (a.state.status === "ready") for (const p of a.state.value.usage.paper_memberships) m[p.stage] = p.roles;
    return m;
  }, [a.state]);

  const setRoot = (el: HTMLElement | null) => {
    rootRef.current = el;
    if (typeof panelRef === "function") panelRef(el);
    else if (panelRef) (panelRef as React.MutableRefObject<HTMLElement | null>).current = el;
  };

  if (!edge || !consumer || !prerequisite) {
    return (
      <aside className="panel" aria-label="Step" ref={setRoot}>
        <header className="panel__head">
          <div className="panel__id">
            <span className="caps">Step</span>
            <CloseButton onClose={onClose} />
          </div>
          <p className="panel__state">No recorded step matches this link.</p>
        </header>
      </aside>
    );
  }

  const w = edge.warrant;
  const app = edge.application ? applicationView(edge.application, edge.application.record) : null;
  const href = passageHref ?? ((stage: Stage, anchor: string) => routeHref({ view: "read", stage, anchor, node: consumer.id }));
  const label = (id: string) => graph.nodes.get(id)?.label ?? id;
  // That no one has reviewed an explanation is true of nearly every step, so it waits with
  // the other notes on the record; a review that has an outcome stays in the header.
  const reviewed = w && ["passed", "failed", "unavailable"].includes(w.status);
  const peek = sheet.phone && sheet.state === "peek";
  const panes: PaneSpec[] = [
    ...(app ? [{ id: "use", title: "How it is applied" }] : []),
    { id: "explanation", title: "Explanation" },
    { id: "passages", title: "Related passages" },
  ];

  const link = (id: string) => {
    const node = graph.nodes.get(id)!;
    return (
      <button
        type="button"
        className={`step__end${node.kind === "declaration" && !recordLine(id)?.short ? " lean" : ""}`}
        data-slot={node.origin.slot}
        onClick={() => onSelect(id)}
        onPointerEnter={() => onEcho?.(new Set([id]))}
        onPointerLeave={() => onEcho?.(new Set([edge.from, edge.to]))}
      >
        {node.kind === "declaration" ? recordLine(id)?.short || node.label : node.label}
      </button>
    );
  };

  return (
    <aside
      ref={setRoot}
      className={`panel panel--step${leaving ? " panel--leaving" : ""}${sheet.dragging ? " panel--dragging" : ""}`}
      aria-labelledby="step-title"
      style={sheet.style}
      {...sheet.attrs}
    >
      {sheet.handle}
      <header className="panel__head">
        <div className="panel__id">
          <span className={`rel-sample rel-sample--${edge.kind}`} aria-hidden="true" />
          <span className="caps panel__rel">{relationName(edge.kind)}</span>
          <CloseButton onClose={onClose} />
        </div>
        {sheet.modal && (
          <button type="button" className="panel__back" onClick={sheet.toPeek}>
            <span aria-hidden="true">↓ </span>Show the map
          </button>
        )}
        <h2 id="step-title" ref={headingRef} tabIndex={-1} className="step__title">
          {link(edge.from)} <span className="step__verb">{stepVerb(edge.kind)}</span> {link(edge.to)}
        </h2>
        {(!w || reviewed) && <p className="panel__status">{w ? warrantStatus(w.status) : "No recorded explanation for this step"}</p>}
        {peek && (
          <div className="panel__peek">
            <button ref={sheet.readRef} type="button" className="panel__action panel__action--primary" onClick={() => sheet.open()}>
              Read the step
            </button>
            <button type="button" className="panel__action" onClick={() => sheet.open("passages")}>
              Related passages
            </button>
          </div>
        )}
      </header>

      <div className="panel__body" ref={bodyRef} hidden={peek || undefined}>
        <Jumps panes={panes} root={rootRef} resetKey={edgeKey} />
        <div className="panel__content" key={`b:${edgeKey}`}>
          <LeanRoute edgeKey={edgeKey} onWalk={onWalk} />
          {app && (
            <Pane id="use" title="How the theorem is applied in this step">
              <p className="panel__note step__app-status">{app.status}</p>
              {app.shared.length > 0 && (
                <div className="step__block">
                  <p className="panel__group">Objects that stay the same throughout this application</p>
                  <dl className="step__shared">
                    {app.shared.map((s) => (
                      <div key={s.name}>
                        <dt>
                          <code className="lean">{s.name}</code>
                        </dt>
                        <dd>{s.value}</dd>
                      </div>
                    ))}
                  </dl>
                </div>
              )}
              <table className="step__premises">
                <thead>
                  <tr>
                    <th scope="col">Hypothesis of the applied theorem</th>
                    <th scope="col">Recorded as supplied by</th>
                  </tr>
                </thead>
                <tbody>
                  {app.premises.map((p) => (
                    <tr key={`${p.premise}:${p.supplier}`}>
                      <td>
                        {graph.nodes.has(p.premise) ? (
                          <button type="button" className="step__cell" onClick={() => onSelect(p.premise)}>
                            {label(p.premise)}
                          </button>
                        ) : (
                          label(p.premise)
                        )}
                        {p.names.length > 0 && <code className="lean step__names">{p.names.join(", ")}</code>}
                      </td>
                      <td>
                        {graph.nodes.has(p.supplier) ? (
                          <button type="button" className="step__cell" onClick={() => onSelect(p.supplier)}>
                            {label(p.supplier)}
                          </button>
                        ) : (
                          label(p.supplier)
                        )}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
              <div className="step__block">
                <p className="panel__group">Hypotheses still assumed after this application</p>
                {app.remaining.length === 0 ? (
                  <p className="panel__note">{NO_REMAINING}.</p>
                ) : (
                  <ul className="step__remaining">
                    {app.remaining.map((id) => (
                      <li key={id}>
                        <span className="rel-sample rel-sample--assumes" aria-hidden="true" />
                        {graph.nodes.has(id) ? (
                          <button type="button" className="step__cell" onClick={() => onSelect(id)}>
                            {label(id)}
                          </button>
                        ) : (
                          label(id)
                        )}
                      </li>
                    ))}
                  </ul>
                )}
              </div>
              {(app.rationale || app.premises.some((p) => p.rationale)) && (
                <details className="panel__more-scope">
                  <summary>Recorded reasons for each hypothesis</summary>
                  {app.rationale && <p>{app.rationale}</p>}
                  {app.premises
                    .filter((p) => p.rationale)
                    .map((p) => (
                      <p key={`${p.premise}:r`}>
                        <strong>{label(p.premise)}.</strong> {p.rationale}
                      </p>
                    ))}
                  {app.span && (
                    <p className="faint">
                      Recorded place in the source: {app.span.sourceId}
                      {app.span.startLine !== null && `, lines ${app.span.startLine}–${app.span.endLine ?? app.span.startLine}`}
                    </p>
                  )}
                </details>
              )}
            </Pane>
          )}

          <Pane id="explanation" title="Recorded explanation">
            {w ? <p className="panel__statement step__warrant">{w.text}</p> : <p className="panel__note">No separate explanation is recorded for this step.</p>}
            {w && (
              <details className="panel__origin">
                <summary>Where this comes from</summary>
                {!reviewed && <p>{warrantStatus(w.status)}.</p>}
                {w.sharedWith > 1 && <p>The same recorded explanation is attached to {w.sharedWith} links, so it was not written for this step alone.</p>}
                {w.sources && <p>As recorded: {w.sources}</p>}
                {w.scope && <p>What it covers: {w.scope}</p>}
              </details>
            )}
          </Pane>

          <Pane id="passages" title="Related passages">
            <Accounts
              nodeId={consumer.id}
              grouped={step?.grouped ?? null}
              memberships={memberships}
              status={request}
              onRetry={() => {
                if (a.state.status === "error") a.retry();
                if (b.state.status === "error") b.retry();
              }}
              href={href}
              label={(stage) => stepBasisLabel(step?.basis.get(stage))}
              note={(stage) =>
                step?.basis.get(stage) === "both"
                  ? "Each passage here is linked to both records. That alone does not show that the passage contains this step of the argument."
                  : step?.basis.get(stage) === "consumer"
                    ? `No passage in this account is linked to both records. The passages here are linked to “${consumer.label}” but not to “${prerequisite.label}”.`
                    : undefined
              }
              empty={() => `No passage in this account is linked to “${consumer.label}”.`}
            />
          </Pane>
        </div>
      </div>
      <p className="visually-hidden" aria-live="polite">
        {leaving ? "" : `Selected step: ${consumer.label} ${stepVerb(edge.kind)} ${prerequisite.label}.`}
      </p>
    </aside>
  );
}

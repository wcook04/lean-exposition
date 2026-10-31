// The record sheet at one Lean declaration: where a card of the Lean graph opens, and where a
// name in any sheet walks to. The declaration itself comes first, then what it is linked to
// in the argument. Each walk is one history entry, so Back returns to the sheet it left.

import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { routeHref } from "../app/router";
import { useAlignment } from "../compare/useAlignment";
import { LazyLeanBlock } from "../lean/lazy";
import type { LeanStep } from "./model";
import { RELATION_WORDS } from "./model";
import type { EchoHandler } from "./RecordPanel";
import { CloseButton } from "./parts";
import { useSheet } from "./sheet";
import "./panel.css";

interface Props {
  name: string;
  module?: string;
  leaving?: boolean;
  onClose(): void;
  onSelect(id: string): void;
  onWalk(walk: LeanStep): void;
  onEcho?: EchoHandler;
}

export function DeclPanel({ name, module, leaving, onClose, onSelect, onWalk, onEcho }: Props) {
  const alignment = useAlignment();
  const rootRef = useRef<HTMLElement | null>(null);
  const headingRef = useRef<HTMLHeadingElement>(null);
  const bodyRef = useRef<HTMLDivElement>(null);
  const sheet = useSheet({ panel: rootRef, title: headingRef });
  const short = name.slice(name.lastIndexOf(".") + 1);

  useLayoutEffect(() => {
    if (bodyRef.current) bodyRef.current.scrollTop = 0;
    headingRef.current?.focus({ preventScroll: true });
  }, [name]);

  const linked = useMemo(() => {
    const out: { id: string; title: string; relation: keyof typeof RELATION_WORDS; note: string }[] = [];
    for (const [id, record] of Object.entries(alignment?.records ?? {})) {
      for (const row of record.lean) if (row.name === name) out.push({ id, title: record.short || id, relation: row.relation, note: row.note });
    }
    return out;
  }, [alignment, name]);

  // Light the records this declaration is linked to, while it is open.
  useEffect(() => {
    if (leaving) return;
    onEcho?.(new Set(linked.map((row) => row.id)));
    return () => onEcho?.(null);
  }, [linked, leaving, onEcho]);

  const peek = sheet.phone && sheet.state === "peek";
  // The name and the way to the Lean browser are in this sheet's head.
  const [slot, setSlot] = useState<HTMLElement | null>(null);
  const walking = { onName: onWalk, noHead: true, previewSlot: slot };

  return (
    <aside ref={rootRef} className={`panel panel--decl${leaving ? " panel--leaving" : ""}${sheet.dragging ? " panel--dragging" : ""}`} aria-labelledby="decl-title" style={sheet.style} {...sheet.attrs}>
      {sheet.handle}
      <header className="panel__head">
        <div className="panel__id">
          <span className="caps">Lean declaration</span>
          <CloseButton onClose={onClose} />
        </div>
        {sheet.modal && (
          <button type="button" className="panel__back" onClick={sheet.toPeek}>
            <span aria-hidden="true">↓ </span>Show the map
          </button>
        )}
        <h2 id="decl-title" ref={headingRef} tabIndex={-1} className="panel__title lean">
          {short}
        </h2>
        <p className="panel__fullname lean" translate="no">
          {name}
        </p>
        <div className="panel__levels">
          {linked.length > 0 && (
            <span className="panel__linked">
              Linked from{" "}
              {linked.slice(0, 2).map((row, i) => (
                <span key={`${row.id}:${i}`}>
                  {i > 0 && ", "}
                  <button type="button" className="linklike" onClick={() => onSelect(row.id)}>
                    {row.title}
                  </button>
                </span>
              ))}
              {linked.length > 2 && `, and ${linked.length - 2} more`}
            </span>
          )}
          <a className="panel__quiet" href={routeHref({ view: "lean", decl: name, module })}>
            Lean browser
          </a>
        </div>
        {peek && (
          <div className="panel__peek">
            <button ref={sheet.readRef} type="button" className="panel__action panel__action--primary" onClick={() => sheet.open()}>
              Read the declaration
            </button>
          </div>
        )}
      </header>
      <div className="panel__body" ref={bodyRef} hidden={peek || undefined}>
        <div className="panel__content" key={name}>
          <div className="panel__lean">
            <LazyLeanBlock name={name} module={module} compact {...walking} />
          </div>
          <section className="pane" aria-labelledby="decl-records">
            <h3 className="pane__h" id="decl-records">
              In the argument
            </h3>
            {linked.length === 0 ? (
              <p className="panel__note">No record of the argument is linked to this declaration. It is a helper between the ones that are.</p>
            ) : (
              <ul className="rels">
                {linked.map((row, i) => (
                  <li key={`${row.id}:${i}`} className="rels__decl" onPointerEnter={() => onEcho?.(new Set([row.id]))} onPointerLeave={() => onEcho?.(new Set(linked.map((r) => r.id)))}>
                    <span className="rels__what">
                      <button type="button" className="rels__name" onClick={() => onSelect(row.id)}>
                        {row.title}
                      </button>
                      <span className="rels__meta">{RELATION_WORDS[row.relation]}</span>
                    </span>
                    {row.note && <p className="panel__note">{row.note}</p>}
                  </li>
                ))}
              </ul>
            )}
            {linked.length > 0 && <p className="panel__note">Linked by reading the source. Not checked as equivalent.</p>}
          </section>
        </div>
      </div>
      <div ref={setSlot} className="lean-slot" />
      <p className="visually-hidden" aria-live="polite">
        {leaving ? "" : `Selected Lean declaration: ${short}.`}
      </p>
    </aside>
  );
}

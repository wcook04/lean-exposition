// A record's sheet, docked in the lower part of the map beside the paper with the
// map staying visible above it, or standing alone in a modal on narrower screens.
// It holds the same record panel as the rest of the site, whose Compare link it keeps. Dragging the handle (or
// the arrow keys on it) sets how much of the pane it takes, and the height is
// remembered for this browser.

import { useEffect, useLayoutEffect, useRef, useState } from "react";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref, type Trace } from "../../app/router";
import { RecordPanel } from "../../panels/RecordPanel";

const HEIGHT_KEY = "lx-reader-sheet";
/** The sheet's share of the pane: the map above it always keeps a useful strip. */
export const DOCK_MIN = 0.28;
export const DOCK_MAX = 0.8;
const DOCK_DEFAULT = 0.5;

export function clampDock(share: number): number {
  return Math.min(DOCK_MAX, Math.max(DOCK_MIN, share));
}

export function readDockShare(): number {
  try {
    const value = Number(localStorage.getItem(HEIGHT_KEY));
    return value ? clampDock(value) : DOCK_DEFAULT;
  } catch {
    return DOCK_DEFAULT;
  }
}

function saveDockShare(share: number) {
  try {
    localStorage.setItem(HEIGHT_KEY, String(share));
  } catch {
    /* storage unavailable: the height lasts until the page closes */
  }
}

export interface OpenRecord {
  id: string;
  /** Open at its Lean rather than at its top. */
  lean?: boolean;
}

interface Props {
  record: OpenRecord;
  /** Docked in the pane; false when it fills a modal, which has its own title bar. */
  docked?: boolean;
  /** The share of the pane it takes. */
  share?: number;
  onShare?(share: number): void;
  onClose(): void;
  onSelect(id: string): void;
  onEcho?(ids: ReadonlySet<string> | null): void;
  passageHref(stage: Stage, anchor: string): string;
}

export function RecordDock({ record, docked = true, share = DOCK_DEFAULT, onShare, onClose, onSelect, onEcho, passageHref }: Props) {
  const { graph } = useEdition();
  const rootRef = useRef<HTMLDivElement>(null);
  const scrollRef = useRef<HTMLDivElement>(null);
  const [dragging, setDragging] = useState(false);
  const node = graph.nodes.get(record.id);

  // The panel loads its detail after it mounts: scroll to the Lean once it is drawn.
  useLayoutEffect(() => {
    const body = scrollRef.current;
    if (!body) return;
    body.scrollTop = 0;
    if (!record.lean) return;
    let tries = 0;
    let timer = 0;
    const find = () => {
      const lean = body.querySelector<HTMLElement>("[data-section='statement']");
      if (lean) {
        body.scrollTop = lean.getBoundingClientRect().top - body.getBoundingClientRect().top + body.scrollTop - 8;
        return;
      }
      if (++tries < 20) timer = window.setTimeout(find, 100);
    };
    find();
    return () => window.clearTimeout(timer);
  }, [record]);

  const setHeight = (value: number) => rootRef.current?.style.setProperty("--dock-share", String(value));
  useEffect(() => setHeight(share), [share]);

  // The drag writes one custom property; the map hears the new room when it ends.
  const onPointerDown = (event: React.PointerEvent<HTMLDivElement>) => {
    if (event.button !== 0) return;
    const pane = rootRef.current?.parentElement;
    if (!pane) return;
    event.preventDefault();
    const handle = event.currentTarget;
    handle.setPointerCapture(event.pointerId);
    const box = pane.getBoundingClientRect();
    let value = share;
    setDragging(true);
    const move = (e: PointerEvent) => {
      value = clampDock((box.bottom - e.clientY) / box.height);
      setHeight(value);
    };
    const end = () => {
      handle.removeEventListener("pointermove", move);
      handle.removeEventListener("pointerup", end);
      handle.removeEventListener("pointercancel", end);
      setDragging(false);
      saveDockShare(value);
      onShare?.(value);
    };
    handle.addEventListener("pointermove", move);
    handle.addEventListener("pointerup", end);
    handle.addEventListener("pointercancel", end);
  };

  const onKeyDown = (event: React.KeyboardEvent) => {
    const step = event.key === "ArrowUp" ? 0.05 : event.key === "ArrowDown" ? -0.05 : 0;
    if (!step) return;
    event.preventDefault();
    const next = clampDock(share + step);
    saveDockShare(next);
    onShare?.(next);
  };

  if (!node) return null;

  return (
    <div ref={rootRef} className={`record-dock${docked ? " record-dock--docked" : ""}${dragging ? " is-dragging" : ""}`} aria-label="Record sheet" role="region">
      {docked && (
        <div
          className="record-dock__handle"
          role="separator"
          aria-orientation="horizontal"
          aria-label="Resize the record sheet"
          aria-valuemin={Math.round(DOCK_MIN * 100)}
          aria-valuemax={Math.round(DOCK_MAX * 100)}
          aria-valuenow={Math.round(share * 100)}
          tabIndex={0}
          onPointerDown={onPointerDown}
          onKeyDown={onKeyDown}
        >
          <span aria-hidden="true" />
        </div>
      )}
      <div className="record-dock__bar">
        <a className="record-dock__map" href={routeHref({ view: "map", node: record.id })}>
          Open in the full map
        </a>
        {docked && (
          <button type="button" className="record-dock__close" aria-label={`Close the record ${node.label}`} onClick={onClose}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
            Close
          </button>
        )}
      </div>
      <div className="record-dock__scroll" ref={scrollRef}>
        <RecordPanel
          key={record.id}
          nodeId={record.id}
          compact
          onClose={onClose}
          onSelect={onSelect}
          onTrace={(trace: Trace | undefined) => navigate({ view: "map", node: record.id, trace })}
          passageHref={passageHref}
          onEcho={onEcho}
        />
      </div>
    </div>
  );
}

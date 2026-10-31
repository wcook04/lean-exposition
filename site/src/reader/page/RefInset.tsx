// References in the reading text. Pointing at one, or focusing it, previews its target on
// the right page after a short dwell and moves nothing. A click opens the target in place
// under the paragraph, typeset as the paper has it, with a jump for those who want to go
// there. Sections jump, and a section of another paper opens beside this one, as any link
// to it does. The paper keeps the reader's line: an inset pushes only what is below it,
// and closing one puts the page back.
//
// The paper's HTML is set once, so an inset is a slot added after the block and filled
// through a portal, the way a passage's tools are.

import { useCallback, useContext, useEffect, useLayoutEffect, useMemo, useRef, useState, useSyncExternalStore, type ReactNode, type RefObject } from "react";
import { createPortal, flushSync } from "react-dom";
import { leaveAs } from "../../app/trail";
import { routeHref } from "../../app/router";
import { alignmentResource } from "../../compare/useAlignment";
import { documentPaths } from "../documents";
import { renderSlice, type PreparedDocument } from "../engine";
import { mountFigures } from "../mount";
import { leanModuleOf, opensInPlace, recordOver, refView, type RefRow, type RefView } from "../references";
import { sectionNumber } from "./model";
import { freshSlots, markWideMaths, PassageBarContext, type BodyHandle } from "./PaperBody";
import "./ref-inset.css";

/** How long a pointer or focus stays on a reference before the right page shows it. */
const DWELL_MS = 150;

// ---- The preview on the right page ------------------------------------------------------

let preview: ReactNode = null;
const listeners = new Set<() => void>();

function showPreview(next: ReactNode): void {
  preview = next;
  listeners.forEach((listener) => listener());
}

function subscribe(listener: () => void): () => void {
  listeners.add(listener);
  return () => {
    listeners.delete(listener);
  };
}

/** The foot of the right page, where a preview stands. The paper never moves for it. */
export function RefPreviewHost() {
  const shown = useSyncExternalStore(subscribe, () => preview);
  return shown ? (
    <aside className="ref-preview" aria-hidden="true" data-testid="ref-preview">
      {shown}
    </aside>
  ) : null;
}

/** What a reference shows on the right page while it is pointed at. */
function RefPreviewContent({ view, html }: { view: RefView; html: string | null }) {
  const text = useRef<HTMLDivElement>(null);
  useLayoutEffect(() => {
    if (!html || !text.current) return;
    const unmount = mountFigures(freshSlots(text.current));
    const unmark = markWideMaths(text.current);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);
  return (
    <>
      {!html && <p className="ref-preview__title">{view.title}</p>}
      {view.note && <p className="ref-preview__note">{view.note}</p>}
      {html && <div ref={text} className="ref-preview__text prose" dangerouslySetInnerHTML={{ __html: html }} />}
      {view.locator && <p className="ref-preview__note">Cited here as: {view.locator}</p>}
    </>
  );
}

// ---- Rendering a target -----------------------------------------------------------------

const rendered = new WeakMap<PreparedDocument, Map<string, string | null>>();

/** A target's Markdown through the paper's own pipeline. */
function bodyHtml(doc: PreparedDocument, stage: string, body: string | null): string | null {
  if (!body) return null;
  let cache = rendered.get(doc);
  if (!cache) rendered.set(doc, (cache = new Map()));
  const hit = cache.get(body);
  if (hit !== undefined) return hit;
  const paths = documentPaths();
  const html = renderSlice(body, { stage, documentPath: paths[stage], documentPaths: paths, references: doc.references }).html;
  cache.set(body, html);
  return html;
}

// ---- One inset --------------------------------------------------------------------------

interface InsetProps {
  id: string;
  stage: string;
  view: RefView;
  html: string | null;
  focusFirst: boolean;
  onClose(): void;
}

function RefInset({ id, stage, view, html, focusFirst, onClose }: InsetProps) {
  const { onRecord } = useContext(PassageBarContext);
  const box = useRef<HTMLDivElement>(null);
  const text = useRef<HTMLDivElement>(null);
  const [record, setRecord] = useState<string | null>(null);

  useEffect(() => {
    const span = view.span;
    if (!span) return;
    let live = true;
    void alignmentResource().then((alignment) => {
      if (live && alignment) setRecord(recordOver(span, stage, alignment.records));
    });
    return () => {
      live = false;
    };
  }, [view, stage]);

  useLayoutEffect(() => {
    if (!html || !text.current) return;
    const unmount = mountFigures(freshSlots(text.current));
    const unmark = markWideMaths(text.current);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);

  useEffect(() => {
    if (focusFirst) box.current?.querySelector<HTMLElement>("a, button")?.focus({ preventScroll: true });
    // Only as it opens.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const module = view.href ? leanModuleOf(view.href) : null;
  return (
    <div ref={box} id={id} className="ref-inset" role="region" aria-label={view.title}>
      {!html && <p className="ref-inset__title">{view.title}</p>}
      {view.note && <p className="ref-inset__note">{view.note}</p>}
      {html && <div ref={text} className="ref-inset__text" dangerouslySetInnerHTML={{ __html: html }} />}
      {view.locator && <p className="ref-inset__note">Cited here as: {view.locator}</p>}
      <div className="ref-inset__bar">
        {view.go && (
          <a href={`#${encodeURIComponent(view.go)}`} className="ref-inset__go" data-ref-go={view.go}>
            Go to {view.title}
          </a>
        )}
        {record && (
          <button type="button" className="ref-inset__lean" onClick={(event) => onRecord(record, event.currentTarget, true)}>
            See its Lean
          </button>
        )}
        {module && <a href={routeHref({ view: "lean", module })}>Read it on the Lean page</a>}
        {view.href && (
          <a href={view.href} className="ext" target="_blank" rel="noopener noreferrer">
            Open source
          </a>
        )}
        <button type="button" className="ref-inset__close" onClick={onClose}>
          Close
        </button>
      </div>
    </div>
  );
}

// ---- The behaviour, for the paper's root ----------------------------------------------------

interface Open {
  id: string;
  row: RefRow;
  link: HTMLElement;
  slot: HTMLElement;
  view: RefView;
  html: string | null;
  focusFirst: boolean;
  /** How far opening scrolled the page to show the inset, and where that left it. */
  nudge: number;
  scrollAfter: number;
}

/** The block an inset opens under. */
function blockOf(link: HTMLElement): HTMLElement | null {
  return link.closest<HTMLElement>("p, li, td, th, blockquote, figcaption");
}

function placeSlot(block: HTMLElement, slot: HTMLElement): void {
  if (block.matches("li, td, th")) {
    block.append(slot);
    return;
  }
  let after: Element = block;
  while (after.nextElementSibling?.matches(".ref-slot")) after = after.nextElementSibling;
  after.after(slot);
}

export interface References {
  onClick(event: React.MouseEvent): void;
  onPointerOver(event: React.PointerEvent): void;
  onPointerOut(event: React.PointerEvent): void;
  onFocus(event: React.FocusEvent): void;
  onBlur(event: React.FocusEvent): void;
  portals: ReactNode;
}

export function useReferences(stage: string, doc: PreparedDocument, body: RefObject<BodyHandle | null>, top: () => number): References {
  const index = doc.refs;
  const [open, setOpen] = useState<Open[]>([]);
  const openRef = useRef(open);
  openRef.current = open;
  const dwell = useRef(0);
  const counter = useRef(0);
  const pointed = useRef<HTMLElement | null>(null);

  const rowOf = useCallback((link: HTMLElement) => index?.rows[Number(link.dataset.ref)], [index]);

  const stopDwell = useCallback(() => {
    window.clearTimeout(dwell.current);
    dwell.current = 0;
  }, []);

  const point = useCallback(
    (link: HTMLElement) => {
      const row = rowOf(link);
      if (!row || !index) return;
      pointed.current = link;
      stopDwell();
      dwell.current = window.setTimeout(() => {
        const view = refView(index, row);
        showPreview(<RefPreviewContent view={view} html={bodyHtml(doc, stage, view.body)} />);
      }, DWELL_MS);
    },
    [doc, index, rowOf, stage, stopDwell],
  );

  const leave = useCallback(() => {
    pointed.current = null;
    stopDwell();
    showPreview(null);
  }, [stopDwell]);

  useEffect(() => leave, [leave]);

  const close = useCallback(
    (item: Open, refocus: boolean) => {
      const { link, slot } = item;
      const before = link.getBoundingClientRect().top;
      const untouched = Math.abs(window.scrollY - item.scrollAfter) < 2;
      flushSync(() => setOpen((list) => list.filter((other) => other !== item)));
      slot.remove();
      link.removeAttribute("aria-expanded");
      link.removeAttribute("aria-controls");
      // The line the reader was on stays where it is, and a nudge made to show the inset is undone.
      const moved = link.getBoundingClientRect().top - before;
      const undo = untouched ? -item.nudge : 0;
      if (Math.abs(moved + undo) >= 0.5) window.scrollBy({ top: moved + undo, behavior: "instant" as ScrollBehavior });
      body.current?.reanchor(true);
      if (refocus) link.focus({ preventScroll: true });
    },
    [body],
  );

  const toggle = useCallback(
    (link: HTMLElement, row: RefRow, focusFirst: boolean) => {
      const existing = openRef.current.find((item) => item.link === link);
      if (existing) {
        close(existing, true);
        return;
      }
      const block = blockOf(link);
      if (!block || !index) return;
      const slot = document.createElement("div");
      slot.className = "ref-slot";
      placeSlot(block, slot);
      const id = `ref-inset-${++counter.current}`;
      link.setAttribute("aria-expanded", "true");
      link.setAttribute("aria-controls", id);
      const view = refView(index, row);
      const item: Open = { id, row, link, slot, view, html: bodyHtml(doc, stage, view.body), focusFirst, nudge: 0, scrollAfter: window.scrollY };
      flushSync(() => setOpen((list) => [...list, item]));
      // An inset opened near the foot of the window is brought into view, as far as the link allows.
      const over = slot.getBoundingClientRect().bottom - window.innerHeight + 16;
      const room = link.getBoundingClientRect().top - top() - 8;
      const nudge = Math.max(0, Math.min(over, room));
      if (nudge > 0) {
        window.scrollBy({ top: nudge, behavior: "instant" as ScrollBehavior });
        item.nudge = nudge;
      }
      item.scrollAfter = window.scrollY;
    },
    [close, doc, index, stage, top],
  );

  // Escape closes the inset last opened; a dialog on top keeps its own Escape.
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented || document.querySelector("[data-modal-open]")) return;
      const last = openRef.current[openRef.current.length - 1];
      if (!last) return;
      event.preventDefault();
      close(last, true);
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [close]);

  /** The place a jump leaves, for the Back that returns to it. */
  const leavePlace = useCallback(
    (link: HTMLElement) => {
      const part = Number(link.closest<HTMLElement>("[data-part]")?.dataset.part ?? -1);
      const scope = link.closest(".part__text");
      let title: string | undefined;
      for (const heading of Array.from(scope?.querySelectorAll("h1,h2,h3,h4,h5,h6") ?? [])) {
        if (heading.compareDocumentPosition(link) & Node.DOCUMENT_POSITION_FOLLOWING) title = heading.textContent ?? undefined;
      }
      for (let i = part - 1; i >= 0 && !title; i--) {
        const headings = doc.parts[i]?.headings.filter((h) => h.level > 1);
        if (headings?.length) title = headings[headings.length - 1].title;
      }
      if (title) leaveAs(sectionNumber(title));
    },
    [doc],
  );

  /** Mark where a jump lands, once, as the reader's eyes get there. */
  const land = useCallback(
    (id: string) => {
      const part = doc.anchorIndex.get(id);
      if (part === undefined) return;
      void body.current?.ensure([part]).then(() => {
        const target = body.current?.partElement(part)?.querySelector<HTMLElement>(`[id="${CSS.escape(id)}"]`);
        if (!target || target.matches("h1,h2,h3,h4,h5,h6")) return;
        target.setAttribute("data-landed", "");
        window.setTimeout(() => target.removeAttribute("data-landed"), 1800);
      });
    },
    [body, doc],
  );

  const onClick = useCallback(
    (event: React.MouseEvent) => {
      if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
      const element = event.target as Element;
      const go = element.closest?.<HTMLElement>("a[data-ref-go]");
      if (go) {
        const from = go.closest(".ref-slot")?.previousElementSibling;
        if (from) leavePlace(from as HTMLElement);
        land(go.dataset.refGo ?? "");
        return; // The reader page makes the jump and its history entry.
      }
      const link = element.closest?.<HTMLElement>("a[data-ref]");
      if (!link) return;
      const row = rowOf(link);
      if (!row) return;
      stopDwell();
      if (opensInPlace(row)) {
        event.preventDefault();
        event.stopPropagation();
        toggle(link, row, event.detail === 0);
        return;
      }
      if (row.kind === "section") {
        leavePlace(link);
        if (row.target) land(row.target);
      }
    },
    [land, leavePlace, rowOf, stopDwell, toggle],
  );

  const onPointerOver = useCallback(
    (event: React.PointerEvent) => {
      if (event.pointerType === "touch") return;
      const link = (event.target as Element).closest?.<HTMLElement>("a[data-ref]");
      if (link && link !== pointed.current) point(link);
    },
    [point],
  );

  const onPointerOut = useCallback(
    (event: React.PointerEvent) => {
      if (!pointed.current) return;
      const to = event.relatedTarget as Node | null;
      if (to && pointed.current.contains(to)) return;
      leave();
    },
    [leave],
  );

  const onFocus = useCallback(
    (event: React.FocusEvent) => {
      const link = event.target as HTMLElement;
      if (link.matches?.("a[data-ref]") && link.matches(":focus-visible")) point(link);
    },
    [point],
  );

  const onBlur = useCallback(
    (event: React.FocusEvent) => {
      if (pointed.current === event.target) leave();
    },
    [leave],
  );

  const portals = useMemo(
    () =>
      open.map((item) =>
        createPortal(
          <RefInset id={item.id} stage={stage} view={item.view} html={item.html} focusFirst={item.focusFirst} onClose={() => close(item, true)} />,
          item.slot,
          item.id,
        ),
      ),
    [close, open, stage],
  );

  return { onClick, onPointerOver, onPointerOut, onFocus, onBlur, portals };
}

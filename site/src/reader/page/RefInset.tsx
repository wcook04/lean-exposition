// References in the reading text. Pointing at one, or focusing it, previews its target on
// the right page after a short dwell and moves nothing. A click opens the target in place
// under the paragraph, typeset as the paper has it, with a jump for those who want to go
// there. Sections jump, and a section of another paper opens beside this one, as any link
// to it does. The paper keeps the reader's line: an inset pushes only what is below it,
// and closing one puts the page back. A citation opens as a card: the entry from the paper's
// own reference list, the place cited, and the source. While a reference is open the right
// page goes on following the paper.
//
// Each open is one history entry at the same address, and the entry remembers which insets
// stand and where the page was. Back, Escape, Close and a second click all end in the same
// place: the entry goes, the inset goes, and the page is back on the pixel it left.
//
// The paper's HTML is set once, so an inset is a slot added after the block and filled
// through a portal, the way a passage's tools are.

import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState, type MouseEvent as ReactMouseEvent, type ReactNode, type RefObject } from "react";
import { createPortal, flushSync } from "react-dom";
import { routeHref } from "../../app/router";
import { pushEntry, readEntry, writeEntry } from "../../app/trail";
import { alignmentResource } from "../../compare/useAlignment";
import { documentPaths } from "../documents";
import { renderSlice, type PreparedDocument } from "../engine";
import { mountFigures } from "../mount";
import { citedView, leanModuleOf, opensInPlace, recordOver, refView, type RecordSlice, type RefIndex, type RefRow, type RefView } from "../references";
import { freshSlots, markWideMaths, type BodyHandle } from "./PaperBody";
import { POINT_DWELL, previewOnRightPage } from "./rightPage";
import "./ref-inset.css";

// ---- The preview on the right page ------------------------------------------------------

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
    <div className="ref-preview" aria-hidden="true" data-testid="ref-preview">
      {!html && <p className="ref-preview__title">{view.title}</p>}
      {view.note && <p className="ref-preview__note">{view.note}</p>}
      {html && <div ref={text} className="ref-preview__text prose" dangerouslySetInnerHTML={{ __html: html }} />}
      {view.locator && <p className="ref-preview__locator">{view.locator}</p>}
    </div>
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
  doc: PreparedDocument;
  index: RefIndex;
  view: RefView;
  html: string | null;
  focusFirst: boolean;
  /** Opened by the reader just now, not brought back by Forward or a reload. */
  fresh: boolean;
  onLean(record: string, at: string | undefined): void;
  onClose(): void;
}

/** The anchor of the heading over a reference-list entry. */
function listAnchor(doc: PreparedDocument, byte: number): string | null {
  for (let i = doc.parts.length - 1; i >= 0; i--) {
    const part = doc.parts[i];
    if (part.span.start > byte) continue;
    const heading = part.headings.filter((h) => h.level > 1).pop();
    if (heading) return heading.id;
  }
  return null;
}

/** The entry of a source, with what it is cited for above it. */
function Card({ view, html }: { view: RefView; html: string | null }) {
  return (
    <>
      {view.note && <p className="ref-inset__note">{view.note}</p>}
      {view.locator && <p className="ref-inset__locator">{view.locator}</p>}
      {html ? <div className="ref-inset__text" dangerouslySetInnerHTML={{ __html: html }} /> : <p className="ref-inset__title">{view.title}</p>}
    </>
  );
}

function RefInset({ id, stage, doc, index, view, html, focusFirst, fresh, onLean, onClose }: InsetProps) {
  const box = useRef<HTMLDivElement>(null);
  const text = useRef<HTMLDivElement>(null);
  const [record, setRecord] = useState<RecordSlice | null>(null);
  /** A citation inside this statement, open under it. */
  const [cited, setCited] = useState<{ href: string; view: RefView } | null>(null);
  const citedBox = useRef<HTMLDivElement>(null);
  useEffect(() => citedBox.current?.scrollIntoView({ block: "nearest", behavior: "instant" as ScrollBehavior }), [cited]);

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

  /** A statement quotes its citations: they open here, under it, and do not leave the paper. */
  const onText = (event: ReactMouseEvent) => {
    if (view.card || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const link = (event.target as Element).closest?.<HTMLAnchorElement>("a.ext");
    const href = link?.getAttribute("href");
    if (!link || !href) return;
    const next = citedView(index, href, (link.textContent ?? "").replace(/\s+/g, " ").trim());
    if (!next) return;
    event.preventDefault();
    setCited((open) => (open?.href === href ? null : { href, view: next }));
  };

  const module = view.href ? leanModuleOf(view.href) : null;
  const list = view.entry !== null ? listAnchor(doc, view.entry) : null;
  return (
    <div ref={box} id={id} className={`ref-inset${view.card ? " ref-inset--card" : ""}`} data-fresh={fresh ? "" : undefined} role="region" aria-label={view.title}>
      {view.card ? (
        <Card view={view} html={html} />
      ) : (
        <>
          {!html && <p className="ref-inset__title">{view.title}</p>}
          {view.note && <p className="ref-inset__note">{view.note}</p>}
          {html && <div ref={text} className="ref-inset__text" onClick={onText} dangerouslySetInnerHTML={{ __html: html }} />}
        </>
      )}
      {cited && (
        <div ref={citedBox} className="ref-inset ref-inset--card ref-inset--nested">
          <Card view={cited.view} html={bodyHtml(doc, stage, cited.view.body)} />
          {cited.view.href && (
            <div className="ref-inset__bar">
              <a href={cited.view.href} className="ext" target="_blank" rel="noopener noreferrer">
                Open source
              </a>
            </div>
          )}
        </div>
      )}
      <div className="ref-inset__bar">
        {view.go && (
          <a href={`#${encodeURIComponent(view.go)}`} className="ref-inset__go" data-ref-go={view.go}>
            Go to {view.title}
          </a>
        )}
        {record && (
          <button type="button" className="ref-inset__lean" onClick={() => onLean(record.id, record.at)}>
            See its Lean
          </button>
        )}
        {module && <a href={routeHref({ view: "lean", module })}>Read it on the Lean page</a>}
        {view.href && (
          <a href={view.href} className="ext" target="_blank" rel="noopener noreferrer">
            Open source
          </a>
        )}
        {list && (
          <a href={`#${encodeURIComponent(list)}`} data-ref-go={list}>
            Go to the reference list
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
  fresh: boolean;
  /** How far opening scrolled the page to show the inset, and where that left it. */
  nudge: number;
  scrollAfter: number;
}

/** The insets standing in a history entry, by the first byte of each reference. */
const ENTRY = "refs";
/** Where the page stood in that entry when the next inset opened. */
const ENTRY_TOP = "refsTop";

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

export function useReferences(
  stage: string,
  doc: PreparedDocument,
  body: RefObject<BodyHandle | null>,
  top: () => number,
  onLean: (record: string, at: string | undefined) => void,
): References {
  const index = doc.refs;
  const [open, setOpen] = useState<Open[]>([]);
  const openRef = useRef(open);
  openRef.current = open;
  const dwell = useRef(0);
  const counter = useRef(0);
  const pointed = useRef<HTMLElement | null>(null);
  /** Just closed: it does not preview until the pointer or the focus has left it. */
  const quiet = useRef<HTMLElement | null>(null);
  /** Closed out of turn, so Back does not bring them back. */
  const dismissed = useRef(new Set<number>());

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
      // One view of a reference at a time: an open one stands under its sentence.
      if (link === quiet.current || link.hasAttribute("aria-expanded")) return;
      dwell.current = window.setTimeout(() => {
        const view = refView(index, row);
        previewOnRightPage(<RefPreviewContent view={view} html={bodyHtml(doc, stage, view.body)} />);
      }, POINT_DWELL);
    },
    [doc, index, rowOf, stage, stopDwell],
  );

  const leave = useCallback(() => {
    pointed.current = null;
    quiet.current = null;
    stopDwell();
    previewOnRightPage(null);
  }, [stopDwell]);

  useEffect(() => leave, [leave]);

  const close = useCallback(
    (item: Open, refocus: boolean) => {
      const { link, slot } = item;
      const before = link.getBoundingClientRect().top;
      const untouched = Math.abs(window.scrollY - item.scrollAfter) < 2;
      const hadFocus = slot.contains(document.activeElement);
      flushSync(() => setOpen((list) => list.filter((other) => other !== item)));
      slot.remove();
      link.removeAttribute("aria-expanded");
      link.removeAttribute("aria-controls");
      // The line the reader was on stays where it is, and a nudge made to show the inset is undone.
      const moved = link.getBoundingClientRect().top - before;
      const undo = untouched ? -item.nudge : 0;
      if (Math.abs(moved + undo) >= 0.5) window.scrollBy({ top: moved + undo, behavior: "instant" as ScrollBehavior });
      body.current?.reanchor(true);
      if (refocus || hadFocus) {
        quiet.current = link;
        link.focus({ preventScroll: true });
      }
    },
    [body],
  );

  /** Stand an inset under its reference, with no history of its own. */
  const stand = useCallback(
    (link: HTMLElement, row: RefRow, focusFirst: boolean, bring: boolean) => {
      const block = blockOf(link);
      if (!block || !index) return;
      const slot = document.createElement("div");
      slot.className = "ref-slot";
      placeSlot(block, slot);
      const id = `ref-inset-${++counter.current}`;
      link.setAttribute("aria-expanded", "true");
      link.setAttribute("aria-controls", id);
      const view = refView(index, row);
      const item: Open = { id, row, link, slot, view, html: bodyHtml(doc, stage, view.body), focusFirst, fresh: bring, nudge: 0, scrollAfter: window.scrollY };
      flushSync(() => setOpen((list) => [...list, item]));
      if (bring) {
        // An inset opened near the foot of the window is brought into view, as far as the link allows.
        const foot = document.querySelector(".reader-bar")?.getBoundingClientRect().top ?? window.innerHeight;
        const over = slot.getBoundingClientRect().bottom - foot + 16;
        const room = link.getBoundingClientRect().top - top() - 8;
        const nudge = Math.max(0, Math.min(over, room));
        if (nudge > 0) {
          window.scrollBy({ top: nudge, behavior: "instant" as ScrollBehavior });
          item.nudge = nudge;
        }
        item.scrollAfter = window.scrollY;
      }
      // What the paper holds in place is now this position, so the nudge stays.
      body.current?.reanchor(true);
    },
    [body, doc, index, stage, top],
  );

  /** Take an inset away. The newest goes with its history entry; another leaves history alone. */
  const dismiss = useCallback(
    (item: Open) => {
      const standing = readEntry<number[]>(ENTRY) ?? [];
      if (standing[standing.length - 1] === item.row.start_byte) {
        window.history.back();
        return;
      }
      dismissed.current.add(item.row.start_byte);
      writeEntry(ENTRY, standing.filter((byte) => byte !== item.row.start_byte));
      close(item, true);
    },
    [close],
  );

  /** The link of a reference, drawn first if the paper has not reached it yet. */
  const linkOf = useCallback(
    async (at: number): Promise<HTMLElement | null> => {
      const row = index?.rows[at];
      if (!row) return null;
      const part = doc.parts.findIndex((p) => row.start_byte >= p.span.start && row.start_byte < p.span.end);
      if (part < 0) return null;
      await body.current?.ensure([part]);
      return body.current?.partElement(part)?.querySelector<HTMLElement>(`a[data-ref="${at}"]`) ?? null;
    },
    [body, doc, index],
  );

  /** Make the page show what this history entry holds. An entry that never held one changes nothing. */
  const settle = useCallback(async () => {
    const standing = readEntry<number[]>(ENTRY);
    if (!standing || !index) return;
    const wanted = standing.filter((byte) => !dismissed.current.has(byte));
    const leaving = openRef.current.filter((item) => !wanted.includes(item.row.start_byte));
    [...leaving].reverse().forEach((item) => close(item, false));
    const top = readEntry<number>(ENTRY_TOP);
    if (leaving.length && top !== undefined && Math.abs(window.scrollY - top) >= 0.5) {
      window.scrollTo({ top, behavior: "instant" as ScrollBehavior });
      body.current?.reanchor(true);
    }
    for (const byte of wanted) {
      if (openRef.current.some((item) => item.row.start_byte === byte)) continue;
      const at = index.rows.findIndex((row) => row.start_byte === byte);
      const link = at >= 0 ? await linkOf(at) : null;
      if (link && !link.hasAttribute("aria-expanded")) stand(link, index.rows[at], false, false);
    }
  }, [body, close, index, linkOf, stand]);

  useEffect(() => {
    const onPop = () => void settle();
    window.addEventListener("popstate", onPop);
    return () => window.removeEventListener("popstate", onPop);
  }, [settle]);

  // On arriving, a reload among them: what this entry held.
  useEffect(() => {
    void settle();
    // Once per mounted paper.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const toggle = useCallback(
    (link: HTMLElement, row: RefRow, focusFirst: boolean) => {
      const existing = openRef.current.find((item) => item.link === link);
      if (existing) {
        dismiss(existing);
        return;
      }
      stopDwell();
      previewOnRightPage(null);
      dismissed.current.delete(row.start_byte);
      const before = openRef.current.map((item) => item.row.start_byte);
      // Written first, so that Back to this entry knows it held these and no more.
      writeEntry(ENTRY, before);
      writeEntry(ENTRY_TOP, window.scrollY);
      pushEntry(new URL(window.location.href));
      writeEntry(ENTRY, [...before, row.start_byte]);
      stand(link, row, focusFirst, true);
    },
    [dismiss, stand, stopDwell],
  );

  // Escape closes the inset last opened; a dialog on top keeps its own Escape.
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented || document.querySelector("[data-modal-open]")) return;
      const last = openRef.current[openRef.current.length - 1];
      if (!last) return;
      event.preventDefault();
      dismiss(last);
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [dismiss]);

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
        land(go.dataset.refGo ?? "");
        return; // The reader page makes the jump, its history entry and the name of its Back.
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
      if (row.kind === "section" && row.target) land(row.target);
    },
    [land, rowOf, stopDwell, toggle],
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
      if (link.matches?.("a[data-ref]") && link.matches(":focus-visible") && link !== quiet.current) point(link);
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
          <RefInset id={item.id} stage={stage} doc={doc} index={index!} view={item.view} html={item.html} focusFirst={item.focusFirst} fresh={item.fresh} onLean={onLean} onClose={() => dismiss(item)} />,
          item.slot,
          item.id,
        ),
      ),
    [dismiss, doc, index, onLean, open, stage],
  );

  return { onClick, onPointerOver, onPointerOut, onFocus, onBlur, portals };
}

// On a phone the panel is a bottom sheet with two modes. Peek is not modal:
// the map stays usable above it, and two buttons say what reading it offers.
// Full is a labelled modal dialog: the rest of the page is inert, Tab and
// Shift+Tab stay inside, the title takes focus on entry, and Escape returns
// to peek with focus on the button that opened it. The grip may be dragged,
// but every change is also a visible button (DESIGN.md § Accessibility).

import { useEffect, useRef, useState, type KeyboardEvent, type PointerEvent, type RefObject } from "react";
import { useEntryState } from "../app/trail";

export type SheetState = "peek" | "full";

const PHONE = "(max-width: 900px)";

/** True while the viewport uses the sheet layout; read live. */
export function usePhone(): boolean {
  const [phone, setPhone] = useState(() => typeof window !== "undefined" && !!window.matchMedia?.(PHONE).matches);
  useEffect(() => {
    const query = window.matchMedia?.(PHONE);
    if (!query) return;
    const on = () => setPhone(query.matches);
    on();
    query.addEventListener("change", on);
    return () => query.removeEventListener("change", on);
  }, []);
  return phone;
}

const FOCUSABLE = 'a[href], button:not([disabled]), select:not([disabled]), input:not([disabled]), textarea, summary, [tabindex]:not([tabindex="-1"])';

/** Make everything outside `el` inert, level by level up to the body. Returns the undo. */
function inertOutside(el: HTMLElement): () => void {
  const changed: HTMLElement[] = [];
  let node: HTMLElement | null = el;
  while (node && node !== document.body) {
    const parent: HTMLElement | null = node.parentElement;
    if (!parent) break;
    for (const sibling of Array.from(parent.children)) {
      if (sibling === node || !(sibling instanceof HTMLElement) || sibling.inert || sibling.tagName === "SCRIPT") continue;
      sibling.inert = true;
      changed.push(sibling);
    }
    node = parent;
  }
  return () => changed.forEach((s) => (s.inert = false));
}

export function useSheet({
  panel,
  title,
  enabled = true,
}: {
  panel?: RefObject<HTMLElement | null>;
  title?: RefObject<HTMLElement | null>;
  enabled?: boolean;
} = {}) {
  const phone = usePhone() && enabled;
  const [state, setState] = useEntryState<SheetState>("sheet", "peek");
  const [drag, setDrag] = useState<number | null>(null); // live height in px while dragging
  const start = useRef<{ y: number; h: number; moved: boolean } | null>(null);
  const readRef = useRef<HTMLButtonElement>(null);
  const pendingSection = useRef<string | null>(null);
  const modal = phone && state === "full";

  // Full mode: inert background, title focus (or the requested section).
  useEffect(() => {
    if (!modal) return;
    const el = panel?.current;
    const undo = el ? inertOutside(el) : () => undefined;
    const section = pendingSection.current;
    pendingSection.current = null;
    const target = section ? el?.querySelector<HTMLElement>(`[data-section="${section}"]`) : null;
    if (target) {
      target.scrollIntoView({ block: "start" });
      target.querySelector<HTMLElement>("h3")?.focus({ preventScroll: true });
    } else title?.current?.focus({ preventScroll: true });
    return undo;
  }, [modal, panel, title]);

  const open = (section?: string) => {
    pendingSection.current = section ?? null;
    setState("full");
  };
  const toPeek = () => {
    setState("peek");
    requestAnimationFrame(() => readRef.current?.focus());
  };

  /** Keyboard containment and Escape for the panel element. */
  const onKeyDown = (event: KeyboardEvent<HTMLElement>) => {
    if (!modal) return;
    if (event.key === "Escape") {
      event.preventDefault();
      event.stopPropagation();
      toPeek();
      return;
    }
    if (event.key !== "Tab") return;
    const el = event.currentTarget;
    const items = Array.from(el.querySelectorAll<HTMLElement>(FOCUSABLE)).filter((x) => !x.closest("[hidden]") && x.offsetParent !== null);
    if (!items.length) return;
    const first = items[0];
    const last = items[items.length - 1];
    const active = document.activeElement;
    if (event.shiftKey && (active === first || !el.contains(active) || active === title?.current)) {
      event.preventDefault();
      last.focus();
    } else if (!event.shiftKey && active === last) {
      event.preventDefault();
      first.focus();
    }
  };

  const onPointerDown = (event: PointerEvent<HTMLButtonElement>) => {
    const sheet = event.currentTarget.closest<HTMLElement>(".panel");
    if (!sheet) return;
    start.current = { y: event.clientY, h: sheet.getBoundingClientRect().height, moved: false };
    event.currentTarget.setPointerCapture(event.pointerId);
  };
  const onPointerMove = (event: PointerEvent<HTMLButtonElement>) => {
    const s = start.current;
    if (!s) return;
    const dy = event.clientY - s.y;
    if (Math.abs(dy) > 4) s.moved = true;
    if (s.moved) setDrag(Math.max(120, Math.min(window.innerHeight - 64, s.h - dy)));
  };
  const onPointerUp = (event: PointerEvent<HTMLButtonElement>) => {
    const s = start.current;
    start.current = null;
    if (!s) return;
    if (!s.moved) {
      if (state === "peek") open();
      else toPeek();
    } else {
      const dy = event.clientY - s.y;
      if (dy < -40) open();
      else if (dy > 40) toPeek();
    }
    setDrag(null);
  };

  const handle = phone ? (
    <button
      type="button"
      className="panel__handle"
      aria-label={state === "peek" ? "Expand this panel" : "Shrink this panel to show the map"}
      aria-expanded={state === "full"}
      onPointerDown={onPointerDown}
      onPointerMove={onPointerMove}
      onPointerUp={onPointerUp}
      onPointerCancel={() => {
        start.current = null;
        setDrag(null);
      }}
      onClick={(event) => {
        // Pointer handlers decide; keyboard activation (detail 0) toggles here.
        if (event.detail === 0) (state === "peek" ? open() : toPeek());
      }}
    >
      <span className="panel__grip" aria-hidden="true" />
    </button>
  ) : null;

  const style = drag !== null ? { ["--sheet-drag" as string]: `${drag}px` } : undefined;
  /** Attributes for the panel element: dialog semantics only in full mode on a phone. */
  const attrs = {
    "data-sheet": phone ? state : undefined,
    role: modal ? "dialog" : undefined,
    "aria-modal": modal ? true : undefined,
    "data-modal-open": modal ? "" : undefined,
    onKeyDown,
  } as const;
  return { phone, state: phone ? state : ("full" as SheetState), modal, dragging: drag !== null, handle, style, attrs, open, toPeek, readRef };
}

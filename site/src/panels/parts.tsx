// Small pieces shared by the record and step panels: a named section, the
// sticky section jumps, the close button, a relation row and a copy button.

import { useEffect, useState, type ReactNode, type RefObject } from "react";
import { prefersReducedMotion } from "../app/theme";

export interface PaneSpec {
  id: string;
  title: string;
}

/** A section of the reading column, reachable from the jumps. */
export function Pane({ id, title, children, label }: { id: string; title: string; children: ReactNode; label?: ReactNode }) {
  return (
    <section className="pane" data-section={id} aria-labelledby={`pane-${id}`}>
      <h3 className="pane__h" id={`pane-${id}`} tabIndex={-1}>
        {title}
        {label}
      </h3>
      {children}
    </section>
  );
}

/** The nearest ancestor that scrolls, or null for the page itself. */
function scroller(el: HTMLElement | null): HTMLElement | null {
  for (let n = el?.parentElement ?? null; n; n = n.parentElement) {
    const o = getComputedStyle(n).overflowY;
    if ((o === "auto" || o === "scroll")) return n;
  }
  return null;
}

/**
 * Jump links to each section; the one in view is underlined. Scrolling the
 * column decides which that is; the jumps change nothing but scroll position.
 */
export function Jumps({ panes, root, resetKey }: { panes: PaneSpec[]; root: RefObject<HTMLElement | null>; resetKey: string }) {
  const [current, setCurrent] = useState(panes[0]?.id);
  useEffect(() => {
    setCurrent(panes[0]?.id);
    const el = root.current;
    if (!el) return;
    const target: HTMLElement | Window = scroller(el.querySelector("[data-section]")) ?? window;
    const measure = () => {
      const nav = el.querySelector<HTMLElement>(".jumps");
      const line = (nav?.getBoundingClientRect().bottom ?? 0) + 24;
      let on = panes[0]?.id;
      for (const p of panes) {
        const s = el.querySelector<HTMLElement>(`[data-section="${p.id}"]`);
        if (s && s.getBoundingClientRect().top <= line) on = p.id;
      }
      // At the very end of the column the last section counts as in view.
      if (target instanceof HTMLElement && target.scrollTop + target.clientHeight >= target.scrollHeight - 2 && target.scrollTop > 0) on = panes[panes.length - 1].id;
      setCurrent(on);
    };
    target.addEventListener("scroll", measure, { passive: true });
    return () => target.removeEventListener("scroll", measure);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [resetKey, root]);

  const go = (id: string) => {
    const s = root.current?.querySelector<HTMLElement>(`[data-section="${id}"]`);
    if (!s) return;
    s.scrollIntoView({ block: "start", behavior: prefersReducedMotion() ? "auto" : "smooth" });
    s.querySelector<HTMLElement>(".pane__h")?.focus({ preventScroll: true });
    setCurrent(id);
  };
  return (
    <nav className="jumps" aria-label="Sections of this panel">
      {panes.map((p) => (
        <a
          key={p.id}
          href={`#pane-${p.id}`}
          className={current === p.id ? "on" : undefined}
          aria-current={current === p.id ? "true" : undefined}
          onClick={(event) => {
            event.preventDefault();
            go(p.id);
          }}
        >
          {p.title}
        </a>
      ))}
    </nav>
  );
}

export function CloseButton({ onClose, label = "Close" }: { onClose(): void; label?: string }) {
  return (
    <button type="button" className="panel__close" aria-label={label} onClick={onClose}>
      <svg viewBox="0 0 12 12" width="13" height="13" aria-hidden="true">
        <path d="M2 2l8 8M10 2l-8 8" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
      </svg>
    </button>
  );
}

/** Copy a recorded string; says so for a moment, in words. */
export function CopyButton({ text, what }: { text: string; what: string }) {
  const [done, setDone] = useState(false);
  useEffect(() => {
    if (!done) return;
    const t = window.setTimeout(() => setDone(false), 1400);
    return () => window.clearTimeout(t);
  }, [done]);
  return (
    <button
      type="button"
      className="copy"
      aria-label={`Copy ${what}`}
      onClick={() => {
        navigator.clipboard?.writeText(text).then(
          () => setDone(true),
          () => undefined,
        );
      }}
    >
      {done ? "Copied" : "Copy"}
    </button>
  );
}

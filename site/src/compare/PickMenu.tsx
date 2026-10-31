// A quiet menu in place of a native select: the map's goal menu, in Compare's sizes.
// ↑ ↓ Home End move, Enter or Space chooses, Escape closes and returns focus to the
// button. Copied from GoalMenu in map/MapPage.tsx, which is private to the map page.

import { useCallback, useEffect, useId, useRef, useState, type KeyboardEvent, type ReactNode } from "react";

export interface PickOption {
  id: string;
  title: string;
  /** A second line under the title: where this choice is stated. */
  where?: string;
  /** A number at the end of the row. */
  count?: number;
}

interface Props {
  /** Names the control for assistive technology, and is shown when `showLabel` is set. */
  label: string;
  showLabel?: boolean;
  options: readonly PickOption[];
  value: string;
  /** What the button says; the chosen option's title unless given. */
  current?: ReactNode;
  variant?: "goal" | "plain" | "title";
  onPick(id: string): void;
}

export function PickMenu({ label, showLabel, options, value, current, variant = "plain", onPick }: Props) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const root = useRef<HTMLSpanElement>(null);
  const button = useRef<HTMLButtonElement>(null);
  const items = useRef<(HTMLButtonElement | null)[]>([]);
  const close = useCallback(() => setOpen(false), []);

  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!root.current?.contains(event.target as Node)) close();
    };
    const onKey = (event: KeyboardEvent | globalThis.KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      event.preventDefault();
      close();
      button.current?.focus();
    };
    document.addEventListener("pointerdown", onDown);
    window.addEventListener("keydown", onKey, true);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      window.removeEventListener("keydown", onKey, true);
    };
  }, [open, close]);

  const focusItem = (i: number) => requestAnimationFrame(() => items.current[(i + options.length) % options.length]?.focus());
  const openAt = (i: number) => {
    setOpen(true);
    focusItem(i);
  };
  const at = Math.max(0, options.findIndex((o) => o.id === value));
  const choose = (option: PickOption) => {
    setOpen(false);
    button.current?.focus();
    if (option.id !== value) onPick(option.id);
  };
  const onButtonKey = (event: KeyboardEvent<HTMLButtonElement>) => {
    if (event.key === "ArrowDown" || event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      openAt(at);
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      openAt(options.length - 1);
    }
  };
  const onMenuKey = (event: KeyboardEvent<HTMLDivElement>) => {
    const here = items.current.indexOf(document.activeElement as HTMLButtonElement);
    let next: number | null = null;
    if (event.key === "ArrowDown") next = here + 1;
    else if (event.key === "ArrowUp") next = here - 1;
    else if (event.key === "Home") next = 0;
    else if (event.key === "End") next = options.length - 1;
    else if (event.key === "Tab") setOpen(false);
    if (next === null) return;
    event.preventDefault();
    focusItem(next);
  };

  return (
    <span className={`pick pick--${variant}`} ref={root}>
      <span className={showLabel ? "pick__label" : "visually-hidden"} id={`${id}-label`}>
        {label}
      </span>
      <button
        ref={button}
        type="button"
        className="pick__button"
        aria-haspopup="menu"
        aria-expanded={open}
        aria-controls={`${id}-menu`}
        aria-labelledby={`${id}-label ${id}-now`}
        onClick={() => (open ? setOpen(false) : openAt(at))}
        onKeyDown={onButtonKey}
      >
        <span className="pick__now" id={`${id}-now`}>
          {current ?? options[at]?.title}
        </span>
        <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true" className={`pick__chev${open ? " is-open" : ""}`}>
          <path d="M2 3.5 L5 6.5 L8 3.5" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
      </button>
      <div id={`${id}-menu`} role="menu" aria-label={label} className="pick__menu" hidden={!open} onKeyDown={onMenuKey}>
        {options.map((option, i) => (
          <button
            key={option.id}
            ref={(el) => {
              items.current[i] = el;
            }}
            type="button"
            role="menuitemradio"
            aria-checked={option.id === value}
            tabIndex={-1}
            className="pick__item"
            onClick={() => choose(option)}
          >
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true" className="pick__tick">
              <path d="M2 6.5 L5 9 L10 3" fill="none" stroke="currentColor" strokeWidth="1.6" strokeLinecap="round" strokeLinejoin="round" />
            </svg>
            <span className="pick__name">{option.title}</span>
            {option.count !== undefined && <span className="pick__count">{option.count}</span>}
            {option.where && <span className="pick__where">{option.where}</span>}
          </button>
        ))}
      </div>
    </span>
  );
}

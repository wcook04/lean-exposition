// Where the reader is in the paper: the sections of levels 2 and 3 with the
// current one marked, and a switch to the other accounts that keeps the
// claim the reader is on. Wide screens set it as a sticky column; narrower
// ones open the same list from a menu that names the current section.

import { useEffect, useId, useRef, useState } from "react";
import type { Stage } from "../../api/types";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { sectionLabel } from "../../map/TheoremPlate";
import type { OutlineEntry } from "./model";

interface Props {
  stage: Stage;
  entries: OutlineEntry[];
  current: string | null;
  switchHref(stage: Stage): string;
  keeping: string | null;
  onJump(id: string): void;
}

export function OutlineColumn(props: Props) {
  const listRef = useRef<HTMLOListElement>(null);
  // Keep the current entry in view inside the column, without moving the page.
  useEffect(() => {
    const list = listRef.current;
    const item = list?.querySelector<HTMLElement>('[aria-current="location"]');
    if (!list || !item) return;
    const top = item.offsetTop - list.offsetTop;
    if (top < list.scrollTop + 24 || top > list.scrollTop + list.clientHeight - 48) {
      list.scrollTop = Math.max(0, top - list.clientHeight / 3);
    }
  }, [props.current]);
  return (
    <nav className="outline" aria-label="This paper">
      <AccountSwitch {...props} />
      <Sections {...props} listRef={listRef} />
    </nav>
  );
}

function AccountSwitch({ stage, switchHref, keeping }: Props) {
  return (
    <div className="accounts">
      <ul className="accounts__list" aria-label="Accounts of the result">
        {STAGE_ORDER.map((s) => (
          <li key={s}>
            <a
              className="accounts__item"
              href={switchHref(s)}
              aria-current={s === stage ? "page" : undefined}
              aria-describedby={s !== stage && keeping ? "accounts-keeping" : undefined}
            >
              {PAPER_NAMES[s].short}
            </a>
          </li>
        ))}
      </ul>
      {keeping && (
        <p id="accounts-keeping" className="accounts__keeping">
          The others open where they discuss {keeping}.
        </p>
      )}
    </div>
  );
}

function Sections({ entries, current, onJump, listRef }: Props & { listRef?: React.RefObject<HTMLOListElement | null> }) {
  return (
    <ol className="outline__list" ref={listRef}>
      {entries.map((entry) => (
        <li key={entry.id} className={`outline__item outline__item--l${entry.level}`}>
          <a
            href={`#${encodeURIComponent(entry.id)}`}
            aria-current={entry.id === current ? "location" : undefined}
            onClick={(event) => {
              if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
              event.preventDefault();
              onJump(entry.id);
            }}
          >
            {sectionLabel(entry.title)}
          </a>
        </li>
      ))}
    </ol>
  );
}

/** The same outline behind a button that names the current section. */
export function OutlineMenu(props: Props & { placement: "pane" | "bar" }) {
  const [open, setOpen] = useState(false);
  const id = useId();
  const rootRef = useRef<HTMLDivElement>(null);
  const currentEntry = props.entries.find((e) => e.id === props.current);
  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!rootRef.current?.contains(event.target as Node)) setOpen(false);
    };
    const onKey = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        event.preventDefault();
        event.stopPropagation();
        setOpen(false);
        rootRef.current?.querySelector<HTMLButtonElement>(".outline-menu__toggle")?.focus();
      }
    };
    document.addEventListener("pointerdown", onDown);
    window.addEventListener("keydown", onKey, true);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      window.removeEventListener("keydown", onKey, true);
    };
  }, [open]);
  useEffect(() => {
    if (!open) return;
    // Scroll the list itself, never the page behind it.
    const list = rootRef.current?.querySelector<HTMLElement>(".outline-menu__sheet .outline__list");
    const item = list?.querySelector<HTMLElement>('[aria-current="location"]');
    if (list && item) list.scrollTop = Math.max(0, item.offsetTop - list.offsetTop - list.clientHeight / 3);
  }, [open]);
  return (
    <div className={`outline-menu outline-menu--${props.placement}`} ref={rootRef}>
      <button
        type="button"
        className="outline-menu__toggle"
        aria-expanded={open}
        aria-controls={id}
        onClick={() => setOpen((v) => !v)}
      >
        <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true">
          <path d="M2.5 4h11M2.5 8h11M2.5 12h7" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
        </svg>
        <span className="outline-menu__current">{currentEntry ? sectionLabel(currentEntry.title) : "Contents"}</span>
      </button>
      <div id={id} className="outline-menu__sheet" hidden={!open}>
        <AccountSwitch {...props} />
        <Sections
          {...props}
          onJump={(target) => {
            setOpen(false);
            props.onJump(target);
          }}
        />
      </div>
    </div>
  );
}

// Where the reader is in the paper: the account, then its sections with the
// current one marked. Levels 2 and 3 are always listed; a level-4 subsection
// (long §8.1.1) appears inside the branch being read, so deep places stay
// reachable without listing every heading at once. Wide screens set it as a
// sticky column; narrower ones open the same list from a "Sections" control.
// Choosing another account is the top bar's job: it opens an account from
// its start, and "Same topic in…" goes from a passage to its treatments.

import { useEffect, useId, useMemo, useRef, useState } from "react";
import { sectionLabel } from "../../map/TheoremPlate";
import { chainOf, type OutlineEntry } from "./model";

interface Props {
  entries: OutlineEntry[];
  current: string | null;
  onJump(id: string): void;
}

export interface AccountHead {
  name: string;
  job: string;
  reader: string;
  status: string;
}

export function OutlineColumn(props: Props & { head: AccountHead }) {
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
  const { head } = props;
  return (
    <nav className="outline" aria-label="Sections of this paper">
      <div className="outline__account">
        <p className="caps">{head.name}</p>
        <p className="outline__job">{head.job}</p>
        <p className="outline__reader">
          {head.reader}
          {head.status && <> {head.status}</>}
        </p>
      </div>
      <Sections {...props} listRef={listRef} />
    </nav>
  );
}

export function Sections({ entries, current, onJump, listRef }: Props & { listRef?: React.RefObject<HTMLOListElement | null> }) {
  const open = useMemo(() => new Set(chainOf(entries, current).map((e) => e.id)), [entries, current]);
  const shown = entries.filter((e) => e.level < 4 || (e.parent && open.has(e.parent)));
  return (
    <ol className="outline__list" ref={listRef}>
      {shown.map((entry) => (
        <li key={entry.id} className={`outline__item outline__item--l${entry.level}${open.has(entry.id) ? " outline__item--open" : ""}`}>
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

/** The sections behind a "Sections" control: a non-modal popover beside the paper. */
export function SectionsPopover(props: Props) {
  const [open, setOpen] = useState(false);
  const id = useId();
  const rootRef = useRef<HTMLDivElement>(null);
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
        rootRef.current?.querySelector<HTMLButtonElement>(".sections-toggle")?.focus();
      }
    };
    document.addEventListener("pointerdown", onDown);
    window.addEventListener("keydown", onKey, true);
    // Scroll the list itself, never the page behind it.
    const list = rootRef.current?.querySelector<HTMLElement>(".sections-popover .outline__list");
    const item = list?.querySelector<HTMLElement>('[aria-current="location"]');
    if (list && item) list.scrollTop = Math.max(0, item.offsetTop - list.offsetTop - list.clientHeight / 3);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      window.removeEventListener("keydown", onKey, true);
    };
  }, [open]);
  return (
    <div className="sections" ref={rootRef}>
      <button type="button" className="sections-toggle" aria-expanded={open} aria-controls={id} onClick={() => setOpen((v) => !v)}>
        <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true">
          <path d="M2.5 4h11M2.5 8h11M2.5 12h7" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
        </svg>
        Sections
      </button>
      <div id={id} className="sections-popover" hidden={!open}>
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

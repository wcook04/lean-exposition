// The site's frame: the family's lockup (the Plectis plait, a rule, this site's mark and name), five jobs
// (Read first, then Map, Compare, Checks and a quiet Lean index), About as a quieter link, search and
// the scheme. Read is a menu button listing the three accounts with the job each one
// does, then the front page's shelf of papers and PDFs. On phones the same items
// sit behind one menu button so the bar never clips.

import { useEffect, useId, useRef, useState, type KeyboardEvent as ReactKeyboardEvent } from "react";
import type { Stage } from "../api/types";
import { BackControl } from "./BackControl";
import { navigate, routeHref, type Route } from "./router";
import { currentScheme, onSchemeChange, setScheme, type Scheme } from "./theme";
import { PAPER_NAMES, STAGE_ORDER } from "./papers";
import { useMaybeEdition } from "./data";
import { FAMILY } from "./family";

interface Props {
  route: Route;
  onSearch: () => void;
}

/** One line on what each account is for, as the Read menu says it. */
export const ACCOUNT_JOBS: Record<Stage, string> = {
  expository: "explains the ideas with worked examples",
  short: "states and proves the result, for specialists",
  long: "reconstructs each step and names its source",
};

/** Where a page may put one line of its own in the bar. */
export const BAR_LINE = "topbar-line";

type Job = "argument" | "compare" | "read" | "lean" | "checks" | "about" | null;

function jobOf(route: Route): Job {
  switch (route.view) {
    case "map":
      return "argument";
    case "compare":
      return "compare";
    case "read":
      return "read";
    case "lean":
      return "lean";
    case "checks":
      return "checks";
    case "about":
      return "about";
    default:
      return null;
  }
}

/** The status word for an account the edition marks as a draft, if any. */
function useDraftWords(): Partial<Record<Stage, string>> {
  const edition = useMaybeEdition();
  const out: Partial<Record<Stage, string>> = {};
  for (const paper of edition?.overview.papers ?? []) if (paper.state === "draft") out[paper.stage] = "draft";
  return out;
}

export function TopBar({ route, onSearch }: Props) {
  const [scheme, setLocalScheme] = useState<Scheme>(currentScheme());
  useEffect(() => onSchemeChange(() => setLocalScheme(currentScheme())), []);
  const job = jobOf(route);
  const drafts = useDraftWords();
  const readStage = route.view === "read" ? route.stage : null;

  return (
    <header className="topbar">
      <a className="skip-link" href="#main">
        Skip to content
      </a>
      {/* The family lockup (docs/family.md): the Plectis plait opens Will Cook's home page,
          which lists every website and film; the rule parts it from this site's mark and name,
          which open this site's front page. */}
      <span className="fam-lockup">
        <a className="fam-lockup__home" href={FAMILY.owner.home} rel="author" title="All of Will Cook's websites and films">
          <img src={`${import.meta.env.BASE_URL}plectis.svg`} alt="Will Cook: all websites and films" width={26} height={26} />
        </a>
        <span className="fam-lockup__rule" aria-hidden="true" />
        <a className="fam-lockup__site" href={routeHref({ view: "home" })} aria-label="Lean Exposition, front page" aria-current={route.view === "home" ? "page" : undefined}>
          <svg viewBox="0 0 32 32" aria-hidden="true" className="wordmark__mark">
            <path d="M4 27 L4 5 M4 27 L28 27" fill="none" strokeWidth="2" strokeLinecap="round" />
            <path d="M5 26 C10 22 13 17 16 14 C19 11 22 9 27 6" fill="none" strokeWidth="2.6" strokeLinecap="round" />
            <circle cx="16" cy="14" r="3" />
          </svg>
          <span className="fam-lockup__name" translate="no">
            Lean Exposition
          </span>
        </a>
      </span>
      <nav className="topnav" aria-label="Main">
        <ReadMenu current={job === "read"} stage={readStage} drafts={drafts} route={route} />
        <a className="topnav__job" href={routeHref({ view: "map" })} aria-current={job === "argument" ? "page" : undefined}>
          Map
        </a>
        <a className="topnav__job" href={routeHref({ view: "compare" })} aria-current={job === "compare" ? "page" : undefined}>
          Compare
        </a>
        <a className="topnav__job" href={routeHref({ view: "checks" })} aria-current={job === "checks" ? "page" : undefined}>
          Checks
        </a>
        <a className="topnav__job topnav__job--quiet" href={routeHref({ view: "lean" })} aria-current={job === "lean" ? "page" : undefined}>
          Lean index
        </a>
      </nav>
      {route.view !== "read" && <BackControl />}
      {/* The Lean index and Compare read a pointed name here, so nothing on the page waits for a hover. */}
      {(route.view === "lean" || route.view === "compare") && <div id={BAR_LINE} className="topbar__line" />}
      <div className="topbar__tools">
        <a className="topbar__about" href={routeHref({ view: "about" })} aria-current={job === "about" ? "page" : undefined}>
          About
        </a>
        <button type="button" className="control control--plain search-trigger" aria-label="Search the papers, the steps and the Lean" onClick={onSearch}>
          <SearchIcon />
          <span className="search-trigger__word" aria-hidden="true">
            Search
          </span>
          <kbd className="kbd" aria-hidden="true">
            /
          </kbd>
        </button>
        <SchemeToggle scheme={scheme} className="topbar__scheme" />
        <PhoneMenu route={route} job={job} drafts={drafts} scheme={scheme} />
      </div>
    </header>
  );
}

// ------------------------------------------------------------------ Read menu

/**
 * The WAI-ARIA menu button pattern: Enter, Space or ↓ opens on the first
 * account, ↑ on the last; ↑ ↓ Home End move; a letter jumps to the account it
 * starts; Escape closes and returns focus to the button; Tab closes and moves on.
 */
function ReadMenu({ current, stage, drafts, route }: { current: boolean; stage: Stage | null; drafts: Partial<Record<Stage, string>>; route: Route }) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const buttonRef = useRef<HTMLButtonElement>(null);
  const itemsRef = useRef<(HTMLAnchorElement | null)[]>([]);
  const wrapRef = useRef<HTMLDivElement>(null);
  const [focusOnOpen, setFocusOnOpen] = useState<number | null>(null);

  useEffect(() => {
    if (!open || focusOnOpen === null) return;
    itemsRef.current[focusOnOpen]?.focus();
    setFocusOnOpen(null);
  }, [open, focusOnOpen]);

  // Close when focus or a pointer leaves the menu.
  useEffect(() => {
    if (!open) return;
    const onPointer = (event: PointerEvent) => {
      if (!wrapRef.current?.contains(event.target as Node)) setOpen(false);
    };
    document.addEventListener("pointerdown", onPointer);
    return () => document.removeEventListener("pointerdown", onPointer);
  }, [open]);

  const openAt = (index: number) => {
    setOpen(true);
    setFocusOnOpen(index);
  };

  const onButtonKey = (event: ReactKeyboardEvent<HTMLButtonElement>) => {
    if (event.key === "ArrowDown" || event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      openAt(0);
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      openAt(STAGE_ORDER.length - 1);
    }
  };

  const onMenuKey = (event: ReactKeyboardEvent<HTMLDivElement>) => {
    const items = [...event.currentTarget.querySelectorAll<HTMLAnchorElement>('[role="menuitem"]')];
    const index = items.indexOf(document.activeElement as HTMLAnchorElement);
    const move = (to: number) => {
      event.preventDefault();
      items[(to + items.length) % items.length]?.focus();
    };
    if (event.key === "ArrowDown") move(index + 1);
    else if (event.key === "ArrowUp") move(index - 1);
    else if (event.key === "Home") move(0);
    else if (event.key === "End") move(items.length - 1);
    else if (event.key === "Escape") {
      event.preventDefault();
      setOpen(false);
      buttonRef.current?.focus();
    } else if (event.key === "Tab") setOpen(false);
    else if (event.key.length === 1 && /\S/.test(event.key)) {
      const letter = event.key.toLowerCase();
      const at = STAGE_ORDER.findIndex((s, i) => i > index && PAPER_NAMES[s].short.toLowerCase().startsWith(letter));
      const first = STAGE_ORDER.findIndex((s) => PAPER_NAMES[s].short.toLowerCase().startsWith(letter));
      if (at >= 0) move(at);
      else if (first >= 0) move(first);
    }
  };

  return (
    <div className="readmenu" ref={wrapRef}>
      <button
        ref={buttonRef}
        type="button"
        className="topnav__job readmenu__button"
        id={`${id}-button`}
        aria-haspopup="menu"
        aria-expanded={open}
        aria-controls={`${id}-menu`}
        aria-current={current ? "page" : undefined}
        onClick={() => (open ? setOpen(false) : openAt(stage ? STAGE_ORDER.indexOf(stage) : 0))}
        onKeyDown={onButtonKey}
      >
        Read
        <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true" className={`readmenu__chev${open ? " is-open" : ""}`}>
          <path d="M2 3.5l3 3 3-3" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
      </button>
      <div
        id={`${id}-menu`}
        role="menu"
        aria-labelledby={`${id}-button`}
        className="readmenu__menu"
        hidden={!open}
        onKeyDown={onMenuKey}
        onClick={() => setOpen(false)}
      >
        {STAGE_ORDER.map((s, i) => (
          <a
            key={s}
            ref={(el) => {
              itemsRef.current[i] = el;
            }}
            role="menuitem"
            tabIndex={-1}
            href={routeHref({ view: "read", stage: s })}
            className="readmenu__item"
            aria-current={stage === s ? "page" : undefined}
          >
            <span className="readmenu__name">
              {PAPER_NAMES[s].short}
              {drafts[s] && <span className="readmenu__state">, {drafts[s]}</span>}
            </span>
            <span className="readmenu__job">{ACCOUNT_JOBS[s]}</span>
          </a>
        ))}
        <PapersLink className="readmenu__item readmenu__item--all" route={route} menu />
      </div>
    </div>
  );
}

// ------------------------------------------------------------------- phones

/** Below 56.25em (900px at the default text size): a disclosure holding the same four jobs, the accounts and About. */
function PhoneMenu({ route, job, drafts, scheme }: { route: Route; job: Job; drafts: Partial<Record<Stage, string>>; scheme: Scheme }) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const buttonRef = useRef<HTMLButtonElement>(null);
  const panelRef = useRef<HTMLDivElement>(null);
  useEffect(() => setOpen(false), [route]);
  useEffect(() => {
    if (!open) return;
    // The menu is fixed; focus must not scroll the page behind it, or the reader loses their place.
    panelRef.current?.querySelector<HTMLElement>("a, button")?.focus({ preventScroll: true });
    const onPointer = (event: PointerEvent) => {
      const target = event.target as Node;
      if (!panelRef.current?.contains(target) && !buttonRef.current?.contains(target)) setOpen(false);
    };
    document.addEventListener("pointerdown", onPointer);
    return () => document.removeEventListener("pointerdown", onPointer);
  }, [open]);

  const stage = route.view === "read" ? route.stage : null;
  return (
    <>
      <button
        ref={buttonRef}
        type="button"
        className="control control--plain menu-toggle"
        aria-expanded={open}
        aria-controls={`${id}-panel`}
        aria-label="Menu"
        onClick={() => setOpen((o) => !o)}
      >
        <svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
          {open ? (
            <path d="M3.5 3.5l9 9M12.5 3.5l-9 9" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
          ) : (
            <path d="M2 4h12M2 8h12M2 12h12" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
          )}
        </svg>
      </button>
      <div
        ref={panelRef}
        id={`${id}-panel`}
        className="phonemenu"
        hidden={!open}
        onKeyDown={(event) => {
          if (event.key === "Escape") {
            event.preventDefault();
            setOpen(false);
            buttonRef.current?.focus();
          }
        }}
      >
        <nav aria-label="Main">
          <ul className="phonemenu__list">
            <li>
              <span className="phonemenu__job phonemenu__job--head" id={`${id}-read`} aria-current={job === "read" ? "true" : undefined}>
                Read
              </span>
              <ul className="phonemenu__accounts" aria-labelledby={`${id}-read`}>
                {STAGE_ORDER.map((s) => (
                  <li key={s}>
                    <a href={routeHref({ view: "read", stage: s })} className="readmenu__item" aria-current={stage === s ? "page" : undefined}>
                      <span className="readmenu__name">
                        {PAPER_NAMES[s].short}
                        {drafts[s] && <span className="readmenu__state">, {drafts[s]}</span>}
                      </span>
                      <span className="readmenu__job">{ACCOUNT_JOBS[s]}</span>
                    </a>
                  </li>
                ))}
              </ul>
            </li>
            <li>
              <PapersLink className="phonemenu__job" route={route} onGo={() => setOpen(false)} />
            </li>
            <li>
              <a className="phonemenu__job" href={routeHref({ view: "map" })} aria-current={job === "argument" ? "page" : undefined}>
                Map
              </a>
            </li>
            <li>
              <a className="phonemenu__job" href={routeHref({ view: "compare" })} aria-current={job === "compare" ? "page" : undefined}>
                Compare
              </a>
            </li>
            <li>
              <a className="phonemenu__job" href={routeHref({ view: "checks" })} aria-current={job === "checks" ? "page" : undefined}>
                Checks
              </a>
            </li>
            <li>
              <a className="phonemenu__job phonemenu__job--quiet" href={routeHref({ view: "lean" })} aria-current={job === "lean" ? "page" : undefined}>
                Lean index
              </a>
            </li>
            <li>
              <a className="phonemenu__job phonemenu__job--quiet" href={routeHref({ view: "about" })} aria-current={job === "about" ? "page" : undefined}>
                About
              </a>
            </li>
          </ul>
        </nav>
        <SchemeToggle scheme={scheme} className="phonemenu__scheme" labelled />
      </div>
    </>
  );
}

// ------------------------------------------------------------------- pieces

/** The id of the front page's shelf of papers, which "Papers" opens. */
export const PAPERS_ANCHOR = "papers";

/**
 * Papers: the front page's shelf, where each paper can be read here or opened as a
 * PDF. On the front page itself the link scrolls to the shelf even when the address
 * already names it.
 */
function PapersLink({ className, route, onGo, menu }: { className: string; route: Route; onGo?: () => void; menu?: boolean }) {
  return (
    <a
      className={className}
      role={menu ? "menuitem" : undefined}
      tabIndex={menu ? -1 : undefined}
      href={routeHref({ view: "home", anchor: PAPERS_ANCHOR })}
      onClick={(event) => {
        onGo?.();
        if (route.view !== "home" || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
        const shelf = document.getElementById(PAPERS_ANCHOR);
        if (!shelf) return;
        event.preventDefault();
        if (route.anchor !== PAPERS_ANCHOR) navigate(routeHref({ view: "home", anchor: PAPERS_ANCHOR }));
        shelf.scrollIntoView({ block: "start" });
      }}
    >
      {menu ? (
        <>
          <span className="readmenu__name">All papers and PDFs</span>
          <span className="readmenu__job">every account on one shelf, with its first page</span>
        </>
      ) : (
        "Papers"
      )}
    </a>
  );
}

function SchemeToggle({ scheme, className, labelled }: { scheme: Scheme; className: string; labelled?: boolean }) {
  const label = scheme === "dark" ? "Switch to light colours" : "Switch to dark colours";
  return (
    <button
      type="button"
      className={`control control--plain scheme-toggle ${className}`}
      aria-label={labelled ? undefined : label}
      onClick={() => setScheme(scheme === "dark" ? "light" : "dark")}
    >
      <svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
        {scheme === "dark" ? (
          <g fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round">
            <circle cx="8" cy="8" r="3.2" />
            <path d="M8 1.5v1.6M8 12.9v1.6M1.5 8h1.6M12.9 8h1.6M3.4 3.4l1.1 1.1M11.5 11.5l1.1 1.1M3.4 12.6l1.1-1.1M11.5 4.5l1.1-1.1" />
          </g>
        ) : (
          <path d="M13.2 10.1A5.6 5.6 0 0 1 5.9 2.8a5.6 5.6 0 1 0 7.3 7.3z" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinejoin="round" />
        )}
      </svg>
      {labelled && <span>{label}</span>}
    </button>
  );
}

function SearchIcon() {
  return (
    <svg viewBox="0 0 16 16" width="15" height="15" aria-hidden="true">
      <circle cx="7" cy="7" r="4.6" fill="none" stroke="currentColor" strokeWidth="1.5" />
      <path d="M10.4 10.4 L14 14" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
    </svg>
  );
}

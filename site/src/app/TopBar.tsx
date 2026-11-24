// A compact title and one disclosure for the reader's site-wide navigation.

import site from "@instance/site";
import { useEffect, useId, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { BackControl } from "./BackControl";
import { navigate, routeHref, type Route } from "./router";
import { currentScheme, onSchemeChange, setScheme } from "./theme";
import { EXTERNAL_DOCUMENTS, PAPER_NAMES, STAGE_ORDER } from "./papers";
import { useMaybeEdition } from "./data";
import { SITE_NAME } from "./siteName";

const EDITIONS: Stage[] = (site.readMenu as Stage[] | undefined) ?? STAGE_ORDER;
const ONLY_EDITIONS = !!site.readMenu;

const COMPANION_GROUPS = (site.library?.companions ?? []).reduce<{
  id: string;
  title: string;
  docs: { slot: string; title: string }[];
}[]>((groups, doc) => {
  let group = groups.find(({ id }) => id === doc.group);
  if (!group) groups.push((group = { id: doc.group, title: doc.group_title, docs: [] }));
  group.docs.push(doc);
  return groups;
}, []);

export const ACCOUNT_JOBS: Record<Stage, string> = {
  expository: "the ideas, with worked examples",
  short: "the result and its proof, for specialists",
  long: "each step, with its source",
};

export const BAR_LINE = "topbar-line";
export const PAPERS_ANCHOR = "papers";

const DESTINATIONS = [
  ["map", "Map"],
  ["compare", "Compare"],
  ["lean", "Lean index"],
] as const;

export function TopBar({ route, onSearch }: { route: Route; onSearch(): void }) {
  const titleHref = site.library ? routeHref({ view: "read", stage: site.library.main }) : routeHref({ view: "home" });
  return (
    <header className="topbar">
      <a className="skip-link" href="#main">Skip to content</a>
      <a className="topbar__title" href={titleHref} translate="no">{SITE_NAME}</a>
      {route.view !== "read" && <BackControl />}
      {(route.view === "lean" || route.view === "compare") && <div id={BAR_LINE} className="topbar__line" />}
      <SiteMenu route={route} onSearch={onSearch} />
    </header>
  );
}

function SiteMenu({ route, onSearch }: { route: Route; onSearch(): void }) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const [scheme, setLocalScheme] = useState(currentScheme);
  const wrapRef = useRef<HTMLDivElement>(null);
  const buttonRef = useRef<HTMLButtonElement>(null);
  const edition = useMaybeEdition();
  const activeStage = route.view === "read" ? route.stage : null;

  useEffect(() => onSchemeChange(() => setLocalScheme(currentScheme())), []);
  useEffect(() => setOpen(false), [route]);
  useEffect(() => {
    if (!open) return;
    const closeOutside = (event: PointerEvent) => {
      if (!wrapRef.current?.contains(event.target as Node)) setOpen(false);
    };
    document.addEventListener("pointerdown", closeOutside);
    return () => document.removeEventListener("pointerdown", closeOutside);
  }, [open]);

  function closeAndFocus() {
    setOpen(false);
    buttonRef.current?.focus({ preventScroll: true });
  }

  return (
    <div
      className="site-menu"
      ref={wrapRef}
      onBlur={(event) => {
        if (!event.currentTarget.contains(event.relatedTarget)) setOpen(false);
      }}
      onKeyDown={(event) => {
        if (event.key === "Escape" && open) {
          event.preventDefault();
          event.stopPropagation();
          closeAndFocus();
        }
      }}
    >
      <button
        type="button"
        ref={buttonRef}
        className="control control--plain menu-toggle"
        aria-expanded={open}
        aria-controls={id}
        onClick={() => setOpen(!open)}
      >
        <svg viewBox="0 0 16 16" width="16" height="16" fill="none" aria-hidden="true">
          <path d={open ? "M3.5 3.5l9 9M12.5 3.5l-9 9" : "M2 4h12M2 8h12M2 12h12"} stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
        </svg>
        Menu
      </button>
      <div id={id} className="site-menu__panel" hidden={!open}>
        <nav aria-label="Main">
          <p className="site-menu__label" id={`${id}-read`}>Read</p>
          <ul className="site-menu__list" aria-labelledby={`${id}-read`}>
            {EDITIONS.map((stage) => {
              const draft = !ONLY_EDITIONS && edition?.overview.papers.some((paper) => paper.stage === stage && paper.state === "draft");
              return (
                <li key={stage}>
                  <a className="readmenu__item" href={routeHref({ view: "read", stage })} aria-current={activeStage === stage ? "page" : undefined} onClick={closeAndFocus}>
                    {site.readMenuNames?.[stage] ?? PAPER_NAMES[stage].short}{draft && <span className="readmenu__state"> (draft)</span>}
                  </a>
                </li>
              );
            })}
            {!ONLY_EDITIONS && COMPANION_GROUPS.map((group) => (
              <li key={group.id}>
                <p className="site-menu__label" id={`${id}-${group.id}`}>{group.title}</p>
                <ul className="site-menu__list" aria-labelledby={`${id}-${group.id}`}>
                  {group.docs.map((doc) => (
                    <li key={doc.slot}>
                      <a className="readmenu__item" href={routeHref({ view: "read", stage: doc.slot })} aria-current={activeStage === doc.slot ? "page" : undefined} onClick={closeAndFocus}>{doc.title}</a>
                    </li>
                  ))}
                </ul>
              </li>
            ))}
            {EXTERNAL_DOCUMENTS.map((doc) => (
              <li key={doc.href}><a className="readmenu__item" href={doc.href} onClick={closeAndFocus}>{doc.title}</a></li>
            ))}
            {!site.library && (
              <li>
                <a
                  className="readmenu__item"
                  href={routeHref({ view: "home", anchor: PAPERS_ANCHOR })}
                  onClick={(event) => {
                    closeAndFocus();
                    if (route.view !== "home" || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
                    const shelf = document.getElementById(PAPERS_ANCHOR);
                    if (!shelf) return;
                    event.preventDefault();
                    if (route.anchor !== PAPERS_ANCHOR) navigate(routeHref({ view: "home", anchor: PAPERS_ANCHOR }));
                    shelf.scrollIntoView({ block: "start" });
                  }}
                >All papers and PDFs</a>
              </li>
            )}
          </ul>
          <ul className="site-menu__list site-menu__routes">
            {DESTINATIONS.map(([view, name]) => (
              <li key={view}>
                <a className="readmenu__item" href={routeHref({ view })} aria-current={route.view === view ? "page" : undefined} onClick={closeAndFocus}>{name}</a>
              </li>
            ))}
          </ul>
        </nav>
        <div className="site-menu__actions">
          <button type="button" className="control control--plain search-trigger" onClick={() => {
            closeAndFocus();
            onSearch();
          }}>
            <SearchIcon />
            Search
            <kbd className="kbd" aria-hidden="true">/</kbd>
          </button>
          <button type="button" className="control control--plain scheme-toggle" onClick={() => setScheme(scheme === "dark" ? "light" : "dark")}>
            {scheme === "dark" ? "Switch to light colours" : "Switch to dark colours"}
          </button>
        </div>
      </div>
    </div>
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

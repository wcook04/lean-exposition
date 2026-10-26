import { useEffect, useState } from "react";
import type { Stage } from "../api/types";
import { routeHref, type Route } from "./router";
import { currentScheme, onSchemeChange, setScheme, type Scheme } from "./theme";
import { PAPER_NAMES } from "./papers";

interface Props {
  route: Route;
  onSearch: () => void;
}

const READ_ORDER: Stage[] = ["expository", "short", "long"];

export function TopBar({ route, onSearch }: Props) {
  const [scheme, setLocalScheme] = useState<Scheme>(currentScheme());
  useEffect(() => onSchemeChange(() => setLocalScheme(currentScheme())), []);
  const [menu, setMenu] = useState(false);
  useEffect(() => setMenu(false), [route]);

  const current = (view: string, stage?: Stage) =>
    route.view === view && (!stage || (route.view === "read" && route.stage === stage)) ? "page" : undefined;

  return (
    <header className="topbar">
      <a className="skip-link" href="#main">
        Skip to content
      </a>
      <a className="wordmark" href={routeHref({ view: "map" })} aria-label="Lean Exposition, the argument map">
        <svg viewBox="0 0 32 32" aria-hidden="true" className="wordmark__mark">
          <path d="M4 27 L4 5 M4 27 L28 27" fill="none" strokeWidth="2" strokeLinecap="round" />
          <path d="M5 26 C10 22 13 17 16 14 C19 11 22 9 27 6" fill="none" strokeWidth="2.6" strokeLinecap="round" />
          <circle cx="16" cy="14" r="3" />
        </svg>
        <span>Lean Exposition</span>
      </a>
      <nav className={`topnav${menu ? " topnav--open" : ""}`} aria-label="Sections">
        <a href={routeHref({ view: "map" })} aria-current={current("map")}>
          Map
        </a>
        {READ_ORDER.map((stage) => (
          <a key={stage} href={routeHref({ view: "read", stage })} aria-current={current("read", stage)}>
            {PAPER_NAMES[stage].short}
          </a>
        ))}
        <a href={routeHref({ view: "checks" })} aria-current={current("checks")}>
          Checks
        </a>
        <a href={routeHref({ view: "about" })} aria-current={current("about")}>
          About
        </a>
      </nav>
      <div className="topbar__tools">
        <button type="button" className="control control--plain search-trigger" onClick={onSearch}>
          <svg viewBox="0 0 16 16" width="15" height="15" aria-hidden="true">
            <circle cx="7" cy="7" r="4.6" fill="none" stroke="currentColor" strokeWidth="1.5" />
            <path d="M10.4 10.4 L14 14" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
          </svg>
          <span>Search</span>
          <kbd className="kbd">/</kbd>
        </button>
        <button
          type="button"
          className="control control--plain scheme-toggle"
          aria-label={scheme === "dark" ? "Use the day scheme" : "Use the night scheme"}
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
        </button>
        <button
          type="button"
          className="control control--plain menu-toggle"
          aria-expanded={menu}
          aria-label="Sections"
          onClick={() => setMenu((m) => !m)}
        >
          <svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
            <path d="M2 4h12M2 8h12M2 12h12" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" />
          </svg>
        </button>
      </div>
    </header>
  );
}

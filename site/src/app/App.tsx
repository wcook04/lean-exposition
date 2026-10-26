import { lazy, Suspense, useEffect, useState } from "react";
import { describeError, EditionProvider, useEdition, useEditionChanged, useEditionRetry } from "./data";
import { routeHref, useLinkInterception, useRoute, type Route } from "./router";
import { TopBar } from "./TopBar";
import { PageTitle } from "./PageTitle";
import { EDITION_PREFIX, linkedEdition, sameEdition } from "./cite";
import { MapPage } from "../map/MapPage";

const FrontPage = lazy(() => import("../home/FrontPage").then((m) => ({ default: m.FrontPage })));
const ReaderPage = lazy(() => import("../reader/ReaderPage").then((m) => ({ default: m.ReaderPage })));
const ChecksPage = lazy(() => import("../checks/ChecksPage").then((m) => ({ default: m.ChecksPage })));
const AboutPage = lazy(() => import("../reader/AboutPage").then((m) => ({ default: m.AboutPage })));
const SearchPage = lazy(() => import("../search/SearchPage").then((m) => ({ default: m.SearchPage })));
const SearchPalette = lazy(() => import("../search/SearchPalette").then((m) => ({ default: m.SearchPalette })));

export function App() {
  useLinkInterception();
  const route = useRoute();
  const [searching, setSearching] = useState(false);

  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      const target = event.target as HTMLElement | null;
      const typing = target && (target.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(target.tagName));
      if (typing) return;
      if (event.key === "/" || ((event.metaKey || event.ctrlKey) && event.key.toLowerCase() === "k")) {
        event.preventDefault();
        setSearching(true);
      }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, []);

  useEffect(() => {
    document.documentElement.dataset.view = route.view;
  }, [route.view]);

  return (
    <div className="app" data-view={route.view}>
      <EditionProvider
        paperFirst={route.view === "read" ? route.stage : null}
        fallback={(state, retry) => (
          <>
            <TopBar route={route} onSearch={() => setSearching(true)} />
            <main id="main" className="app__main" tabIndex={-1}>
              <BootScreen state={state} retry={retry} view={route.view} />
            </main>
          </>
        )}
      >
        <TopBar route={route} onSearch={() => setSearching(true)} />
        <PageTitle route={route} />
        <EditionBanner />
        <LinkedEditionNotice />
        <main id="main" className="app__main" tabIndex={-1}>
          <Suspense fallback={<Skeleton view={route.view} />}>
            <Page route={route} />
          </Suspense>
        </main>
        {searching && (
          <Suspense fallback={null}>
            <SearchPalette onClose={() => setSearching(false)} />
          </Suspense>
        )}
      </EditionProvider>
    </div>
  );
}

function Page({ route }: { route: Route }) {
  switch (route.view) {
    case "home":
      return <FrontPage />;
    case "map":
      return <MapGate route={route} />;
    case "read":
      return <ReaderPage route={route} />;
    case "checks":
      return <ChecksPage route={route} />;
    case "about":
      return <AboutPage route={route} />;
    case "search":
      return <SearchPage route={route} />;
    case "missing":
      return (
        <div className="page-message">
          <h1>No page at this address</h1>
          <p>
            Go to the <a href={routeHref({ view: "home" })}>front page</a> or the <a href={routeHref({ view: "map" })}>argument map</a>,
            or use search to find a result, a section or a passage.
          </p>
        </div>
      );
  }
}

function EditionBanner() {
  const changed = useEditionChanged();
  if (!changed) return null;
  return (
    <div className="edition-banner" role="alert">
      <span>
        The server has started serving a different edition, that is, a different fixed set of records and papers. This page
        still shows the earlier edition.
      </span>
      <button type="button" className="control" onClick={() => window.location.reload()}>
        Reload to read the new edition
      </button>
    </div>
  );
}

/**
 * The map draws theorem applications from the stored edges, so it waits for
 * them (and for the warrants) rather than re-laying itself out when they
 * arrive. Until then it shows the goal plate it is about to draw.
 */
function MapGate({ route }: { route: Extract<Route, { view: "map" }> }) {
  const edition = useEdition();
  const retry = useEditionRetry();
  if (edition.context === "ready") return <MapPage route={route} />;
  if (edition.context === "error") {
    const { title, detail } = describeError(edition.contextError);
    return (
      <div className="boot boot--error" role="alert">
        <h1>The links between records could not be loaded</h1>
        <p>
          {title}. {detail}
        </p>
        <button type="button" className="control" onClick={retry}>
          Try again
        </button>
      </div>
    );
  }
  const long = edition.overview.papers.find((p) => p.stage === "long");
  const goal = (long?.paper_scope.selected_goal_ids ?? edition.graph.goals).find((g) => edition.graph.nodes.has(g));
  return <Skeleton view="map" title={goal ? edition.graph.nodes.get(goal)!.label : undefined} />;
}

/**
 * A still outline of the page that is about to appear: the goal plate for
 * the map, a reading column for an account. It does not animate (nothing on
 * the site loops); the words for assistive technology say what is happening.
 */
function Skeleton({ view, title }: { view: Route["view"]; title?: string }) {
  if (view === "read") {
    return (
      <div className="skeleton skeleton--paper" aria-busy="true">
        <p className="visually-hidden" role="status">
          Loading the paper…
        </p>
        <span className="skeleton__bar skeleton__bar--caps" />
        <span className="skeleton__bar skeleton__bar--title" />
        <span className="skeleton__bar skeleton__bar--title skeleton__bar--short" />
        {[100, 96, 98, 92, 60, 0, 100, 94, 97, 88, 99, 45].map((w, i) =>
          w ? <span key={i} className="skeleton__bar skeleton__bar--line" style={{ width: `${w}%` }} /> : <span key={i} className="skeleton__gap" />,
        )}
      </div>
    );
  }
  return (
    <div className={`skeleton${view === "map" ? " skeleton--plate" : ""}`} aria-busy="true">
      <p className="visually-hidden" role="status">
        {view === "map" ? "Loading the argument map…" : "Loading the records…"}
      </p>
      <span className="skeleton__bar skeleton__bar--caps" />
      {title ? <p className="skeleton__title">{title}</p> : <span className="skeleton__bar skeleton__bar--title" />}
      <span className="skeleton__bar skeleton__bar--line" style={{ width: "92%" }} />
      <span className="skeleton__bar skeleton__bar--line" style={{ width: "86%" }} />
      <span className="skeleton__bar skeleton__bar--line" style={{ width: "54%" }} />
      <span className="skeleton__actions">
        <span className="skeleton__bar skeleton__bar--button" />
        <span className="skeleton__bar skeleton__bar--button" />
      </span>
    </div>
  );
}

/**
 * A link copied with "Copy link to this edition" names its edition. When the
 * server now serves another one, say so before anything is read as cited.
 */
function LinkedEditionNotice() {
  const { snapshot } = useEdition();
  const [linked] = useState(() => linkedEdition());
  const [dismissed, setDismissed] = useState(false);
  if (!linked || dismissed || sameEdition(linked, snapshot)) return null;
  return (
    <div className="edition-banner" role="alert">
      <span>
        The link you followed was copied from edition <code translate="no">{linked.slice(0, EDITION_PREFIX)}</code> of the
        records and papers. The server is serving edition{" "}
        <code translate="no">{snapshot.manifest_sha256.slice(0, EDITION_PREFIX)}</code>, so this page shows that edition, not the
        one the link was copied from.
      </span>
      <button type="button" className="control" onClick={() => setDismissed(true)}>
        Close this notice
      </button>
    </div>
  );
}

function BootScreen({ state, retry, view }: { state: { status: string; error?: unknown }; retry: () => void; view: Route["view"] }) {
  if (state.status === "loading") return <Skeleton view={view} />;
  const { title, detail } = describeError(state.error);
  return (
    <div className="boot boot--error" role="alert">
      <h1>{title}</h1>
      <p>{detail}</p>
      <button type="button" className="control" onClick={retry}>
        Try again
      </button>
    </div>
  );
}

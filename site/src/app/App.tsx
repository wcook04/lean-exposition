import { lazy, Suspense, useEffect, useState } from "react";
import { describeError, EditionProvider, useEditionChanged } from "./data";
import { useLinkInterception, useRoute, type Route } from "./router";
import { TopBar } from "./TopBar";
import { MapPage } from "../map/MapPage";

const ReaderPage = lazy(() => import("../reader/ReaderPage").then((m) => ({ default: m.ReaderPage })));
const ChecksPage = lazy(() => import("../checks/ChecksPage").then((m) => ({ default: m.ChecksPage })));
const AboutPage = lazy(() => import("../reader/AboutPage").then((m) => ({ default: m.AboutPage })));
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
      <TopBar route={route} onSearch={() => setSearching(true)} />
      <EditionProvider fallback={(state, retry) => <BootScreen state={state} retry={retry} />}>
        <EditionBanner />
        <main id="main" className="app__main" tabIndex={-1}>
          <Suspense fallback={<div className="page-loading" aria-live="polite">Opening…</div>}>
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
    case "map":
      return <MapPage route={route} />;
    case "read":
      return <ReaderPage route={route} />;
    case "checks":
      return <ChecksPage route={route} />;
    case "about":
      return <AboutPage route={route} />;
    case "missing":
      return (
        <div className="page-message">
          <h1>No page at this address</h1>
          <p>
            <a href="/">Open the argument map</a> or use search to find a result, a section or a passage.
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
      <span>The server now serves a different edition of the papers. What you are reading belongs to the earlier edition.</span>
      <button type="button" className="control" onClick={() => window.location.reload()}>
        Open the new edition
      </button>
    </div>
  );
}

function BootScreen({ state, retry }: { state: { status: string; error?: unknown }; retry: () => void }) {
  if (state.status === "loading") {
    return (
      <div className="boot" aria-live="polite">
        <svg viewBox="0 0 120 60" className="boot__mark" aria-hidden="true">
          <path d="M6 54 C30 46 42 30 60 24 C78 18 92 12 114 6" />
        </svg>
        <p>Opening the edition…</p>
      </div>
    );
  }
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

// The full results page for one query: every match of one kind, in the API's
// bounded pages. The address holds the exact query, the kind and the page,
// so Back from an opened result returns here, to the same page.

import { useEffect, useRef, useState, type FormEvent } from "react";
import "katex/dist/katex.min.css";
import { get } from "../api/client";
import type { Page, SearchItem } from "../api/types";
import { describeError, useEdition, useResource } from "../app/data";
import { navigate, routeHref, type Route, type SearchType } from "../app/router";
import { destination, destinationWords, directHref, nounFor, ResultBody, SEARCH_HELP, SEARCH_TABLES, tableOf } from "./results";
import "./search.css";

/** Results per page; well inside the API's page limit. */
export const PER_PAGE = 20;
const MAX_CHARS = 256;
const MAX_TOKENS = 16;

type SearchRoute = Extract<Route, { view: "search" }>;

/** How many matches each kind has: one request per table, one item each. */
function useCounts(q: string) {
  return useResource(q ? `search-counts:${q}` : null, () =>
    Promise.all(
      SEARCH_TABLES.map(({ type, table }) => get<Page<SearchItem>>("/search", { q, table, limit: 1 }).then((r) => [type, r.data.total] as const)),
    ).then((pairs) => new Map<SearchType, number>(pairs)),
  );
}

function usePageOf(q: string, type: SearchType | null, page: number) {
  const offset = (page - 1) * PER_PAGE;
  const key = q && type ? `search:${q}:${type}:${offset}` : null;
  return useResource(key, () => get<Page<SearchItem>>("/search", { q, table: tableOf(type!), limit: PER_PAGE, offset }).then((r) => r.data));
}

/** The 1-based page holding results `from`…`to` and the page count, from a total. */
export function pageWindow(total: number, page: number, per = PER_PAGE): { from: number; to: number; pages: number; page: number } {
  const pages = Math.max(1, Math.ceil(total / per));
  const p = Math.min(Math.max(1, page), pages);
  return { from: total === 0 ? 0 : (p - 1) * per + 1, to: Math.min(total, p * per), pages, page: p };
}

export function SearchPage({ route }: { route: SearchRoute }) {
  const q = route.q.trim();
  const tokens = q ? q.split(/\s+/) : [];
  const tooLong = tokens.length > MAX_TOKENS || q.length > MAX_CHARS;
  const counts = useCounts(tooLong ? "" : q);
  const ready = counts.status === "ready" ? counts.value : null;
  // Without a kind in the address, list the first kind that has matches.
  const type: SearchType | null = route.type ?? (ready ? (SEARCH_TABLES.find((t) => (ready.get(t.type) ?? 0) > 0)?.type ?? null) : null);
  const total = type && ready ? ready.get(type) ?? 0 : 0;
  const win = pageWindow(total, route.page ?? 1);
  const results = usePageOf(tooLong ? "" : q, type, win.page);
  const grand = ready ? [...ready.values()].reduce((s, n) => s + n, 0) : 0;

  const headingRef = useRef<HTMLHeadingElement>(null);
  const resultsKey = `${q}|${type}|${win.page}`;
  useEffect(() => {
    // A new query, kind or page starts at its heading for keyboard and screen-reader users.
    headingRef.current?.focus({ preventScroll: true });
    window.scrollTo({ top: 0 });
  }, [resultsKey]);

  return (
    <div className="search-page">
      <header className="search-page__head">
        <p className="caps">Search</p>
        <h1 ref={headingRef} tabIndex={-1}>
          {q ? (
            <>
              Results for <q>{q}</q>
            </>
          ) : (
            "Search records and passages"
          )}
        </h1>
        <SearchForm q={route.q} />
        <p className="search-page__help">{SEARCH_HELP}</p>
      </header>

      {tooLong && (
        <p className="search-page__status" role="status">
          Search takes at most {MAX_TOKENS} words and {MAX_CHARS} characters. Remove some words.
        </p>
      )}
      {counts.status === "error" && <ErrorNote error={counts.error} />}
      {q && !tooLong && counts.status === "loading" && (
        <p className="search-page__status" role="status">
          Searching…
        </p>
      )}

      {ready && grand === 0 && (
        <p className="search-page__status" role="status">
          No record, section heading or linked passage contains all of these words. Search covers only records, section
          headings and passages linked to records, so other text in the papers is not searched. Try fewer words, or another
          spelling.
        </p>
      )}

      {ready && grand > 0 && (
        <>
          <nav className="search-kinds" aria-label="Kinds of result">
            <ul>
              {SEARCH_TABLES.map((t) => {
                const n = ready.get(t.type) ?? 0;
                return (
                  <li key={t.type}>
                    {n > 0 ? (
                      <a href={routeHref({ view: "search", q: route.q, type: t.type })} aria-current={t.type === type ? "page" : undefined}>
                        <span className="num">{n}</span> {nounFor(t.type, n)}
                      </a>
                    ) : (
                      <span className="search-kinds__none">
                        <span className="num">0</span> {nounFor(t.type, 0)}
                      </span>
                    )}
                  </li>
                );
              })}
            </ul>
          </nav>

          {type && (
            <section className="search-results" aria-labelledby="search-results-title">
              <h2 id="search-results-title" className="search-results__title">
                {total} matching {nounFor(type, total)}
                {win.pages > 1 && (
                  <span className="search-results__range num">
                    {", "}
                    showing {win.from}–{win.to}
                  </span>
                )}
              </h2>
              {total === 0 && <p className="search-page__status">No {nounFor(type, 0)} match these words.</p>}
              {results.status === "error" && <ErrorNote error={results.error} />}
              {results.status === "loading" && total > 0 && (
                <p className="search-page__status" role="status">
                  Loading results {win.from}–{win.to}…
                </p>
              )}
              {results.status === "ready" && (
                <ol className="search-results__list" start={win.from}>
                  {results.value.items.map((item) => (
                    <li key={item.ref}>
                      <Result item={item} />
                    </li>
                  ))}
                </ol>
              )}
              {win.pages > 1 && <Pager route={route} type={type} page={win.page} pages={win.pages} />}
            </section>
          )}
        </>
      )}
    </div>
  );
}

function SearchForm({ q }: { q: string }) {
  const [text, setText] = useState(q);
  useEffect(() => setText(q), [q]);
  const submit = (event: FormEvent) => {
    event.preventDefault();
    const next = text.trim();
    if (next) navigate({ view: "search", q: next });
  };
  return (
    <form role="search" className="search-form" onSubmit={submit}>
      <label className="visually-hidden" htmlFor="search-page-input">
        Words to find
      </label>
      <input
        id="search-page-input"
        className="search-form__input"
        type="search"
        value={text}
        maxLength={MAX_CHARS + 40}
        autoComplete="off"
        spellCheck={false}
        onChange={(e) => setText(e.target.value)}
      />
      <button type="submit" className="control search-form__go">
        Search
      </button>
    </form>
  );
}

/** One result: what it is (kind, in words) and where it opens, then the match. */
function Result({ item }: { item: SearchItem }) {
  const { graph } = useEdition();
  const [opening, setOpening] = useState(false);
  const [failed, setFailed] = useState<string | null>(null);
  const href = directHref(item);
  const body = (
    <>
      <ResultBody item={item} opening={opening} />
      <span className="search-result__dest">{destinationWords(item)}</span>
    </>
  );
  if (href) {
    return (
      <a className="search-result" href={href}>
        {body}
      </a>
    );
  }
  const open = async () => {
    setOpening(true);
    setFailed(null);
    try {
      const target = await destination(item, graph);
      setOpening(false);
      if (!target) {
        setFailed("This result has no page to open on this site.");
        return;
      }
      if (/^https?:\/\//.test(target)) window.open(target, "_blank", "noopener,noreferrer");
      else navigate(target);
    } catch (error) {
      setOpening(false);
      setFailed(describeError(error).title);
    }
  };
  return (
    <>
      <button type="button" className="search-result" onClick={() => void open()}>
        {body}
      </button>
      {failed && (
        <p className="search-result__error" role="alert">
          {failed}
        </p>
      )}
    </>
  );
}

function Pager({ route, type, page, pages }: { route: SearchRoute; type: SearchType; page: number; pages: number }) {
  const at = (p: number) => routeHref({ view: "search", q: route.q, type, page: p });
  return (
    <nav className="pager" aria-label="Result pages">
      {page > 1 ? (
        <a className="control" href={at(page - 1)} rel="prev">
          ← Previous page
        </a>
      ) : (
        <span />
      )}
      <span className="pager__where num">
        Page {page} of {pages}
      </span>
      {page < pages ? (
        <a className="control" href={at(page + 1)} rel="next">
          Next page →
        </a>
      ) : (
        <span />
      )}
    </nav>
  );
}

function ErrorNote({ error }: { error: unknown }) {
  const { title, detail } = describeError(error);
  return (
    <p className="search-page__status search-page__error" role="alert">
      {title}. {detail}{" "}
      <button type="button" className="control" onClick={() => window.location.reload()}>
        Try again
      </button>
    </p>
  );
}

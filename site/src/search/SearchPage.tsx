// The full results page for one query: every match of one kind, best first
// (rank.ts), with the matching Lean declarations beside them. The address holds
// the exact query, the kind and the page, so Back from an opened result returns
// here, to the same page.

import { useEffect, useRef, useState, type FormEvent } from "react";
import "katex/dist/katex.min.css";
import type { SearchItem } from "../api/types";
import { describeError, useEdition, useResource } from "../app/data";
import { navigate, routeHref, type Route, type SearchType } from "../app/router";
import { destination, destinationWords, directHref, LeanResultBody, nounFor, ResultBody, SEARCH_HELP, SEARCH_TABLES } from "./results";
import { rankedSearch } from "./rank";
import { leanNames, searchLean, type LeanHit } from "./leanNames";
import "./search.css";

/** Results per page; well inside the API's page limit. */
export const PER_PAGE = 20;
const MAX_CHARS = 256;
const MAX_TOKENS = 16;

type SearchRoute = Extract<Route, { view: "search" }>;

const LEAN_SHOWN = 8;

/** Every match of every kind, ranked. Nothing is requested until a query is typed. */
function useRanked(q: string) {
  return useResource(q ? `search-ranked:${q}` : null, () => rankedSearch(q, SEARCH_TABLES.map((t) => t.table)));
}

function useLean(q: string) {
  return useResource(q ? `search-lean:${q}` : null, () => leanNames().then((index) => (index ? searchLean(index, q) : null)));
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
  const ranked = useRanked(tooLong ? "" : q);
  const lean = useLean(tooLong ? "" : q);
  const leanHits = lean.status === "ready" ? lean.value : null;
  const ready = ranked.status === "ready" ? new Map<SearchType, SearchItem[]>(SEARCH_TABLES.map((t) => [t.type, ranked.value.get(t.table) ?? []])) : null;
  // Without a kind in the address, list the first kind that has matches.
  const type: SearchType | null = route.type ?? (ready ? (SEARCH_TABLES.find((t) => (ready.get(t.type)?.length ?? 0) > 0)?.type ?? null) : null);
  const listed = type && ready ? ready.get(type) ?? [] : [];
  const total = listed.length;
  const win = pageWindow(total, route.page ?? 1);
  const grand = ready ? [...ready.values()].reduce((s, list) => s + list.length, 0) : 0;

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
        <h1 ref={headingRef} tabIndex={-1}>
          {q ? (
            <>
              Results for <q>{q}</q>
            </>
          ) : (
            "Search records, passages and Lean"
          )}
        </h1>
        <SearchForm q={route.q} />
        {!q && <p className="search-page__help">{SEARCH_HELP}</p>}
      </header>

      {tooLong && (
        <p className="search-page__status" role="status">
          Search takes at most {MAX_TOKENS} words and {MAX_CHARS} characters. Remove some words.
        </p>
      )}
      {ranked.status === "error" && <ErrorNote error={ranked.error} />}
      {q && !tooLong && ranked.status === "loading" && (
        <p className="search-page__status" role="status">
          Searching…
        </p>
      )}

      {ready && (
        <div className="search-body">
          <div className="search-body__main">
          {grand === 0 && (
            <p className="search-page__status" role="status">
              No record, section heading or linked passage contains all of these words, as whole words or the starts of words.
              Other text in the papers is not searched. Try fewer words, or another spelling.
            </p>
          )}
          {grand > 0 && <nav className="search-kinds" aria-label="Kinds of result">
            <ul>
              {SEARCH_TABLES.map((t) => {
                const n = ready.get(t.type)?.length ?? 0;
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
          </nav>}

          {grand > 0 && type && (
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
              <ol className="search-results__list" start={win.from}>
                {listed.slice(win.from > 0 ? win.from - 1 : 0, win.to).map((item) => (
                  <li key={item.ref}>
                    <Result item={item} />
                  </li>
                ))}
              </ol>
              {win.pages > 1 && <Pager route={route} type={type} page={win.page} pages={win.pages} />}
              <p className="search-page__foot">
                Results come first when the words occur in a title, then when they occur close together and in the order typed.
                Other text in the papers is not searched.
              </p>
            </section>
          )}
          </div>
          <LeanResults hits={leanHits} loading={lean.status === "loading"} />
        </div>
      )}
    </div>
  );
}

function LeanResults({ hits, loading }: { hits: LeanHit[] | null; loading: boolean }) {
  const [all, setAll] = useState(false);
  useEffect(() => setAll(false), [hits]);
  const shown = hits ? (all ? hits : hits.slice(0, LEAN_SHOWN)) : [];
  return (
    <section className="search-lean" aria-labelledby="search-lean-title">
      <h2 id="search-lean-title" className="search-results__title">
        {hits ? `${hits.length} Lean ${hits.length === 1 ? "declaration" : "declarations"}` : "Lean declarations"}
      </h2>
      {loading && <p className="search-page__status">Searching the Lean names…</p>}
      {!loading && !hits && <p className="search-page__status">This edition has no Lean index.</p>}
      {hits && hits.length === 0 && <p className="search-page__status">No Lean declaration name contains these words.</p>}
      {shown.length > 0 && (
        <ol className="search-results__list">
          {shown.map((hit) => (
            <li key={`${hit.module}:${hit.name}`}>
              <a className="search-result" href={routeHref({ view: "lean", module: hit.module, decl: hit.name })}>
                <LeanResultBody hit={hit} />
              </a>
            </li>
          ))}
        </ol>
      )}
      {hits && hits.length > LEAN_SHOWN && (
        <button type="button" className="control search-lean__more" aria-expanded={all} onClick={() => setAll((a) => !a)}>
          {all ? `Show the first ${LEAN_SHOWN}` : `Show all ${hits.length}`}
        </button>
      )}
    </section>
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

// Where the reader is in the paper: the account, then its sections with the
// current one marked. Levels 2 and 3 are always listed; a level-4 subsection
// (long §8.1.1) appears inside the branch being read, so deep places stay
// reachable without listing every heading at once. Wide screens set it as a
// sticky column; narrower ones open the same list from a "Sections" control.
// Choosing another account is the top bar's job: it opens an account from
// its start, and "Same topic in…" goes from a passage to its treatments.

import { useEffect, useMemo, useRef, useState } from "react";
import { sectionLabel } from "../../map/TheoremPlate";
import type { PreparedDocument, TextBlock } from "../engine";
import type { TieCount } from "../ties";
import { chainOf, type OutlineEntry } from "./model";

interface Props {
  entries: OutlineEntry[];
  current: string | null;
  /** Statements with Lean per section. */
  counts?: Map<string, TieCount>;
  /** The paper, for search. */
  doc?: PreparedDocument;
  onJump(id: string): void;
  /** Go to a source line found by search. */
  onLine?(line: number): void;
}

const HITS = 24;

/** One hit's words around the match, the match marked. Adapted from Proof Reader's Contents. */
function Snippet({ text, at, length }: { text: string; at: number; length: number }) {
  const from = Math.max(0, text.lastIndexOf(" ", Math.max(0, at - 28)));
  const to = Math.min(text.length, at + length + 44);
  return (
    <>
      {from > 0 && "…"}
      {text.slice(from, at)}
      <mark>{text.slice(at, at + length)}</mark>
      {text.slice(at + length, to)}
      {to < text.length && "…"}
    </>
  );
}

/** Search within this paper, including what has not rendered yet. `/` stays the site's search. */
function PaperSearch({ doc, onLine, onQuery }: { doc: PreparedDocument; onLine(line: number): void; onQuery(active: boolean): void }) {
  const [query, setQuery] = useState("");
  const needle = query.trim().toLowerCase();
  useEffect(() => onQuery(!!needle), [needle, onQuery]);
  const found = useMemo(() => {
    if (needle.length < 2) return [];
    const hits: { block: TextBlock; at: number }[] = [];
    for (const block of doc.textBlocks()) {
      const at = block.text.toLowerCase().indexOf(needle);
      if (at >= 0) hits.push({ block, at });
      if (hits.length === HITS) break;
    }
    return hits;
  }, [doc, needle]);
  return (
    <div className="paper-search" role="search">
      <input
        type="search"
        value={query}
        placeholder="Search this paper"
        aria-label="Search this paper"
        onChange={(event) => setQuery(event.target.value)}
        onKeyDown={(event) => {
          if (event.key === "Enter" && found[0]) onLine(found[0].block.line);
          if (event.key === "Escape") {
            event.stopPropagation();
            setQuery("");
            event.currentTarget.blur();
          }
        }}
      />
      {needle.length >= 2 &&
        (found.length ? (
          <ul className="paper-search__found">
            {found.map(({ block, at }) => (
              <li key={`${block.line}:${at}`}>
                <button type="button" onClick={() => onLine(block.line)}>
                  <Snippet text={block.text} at={at} length={needle.length} />
                </button>
              </li>
            ))}
          </ul>
        ) : (
          <p className="paper-search__none">Nothing in this paper matches that.</p>
        ))}
    </div>
  );
}

export interface AccountHead {
  name: string;
  job: string;
  reader: string;
  status: string;
  /** The paper's PDF, opened in a new tab. */
  pdf?: { href: string; pages: number };
}

/** "Open PDF, 21 pages": the account's PDF, beside the words that say who it is for. */
export function PdfLink({ pdf }: { pdf: NonNullable<AccountHead["pdf"]> }) {
  return (
    <a className="pdf-link" href={pdf.href} target="_blank" rel="noopener">
      Open PDF, {pdf.pages} {pdf.pages === 1 ? "page" : "pages"}
    </a>
  );
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
        {head.pdf && (
          <p className="outline__pdf">
            <PdfLink pdf={head.pdf} />
          </p>
        )}
      </div>
      <Sections {...props} listRef={listRef} />
    </nav>
  );
}

export function Sections({ entries, current, counts, doc, onJump, onLine, listRef }: Props & { listRef?: React.RefObject<HTMLOListElement | null> }) {
  const open = useMemo(() => new Set(chainOf(entries, current).map((e) => e.id)), [entries, current]);
  const shown = entries.filter((e) => e.level < 4 || (e.parent && open.has(e.parent)));
  const [searching, setSearching] = useState(false);
  const any = !!counts && [...counts.values()].some((c) => c.lean);
  return (
    <>
    {doc && onLine && <PaperSearch doc={doc} onLine={onLine} onQuery={setSearching} />}
    <ol className="outline__list" ref={listRef} hidden={searching}>
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
            <span className="outline__title">{sectionLabel(entry.title)}</span>
            {!!counts?.get(entry.id)?.lean && (
              <span className="outline__ties num" title={`${counts.get(entry.id)!.lean} statements with Lean, of ${counts.get(entry.id)!.all} tied`}>
                {counts.get(entry.id)!.lean}
              </span>
            )}
          </a>
        </li>
      ))}
    </ol>
    {any && !searching && <p className="outline__key">Numbers count the statements with Lean in each section.</p>}
    </>
  );
}

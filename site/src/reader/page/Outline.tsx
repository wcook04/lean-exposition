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
import type { PhraseFamily, PhrasePart, PhraseTopic } from "../../api/lean";
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
  /** Phrase layer: the paper's topics and its parts, for the colour key. */
  topics?: PhraseTopic[];
  families?: PhraseFamily[];
  parts?: PhrasePart[];
}

/**
 * The colour key: each topic's colour beside its name, grouped under its family. Families the
 * authors named carry their name; families derived from how the topics co-occur are set apart
 * without one. A paper whose topics come in parts shows the topics of the part being read.
 */
/** Topic colours are on by default. Turning them off makes the phrase and margin marks neutral. */
export function TonesSwitch() {
  // Topic colours are always on; the switch is gone.
  return null;
}

/** The topics a reader last pointed at, focused or selected in the paper, most recent first:
 * the key lists them in that order, like the atlas's family list, so the one being read is on top. */
function useRecentTones(): string[] {
  const [recent, setRecent] = useState<string[]>([]);
  useEffect(() => {
    const bump = (tone?: string | null) => {
      if (!tone) return;
      setRecent((r) => (r[0] === tone ? r : [tone, ...r.filter((t) => t !== tone)]));
    };
    const fromEvent = (event: Event) => {
      const target = event.target as Element | null;
      const tie = target && typeof target.closest === "function" ? (target.closest(".paper .tie[data-tone]") as HTMLElement | null) : null;
      bump(tie?.dataset.tone);
    };
    const pinned = () => bump((document.querySelector(".paper .tie[data-pin][data-tone]") as HTMLElement | null)?.dataset.tone);
    document.addEventListener("pointerover", fromEvent, { passive: true });
    document.addEventListener("focusin", fromEvent);
    const watch = new MutationObserver(pinned);
    watch.observe(document.body, { subtree: true, attributes: true, attributeFilter: ["data-pin"] });
    pinned();
    return () => {
      document.removeEventListener("pointerover", fromEvent);
      document.removeEventListener("focusin", fromEvent);
      watch.disconnect();
    };
  }, []);
  return recent;
}

function PhraseKey({ topics, families, parts, part }: { topics: PhraseTopic[]; families: PhraseFamily[]; parts: PhrasePart[]; part: number }) {
  const shown = topics.filter((topic) => topic.part === part);
  if (!shown.length) return null;
  const several = parts.length > 1;
  const byId = new Map(shown.map((topic) => [topic.id, topic]));
  const recent = useRecentTones();
  const rank = (tone: number | string | undefined) => {
    const at = tone == null ? -1 : recent.indexOf(String(tone));
    return at < 0 ? Number.POSITIVE_INFINITY : at;
  };
  const familyRank = (family: PhraseFamily) => Math.min(...family.topics.map((id) => rank(byId.get(id)?.tone)));
  // Most recently read first; untouched families and topics keep the paper's order (sort is stable).
  const groups = families.filter((family) => family.part === part).sort((a, b) => familyRank(a) - familyRank(b));
  const current = recent[0];
  const item = (topic: PhraseTopic) => (
    <li
      key={topic.id}
      data-tone={topic.tone}
      data-current={current != null && String(topic.tone) === current ? "" : undefined}
      style={current != null && String(topic.tone) === current ? { outline: "1.5px solid var(--tone)", outlineOffset: "2px", borderRadius: "4px" } : undefined}
      title={topic.description || undefined}
    >
      <span className="phrase-key__swatch" aria-hidden="true" />
      {topic.name}
    </li>
  );
  return (
    <section className="phrase-key" aria-label="Topic colours">
      <p className="phrase-key__head">
        Topic colours{several && parts[part]?.name ? <span> · {parts[part].name}</span> : null}
      </p>
      {groups.length ? (
        <div className="phrase-key__families">
          {groups.map((family) => (
            <div key={family.id} className="phrase-key__family">
              {family.named && family.topics.length > 1 && <p className="phrase-key__family-name">{family.name}</p>}
              <ul>{[...family.topics].sort((a, b) => rank(byId.get(a)?.tone) - rank(byId.get(b)?.tone)).flatMap((id) => (byId.has(id) ? [item(byId.get(id)!)] : []))}</ul>
            </div>
          ))}
        </div>
      ) : (
        <ul>{[...shown].sort((a, b) => rank(a.tone) - rank(b.tone)).map(item)}</ul>
      )}
      <details className="phrase-key__about">
        <summary>What the colours mean</summary>
        <p className="phrase-key__note">
          Colours group topics within this paper; topics of one family share a hue. They do not say whether a statement is proved or whether it matches the paper. Topics and links are AI-drafted.
          {several ? " Each part of this paper has its own topics." : ""}
        </p>
      </details>
      <TonesSwitch />
    </section>
  );
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
  pdf?: { href: string; pages: number; label?: string };
  /** Shown after the credit: an adapted edition's link to the authors' paper. */
  after?: import("react").ReactNode;
  /** Shown after the PDF link: an adapted edition's further PDFs. */
  pdfAfter?: import("react").ReactNode;
}

/** "Open PDF, 21 pages": the account's PDF, beside the words that say who it is for. */
export function PdfLink({ pdf }: { pdf: NonNullable<AccountHead["pdf"]> }) {
  return (
    <a className="pdf-link" href={pdf.href} target="_blank" rel="noopener">
      {pdf.label ?? "Open PDF"}, {pdf.pages} {pdf.pages === 1 ? "page" : "pages"}
    </a>
  );
}

/**
 * The left column: the paper's contents and nothing else. Top to bottom: search, the sections with
 * their topic colours, then the colour key grouped by family. The whole column is sticky under the
 * top bar and scrolls on its own, so the contents and the key stay reachable whatever their length.
 * Who wrote the paper, and who made the links, is said once, under the paper's title.
 */
export function OutlineColumn(props: Props) {
  const navRef = useRef<HTMLElement>(null);
  // Keep the current entry in view inside the column, without moving the page.
  useEffect(() => {
    const nav = navRef.current;
    const item = nav?.querySelector<HTMLElement>('[aria-current="location"]');
    if (!nav || !item) return;
    const top = item.getBoundingClientRect().top - nav.getBoundingClientRect().top + nav.scrollTop;
    if (top < nav.scrollTop + 24 || top > nav.scrollTop + nav.clientHeight - 48) {
      nav.scrollTop = Math.max(0, top - nav.clientHeight / 3);
    }
  }, [props.current]);
  return (
    <nav className="outline" aria-label="Contents of this paper" ref={navRef}>
      <Sections {...props} />
    </nav>
  );
}


const DOUBLE: Record<string, string> = { R: "ℝ", T: "𝕋", Z: "ℤ", N: "ℕ", Q: "ℚ", C: "ℂ" };
const SUP: Record<string, string> = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "*": "*", "+": "⁺", "-": "⁻", n: "ⁿ" };
const SUB: Record<string, string> = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉" };
const SYMBOLS: Record<string, string> = { to: "→", in: "∈", le: "≤", leq: "≤", ge: "≥", geq: "≥", infty: "∞", times: "×", cdot: "·", nabla: "∇", partial: "∂", Delta: "Δ", Omega: "Ω", alpha: "α", beta: "β", gamma: "γ", lambda: "λ", mu: "μ", nu: "ν", omega: "ω", sigma: "σ", tau: "τ", varepsilon: "ε", epsilon: "ε" };
const script = (body: string, table: Record<string, string>) => ([...body].every((c) => table[c]) ? [...body].map((c) => table[c]).join("") : null);

/** A section's title as plain text for the contents: what a heading's formula says, without its TeX ("Blow-up on ℝ³"). */
export function plainTitle(title: string): string {
  return title
    .replace(/\\mathbb\s*\{?\s*([A-Z])\s*\}?/g, (_m, letter: string) => DOUBLE[letter] ?? letter)
    .replace(/\\(?:operatorname|mathrm|mathbf|mathcal|text|mathit)\s*\{([^{}]*)\}/g, "$1")
    .replace(/\^\{([^{}]*)\}|\^(\S)/g, (_m, braced: string | undefined, one: string | undefined) => script(braced ?? one ?? "", SUP) ?? `^${braced ?? one}`)
    .replace(/_\{([^{}]*)\}|_(\d)/g, (_m, braced: string | undefined, one: string | undefined) => script(braced ?? one ?? "", SUB) ?? `_${braced ?? one}`)
    .replace(/\\([A-Za-z]+)/g, (_m, name: string) => SYMBOLS[name] ?? name)
    .replace(/\\[,;!: ]/g, " ")
    .replace(/\s+/g, " ")
    .trim();
}

const Chevron = ({ open }: { open: boolean }) => (
  <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true" className={`outline__chev${open ? " is-open" : ""}`}>
    <path d="M3.5 2l3 3-3 3" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" strokeLinejoin="round" />
  </svg>
);

export function Sections({ entries, current, counts, doc, onJump, onLine, topics, families, parts }: Props) {
  // A section's subsections are folded, except along the way to the place being read; a reader's
  // own opening or closing of a section holds until they change it.
  const chain = useMemo(() => new Set(chainOf(entries, current).map((e) => e.id)), [entries, current]);
  const [chosen, setChosen] = useState<ReadonlyMap<string, boolean>>(() => new Map());
  const parents = useMemo(() => new Set(entries.flatMap((e) => (e.parent ? [e.parent] : []))), [entries]);
  const byEntry = useMemo(() => new Map(entries.map((e) => [e.id, e])), [entries]);
  const isOpen = (id: string) => chosen.get(id) ?? chain.has(id);
  const shown = entries.filter((e) => {
    for (let up = e.parent; up; up = byEntry.get(up)?.parent ?? null) if (!isOpen(up)) return false;
    return true;
  });
  const [searching, setSearching] = useState(false);
  const byId = useMemo(() => new Map((topics ?? []).map((topic) => [topic.id, topic])), [topics]);
  const part = (current ? counts?.get(current)?.part : undefined) ?? 0;
  return (
    <>
    {doc && onLine && <PaperSearch doc={doc} onLine={onLine} onQuery={setSearching} />}
    <ol className="outline__list" hidden={searching}>
      {shown.map((entry) => {
        const count = counts?.get(entry.id);
        const folds = parents.has(entry.id);
        const open = folds && isOpen(entry.id);
        return (
          <li key={entry.id} className={`outline__item outline__item--l${entry.level}${chain.has(entry.id) ? " outline__item--open" : ""}${folds ? " outline__item--folds" : ""}`}>
            {folds && (
              <button
                type="button"
                className="outline__fold"
                aria-expanded={open}
                aria-label={`${open ? "Fold" : "Unfold"} the subsections of ${sectionLabel(plainTitle(entry.title))}`}
                onClick={() => setChosen((was) => new Map(was).set(entry.id, !open))}
              >
                <Chevron open={open} />
              </button>
            )}
            <a
              href={`#${encodeURIComponent(entry.id)}`}
              aria-current={entry.id === current ? "location" : undefined}
              onClick={(event) => {
                if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
                event.preventDefault();
                onJump(entry.id);
              }}
            >
              <span className="outline__name">
                {sectionLabel(plainTitle(entry.title))}
                {!!count?.topics?.length && (
                  <span className="phrase-bars" title={`Topics here: ${count.topics.map((id) => byId.get(id)?.name ?? id).join(", ")}`}>
                    {count.topics.slice(0, 6).map((id) => (
                      <span key={id} data-tone={byId.get(id)?.tone ?? 0} />
                    ))}
                  </span>
                )}
              </span>
              {!!count?.lean && (
                <span className="outline__ties num" title={`${count.lean} statements with Lean, of ${count.all} tied`}>
                  {count.lean}
                </span>
              )}
            </a>
          </li>
        );
      })}
    </ol>
    {!!topics?.length && !searching && <PhraseKey topics={topics} families={families ?? []} parts={parts ?? []} part={part} />}
    </>
  );
}

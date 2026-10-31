// "Passages": one tab per account and, under the tabs, one line saying
// what that account records for this record (DESIGN.md § Wording). When the
// account links passages directly, a named passage selector and an excerpt of
// the passage in complete blocks, rendered exactly as the reader renders it.
// A pending or failed request is a state of its own, never an absence.

import { useLayoutEffect, useMemo, useRef, useState, type KeyboardEvent } from "react";
import type { AlignedPassage, Stage } from "../api/types";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { sectionLabel } from "../map/TheoremPlate";
import { partOfPassage, sectionTitleOf, useDocument } from "../reader/documents";
import { mountFigures } from "../reader/mount";
import { freshSlots, markWideMaths } from "../reader/page/PaperBody";
import { withoutIds } from "../reader/page/model";
import { get } from "../api/client";
import { useEdition, useResource } from "../app/data";
import { chooseAccount, useChosenAccount } from "./accountStore";
import {
  accountName,
  accountState,
  accountStateLine,
  defaultAccount,
  excerptLength,
  treatmentWords,
  webUrl,
  type AccountState,
  type ExcerptBlock,
} from "./model";

/** A passage outside any numbered section, named from its anchor: "abstract" -> "Abstract". */
function anchorName(anchor: string): string {
  const words = anchor.replace(/-/g, " ");
  return words.charAt(0).toUpperCase() + words.slice(1);
}

export type RequestStatus = "loading" | "error" | "ready";

interface Props {
  nodeId: string;
  grouped: Map<Stage, AlignedPassage[]> | null;
  memberships: Partial<Record<Stage, string[]>>;
  /** The state of the request behind `grouped`; defaults to ready when it is given. */
  status?: RequestStatus;
  /** Ask again for the passages, keeping the selection. */
  onRetry?(): void;
  /** Kept for existing callers; absence wording no longer depends on it. */
  unused?: Partial<Record<Stage, boolean>>;
  href(stage: Stage, anchor: string): string;
  /** A short label before the count for the chosen account (the step view's "Both records linked"). */
  label?(stage: Stage): string | null;
  /** A line shown under the state line, optionally specific to the chosen account. */
  note?: string | ((stage: Stage) => string | undefined);
  /** Replaces the default wording for an account with no passage. */
  empty?(stage: Stage): string;
}

export function Accounts({ nodeId, grouped, memberships, status, onRetry, href, label, note, empty }: Props) {
  const chosen = useChosenAccount();
  const request: RequestStatus = status ?? (grouped ? "ready" : "loading");
  const counts = useMemo(() => {
    const out: Partial<Record<Stage, number>> = {};
    if (grouped && request === "ready") for (const s of STAGE_ORDER) out[s] = grouped.get(s)?.length ?? 0;
    return out;
  }, [grouped, request]);
  const stage = defaultAccount(counts, chosen);

  const tabRefs = useRef<Partial<Record<Stage, HTMLButtonElement | null>>>({});
  const onKey = (event: KeyboardEvent<HTMLDivElement>) => {
    const i = STAGE_ORDER.indexOf(stage);
    let next: number | null = null;
    if (event.key === "ArrowRight") next = (i + 1) % STAGE_ORDER.length;
    else if (event.key === "ArrowLeft") next = (i - 1 + STAGE_ORDER.length) % STAGE_ORDER.length;
    else if (event.key === "Home") next = 0;
    else if (event.key === "End") next = STAGE_ORDER.length - 1;
    if (next === null) return;
    event.preventDefault();
    const s = STAGE_ORDER[next];
    chooseAccount(s);
    tabRefs.current[s]?.focus();
  };

  const passages = request === "ready" ? (grouped?.get(stage) ?? []) : [];
  const state = accountState(request, passages.length, memberships[stage]);
  const selectedNote = typeof note === "function" ? note(stage) : note;
  const base = `acct-${nodeId.replace(/[^\w-]/g, "_")}`;

  return (
    <div className="acct">
      <div className="acct__tabs" role="tablist" aria-label="Accounts" onKeyDown={onKey}>
        {STAGE_ORDER.map((s) => {
          const n = counts[s];
          return (
            <button
              key={s}
              ref={(el) => {
                tabRefs.current[s] = el;
              }}
              type="button"
              role="tab"
              id={`${base}-tab-${s}`}
              aria-controls={`${base}-panel`}
              aria-selected={s === stage}
              tabIndex={s === stage ? 0 : -1}
              className="acct__tab"
              onClick={() => chooseAccount(s)}
            >
              {PAPER_NAMES[s].short}
              {n !== undefined && (
                <b className="num" aria-label={`, ${n} ${n === 1 ? "passage" : "passages"} linked directly`}>
                  {n}
                </b>
              )}
            </button>
          );
        })}
      </div>
      <div id={`${base}-panel`} role="tabpanel" aria-labelledby={`${base}-tab-${stage}`} className="acct__panel">
        {state.kind === "direct" ? (
          <Direct
            key={stage}
            stage={stage}
            nodeId={nodeId}
            passages={passages}
            href={href}
            lead={label?.(stage) ?? null}
            note={selectedNote}
          />
        ) : (
          <div className="acct__swap" key={`${stage}:${state.kind}`}>
            {empty && state.kind !== "loading" && state.kind !== "error" ? (
              <StateLine state={state} text={empty(stage)} />
            ) : (
              <StateLine state={state} />
            )}
            {state.kind === "error" && onRetry && (
              <button type="button" className="control acct__retry" onClick={onRetry}>
                Retry
              </button>
            )}
            {!empty && state.kind === "used" && <UsedBy stage={stage} nodeId={nodeId} href={href} />}
            {!empty && state.kind === "outside" && <SourceDestination nodeId={nodeId} />}
          </div>
        )}
      </div>
    </div>
  );
}

const MARK: Record<AccountState["kind"], string | null> = { direct: "own", used: "relied", outside: "outside", loading: null, error: null };

function StateLine({ state, text, children }: { state: AccountState; text?: string; children?: React.ReactNode }) {
  const mark = MARK[state.kind];
  return (
    <p className={`acct__state acct__state--${state.kind}`} role={state.kind === "error" ? "alert" : undefined}>
      {mark && <span className={`cov-mark cov-mark--${mark}`} aria-hidden="true" />}
      <span>
        {text ?? accountStateLine(state)}
        {children}
      </span>
    </p>
  );
}

// ------------------------------------------------------------ direct links

interface Named {
  passage: AlignedPassage;
  name: string;
  does: string[];
}

function Direct({
  stage,
  nodeId,
  passages,
  href,
  lead,
  note,
}: {
  stage: Stage;
  nodeId: string;
  passages: AlignedPassage[];
  href(stage: Stage, anchor: string): string;
  lead: string | null;
  note?: string;
}) {
  const loaded = useDocument(stage);
  const [anchor, setAnchor] = useState(passages[0].anchor);
  const current = passages.find((p) => p.anchor === anchor) ?? passages[0];

  const named: Named[] = useMemo(
    () =>
      passages.map((passage) => {
        if (loaded.status !== "ready") return { passage, name: anchorName(passage.anchor), does: [] };
        const { paper } = loaded.value;
        const section = sectionTitleOf(paper, passage.anchor);
        const structure = paper.structure.paper.passages.find((q) => q.anchor === passage.anchor);
        return {
          passage,
          name: section ? sectionLabel(section) : anchorName(passage.anchor),
          does: treatmentWords(structure?.treatments, nodeId, passage.mapping_field),
        };
      }),
    [passages, loaded, nodeId],
  );
  const chosen = named.find((n) => n.passage.anchor === current.anchor)!;
  const optionText = (n: Named) => (n.does.length ? `${n.name} (${n.does.join(", ")})` : n.name);
  const selectId = `acct-pick-${stage}-${nodeId.replace(/[^\w-]/g, "_")}`;

  return (
    <div className="acct__direct">
      <StateLine state={{ kind: "direct", count: passages.length }} text={`${lead ? `${lead}. ` : ""}${accountStateLine({ kind: "direct", count: passages.length })}`}>
        {passages.length === 1 && (
          <>
            {", "}
            <span className="acct__name">{chosen.name}</span>
            {chosen.does.length > 0 && <span className="acct__does"> ({chosen.does.join(", ")})</span>}
          </>
        )}
      </StateLine>
      {passages.length > 1 && (
        <p className="acct__pick">
          <label htmlFor={selectId} className="visually-hidden">
            Linked passage
          </label>
          <select id={selectId} value={current.anchor} onChange={(e) => setAnchor(e.target.value)}>
            {named.map((n) => (
              <option key={n.passage.anchor} value={n.passage.anchor}>
                {optionText(n)}
              </option>
            ))}
          </select>
        </p>
      )}
      {note && <p className="acct__note">{note}</p>}
      <Excerpt key={current.anchor} stage={stage} passage={current} href={href(stage, current.anchor)} loaded={loaded} section={chosen.name} />
    </div>
  );
}

/** The role of one rendered block of a passage, for choosing a complete preview. */
function blockOf(el: HTMLElement): ExcerptBlock {
  const tag = el.tagName;
  const text = (el.textContent ?? "").replace(/\s+/g, " ").trim();
  let role = "other";
  if (/^H[1-6]$/.test(tag)) role = "heading";
  else if (tag === "UL" || tag === "OL") role = "list";
  else if (tag === "FIGURE" || el.querySelector("figure, [data-figure]")) role = "figure";
  else if (el.matches(".math-display, .katex-display") || (el.querySelector(".katex-display, .math-display") && text.length < 400 && el.children.length === 1))
    role = "math";
  else if (tag === "P") role = "p";
  return {
    role,
    height: el.offsetHeight,
    leads: role === "p" && /:$/.test(text),
    continues: role === "p" && /^[a-z(]/.test(text),
  };
}

function Excerpt({
  stage,
  passage,
  href,
  loaded,
  section,
}: {
  stage: Stage;
  passage: AlignedPassage;
  href: string;
  loaded: ReturnType<typeof useDocument>;
  section: string;
}) {
  const textRef = useRef<HTMLDivElement>(null);
  const [open, setOpen] = useState(false);
  const [more, setMore] = useState(false);

  const html = useMemo(() => {
    if (loaded.status !== "ready") return null;
    const index = partOfPassage(loaded.value.doc, passage.anchor);
    return index >= 0 ? withoutIds(loaded.value.doc.render(index).html) : null;
  }, [loaded, passage.anchor]);

  // Figures and wide formulas are mounted once per rendering.
  useLayoutEffect(() => {
    const el = textRef.current;
    if (!el || !html) return;
    const unmount = mountFigures(freshSlots(el));
    const unmark = markWideMaths(el);
    return () => {
      unmount();
      unmark();
    };
  }, [html]);

  // Preview whole blocks; the rest is hidden (and so not focusable) until opened.
  useLayoutEffect(() => {
    const el = textRef.current;
    if (!el || !html) return;
    const norm = (t: string | null | undefined) => (t ?? "").replace(/\s+/g, " ").trim();
    const blocks = Array.from(el.children).filter((c): c is HTMLElement => c instanceof HTMLElement && !c.matches("a.anchor"));
    blocks.forEach((b) => (b.hidden = false));
    // The passage often opens with the heading already named above it.
    const first = blocks[0];
    const bare = section.replace(/^§[\d.]+\s+/, "");
    const shown = first && /^H[1-6]$/.test(first.tagName) && norm(first.textContent).endsWith(norm(bare)) ? blocks.slice(1) : blocks;
    if (shown !== blocks) first.hidden = true;
    if (open) {
      setMore(true);
      return;
    }
    const n = excerptLength(shown.map(blockOf), 300);
    shown.slice(n).forEach((b) => (b.hidden = true));
    setMore(n < shown.length);
  }, [html, open, section]);

  const where = accountName(stage);
  return (
    <article className="acct__passage" aria-label={`${section}, ${PAPER_NAMES[stage].short}`}>
      {loaded.status === "loading" && <p className="acct__state faint">Loading the passage…</p>}
      {loaded.status === "error" && <p className="acct__state">This passage could not be loaded.</p>}
      {html !== null && <div ref={textRef} className="acct__text prose" dangerouslySetInnerHTML={{ __html: html }} />}
      <p className="acct__actions">
        {more && (
          <button type="button" className="control acct__more" aria-expanded={open} onClick={() => setOpen((o) => !o)}>
            {open ? "Show less" : "Show the full passage"}
          </button>
        )}
        <a className="acct__open" href={href}>
          Read it in {where} <span aria-hidden="true">→</span>
        </a>
      </p>
    </article>
  );
}

// ------------------------------------------------------- used, no passage

interface QueryMatch {
  anchor: string;
  witnesses?: { root_node_id?: string }[];
}

/** Passages for results whose recorded argument uses this record. */
function UsedBy({ stage, nodeId, href }: { stage: Stage; nodeId: string; href(stage: Stage, anchor: string): string }) {
  const { graph } = useEdition();
  const [attempt, setAttempt] = useState(0);
  const where = useResource<QueryMatch[]>(`panel:used-where:${stage}:${nodeId}${attempt ? `#${attempt}` : ""}`, () =>
    get<{ papers: { stage: Stage; matches: QueryMatch[] }[] }>("/papers/query", {
      node: nodeId,
      relation: "prerequisites",
      representation: "matches",
      paper: stage,
    }).then((r) => r.data.papers.find((p) => p.stage === stage)?.matches ?? []),
  );
  const doc = useDocument(stage);
  const items = useMemo(() => {
    if (where.status !== "ready") return [];
    const seen = new Set<string>();
    return where.value
      .filter((m) => !seen.has(m.anchor) && seen.add(m.anchor))
      .map((m) => {
        const root = m.witnesses?.[0]?.root_node_id;
        const section = doc.status === "ready" ? sectionTitleOf(doc.value.paper, m.anchor) : null;
        return { anchor: m.anchor, section, root: root && root !== nodeId ? graph.nodes.get(root) : undefined };
      });
  }, [where, doc, graph, nodeId]);
  if (where.status === "loading") return <p className="acct__state faint">Loading passages…</p>;
  if (where.status === "error")
    return (
      <p className="acct__state" role="alert">
        These passages could not be loaded.{" "}
        <button type="button" className="linklike" onClick={() => setAttempt((n) => n + 1)}>
          Retry
        </button>
      </p>
    );
  if (items.length === 0) return <p className="acct__state faint">No passage is recorded for a result that uses this step.</p>;
  return (
    <ul className="acct__used">
      {items.map((m) => (
        <li key={m.anchor}>
          <a href={href(stage, m.anchor)}>{m.section ? sectionLabel(m.section) : m.anchor.replace(/-/g, " ")}</a>
          {m.root && <span className="acct__used-as"> in the argument for {m.root.label}</span>}
        </li>
      ))}
    </ul>
  );
}

/** Outside the account's selection: the record's own source is the destination. */
function SourceDestination({ nodeId }: { nodeId: string }) {
  const { graph } = useEdition();
  const origin = graph.nodes.get(nodeId)!.origin;
  if (origin.family === "none") return null;
  const url = webUrl(origin.url);
  const name = `${origin.label}${origin.place && origin.family !== "lean" ? `, ${origin.place}` : ""}`;
  return (
    <p className="acct__source">
      {url ? (
        <a href={url} data-external rel="noopener" target="_blank">
          {name} <span aria-hidden="true">↗</span>
        </a>
      ) : (
        <span>{name}</span>
      )}
      {origin.locator && <span className="acct__locator">{origin.locator}</span>}
    </p>
  );
}

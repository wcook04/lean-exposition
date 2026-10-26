// "How each account says it": one tab per account, and in each the account's
// own passages for the record, rendered exactly as the reader renders them.

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
import { accountName, defaultAccount, relationLine, treatmentWords, webUrl } from "./model";

interface Props {
  nodeId: string;
  grouped: Map<Stage, AlignedPassage[]> | null;
  memberships: Partial<Record<Stage, string[]>>;
  /** Accounts none of whose selected results rest on this record. */
  unused?: Partial<Record<Stage, boolean>>;
  href(stage: Stage, anchor: string): string;
  /** A line shown above the passages of every account (the step view's fallback note). */
  note?: string;
  /** Replaces the default wording for an account with no passage. */
  empty?(stage: Stage): string;
}

export function Accounts({ nodeId, grouped, memberships, unused, href, note, empty }: Props) {
  const chosen = useChosenAccount();
  const counts = useMemo(() => {
    const out: Partial<Record<Stage, number>> = {};
    if (grouped) for (const s of STAGE_ORDER) out[s] = grouped.get(s)?.length ?? 0;
    return out;
  }, [grouped]);
  const stage = defaultAccount(counts, chosen);

  // Direction of travel between accounts, in account order.
  const previous = useRef(stage);
  const direction = useRef(0);
  if (previous.current !== stage) {
    direction.current = STAGE_ORDER.indexOf(stage) > STAGE_ORDER.indexOf(previous.current) ? 1 : -1;
    previous.current = stage;
  }

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

  const passages = grouped?.get(stage) ?? [];
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
              <span className="acct__tab-name">{PAPER_NAMES[s].short}</span>
              <span className={`acct__count num${n ? "" : " acct__count--none"}`} aria-label={n === undefined ? undefined : `${n} ${n === 1 ? "passage" : "passages"}`}>
                {n === undefined ? "·" : n}
              </span>
            </button>
          );
        })}
      </div>
      <div
        key={stage}
        id={`${base}-panel`}
        role="tabpanel"
        aria-labelledby={`${base}-tab-${stage}`}
        className="acct__panel"
        data-dir={direction.current}
        tabIndex={-1}
      >
        {!grouped && <p className="acct__none faint">Finding passages…</p>}
        {note && grouped && <p className="acct__note">{note}</p>}
        {grouped && passages.length === 0 &&
          (empty ? (
            <p className="acct__none">{empty(stage)}</p>
          ) : (
            <Absent stage={stage} nodeId={nodeId} roles={memberships[stage]} unused={!!unused?.[stage]} href={href} />
          ))}
        {passages.map((p) => (
          <PassageView key={p.anchor} stage={stage} passage={p} nodeId={nodeId} href={href(stage, p.anchor)} />
        ))}
      </div>
    </div>
  );
}

interface QueryMatch {
  anchor: string;
  witnesses?: { root_node_id?: string }[];
}

/** No passage of its own: say how the account relates, and lead to where it is used. */
function Absent({
  stage,
  nodeId,
  roles,
  unused,
  href,
}: {
  stage: Stage;
  nodeId: string;
  roles?: string[];
  unused: boolean;
  href(stage: Stage, anchor: string): string;
}) {
  const { graph } = useEdition();
  const node = graph.nodes.get(nodeId)!;
  const inArgument = !!roles && roles.length > 0;
  const where = useResource<QueryMatch[]>(inArgument ? `panel:used-where:${stage}:${nodeId}` : null, () =>
    get<{ papers: { stage: Stage; matches: QueryMatch[] }[] }>("/papers/query", {
      node: nodeId,
      relation: "prerequisites",
      representation: "matches",
      paper: stage,
    }).then((r) => r.data.papers.find((p) => p.stage === stage)?.matches ?? []),
  );
  const doc = useDocument(inArgument ? stage : null);
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
  const roots = new Set(items.map((m) => m.root?.id));
  const oneRoot = items.length > 1 && roots.size === 1 ? items[0].root : undefined;
  const origin = node.origin;
  const url = webUrl(origin.url);
  return (
    <div className="acct__absent">
      <p className="acct__none">{relationLine(stage, roles, unused)}</p>
      {inArgument && where.status === "loading" && <p className="acct__none faint">Finding where it is used…</p>}
      {inArgument && items.length > 0 && (
        <>
          <p className="acct__used-title">
            Discussed where it is used{oneRoot ? `, as part of ${oneRoot.label}` : ""}
          </p>
          <ul className="acct__used">
            {items.map((m) => (
              <li key={m.anchor}>
                <a href={href(stage, m.anchor)}>{m.section ? sectionLabel(m.section) : m.anchor.replace(/-/g, " ")}</a>
                {!oneRoot && m.root && <span className="acct__used-as"> as part of {m.root.label}</span>}
              </li>
            ))}
          </ul>
        </>
      )}
      {!inArgument && origin.family !== "none" && (
        <p className="acct__source">
          <span className="swatch" data-slot={origin.slot} aria-hidden="true" />
          {url ? (
            <a href={url} data-external rel="noopener" target="_blank">
              {origin.label}
              {origin.place ? ` · ${origin.place}` : ""}
            </a>
          ) : (
            <span>
              {origin.label}
              {origin.place ? ` · ${origin.place}` : ""}
            </span>
          )}
          {origin.locator && <span className="acct__locator">{origin.locator}</span>}
        </p>
      )}
    </div>
  );
}

function PassageView({ stage, passage, nodeId, href }: { stage: Stage; passage: AlignedPassage; nodeId: string; href: string }) {
  const loaded = useDocument(stage);
  const textRef = useRef<HTMLDivElement>(null);
  const [open, setOpen] = useState(false);
  const [clamped, setClamped] = useState(false);

  const view = useMemo(() => {
    if (loaded.status !== "ready") return null;
    const { doc, paper } = loaded.value;
    const index = partOfPassage(doc, passage.anchor);
    const section = sectionTitleOf(paper, passage.anchor);
    const structure = paper.structure.paper.passages.find((q) => q.anchor === passage.anchor);
    const does = treatmentWords(structure?.treatments, nodeId, passage.mapping_field);
    return { html: index >= 0 ? withoutIds(doc.render(index).html) : null, section, does };
  }, [loaded, passage.anchor, passage.mapping_field, nodeId]);

  useLayoutEffect(() => {
    const el = textRef.current;
    if (!el || !view?.html) return;
    // The passage often opens with the heading already named above it.
    const first = Array.from(el.children).find((c) => !c.matches("a.anchor"));
    const norm = (t: string | null | undefined) => (t ?? "").replace(/\s+/g, " ").trim();
    if (first && /^H[1-6]$/.test(first.tagName) && view.section && norm(first.textContent) === norm(view.section)) {
      first.classList.add("acct__dup-heading");
    }
    const unmount = mountFigures(freshSlots(el));
    const unmark = markWideMaths(el);
    const measure = () => setClamped(el.scrollHeight > el.clientHeight + 4);
    measure();
    const observer = typeof ResizeObserver === "function" ? new ResizeObserver(measure) : null;
    observer?.observe(el);
    return () => {
      observer?.disconnect();
      unmount();
      unmark();
    };
  }, [view]);

  const title = view?.section ? sectionLabel(view.section) : passage.anchor.replace(/-/g, " ");
  return (
    <article className="acct__passage">
      <header className="acct__head">
        <h4 className="acct__section">{title}</h4>
        {view && view.does.length > 0 && <p className="acct__does">{view.does.join(", ")}</p>}
      </header>
      {loaded.status === "loading" && <p className="acct__none faint">Opening {accountName(stage)}…</p>}
      {loaded.status === "error" && <p className="acct__none">This passage could not be opened.</p>}
      {view && view.html !== null && (
        <div
          ref={textRef}
          className={`acct__text prose${open ? " is-open" : ""}${clamped && !open ? " is-clamped" : ""}`}
          dangerouslySetInnerHTML={{ __html: view.html }}
        />
      )}
      <p className="acct__actions">
        {(clamped || open) && (
          <button type="button" className="linklike acct__more" aria-expanded={open} onClick={() => setOpen((o) => !o)}>
            {open ? "Show less" : "Show all"}
          </button>
        )}
        <a className="acct__open" href={href}>
          Open in {accountName(stage)} <span aria-hidden="true">→</span>
        </a>
      </p>
    </article>
  );
}

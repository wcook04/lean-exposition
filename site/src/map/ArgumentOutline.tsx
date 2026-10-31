// The argument as a list: the same records and typed relations the map draws
// for a goal, read with ordinary scrolling. It is the default on phones and a
// choice on desktop. It uses the tree's own projection (usesOf, with the same
// account scope), so a row is the same record, joined by the same relation, as
// the card on the map.
//
// It reads like a table of contents: a row is a record's name, the whole row opens
// the record and unfolds what it uses, and the chevron beside it only unfolds.
//
// The argument is not a tree. A record used by several others appears once per
// use; its inputs are listed under one of them only (its "home", the first
// consumer met walking down from the top), and every other occurrence says who
// else uses it instead of repeating the subtree.

import { useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { ArgEdge, ArgGraph } from "../model/graph";
import { pathFromGoal, reach, usesOf } from "./treeModel";
import { recordMark } from "./leanMarks";
import { recordLine } from "../compare/useAlignment";
import { LeanGlyph } from "./LeanGlyph";
import { markWords } from "../model/leanStatus";
import "./outline.css";

type Within = ReadonlySet<string> | undefined;

/** Indented levels before the outline refocuses on a branch instead of indenting further. */
export const MAX_DEPTH = 3;

const KIND_ORDER: Record<string, number> = { supports: 0, assumes: 1, formalizes: 2 };

export const RELATION_WORDS: Record<string, string> = {
  supports: "Recorded support",
  assumes: "Explicit assumption",
  formalizes: "Recorded Lean correspondence",
};

export function kindWord(kind: string): string {
  switch (kind) {
    case "goal":
      return "Main result";
    case "declaration":
      return "Lean declaration";
    case "assumption":
      return "Assumption";
    default:
      return "Claim";
  }
}

/** The relations under one record, in the tree's projection: supports, then assumptions, then Lean. */
export function outlineChildren(graph: ArgGraph, id: string, within?: Within): ArgEdge[] {
  return usesOf(graph, id, within)
    .map((e, i) => ({ e, i }))
    .sort((a, b) => (KIND_ORDER[a.e.kind] ?? 9) - (KIND_ORDER[b.e.kind] ?? 9) || a.i - b.i)
    .map(({ e }) => e);
}

/** For every record below `top`, the consumer whose occurrence lists its inputs (breadth first, in outline order). */
export function homeParents(graph: ArgGraph, top: string, within?: Within): Map<string, string> {
  const home = new Map<string, string>();
  const seen = new Set([top]);
  const queue = [top];
  while (queue.length) {
    const id = queue.shift()!;
    for (const e of outlineChildren(graph, id, within)) {
      if (seen.has(e.to)) continue;
      seen.add(e.to);
      home.set(e.to, id);
      queue.push(e.to);
    }
  }
  return home;
}

/** Every recorded consumer of `id` inside the argument shown, other than `except`. */
export function otherConsumers(graph: ArgGraph, id: string, inArgument: ReadonlySet<string>, except: string): string[] {
  return [...new Set((graph.in.get(id) ?? []).filter((e) => RELATION_WORDS[e.kind] && inArgument.has(e.from) && e.from !== except).map((e) => e.from))];
}

const occKey = (path: string[]) => path.join("/");

interface Props {
  graph: ArgGraph;
  goal: string;
  goalTitle: string;
  /** One short line under the title: the account scope and the argument's size. */
  scope: string;
  within?: Within;
  selected?: string;
  selectedEdge?: string;
  /** The exact theorem, behind a disclosure. */
  statement?: ReactNode;
  onSelect(id: string): void;
  /** How much of the list's bottom a phone sheet covers. */
  bottomInset?: number;
}

export function ArgumentOutline({ graph, goal, goalTitle, scope, within, selected, selectedEdge, statement, onSelect, bottomInset = 0 }: Props) {
  // The route from the goal down to the record whose inputs are listed (the goal itself at first).
  const [trail, setTrail] = useState<string[]>([goal]);
  const [open, setOpen] = useState<Set<string>>(() => new Set());
  const [focusOcc, setFocusOcc] = useState<string | null>(null);
  const rootRef = useRef<HTMLDivElement>(null);
  const listHeadRef = useRef<HTMLHeadingElement>(null);

  // A new goal or account starts the outline afresh.
  const [lastScope, setLastScope] = useState({ goal, within });
  if (lastScope.goal !== goal || lastScope.within !== within) {
    setLastScope({ goal, within });
    setTrail([goal]);
    setOpen(new Set());
  }

  const top = trail[trail.length - 1];
  const topNode = graph.nodes.get(top)!;
  const goalNode = graph.nodes.get(goal)!;
  const home = useMemo(() => homeParents(graph, top, within), [graph, top, within]);
  const argument = useMemo(() => reach(graph, goal, within), [graph, goal, within]);
  const inputs = useMemo(() => outlineChildren(graph, top, within), [graph, top, within]);

  /** Open the rows on the way to `id`'s home occurrence, refocusing on a deeper branch when needed. */
  const reveal = (id: string) => {
    let path = pathFromGoal(graph, top, id, within);
    let base = trail;
    if (!path) {
      path = pathFromGoal(graph, goal, id, within);
      base = [goal];
      if (!path) return;
    }
    // path: top … id. Its rows sit at depths 1 … path.length - 1.
    if (path.length - 1 > MAX_DEPTH) {
      const cut = path.length - 2; // the home parent becomes the new top
      base = [...base, ...path.slice(1, cut + 1)];
      path = path.slice(cut);
    }
    setTrail(base);
    setOpen((prev) => {
      const next = base === trail ? new Set(prev) : new Set<string>();
      for (let i = 2; i < path!.length; i++) next.add(occKey(path!.slice(0, i)));
      return next;
    });
    setFocusOcc(occKey(path));
  };

  // A record selected elsewhere (the map, the inspector, search) is brought into the list.
  useEffect(() => {
    if (!selected || !argument.has(selected) || selected === top) return;
    const row = rootRef.current?.querySelector<HTMLElement>(`[data-outline-id="${CSS.escape(selected)}"]`);
    if (row) row.scrollIntoView({ block: "nearest" });
    else reveal(selected);
    // Only a change of selection should move the list.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [selected]);

  // When the phone's sheet settles over the list, keep the selected row above it.
  useEffect(() => {
    if (!selected || !bottomInset) return;
    rootRef.current?.querySelector<HTMLElement>(`[data-outline-id="${CSS.escape(selected)}"]`)?.scrollIntoView({ block: "nearest" });
  }, [bottomInset, selected]);

  useEffect(() => {
    if (!focusOcc) return;
    const row = rootRef.current?.querySelector<HTMLElement>(`[data-occ="${CSS.escape(focusOcc)}"]`);
    if (row) {
      row.scrollIntoView({ block: "nearest" });
      row.querySelector<HTMLElement>(".orow__open")?.focus({ preventScroll: true });
    }
    setFocusOcc(null);
  }, [focusOcc, open, trail]);

  const toggle = (key: string) =>
    setOpen((prev) => {
      const next = new Set(prev);
      if (next.has(key)) next.delete(key);
      else next.add(key);
      return next;
    });

  const focusBranch = (path: string[]) => {
    // path: top … id; the branch at id becomes the new top.
    setTrail([...trail, ...path.slice(1)]);
    setOpen(new Set());
    requestAnimationFrame(() => listHeadRef.current?.focus());
  };

  const renderRows = (parent: string, path: string[], depth: number): ReactNode => (
    <ul className="outline__list" role="list">
      {outlineChildren(graph, parent, within).map((edge) => {
        const node = graph.nodes.get(edge.to);
        if (!node) return null;
        const rowPath = [...path, edge.to];
        const key = occKey(rowPath);
        const isHome = home.get(edge.to) === parent;
        const n = outlineChildren(graph, edge.to, within).length;
        const expanded = open.has(key);
        const canOpen = isHome && n > 0;
        const inline = canOpen && depth < MAX_DEPTH;
        const mark = recordMark(edge.to, node);
        return (
          <li key={key} className="orow" data-occ={key} data-outline-id={edge.to} data-depth={depth}>
            <div className={`orow__body${selected === edge.to || selectedEdge === edge.key ? " is-selected" : ""}`}>
              {canOpen && (
                <button
                  type="button"
                  className="orow__inputs"
                  aria-expanded={inline ? expanded : false}
                  aria-label={`${expanded ? "Hide" : "Show"} the ${n === 1 ? "record" : `${n} records`} that ${node.label} uses directly`}
                  onClick={() => (inline ? toggle(key) : focusBranch(rowPath))}
                >
                  <Chevron open={expanded} />
                </button>
              )}
              <button
                type="button"
                className="orow__open"
                aria-pressed={selected === edge.to}
                aria-label={`${node.label}. ${RELATION_WORDS[edge.kind] ?? edge.kind}, ${kindWord(node.kind).toLowerCase()}. ${markWords(mark)}. Open the record`}
                onClick={() => {
                  if (inline && (!expanded || selected === edge.to)) toggle(key);
                  onSelect(edge.to);
                }}
              >
                <span className={`orow__title${node.kind === "declaration" && !recordLine(edge.to)?.short ? " lean" : ""}`}>{node.kind === "declaration" ? recordLine(edge.to)?.short || node.label : node.label}</span>
                {node.kind !== "claim" && <span className="orow__kind caps">{kindWord(node.kind)}</span>}
                <span className="orow__lean">
                  <LeanGlyph mark={mark} label="" />
                  {markWords(mark)}
                </span>
              </button>
              {!isHome && <AlsoUsed graph={graph} id={edge.to} home={home.get(edge.to)} others={otherConsumers(graph, edge.to, argument, parent)} onReveal={() => reveal(edge.to)} />}
            </div>
            {inline && expanded && renderRows(edge.to, rowPath, depth + 1)}
          </li>
        );
      })}
    </ul>
  );

  return (
    <div className="outline" ref={rootRef}>
      <header className="outline__goal">
        <p className="caps">{kindWord(goalNode.kind)}</p>
        <h2 className="outline__title">
          <button type="button" className="outline__open-goal" aria-pressed={selected === goal} aria-label={`${goalNode.label}. Open the record`} onClick={() => onSelect(goal)}>
            {goalNode.label}
          </button>
        </h2>
        <p className="outline__scope">{scope}</p>
        {statement && (
          <details className="outline__statement">
            <summary>Statement of the result</summary>
            <div className="outline__statement-body">{statement}</div>
          </details>
        )}
      </header>

      {trail.length > 1 && (
        <nav className="outline__route" aria-label={`One recorded route from ${goalTitle}`}>
          <p className="outline__route-title">One recorded route from {goalTitle}</p>
          <ol>
            {trail.map((id, i) =>
              i === trail.length - 1 ? (
                <li key={id} aria-current="location">
                  {graph.nodes.get(id)?.label}
                </li>
              ) : (
                <li key={id}>
                  <button
                    type="button"
                    className="linklike"
                    onClick={() => {
                      setTrail(trail.slice(0, i + 1));
                      setOpen(new Set());
                    }}
                  >
                    {i === 0 ? goalTitle : graph.nodes.get(id)?.label}
                  </button>
                </li>
              ),
            )}
          </ol>
        </nav>
      )}

      <section className="outline__inputs" aria-labelledby="outline-inputs-head">
        <h3 id="outline-inputs-head" className="outline__inputs-head" ref={listHeadRef} tabIndex={-1}>
          {trail.length > 1 ? (
            <>
              Records used directly by{" "}
              <button type="button" className="linklike outline__inputs-of" onClick={() => onSelect(top)} aria-label={`Open the record ${topNode.label}`}>
                {topNode.label}
              </button>
            </>
          ) : (
            "Records used directly"
          )}
        </h3>
        {inputs.length ? renderRows(top, [top], 1) : <p className="outline__empty">No recorded inputs.</p>}
      </section>
    </div>
  );
}

function AlsoUsed({ graph, id, home, others, onReveal }: { graph: ArgGraph; id: string; home?: string; others: string[]; onReveal(): void }) {
  const homeLabel = home ? graph.nodes.get(home)?.label : undefined;
  const rest = others.filter((o) => o !== home).length;
  if (!homeLabel) return null;
  return (
    <button type="button" className="orow__also linklike" onClick={onReveal} aria-label={`${graph.nodes.get(id)?.label} is also used by ${homeLabel}${rest ? ` and ${rest} more` : ""}. Show it under ${homeLabel}, where its inputs are listed`}>
      Also used by {homeLabel}
      {rest > 0 && ` and ${rest} more`}
    </button>
  );
}

function Chevron({ open }: { open: boolean }) {
  return (
    <svg viewBox="0 0 10 10" width="10" height="10" aria-hidden="true">
      <path d={open ? "M2 3.5 L5 6.5 L8 3.5" : "M3.5 2 L6.5 5 L3.5 8"} fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  );
}

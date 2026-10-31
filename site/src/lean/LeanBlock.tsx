import { memo, useCallback, useEffect, useMemo, useRef, useState, type MouseEvent, type ReactNode } from "react";
import "katex/dist/katex.min.css";
import { leanSourceUrl, type LeanDeclaration, type LeanModule, type LeanRelation } from "../api/lean";
import { routeHref } from "../app/router";
import { useEntryState } from "../app/trail";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { statementHref } from "../reader/links";
import { buildCode, CodeView, type BuiltCode } from "./CodeView";
import {
  compiled,
  declIn,
  dependencyWords,
  kindWord,
  LINK_CAVEAT,
  RELATION_WORDS,
  sectionPlace,
  sourceLines,
  useLeanModule,
  useLeanModules,
  useLeanShell,
  type LeanShell,
} from "./data";
import "./lean.css";
import { Breakable, Notation, PathText, Prose, ReadingFoot, readingStore } from "./ReadingStrip";
import { SITE_FACTS } from "virtual:site-facts";
import { useAlignment } from "../compare/useAlignment";
import { declTitle } from "../model/declTitle";
import { collectLocals, findDecl, makeScope, resolveName, splitUses, statementShape, type DeclRow, type NameTarget, type Scope } from "./resolve";
import { tokenize, type LeanToken } from "./tokenize";
import type { LeanWalk } from "./walk";

export type LineRange = readonly [first: number, last: number];

type LineRanges = LineRange | readonly LineRange[];

export interface LeanBlockProps {
  /** Full declaration name. */
  name: string;
  /** The module, where the caller knows it; a name can be declared in two modules. */
  module?: string;
  relation?: LeanRelation;
  note?: string;
  /** Start with the proof open. */
  proofOpen?: boolean;
  /** Tighter header and type for side panels and the map pane. */
  compact?: boolean;
  /** How many blocks this one is opened inside. */
  depth?: number;
  /** Leave uses and used by to a column of their own. */
  noDependencies?: boolean;
  /** Leave "Names in this statement" to a column of its own. */
  noTerms?: boolean;
  /** An exact substring of the source to mark, here or in a definition shown under the statement. */
  clause?: string;
  /** Shown after the block's actions. */
  below?: ReactNode;
  /** The statement alone, for a cell of Compare's table: no caveat, proof or actions. */
  bare?: boolean;
  /** Source lines to light, first and last inclusive. A range past the statement opens the proof. */
  lines?: LineRanges;
  /** Light `lines` without moving the scroller, for a host with several blocks in one column. */
  quietLines?: boolean;
  /** Lines lit by pointing: lit where they show, and nothing opens or scrolls. */
  pointed?: LineRanges;
  /** Walk in place: a plain click on a name reports here and the page stays. Without it a name is a link. */
  onName?(walk: LeanWalk): void;
  /** Fill the host's height: the head and the reading line stay, and the code scrolls between them. */
  fill?: boolean;
  /** Where the reading line goes, in place of the block's own foot. */
  previewSlot?: HTMLElement | null;
  /** Leave "In the papers" to the host. */
  noPapers?: boolean;
  /** Leave the name and its actions to the host. */
  noHead?: boolean;
}

/** A conclusion or hypothesis this short is shown under the statement. */
const SHOWN_CONCLUSION = 20;
const SHOWN_HYPOTHESIS = 6;
const SHOWN_HYPOTHESES = 2;

/** A definition this short is read whole; a longer one folds like a proof. */
const SHORT_DEFINITION = 12;
const LIST_LIMIT = 8;

const lineWord = (n: number) => `${n.toLocaleString("en-GB")} ${n === 1 ? "line" : "lines"}`;

const rangesOf = (lines: LeanBlockProps["lines"]): readonly LineRange[] => {
  if (!lines || lines.length === 0) return [];
  return typeof lines[0] === "number" ? [lines as LineRange] : (lines as readonly LineRange[]);
};

export const walkOf = (row: DeclRow, from?: string): LeanWalk => ({ name: row.name, module: row.module, short: row.short, from });
const declHref = (row: DeclRow) => routeHref({ view: "lean", module: row.module, decl: row.name });

/** The nearest scroller inside the page, so the window itself never moves. */
function scrollerOf(element: HTMLElement): HTMLElement | null {
  for (let at = element.parentElement; at && at !== document.body; at = at.parentElement) {
    const { overflowY } = getComputedStyle(at);
    if ((overflowY === "auto" || overflowY === "scroll") && at.scrollHeight > at.clientHeight) return at;
  }
  return null;
}

/** Bring the first lit line into its scroller, unless it is in view already. */
function showLine(line: HTMLElement): void {
  const scroller = scrollerOf(line);
  if (!scroller) return;
  const view = scroller.getBoundingClientRect();
  const box = line.getBoundingClientRect();
  if (box.top >= view.top && box.bottom <= view.bottom) return;
  scroller.scrollTop += box.top - view.top - Math.min(48, view.height / 4);
}

export interface WhereBody {
  row: DeclRow;
  code: BuiltCode;
}

function statementLastLine(decl: LeanDeclaration, kindWhole: boolean): number {
  return kindWhole ? decl.end_line : decl.signature_end_line;
}

/** Whether this declaration is read whole: its fields, or a short definition, are what it says. */
export function readsWhole(decl: LeanDeclaration): boolean {
  if (decl.kind === "structure" || decl.kind === "class" || decl.kind === "inductive") return true;
  return (decl.kind === "def" || decl.kind === "abbrev") && decl.end_line - decl.signature_end_line <= SHORT_DEFINITION;
}

/** The statement's conclusion and short hypotheses, resolved to in-tree predicates and laid out. */
function useWhere(decl: LeanDeclaration, tokens: LeanToken[], scope: Scope, shell: LeanShell, compact: boolean | undefined, clause: string | undefined): WhereBody[] {
  const candidates = useMemo(() => {
    const shape = statementShape(tokens);
    const found: { row: DeclRow; conclusion: boolean }[] = [];
    const add = (text: string | undefined, conclusion: boolean) => {
      const target = text ? resolveName(text, scope) : null;
      if (target?.kind !== "decl" || target.row.name === decl.name || found.some((f) => f.row.name === target.row.name)) return;
      if (target.row.endLine - target.row.line + 1 <= (conclusion ? SHOWN_CONCLUSION : SHOWN_HYPOTHESIS)) found.push({ row: target.row, conclusion });
    };
    add(shape.conclusion, true);
    shape.hypotheses.forEach((name) => add(name, false));
    return found;
  }, [tokens, scope, decl.name]);
  const names = useMemo(() => [...new Set(candidates.map((c) => c.row.module))], [candidates]);
  const arrived = useLeanModules(names);
  const key = arrived.map((m) => m.module).join(" ");
  return useMemo(() => {
    const bodies: WhereBody[] = [];
    let hypotheses = 0;
    for (const { row, conclusion } of candidates) {
      const module = arrived.find((m) => m.module === row.module);
      const target = module && declIn(module, row.name);
      if (!module || !target) continue;
      const lines = sourceLines(module);
      const head = lines.slice(target.line - 1, target.signature_end_line).join("\n");
      const isPredicate = /:\s*Prop\b/.test(head) || (conclusion && target.kind === "structure");
      if (!isPredicate) continue;
      const text = lines.slice(target.line - 1, target.end_line).join("\n");
      const holdsClause = Boolean(clause && text.includes(clause));
      if (!conclusion && !holdsClause && (compact || hypotheses >= SHOWN_HYPOTHESES)) continue;
      if (!conclusion) hypotheses++;
      const inner = makeScope(target, module, shell.index, shell.terms);
      const tokensThere = tokenize(text);
      collectLocals(tokensThere, inner.locals);
      bodies.push({ row, code: buildCode(tokensThere, target.line, inner, clause) });
    }
    return bodies;
    // `arrived` is a new list each render; its joined key says when it changed.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [candidates, key, shell.index, shell.terms, compact, clause]);
}

/** Everything the statement names, the shown definitions included, for a list kept elsewhere. */
export function useStatementTargets(decl: LeanDeclaration, module: LeanModule, shell: LeanShell): NameTarget[] {
  const { tokens, scope, code } = useMemo(() => {
    const scope = makeScope(decl, module, shell.index, shell.terms);
    const end = statementLastLine(decl, readsWhole(decl));
    const tokens = tokenize(sourceLines(module).slice(decl.line - 1, end).join("\n"));
    collectLocals(tokens, scope.locals);
    return { tokens, scope, code: buildCode(tokens, decl.line, scope) };
  }, [decl, module, shell.index, shell.terms]);
  const where = useWhere(decl, tokens, scope, shell, false, undefined);
  return useMemo(() => [...code.targets, ...where.flatMap((body) => body.code.targets)], [code, where]);
}

export function Terms({ targets, onWalk }: { targets: NameTarget[]; onWalk?(row: DeclRow): void }) {
  const terms = useMemo(() => {
    const seen = new Set<string>();
    const rows: Extract<NameTarget, { kind: "decl" }>[] = [];
    for (const target of targets) {
      if (target.kind !== "decl" || !target.term || seen.has(target.row.name)) continue;
      seen.add(target.row.name);
      rows.push(target);
    }
    return rows;
  }, [targets]);
  if (!terms.length) return null;
  return (
    <section className="lean-terms" aria-label="Names in this statement">
      <p className="lean-terms__title">
        Names in this statement <span className="lean-terms__hint">Point at a name to read it.</span>
      </p>
      <dl className="lean-terms__list">
        {terms.map(({ row, term }) => (
          <div key={row.name} className="lean-terms__row">
            <dt>
              <a
                href={declHref(row)}
                onClick={onWalk && plainClick(() => onWalk(row))}
              >
                {term?.tex ? <Notation term={term} /> : <code>{row.short}</code>}
              </a>
            </dt>
            <dd>{term ? <Prose text={term.words} /> : null}</dd>
          </div>
        ))}
      </dl>
    </section>
  );
}

/** A click handler for a real link: a plain click walks; a modified one is the browser's. */
function plainClick(walk: () => void) {
  return (event: MouseEvent) => {
    if (event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    event.preventDefault();
    walk();
  };
}

export function CopyName({ name }: { name: string }) {
  const [copied, setCopied] = useState(false);
  useEffect(() => {
    if (!copied) return;
    const timer = window.setTimeout(() => setCopied(false), 1600);
    return () => window.clearTimeout(timer);
  }, [copied]);
  return (
    <button
      type="button"
      className="lean-action"
      onClick={() => {
        void navigator.clipboard?.writeText(name).then(() => setCopied(true));
      }}
    >
      <span aria-live="polite">{copied ? "Copied" : "Copy name"}</span>
    </button>
  );
}

/** This file on this site, at this declaration; Back returns from it. GitHub is the quiet second. */
export function SourceLink({ decl, module, shell }: { decl: LeanDeclaration; module: LeanModule; shell: LeanShell }) {
  const path = shell.paths.get(module.module)?.path ?? module.path;
  return (
    <>
      <a className="lean-action" href={routeHref({ view: "lean", module: module.module, file: `${decl.line}-${decl.end_line}` })}>
        Whole file
      </a>
      <a className="lean-action lean-action--quiet" href={leanSourceUrl(shell.modules, path, decl.line, decl.end_line)} target="_blank" rel="noreferrer" title={`${path}, lines ${decl.line} to ${decl.end_line}, at commit ${shell.modules.revision.slice(0, 7)} of OpenAI's repository`}>
        On GitHub
      </a>
    </>
  );
}

function DependencyList({ title, names, decl, shell, onWalk }: { title: string; names: readonly string[]; decl: LeanDeclaration; shell: LeanShell; onWalk?(row: DeclRow): void }) {
  const [all, setAll] = useEntryState(`lean-list:${decl.name}:${title}`, false);
  const alignment = useAlignment();
  const near = (decl as { module?: string }).module;
  const rows = useMemo(() => {
    const found = names.flatMap((name) => {
      const row = findDecl(shell.index, name, near);
      return row ? [row] : [];
    });
    const rank = (row: DeclRow) => (shell.linked.has(row.name) ? 0 : shell.terms.has(row.name) ? 1 : 2);
    return found.sort((a, b) => rank(a) - rank(b) || a.short.localeCompare(b.short));
  }, [names, near, shell]);
  const shown = all ? rows : rows.slice(0, LIST_LIMIT);
  return (
    <section className="lean-deps__list" aria-label={title}>
      <p className="lean-deps__title">
        {title} <span className="lean-deps__count">{rows.length.toLocaleString("en-GB")}</span>
      </p>
      {rows.length === 0 && <p className="lean-deps__none">None found.</p>}
      <ul>
        {shown.map((row) => {
          const record = shell.linked.get(row.name)?.[0];
          const plain = declTitle(alignment, row.name);
          return (
            <li key={`${row.module}:${row.name}`}>
              <a href={declHref(row)} title={row.name} onClick={onWalk && plainClick(() => onWalk(row))}>
                {plain ? <span className="lean-deps__plain">{plain}</span> : <Breakable name={row.short} />}
                <span className="lean-deps__kind">{kindWord(row.kind)}</span>
                {record && record.title !== plain && <span className="lean-deps__record">In the argument: {record.title}</span>}
              </a>
            </li>
          );
        })}
      </ul>
      {rows.length > LIST_LIMIT && (
        <button type="button" className="lean-action" aria-expanded={all} onClick={() => setAll(!all)}>
          {all ? `Show the first ${LIST_LIMIT}` : `Show all ${rows.length.toLocaleString("en-GB")}`}
        </button>
      )}
    </section>
  );
}

/** Uses split by where they appear, with the wording kept in one place. */
export function usesOf(decl: LeanDeclaration, module: LeanModule) {
  const facts = compiled(decl);
  if (facts.statement_uses && facts.proof_uses) return { statement: facts.statement_uses, proof: facts.proof_uses };
  const text = sourceLines(module).slice(decl.line - 1, statementLastLine(decl, readsWhole(decl))).join("\n");
  const split = splitUses(decl.uses, tokenize(text));
  return readsWhole(decl) ? { statement: decl.uses, proof: [] } : split;
}

/** Uses and used by, with the same wording wherever they appear. */
export function Dependencies({ decl, module, shell, onWalk }: { decl: LeanDeclaration; module: LeanModule; shell: LeanShell; onWalk?(row: DeclRow): void }) {
  const uses = useMemo(() => usesOf(decl, module), [decl, module]);
  return (
    <div className="lean-deps">
      <p className="lean-deps__source">{dependencyWords(decl.dependency_source ?? shell.modules.dependency_source)}.</p>
      <div className="lean-deps__columns">
        <DependencyList title="Uses in its statement" names={uses.statement} decl={decl} shell={shell} onWalk={onWalk} />
        {uses.proof.length > 0 && <DependencyList title="Uses in its proof" names={uses.proof} decl={decl} shell={shell} onWalk={onWalk} />}
        <DependencyList title="Used by" names={decl.used_by} decl={decl} shell={shell} onWalk={onWalk} />
      </div>
    </div>
  );
}

const SORRY = /\bsorry\b/;

/** Axioms and `sorry`: Lean's report where this edition has one, and the text scan said to be one. */
export function LeanFacts({ decl, module }: { decl: LeanDeclaration; module: LeanModule }) {
  const facts = compiled(decl);
  const says = useMemo(() => {
    if (decl.kind === "axiom") return <>Assumed, not proved. Lean takes this as given.</>;
    if (facts.axioms) {
      const names = facts.axioms.filter((name) => name !== "sorryAx");
      return (
        <>
          {facts.sorry || facts.axioms.includes("sorryAx") ? (
            <>
              Lean reports <code>sorry</code> in this declaration.{" "}
            </>
          ) : null}
          Lean reports {names.length ? "that it rests on the axioms " : "that it rests on no axioms."}
          {names.map((name, k) => (
            <span key={name}>
              {k > 0 && (k === names.length - 1 ? " and " : ", ")}
              <code>{name}</code>
            </span>
          ))}
          {names.length ? "." : ""}
        </>
      );
    }
    const code = tokenize(sourceLines(module).slice(decl.line - 1, decl.end_line).join("\n"))
      .filter((token) => token.kind !== "comment" && token.kind !== "doc" && token.kind !== "string")
      .map((token) => token.text)
      .join("");
    // The published extraction covers one theorem; the edition itself carries no axiom report.
    if (decl.name === SITE_FACTS.extraction?.root && !SITE_FACTS.extraction.hasSorry) {
      return (
        <>
          Lean’s extraction lists {SITE_FACTS.extraction.axioms.map((axiom, k) => (
            <span key={axiom}>
              {k > 0 && ", "}
              <code>{axiom}</code>
            </span>
          ))} for this theorem, and no <code>sorryAx</code>. <a href={routeHref({ view: "checks" })}>What ran</a>
        </>
      );
    }
    return SORRY.test(code) ? (
      <>
        A text scan finds <code>sorry</code> in this declaration. This edition has no report from Lean on its axioms.
      </>
    ) : (
      <>
        A text scan finds no <code>sorry</code> in this declaration. This edition has no report from Lean on its axioms.
      </>
    );
  }, [decl, module, facts]);
  return <p className="lean-block__facts">{says}</p>;
}

/** Where each paper states this declaration, as links that go there. */
function PapersLine({ name, shell }: { name: string; shell: LeanShell }) {
  const rows = shell.statements?.get(name);
  if (!rows?.length) return null;
  const shown = STAGE_ORDER.flatMap((stage) => rows.find((row) => row.statement.paper === stage) ?? []);
  return (
    <p className="lean-block__papers">
      <span>In the papers:</span>{" "}
      {shown.map((row, k) => (
        <span key={row.statement.paper}>
          {k > 0 && ", "}
          <a href={statementHref(row.statement)}>
            {PAPER_NAMES[row.statement.paper].short} {sectionPlace(row.statement.section)}
          </a>
        </span>
      ))}
    </p>
  );
}

export interface DeclViewProps {
  decl: LeanDeclaration;
  module: LeanModule;
  shell: LeanShell;
  relation?: LeanRelation;
  note?: string;
  proofOpen?: boolean;
  compact?: boolean;
  depth?: number;
  /** A row in a module's list: a short header that links to the declaration's page. */
  row?: { href: string };
  noDependencies?: boolean;
  noTerms?: boolean;
  clause?: string;
  below?: ReactNode;
  bare?: boolean;
  lines?: LeanBlockProps["lines"];
  quietLines?: boolean;
  pointed?: LeanBlockProps["pointed"];
  onName?(walk: LeanWalk): void;
  fill?: boolean;
  previewSlot?: HTMLElement | null;
  noPapers?: boolean;
  noHead?: boolean;
}

export const DeclView = memo(function DeclView({ decl, module, shell, relation, note, proofOpen, compact, depth = 0, row, noDependencies, noTerms, clause, below, bare, lines: litLines, quietLines, pointed, onName, fill, previewSlot, noPapers, noHead }: DeclViewProps) {
  // Open or folded belongs to the history entry, so Back finds the proof as it was left.
  const [proofChosen, setShowProof] = useEntryState<boolean | null>(`lean-proof:${module.module}:${decl.name}`, null);
  const store = useMemo(readingStore, []);
  const root = useRef<HTMLElement>(null);

  const lines = sourceLines(module);
  const isDefinition = decl.kind === "def" || decl.kind === "abbrev";
  const statementEnd = statementLastLine(decl, readsWhole(decl));
  const foldLines = decl.end_line - statementEnd;
  const ranges = rangesOf(litLines);
  const rangesKey = ranges.map(([a, b]) => `${a}-${b}`).join(",");
  const clauseInProof = Boolean(clause && foldLines > 0 && !lines.slice(decl.line - 1, statementEnd).join("\n").includes(clause) && lines.slice(statementEnd, decl.end_line).join("\n").includes(clause));
  const litInProof = foldLines > 0 && ranges.some(([, last]) => last > statementEnd);
  const showProof = proofChosen ?? (Boolean(proofOpen) || ((clauseInProof || litInProof) && !bare));
  const lit = [...ranges, ...rangesOf(pointed)];
  const litKey = lit.map(([a, b]) => `${a}-${b}`).join(",");
  const isLit = useMemo(() => (lit.length ? (line: number) => lit.some(([first, last]) => line >= first && line <= last) : undefined), [litKey]); // eslint-disable-line react-hooks/exhaustive-deps

  const { statement, scope, tokens } = useMemo(() => {
    const scope = makeScope(decl, module, shell.index, shell.terms);
    const tokens = tokenize(lines.slice(decl.line - 1, statementEnd).join("\n"));
    collectLocals(tokens, scope.locals);
    return { statement: buildCode(tokens, decl.line, scope, clause), scope, tokens };
  }, [decl, module, shell.index, shell.terms, lines, statementEnd, clause]);
  const where = useWhere(decl, tokens, scope, shell, compact, clause);

  const proof = useMemo(() => {
    if (!showProof || foldLines === 0) return null;
    const tokens = tokenize(lines.slice(statementEnd, decl.end_line).join("\n"), { signature: false });
    collectLocals(tokens, scope.locals);
    return buildCode(tokens, statementEnd + 1, scope, clause);
  }, [showProof, foldLines, lines, statementEnd, decl.end_line, scope, clause]);

  const allTargets = useMemo(() => [...statement.targets, ...where.flatMap((body) => body.code.targets)], [statement, where]);

  const read = useCallback((target: NameTarget | null, element: HTMLElement | null) => (target && element ? store.read({ target, shell }) : store.clear()), [store, shell]);

  const walk = onName ? (next: DeclRow) => onName(walkOf(next, decl.name)) : undefined;
  const plain = shell.plain.get(decl.name);
  const onOpen = useMemoStable((target: NameTarget, _element: HTMLElement, event: MouseEvent) => {
    if (target.kind === "mathlib" || !walk) return;
    event.preventDefault();
    walk(target.row);
  });

  // A range that changes is what the reader is now looking at; pointing and scrolling never reach here.
  useEffect(() => {
    if (!rangesKey || quietLines) return;
    const first = root.current?.querySelector<HTMLElement>(".lean-line.is-lit");
    if (first) showLine(first);
  }, [rangesKey, proof, quietLines]);

  const parent = (decl as LeanDeclaration & { parent?: string }).parent;
  const Title = depth > 0 ? "h3" : "h2";
  const path = shell.paths.get(module.module)?.path ?? module.path;
  const foldWord = isDefinition ? "Definition" : "Proof";
  const showHead = !noHead;
  const term = shell.terms.get(decl.name);

  const body = (
    <>
      {relation && (
        <div className="lean-block__link">
          <p className="lean-block__relation">
            {RELATION_WORDS[relation]}.{note ? " " : ""}
            {note ? <Prose text={note} /> : null}
          </p>
          {!bare && <p className="lean-block__caveat">{LINK_CAVEAT}</p>}
        </div>
      )}
      {decl.doc && !compact && <p className="lean-block__doc">{decl.doc}</p>}

      <CodeView code={statement} label={`Statement of ${decl.short}. Tab reaches a name; the arrow keys move between names.`} onRead={read} onOpen={onOpen} lit={isLit} />
      {where.map((body) => (
        <section className="lean-where" key={body.row.name} aria-label={`Where ${body.row.short} says`}>
          <p className="lean-where__label">
            Where <code>{body.row.short}</code> says
            <span>
              {" "}
              in {(shell.paths.get(body.row.module)?.path ?? body.row.module).split("/").pop()}, line {body.row.line}
            </span>
          </p>
          <CodeView code={body.code} label={`Definition of ${body.row.short}`} onRead={read} onOpen={onOpen} />
        </section>
      ))}

      {foldLines > 0 && !bare && (
        <button type="button" className="lean-fold" aria-expanded={showProof} onClick={() => setShowProof(!showProof)}>
          {foldWord} <span className="lean-fold__mark" aria-hidden="true" /> <span className="lean-fold__lines">{lineWord(foldLines)}</span>
        </button>
      )}
      {proof && (
        <div className="lean-block__proof">
          <CodeView code={proof} label={`${foldWord} of ${decl.short}. Tab reaches a name; the arrow keys move between names.`} onRead={read} onOpen={onOpen} lit={isLit} />
        </div>
      )}
      {!bare && !row && <LeanFacts decl={decl} module={module} />}
      {!row && !noPapers && !bare && <PapersLine name={decl.name} shell={shell} />}
      {!row && !noTerms && !bare && <Terms targets={allTargets} onWalk={walk} />}
      {!row && !noDependencies && !bare && <Dependencies decl={decl} module={module} shell={shell} onWalk={walk} />}
      {below}
    </>
  );

  return (
    <article ref={root} className={`lean-block${compact ? " is-compact" : ""}${row ? " is-row" : ""}${fill ? " is-fill" : ""}${bare ? " is-bare" : ""}`}>
      {showHead && (
        <header className="lean-block__head">
          <div className="lean-block__title">
            <p className="lean-block__kind">{parent ? `Field of ${parent.slice(parent.lastIndexOf(".") + 1)}` : kindWord(decl.kind)}</p>
            {plain && (
              <Title className="lean-block__plain">{row ? <a href={row.href}>{plain}</a> : plain}</Title>
            )}
            {plain ? (
              <p className="lean-block__rawname">
                <Breakable name={decl.short} />
              </p>
            ) : (
              <Title className="lean-block__name">
                {row ? (
                  <a href={row.href}>
                    <Breakable name={decl.short} />
                  </a>
                ) : (
                  <Breakable name={decl.short} />
                )}
              </Title>
            )}
            {term?.tex && <Notation term={term} />}
          </div>
          {!row && !compact && (
            <p className="lean-block__path">
              <PathText path={path} />, lines {decl.line} to {decl.end_line}
            </p>
          )}
          {!bare && (
            <p className="lean-block__actions">
              <SourceLink decl={decl} module={module} shell={shell} />
              {!row && <CopyName name={decl.name} />}
            </p>
          )}
        </header>
      )}
      {fill ? (
        <div className="lean-block__scroll" data-keep="">
          {body}
        </div>
      ) : (
        body
      )}
      {(!row || previewSlot) && <ReadingFoot store={store} slot={previewSlot} />}
    </article>
  );
});

/** A stable function that always calls the latest closure, so the code stays memoised. */
function useMemoStable<A extends unknown[]>(fn: (...args: A) => void): (...args: A) => void {
  const latest = useRef(fn);
  latest.current = fn;
  return useCallback((...args: A) => latest.current(...args), []);
}

/** One Lean declaration: its statement, readable names, its proof on demand and where it comes from. */
export function LeanBlock({ name, module: moduleName, relation, note, proofOpen, compact, depth, noDependencies, noTerms, clause, below, bare, lines, quietLines, pointed, onName, fill, previewSlot, noPapers, noHead }: LeanBlockProps) {
  const state = useLeanShell();
  const shell = state.status === "ready" ? state.shell : null;
  const row = shell ? findDecl(shell.index, name, moduleName) : undefined;
  const loaded = useLeanModule(moduleName ?? row?.module);
  if (state.status === "missing") return <p className="lean-note">This edition does not include the Lean source.</p>;
  if (shell && !row) return <p className="lean-note">No declaration named <code>{name}</code> in this source.</p>;
  if (loaded.status === "failed") return <p className="lean-note">The Lean source for this declaration could not be loaded.</p>;
  if (!shell || loaded.status !== "ready") return <div className={`lean-wait${compact ? " is-compact" : ""}`}>Loading the Lean source</div>;
  const decl = declIn(loaded.module, name);
  if (!decl) return <p className="lean-note">No declaration named <code>{name}</code> in {loaded.module.module}.</p>;
  return <DeclView key={`${loaded.module.module}:${name}`} decl={decl} module={loaded.module} shell={shell} relation={relation} note={note} proofOpen={proofOpen} compact={compact} depth={depth} noDependencies={noDependencies} noTerms={noTerms} clause={clause} below={below} bare={bare} lines={lines} quietLines={quietLines} pointed={pointed} onName={onName} fill={fill} previewSlot={previewSlot} noPapers={noPapers} noHead={noHead} />;
}

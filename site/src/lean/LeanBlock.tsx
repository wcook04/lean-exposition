import { memo, useCallback, useEffect, useMemo, useRef, useState, type MouseEvent, type ReactNode } from "react";
import "katex/dist/katex.min.css";
import { leanSourceUrl, type LeanDeclaration, type LeanModule, type LeanRelation } from "../api/lean";
import { routeHref } from "../app/router";
import { buildCode, CodeView, type BuiltCode } from "./CodeView";
import {
  declIn,
  dependencyWords,
  kindWord,
  LINK_CAVEAT,
  RELATION_WORDS,
  sourceLines,
  useLeanModule,
  useLeanModules,
  useLeanShell,
  type LeanShell,
} from "./data";
import "./lean.css";
import { Breakable, clearName, Notation, PathText, Prose, readName } from "./ReadingStrip";
import { collectLocals, findDecl, makeScope, resolveName, statementShape, type DeclRow, type NameTarget, type Scope } from "./resolve";
import { tokenize, type LeanToken } from "./tokenize";

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
}

/** A conclusion or hypothesis this short is shown under the statement. */
const SHOWN_CONCLUSION = 20;
const SHOWN_HYPOTHESIS = 6;
const SHOWN_HYPOTHESES = 2;

/** How far a name opens in place; past this a name goes to its page. */
const MAX_DEPTH = 3;
/** A definition this short is read whole; a longer one folds like a proof. */
const SHORT_DEFINITION = 12;
const LIST_LIMIT = 8;

const lineWord = (n: number) => `${n.toLocaleString("en-GB")} ${n === 1 ? "line" : "lines"}`;

interface Opened {
  row: DeclRow;
  slot: "statement" | "proof" | "relations";
  from: HTMLElement | null;
}

function Nest({ opened, parent, depth, onBack }: { opened: Opened; parent: string; depth: number; onBack(): void }) {
  const ref = useRef<HTMLElement>(null);
  useEffect(() => {
    ref.current?.focus({ preventScroll: true });
    ref.current?.scrollIntoView({ block: "nearest" });
  }, [opened.row.name]);
  return (
    <section className="lean-nest" ref={ref} tabIndex={-1} aria-label={`Definition of ${opened.row.short}`}>
      <button type="button" className="lean-nest__back" onClick={onBack}>
        Back to <code>{parent}</code>
      </button>
      <LeanBlock key={`${opened.row.module}:${opened.row.name}`} name={opened.row.name} module={opened.row.module} compact depth={depth + 1} />
    </section>
  );
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

export function Terms({ targets, onOpen }: { targets: NameTarget[]; onOpen(row: DeclRow, element: HTMLElement): void }) {
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
                href={routeHref({ view: "lean", module: row.module, decl: row.name })}
                onClick={(event) => {
                  event.preventDefault();
                  onOpen(row, event.currentTarget);
                }}
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

function CopyName({ name }: { name: string }) {
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

function DependencyList({ title, names, decl, shell, onOpen }: { title: string; names: readonly string[]; decl: LeanDeclaration; shell: LeanShell; onOpen(row: DeclRow, element: HTMLElement): void }) {
  const [all, setAll] = useState(false);
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
          return (
            <li key={`${row.module}:${row.name}`}>
              <a
                href={routeHref({ view: "lean", module: row.module, decl: row.name })}
                onClick={(event) => {
                  if (event.metaKey || event.ctrlKey || event.shiftKey) return;
                  event.preventDefault();
                  onOpen(row, event.currentTarget);
                }}
              >
                <Breakable name={row.short} />
                <span className="lean-deps__kind">{kindWord(row.kind)}</span>
                {record && <span className="lean-deps__record">In the argument: {record.title}</span>}
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

/** Uses and used by, with the same wording wherever they appear. */
export function Dependencies({ decl, shell, onOpen }: { decl: LeanDeclaration; shell: LeanShell; onOpen(row: DeclRow, element: HTMLElement): void }) {
  return (
    <div className="lean-deps">
      <p className="lean-deps__source">{dependencyWords(decl.dependency_source ?? shell.modules.dependency_source)}.</p>
      <div className="lean-deps__columns">
        <DependencyList title="Uses" names={decl.uses} decl={decl} shell={shell} onOpen={onOpen} />
        <DependencyList title="Used by" names={decl.used_by} decl={decl} shell={shell} onOpen={onOpen} />
      </div>
    </div>
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
  /** A row in a module's list: a short header, and the fuller parts only while selected. */
  row?: { href: string; selected: boolean; onSelect(): void };
  noDependencies?: boolean;
  noTerms?: boolean;
  clause?: string;
  below?: ReactNode;
  bare?: boolean;
}

export const DeclView = memo(function DeclView({ decl, module, shell, relation, note, proofOpen, compact, depth = 0, row, noDependencies, noTerms, clause, below, bare }: DeclViewProps) {
  const [proofChosen, setShowProof] = useState(Boolean(proofOpen));
  const [opened, setOpened] = useState<Opened | null>(null);

  const lines = sourceLines(module);
  const isDefinition = decl.kind === "def" || decl.kind === "abbrev";
  const statementEnd = statementLastLine(decl, readsWhole(decl));
  const foldLines = decl.end_line - statementEnd;
  const clauseInProof = Boolean(clause && foldLines > 0 && !lines.slice(decl.line - 1, statementEnd).join("\n").includes(clause) && lines.slice(statementEnd, decl.end_line).join("\n").includes(clause));
  const showProof = proofChosen || (clauseInProof && !bare);

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

  const read = useCallback((target: NameTarget | null, element: HTMLElement | null) => (target && element ? readName(target, element, shell) : clearName()), [shell]);

  const open = (next: Opened["row"], slot: Opened["slot"], from: HTMLElement | null) => setOpened({ row: next, slot, from });
  const onOpenIn = (slot: Opened["slot"]) => (target: NameTarget, element: HTMLElement, event: MouseEvent) => {
    if (target.kind === "mathlib" || depth >= MAX_DEPTH) return;
    event.preventDefault();
    open(target.row, slot, element);
  };
  const onOpenStatement = useMemoStable(onOpenIn("statement"));
  const onOpenProof = useMemoStable(onOpenIn("proof"));

  const nest = (slot: Opened["slot"]) =>
    opened?.slot === slot && (
      <Nest
        opened={opened}
        parent={decl.short}
        depth={depth}
        onBack={() => {
          opened.from?.focus();
          setOpened(null);
        }}
      />
    );

  const parent = (decl as LeanDeclaration & { parent?: string }).parent;
  const selected = row ? row.selected : true;
  const Title = depth > 0 ? "h3" : "h2";
  const path = shell.paths.get(module.module)?.path ?? module.path;
  const foldWord = isDefinition ? "Definition" : "Proof";
  const repoUrl = leanSourceUrl(shell.modules, path, decl.line, decl.end_line);

  return (
    <article className={`lean-block${compact ? " is-compact" : ""}${row ? " is-row" : ""}${row?.selected ? " is-selected" : ""}`}>
      <header className="lean-block__head">
        <div className="lean-block__title">
          <p className="lean-block__kind">{parent ? `Field of ${parent.slice(parent.lastIndexOf(".") + 1)}` : kindWord(decl.kind)}</p>
          <Title className="lean-block__name">
            {row ? (
              <a
                href={row.href}
                onClick={(event) => {
                  if (event.metaKey || event.ctrlKey || event.shiftKey) return;
                  event.preventDefault();
                  row.onSelect();
                }}
              >
                <Breakable name={decl.short} />
              </a>
            ) : (
              <Breakable name={decl.short} />
            )}
          </Title>
        </div>
        {!row && (
          <p className="lean-block__path">
            <PathText path={path} />, line {decl.line}
          </p>
        )}
        {relation && (
          <>
            <p className="lean-block__relation">
              {compact && note ? (
                <Prose text={note} />
              ) : (
                <>
                  {RELATION_WORDS[relation]}.{note ? " " : ""}
                  {note ? <Prose text={note} /> : null}
                </>
              )}
            </p>
            {!bare && <p className="lean-block__caveat">{LINK_CAVEAT}</p>}
          </>
        )}
      </header>
      {decl.doc && <p className="lean-block__doc">{decl.doc}</p>}

      <CodeView code={statement} label={`Statement of ${decl.short}. Tab reaches a name; the arrow keys move between names.`} onRead={read} onOpen={onOpenStatement} />
      {where.map((body) => (
        <section className="lean-where" key={body.row.name} aria-label={`Where ${body.row.short} says`}>
          <p className="lean-where__label">
            Where <code>{body.row.short}</code> says
            <span>
              {" "}
              in {(shell.paths.get(body.row.module)?.path ?? body.row.module).split("/").pop()}, line {body.row.line}
            </span>
          </p>
          <CodeView code={body.code} label={`Definition of ${body.row.short}`} onRead={read} onOpen={onOpenStatement} />
        </section>
      ))}
      {nest("statement")}
      {selected && !noTerms && !bare && <Terms targets={allTargets} onOpen={(next, from) => open(next, "statement", from)} />}

      {foldLines > 0 && !bare && (
        <button type="button" className="lean-fold" aria-expanded={showProof} onClick={() => setShowProof(!proofChosen)}>
          {foldWord}, {lineWord(foldLines)}
        </button>
      )}
      {proof && (
        <div className="lean-block__proof">
          <CodeView code={proof} label={`${foldWord} of ${decl.short}. Tab reaches a name; the arrow keys move between names.`} onRead={read} onOpen={onOpenProof} />
        </div>
      )}
      {nest("proof")}

      {selected && !bare && (
        <p className="lean-block__actions">
          <a className="lean-action" href={repoUrl} target="_blank" rel="noreferrer">
            Open in OpenAI's repository
          </a>
          <CopyName name={decl.name} />
        </p>
      )}
      {selected && !noDependencies && !bare && <Dependencies decl={decl} shell={shell} onOpen={(next, from) => open(next, "relations", from)} />}
      {nest("relations")}
      {selected && below}
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
export function LeanBlock({ name, module: moduleName, relation, note, proofOpen, compact, depth, noDependencies, noTerms, clause, below, bare }: LeanBlockProps) {
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
  return <DeclView decl={decl} module={loaded.module} shell={shell} relation={relation} note={note} proofOpen={proofOpen} compact={compact} depth={depth} noDependencies={noDependencies} noTerms={noTerms} clause={clause} below={below} bare={bare} />;
}

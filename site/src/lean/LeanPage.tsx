// The index at the back of the book: OpenAI's Lean source for anyone who wants the files and
// declarations themselves. Readers reach the Lean from the papers; this page is the list.
// Every declaration has its own page and address: where the papers state it, then the Lean,
// then what it uses and what uses it. A module page lists its declarations in source order, a
// folder page its modules, and the first screen says what this tree is, what has been run on
// it and where to begin. A plain title comes first wherever one exists, the Lean name small
// beside it.

import { memo, useCallback, useEffect, useId, useMemo, useRef, useState, type ReactNode } from "react";
import type { AlignedStatement, LeanDeclaration, LeanFolder, LeanModule } from "../api/lean";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { useBarLine } from "./barLine";
import { navigate, routeHref, type Route } from "../app/router";
import { arrivedBy, namePlace, useEntryState } from "../app/trail";
import { useCheckedWords } from "./checked";
import { LazyStatementSlice } from "../compare/lazy";
import { statementHref } from "../reader/links";
import { CHALLENGE_FILE, declIn, sourceLines, kindWord, LINK_CAVEAT, MAIN_THEOREM, MINIMIZER, RELATION_WORDS, sectionPlace, useLeanModule, useLeanShell, VALUE_CHALLENGE_FILE, VALUE_THEOREM, type LeanShell, type LinkedRecord, type PaperStatement } from "./data";
import { rankNames } from "./find";
import { folderLabel, FOLDER_WORDS } from "./folders";
import { CopyName, DeclView, LeanBlock, SourceLink, usesOf } from "./LeanBlock";
import "./lean.css";
import { Neighbourhood } from "./Neighbourhood";
import { Breakable, Notation, PathText, Prose, ReadingFoot, readingStore } from "./ReadingStrip";
import { buildCode, CodeView, type BuiltCode } from "./CodeView";
import { collectLocals, findDecl, makeScope, type DeclRow, type NameTarget } from "./resolve";
import { tokenize } from "./tokenize";

const count = (n: number) => n.toLocaleString("en-GB");

function useMedia(query: string): boolean {
  const [on, setOn] = useState(() => (typeof window.matchMedia === "function" ? window.matchMedia(query).matches : true));
  useEffect(() => {
    if (typeof window.matchMedia !== "function") return;
    const list = window.matchMedia(query);
    const update = () => setOn(list.matches);
    update();
    list.addEventListener("change", update);
    return () => list.removeEventListener("change", update);
  }, [query]);
  return on;
}

const declHref = (row: Pick<DeclRow, "name" | "module">) => routeHref({ view: "lean", module: row.module, decl: row.name });
const lastPart = (dotted: string) => dotted.slice(dotted.lastIndexOf(".") + 1);

const READING = [
  ["theorem name (inputs) : claim", "Given these inputs, the claim holds."],
  ["∀ x, P x", "For every x, P x holds."],
  ["A → B", "If A then B. Between types, a function from A to B."],
  ["A ∧ B", "A and B."],
  [":=", "Is defined as, or is proved by, what follows."],
  ["by", "Starts a proof written as steps. Lean checks each step."],
] as const;

function HowToRead() {
  return (
    <section className="lean-how" aria-labelledby="lean-how">
      <h2 id="lean-how">How to read Lean</h2>
      <dl>
        {READING.map(([code, words]) => (
          <div key={code}>
            <dt>
              <code>{code}</code>
            </dt>
            <dd>{words}</dd>
          </div>
        ))}
      </dl>
    </section>
  );
}

function Folders({ shell }: { shell: LeanShell }) {
  return (
    <section className="lean-folders" aria-labelledby="lean-folders">
      <h2 id="lean-folders">What each folder holds</h2>
      <ul>
        {shell.modules.folders.map((folder) => (
          <li key={folder.path}>
            <a href={routeHref({ view: "lean", folder: folder.path })}>{folderLabel(folder.path)}</a>
            <span className="lean-folders__count">{count(folder.modules.length)} modules</span>
            {FOLDER_WORDS[folder.path] && <p>{FOLDER_WORDS[folder.path]}</p>}
          </li>
        ))}
      </ul>
    </section>
  );
}

// ------------------------------------------------------------------ first screen

interface Tree {
  path: string;
  modules: number;
  declarations: number;
}

function treeOf(shell: LeanShell, prefix: string): Tree {
  const folders = shell.modules.folders.filter((folder) => folder.path === prefix || folder.path.startsWith(`${prefix}/`));
  return {
    path: prefix,
    modules: folders.reduce((sum, folder) => sum + folder.modules.length, 0),
    declarations: folders.reduce((sum, folder) => sum + folder.modules.reduce((n, row) => n + row.declarations, 0), 0),
  };
}

/** The record a theorem states, by the paper's name for it. */
const stated = (shell: LeanShell, name: string) => (shell.linked.get(name) ?? []).find((row) => row.relation === "states" && !row.id.startsWith("lean."))?.title ?? lastPart(name);

function Start({ href, name, title, children }: { href: string; name?: string; title: string; children: ReactNode }) {
  return (
    <li>
      <a href={href}>
        <span className="lean-start__title">{title}</span>
        {name && <code>{name}</code>}
      </a>
      <p>{children}</p>
    </li>
  );
}

function Landing({ shell, slot }: { shell: LeanShell; slot: HTMLElement | null }) {
  const { modules } = shell;
  const main = findDecl(shell.index, MAIN_THEOREM);
  const value = findDecl(shell.index, VALUE_THEOREM);
  const minimizer = findDecl(shell.index, MINIMIZER);
  const support = treeOf(shell, "OAI/Probability/SKSupport");
  const scalar = treeOf(shell, "OAI/Probability/SKValue");
  const revisionUrl = modules.base_url.replace(/\/blob\//, "/tree/");
  const checked = useCheckedWords();
  const resting = shell.linked.size;
  return (
    <>
      <header className="lean-intro">
        <h1>Lean index</h1>
        <p>
          The index at the back of the book, for anyone who wants the files and declarations themselves. To read the mathematics,{" "}
          <a href={routeHref({ view: "read", stage: "short" })}>open a paper</a>: a statement with a dark tick there opens its Lean beside the text.
        </p>
        <p>
          This is OpenAI's Lean at commit{" "}
          <a href={revisionUrl} target="_blank" rel="noreferrer">
            <code>{modules.revision.slice(0, 7)}</code>
          </a>{" "}
          on <code>{modules.toolchain.split(":").pop()}</code>: {count(modules.counts.modules)} modules and {count(modules.counts.declarations)} declarations. It holds two proof trees,{" "}
          <a href={routeHref({ view: "lean", folder: support.path })}>
            <code>SKSupport</code>
          </a>{" "}
          with {count(support.modules)} modules, ending in <code>full_support</code>, and{" "}
          <a href={routeHref({ view: "lean", folder: scalar.path })}>
            <code>SKValue</code>
          </a>{" "}
          with {count(scalar.modules)}, ending in <code>value_consequences</code>, and two challenge files for Comparator.
        </p>
        <p className="lean-intro__checked">
          {checked}{" "}
          <a href={routeHref({ view: "checks" })}>Every recorded check</a>
        </p>
      </header>
      <div className="lean-landing">
        <section className="lean-start" aria-labelledby="lean-start">
          <h2 id="lean-start">Start here</h2>
          <ul>
            {main && (
              <Start href={declHref(main)} name={main.short} title="The main theorem">
                {stated(shell, main.name)}, in <code>SKSupport/Main.lean</code>.
              </Start>
            )}
            {minimizer && (
              <Start href={declHref(minimizer)} name={minimizer.short} title="Its hypothesis">
                {shell.terms.get(minimizer.name) ? <Prose text={shell.terms.get(minimizer.name)!.words} /> : "What it assumes of the order parameter."}
              </Start>
            )}
            {value && (
              <Start href={declHref(value)} name={value.short} title="The second main theorem">
                {stated(shell, value.name)}, in <code>SKValue/Main.lean</code>.
              </Start>
            )}
            <Start href={routeHref({ view: "lean", module: CHALLENGE_FILE })} name="SKFullSupport.lean" title="The Comparator challenge file">
              {FOLDER_WORDS.ComparatorChallenges} The other is{" "}
              <a href={routeHref({ view: "lean", module: VALUE_CHALLENGE_FILE })}>
                <code>SKValue.lean</code>
              </a>
              .
            </Start>
            <Start href={routeHref({ view: "lean", index: "papers" })} title={`The ${count(resting)} declarations the papers rest on`}>
              Each with the step that links it and where the papers state it.
            </Start>
          </ul>
        </section>
        <section className="lean-landing__main" aria-label="The main theorem">
          {main && <LeanBlock name={main.name} module={main.module} noDependencies noPapers noTerms previewSlot={slot} />}
        </section>
      </div>
      <HowToRead />
      <Folders shell={shell} />
    </>
  );
}

// ------------------------------------------------------------------ the tree

/** The folders last open, which a new entry starts from; Back keeps each entry's own. */
let foldersOpen: string[] = [];

function TreeNav({ shell, current, landing, index, folder }: { shell: LeanShell; current?: string; landing: boolean; index: boolean; folder?: string }) {
  const folders = shell.modules.folders;
  const currentFolder = folder ?? (current ? folders.find((f) => f.modules.some((m) => m.module === current))?.path : undefined);
  const [list, setList] = useEntryState<string[]>("lean-folders", foldersOpen);
  const setOpen = (next: string[]) => {
    foldersOpen = next;
    setList(next);
  };
  const open = new Set(list);
  useEffect(() => {
    if (currentFolder && !open.has(currentFolder)) setOpen([...list, currentFolder]);
    // Only arriving somewhere new opens a folder; closing the current one stays closed.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [currentFolder]);
  return (
    <nav className="lean-tree" aria-label="Folders and modules">
      <a className={`lean-tree__main${landing ? " is-current" : ""}`} href={routeHref({ view: "lean" })} aria-current={landing ? "page" : undefined}>
        Start here
      </a>
      <a className={`lean-tree__main${index ? " is-current" : ""}`} href={routeHref({ view: "lean", index: "papers" })} aria-current={index ? "page" : undefined}>
        The {count(shell.linked.size)} declarations the papers rest on
      </a>
      <p className="lean-tree__key">
        <span>Folders and modules</span>
        <span>Declarations</span>
      </p>
      <ul>
        {folders.map((entry) => {
          const isOpen = open.has(entry.path);
          const total = entry.modules.reduce((sum, m) => sum + m.declarations, 0);
          return (
            <li key={entry.path}>
              <button
                type="button"
                className="lean-tree__folder"
                aria-expanded={isOpen}
                onClick={() => setOpen(isOpen ? list.filter((path) => path !== entry.path) : [...list, entry.path])}
              >
                <span>{folderLabel(entry.path)}</span>
                <span className="lean-tree__n">{count(total)}</span>
              </button>
              {isOpen && (
                <ul>
                  {entry.modules.map((row) => (
                    <li key={row.module}>
                      <a className={`lean-tree__module${row.module === current ? " is-current" : ""}`} href={routeHref({ view: "lean", module: row.module })} aria-current={row.module === current ? "page" : undefined}>
                        <span>{lastPart(row.module)}</span>
                        <span className="lean-tree__n">{count(row.declarations)}</span>
                      </a>
                    </li>
                  ))}
                </ul>
              )}
            </li>
          );
        })}
      </ul>
    </nav>
  );
}

// ---------------------------------------------------------------- the find box

const FILTER_LIMIT = 80;

function NameFilter({ shell, children }: { shell: LeanShell; children: ReactNode }) {
  const uid = useId();
  const input = useRef<HTMLInputElement>(null);
  const [query, setQuery] = useState("");
  const [active, setActive] = useState(0);
  const result = useMemo(() => (query.trim() ? rankNames(shell.index.rows, shell.index.lower, query, FILTER_LIMIT, (name) => shell.linked.has(name)) : null), [shell, query]);
  useEffect(() => setActive(0), [query]);
  const at = result ? Math.min(active, Math.max(0, result.rows.length - 1)) : 0;
  useEffect(() => {
    document.getElementById(`${uid}-${at}`)?.scrollIntoView({ block: "nearest" });
  }, [uid, at]);
  const open = (row: DeclRow) => {
    setQuery("");
    input.current?.blur();
    navigate(declHref(row));
  };
  return (
    <>
      <label className="lean-filter">
        <span>Find a declaration by name</span>
        <input
          ref={input}
          type="search"
          role="combobox"
          aria-expanded={Boolean(result?.rows.length)}
          aria-controls={`${uid}-list`}
          aria-activedescendant={result?.rows.length ? `${uid}-${at}` : undefined}
          aria-autocomplete="list"
          value={query}
          placeholder={`${count(shell.modules.counts.declarations)} names`}
          autoComplete="off"
          spellCheck={false}
          onChange={(event) => setQuery(event.target.value)}
          onKeyDown={(event) => {
            if (event.key === "Escape") setQuery("");
            if (!result?.rows.length) return;
            if (event.key === "Enter") {
              event.preventDefault();
              open(result.rows[at]);
            } else if (event.key === "ArrowDown" || event.key === "ArrowUp") {
              event.preventDefault();
              const step = event.key === "ArrowDown" ? 1 : -1;
              setActive((at + step + result.rows.length) % result.rows.length);
            }
          }}
        />
      </label>
      {result ? (
        <div className="lean-hits">
          <p role="status">
            {result.total > FILTER_LIMIT ? `First ${FILTER_LIMIT} of ${count(result.total)} names` : `${count(result.total)} ${result.total === 1 ? "name" : "names"}`}
            {result.total > 0 ? ". Enter opens the first." : ""}
          </p>
          <ul id={`${uid}-list`} role="listbox" aria-label="Declarations">
            {result.rows.map((row, k) => (
              <li key={`${row.module}:${row.name}`} role="option" aria-selected={k === at} id={`${uid}-${k}`} className={k === at ? "is-active" : undefined}>
                <a
                  href={declHref(row)}
                  tabIndex={-1}
                  onClick={(event) => {
                    if (event.metaKey || event.ctrlKey || event.shiftKey) return;
                    event.preventDefault();
                    open(row);
                  }}
                >
                  {shell.plain.get(row.name) && <strong>{shell.plain.get(row.name)}</strong>}
                  <code>{row.short}</code>
                  <span>
                    {kindWord(row.kind)} in {row.module.startsWith("Comparator") ? `the challenge file ${lastPart(row.module)}` : lastPart(row.module)}
                  </span>
                </a>
              </li>
            ))}
          </ul>
        </div>
      ) : (
        children
      )}
    </>
  );
}

function ModuleSelect({ shell, current }: { shell: LeanShell; current?: string }) {
  return (
    <label className="lean-select">
      <span>Module</span>
      <select value={current ?? ""} onChange={(event) => navigate(event.target.value ? routeHref({ view: "lean", module: event.target.value }) : routeHref({ view: "lean" }))}>
        <option value="">Start here</option>
        {shell.modules.folders.map((folder) => (
          <optgroup key={folder.path} label={folderLabel(folder.path)}>
            {folder.modules.map((row) => (
              <option key={row.module} value={row.module}>
                {lastPart(row.module)} ({row.declarations})
              </option>
            ))}
          </optgroup>
        ))}
      </select>
    </label>
  );
}

// ---------------------------------------------------------------- way up

function folderOf(shell: LeanShell, module: string): LeanFolder | undefined {
  return shell.modules.folders.find((folder) => folder.modules.some((row) => row.module === module));
}

function Crumbs({ shell, module, folder, here }: { shell: LeanShell; module?: string; folder?: string; here?: string }) {
  const place = folder ?? (module ? folderOf(shell, module)?.path : undefined);
  return (
    <nav className="lean-crumbs" aria-label="Where this is in the tree">
      <a href={routeHref({ view: "lean" })}>Lean index</a>
      {place && (
        <>
          <span aria-hidden="true">/</span>
          {folder && !module ? <span aria-current="page">{folderLabel(place)}</span> : <a href={routeHref({ view: "lean", folder: place })}>{folderLabel(place)}</a>}
        </>
      )}
      {module && (
        <>
          <span aria-hidden="true">/</span>
          {here ? <a href={routeHref({ view: "lean", module })}>{lastPart(module)}</a> : <span aria-current="page">{lastPart(module)}</span>}
        </>
      )}
    </nav>
  );
}

// ------------------------------------------------------------ a declaration's page

/** Where a statement's lines lie in this declaration, for lighting them from its quotation. */
function linesFor(statement: AlignedStatement, name: string): readonly [number, number] | undefined {
  return statement.lean?.find((row) => row.name === name)?.lines;
}

function Quote({ row, name, onPoint }: { row: PaperStatement; name: string; onPoint(lines: readonly [number, number] | undefined): void }) {
  const { statement } = row;
  const lines = linesFor(statement, name);
  return (
    <section className="lean-quote" aria-label={`${PAPER_NAMES[statement.paper].short}, ${statement.section}`} onPointerEnter={() => onPoint(lines)} onPointerLeave={() => onPoint(undefined)}>
      <p className="lean-quote__where">
        <strong>{PAPER_NAMES[statement.paper].short}</strong> {statement.section}
      </p>
      <LazyStatementSlice statement={statement} compact />
      <a className="lean-quote__go" href={statementHref(statement)} onFocus={() => onPoint(lines)} onBlur={() => onPoint(undefined)}>
        Read in context
      </a>
    </section>
  );
}

function RecordRow({ record, recordStatements }: { record: LinkedRecord; recordStatements: PaperStatement[] }) {
  const papers = STAGE_ORDER.flatMap((stage) => recordStatements.find((row) => row.statement.paper === stage) ?? []);
  return (
    <li>
      <a className="lean-records__title" href={routeHref({ view: "map", node: record.id })}>
        {record.title}
      </a>
      <p>
        {RELATION_WORDS[record.relation]}. <Prose text={record.note} />
      </p>
      {papers.length > 0 && (
        <p className="lean-records__papers">
          {papers.map((row, k) => (
            <span key={row.statement.paper}>
              {k > 0 && ", "}
              <a href={statementHref(row.statement)}>
                {k === 0 ? "Read in the " : ""}
                {k === 0 ? PAPER_NAMES[row.statement.paper].short.toLowerCase() : `the ${PAPER_NAMES[row.statement.paper].short.toLowerCase()}`} {sectionPlace(row.statement.section)}
              </a>
            </span>
          ))}
        </p>
      )}
    </li>
  );
}

function Papers({ decl, shell, onPoint }: { decl: LeanDeclaration; shell: LeanShell; onPoint(lines: readonly [number, number] | undefined): void }) {
  const all = shell.statements?.get(decl.name) ?? [];
  const records = shell.linked.get(decl.name) ?? [];
  const first = STAGE_ORDER.flatMap((stage) => all.find((row) => row.statement.paper === stage) ?? []).sort((a, b) => all.indexOf(a) - all.indexOf(b));
  return (
    <section className="lean-decl__papers" aria-labelledby="lean-papers">
      <h2 id="lean-papers">Where the papers state it</h2>
      {first.length === 0 && records.length === 0 && (
        <p className="lean-side__hint">
          No paper states this declaration directly. The papers rest on <a href={routeHref({ view: "lean", index: "papers" })}>{count(shell.linked.size)} declarations</a>, and this one may be used by them.
        </p>
      )}
      {first.map((row) => (
        <Quote key={`${row.statement.paper}:${row.statement.start_byte}`} row={row} name={decl.name} onPoint={onPoint} />
      ))}
      {records.length > 0 && (
        <div className="lean-records">
          <h3>Linked steps</h3>
          <ul>
            {records.map((record, k) => (
              <RecordRow key={`${record.id}:${k}`} record={record} recordStatements={all.filter((row) => row.record === record.id)} />
            ))}
          </ul>
        </div>
      )}
      {(first.length > 0 || records.length > 0) && <p className="lean-block__caveat">{LINK_CAVEAT}</p>}
    </section>
  );
}

function DeclPage({ decl, module, shell, slot }: { decl: LeanDeclaration; module: LeanModule; shell: LeanShell; slot: HTMLElement | null }) {
  const row = findDecl(shell.index, decl.name, module.module);
  const term = shell.terms.get(decl.name);
  const path = shell.paths.get(module.module)?.path ?? module.path;
  const split = useMemo(() => usesOf(decl, module), [decl, module]);
  const [lit, setLit] = useState<readonly [number, number] | undefined>();
  const onPoint = useCallback((lines: readonly [number, number] | undefined) => setLit(lines), []);
  const copies = (shell.index.byName.get(decl.name) ?? []).filter((other) => other.module !== module.module);
  const inChallenge = module.module.startsWith("ComparatorChallenges");
  const plain = shell.plain.get(decl.name);
  return (
    <article className="lean-decl" data-decl={decl.name}>
      <header className="lean-decl__head">
        <Crumbs shell={shell} module={module.module} here={decl.short} />
        <p className="lean-block__kind">{kindWord(decl.kind)}</p>
        <div className="lean-decl__title">
          {plain ? (
            <h1 className="is-plain">{plain}</h1>
          ) : (
            <h1>
              <Breakable name={decl.short} />
            </h1>
          )}
          {term?.tex && <Notation term={term} />}
          <p className="lean-block__actions">
            <SourceLink decl={decl} module={module} shell={shell} />
            <CopyName name={decl.name} />
          </p>
        </div>
        <p className="lean-decl__full">
          <code>{decl.name}</code>
          <span>
            {" "}
            <PathText path={path} />, lines {decl.line} to {decl.end_line}
          </span>
        </p>
        {term && <p className="lean-decl__words"><Prose text={term.words} /></p>}
        {copies.map((copy) => (
          <p className="lean-decl__copy" key={copy.module}>
            {inChallenge ? (
              <>
                This is the copy in a Comparator challenge file. <a href={declHref(copy)}>See it in the proof tree</a>.
              </>
            ) : (
              <>
                A copy stands in the Comparator challenge file <a href={declHref(copy)}>{lastPart(copy.module)}.lean</a>.
              </>
            )}
          </p>
        ))}
      </header>
      <div className="lean-decl__pair">
        <Papers decl={decl} shell={shell} onPoint={onPoint} />
        <section className="lean-decl__lean" aria-label="The Lean">
          <h2>The Lean</h2>
          <LeanBlock name={decl.name} module={module.module} noHead noPapers noDependencies pointed={lit} previewSlot={slot} />
        </section>
      </div>
      {row && <Neighbourhood key={decl.name} decl={decl} module={module} shell={shell} split={split} />}
    </article>
  );
}

// ------------------------------------------------------------------ module and folder

const Rows = memo(function Rows({ module, shell, slot }: { module: LeanModule; shell: LeanShell; slot: HTMLElement | null }) {
  return (
    <>
      {module.declarations.map((decl, k) => (
        <div key={`${decl.name}:${decl.line}`} id={`lean-d-${k}`} data-decl={decl.name}>
          <DeclView decl={decl} module={module} shell={shell} noDependencies noTerms noPapers previewSlot={slot} row={{ href: routeHref({ view: "lean", module: module.module, decl: decl.name }) }} />
        </div>
      ))}
    </>
  );
});

function ModuleView({ module, shell, slot, scroller }: { module: LeanModule; shell: LeanShell; slot: HTMLElement | null; scroller: React.RefObject<HTMLDivElement | null> }) {
  const row = shell.paths.get(module.module);
  const imports = module.imports.filter((name) => shell.paths.has(name));
  useEffect(() => {
    if (arrivedBy() === "push") scroller.current?.scrollTo(0, 0);
  }, [module.module, scroller]);
  return (
    <>
      <header className="lean-modhead">
        <Crumbs shell={shell} module={module.module} />
        <h1>
          <PathText path={module.path} />
        </h1>
        <p>
          {count(module.declarations.length)} declarations in {count(row?.lines ?? 0)} lines, in source order, with each proof on the declaration's own page.
          {module.module.startsWith("ComparatorChallenges") ? ` ${FOLDER_WORDS.ComparatorChallenges}` : ""}
        </p>
        <ModuleViews module={module.module} file={false} />
        {imports.length > 0 && (
          <p className="lean-modhead__imports">
            Imports{" "}
            {imports.map((name, k) => (
              <span key={name}>
                {k > 0 && ", "}
                <a href={routeHref({ view: "lean", module: name })}>
                  <code>{lastPart(name)}</code>
                </a>
              </span>
            ))}
          </p>
        )}
      </header>
      <Rows module={module} shell={shell} slot={slot} />
    </>
  );
}

function ModuleViews({ module, file }: { module: string; file: boolean }) {
  return (
    <nav className="lean-views" aria-label="How to read this module">
      <a href={routeHref({ view: "lean", module })} aria-current={file ? undefined : "page"} onClick={replaceClick}>
        Declarations
      </a>
      <a href={routeHref({ view: "lean", module, file: "all" })} aria-current={file ? "page" : undefined} onClick={replaceClick}>
        Whole file
      </a>
    </nav>
  );
}

/** A tab keeps the entry: choosing how to read a module is a refinement of the same place. */
function replaceClick(event: React.MouseEvent<HTMLAnchorElement>) {
  if (event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
  event.preventDefault();
  const url = new URL(event.currentTarget.href);
  navigate(url.pathname + url.search, { replace: true });
}

/** A declaration's lines, or the source between them, each read with what it can resolve. */
function buildFile(module: LeanModule, shell: LeanShell): BuiltCode {
  const lines = sourceLines(module);
  const code: BuiltCode = { lines: [], targets: [], marked: false };
  const add = (built: BuiltCode) => {
    const base = code.targets.length;
    code.targets.push(...built.targets);
    for (const line of built.lines) code.lines.push({ ...line, parts: line.parts.map((part) => (part.target === undefined ? part : { ...part, target: part.target + base })) });
  };
  const decls = [...module.declarations].sort((a, b) => a.line - b.line);
  const empty = decls[0] && makeScope({ ...decls[0], uses: [], name: "" }, module, shell.index, shell.terms);
  const plain = (first: number, last: number) => {
    if (first > last) return;
    add(buildCode(tokenize(lines.slice(first - 1, last).join("\n"), { signature: false }), first, empty ?? makeScope(module.declarations[0], module, shell.index, shell.terms)));
  };
  let at = 1;
  for (const decl of decls) {
    if (decl.line < at) continue;
    plain(at, decl.line - 1);
    const scope = makeScope(decl, module, shell.index, shell.terms);
    const tail = Math.min(decl.signature_end_line, decl.end_line);
    const head = tokenize(lines.slice(decl.line - 1, tail).join("\n"));
    collectLocals(head, scope.locals);
    add(buildCode(head, decl.line, scope));
    if (decl.end_line > tail) {
      const body = tokenize(lines.slice(tail, decl.end_line).join("\n"), { signature: false });
      collectLocals(body, scope.locals);
      add(buildCode(body, tail + 1, scope));
    }
    at = decl.end_line + 1;
  }
  if (decls.length) plain(at, lines.length);
  else code.lines = lines.map((text, k) => ({ n: k + 1, indent: 0, parts: [{ text, className: "" }] }));
  return code;
}

function FileView({ module, shell, slot, file, scroller }: { module: LeanModule; shell: LeanShell; slot: HTMLElement | null; file: string; scroller: React.RefObject<HTMLDivElement | null> }) {
  const code = useMemo(() => buildFile(module, shell), [module, shell]);
  const range = /^(\d+)(?:-(\d+))?$/.exec(file);
  const first = range ? Number(range[1]) : 0;
  const last = range ? Number(range[2] ?? range[1]) : 0;
  const lit = useCallback((line: number) => line >= first && line <= last, [first, last]);
  const store = useMemo(readingStore, []);
  const read = useCallback((target: NameTarget | null, element: HTMLElement | null) => (target && element ? store.read({ target, shell }) : store.clear()), [store, shell]);
  const open = useCallback(() => undefined, []);
  const path = shell.paths.get(module.module)?.path ?? module.path;
  useEffect(() => {
    if (arrivedBy() !== "push") return;
    const host = scroller.current;
    const line = first ? host?.querySelector<HTMLElement>(`[data-line="${first}"]`) : null;
    if (!host) return;
    if (!line) return host.scrollTo(0, 0);
    host.scrollTop += line.getBoundingClientRect().top - host.getBoundingClientRect().top - 72;
  }, [first, module.module, scroller]);
  return (
    <>
      <header className="lean-modhead">
        <Crumbs shell={shell} module={module.module} />
        <h1>
          <PathText path={path} />
        </h1>
        <p>
          The whole file, {count(shell.paths.get(module.module)?.lines ?? code.lines.length)} lines, at commit {shell.modules.revision.slice(0, 7)} of OpenAI's repository.
        </p>
        <ModuleViews module={module.module} file />
      </header>
      <CodeView code={code} label={`The whole of ${path}. Tab reaches a name; the arrow keys move between names.`} onRead={read} onOpen={open} lit={range ? lit : undefined} />
      <ReadingFoot store={store} slot={slot} />
    </>
  );
}

function FolderView({ shell, path }: { shell: LeanShell; path: string }) {
  const folder = shell.modules.folders.find((entry) => entry.path === path);
  if (!folder) return <p className="lean-note">No folder at this address.</p>;
  return (
    <>
      <header className="lean-modhead">
        <Crumbs shell={shell} folder={path} />
        <h1>
          <PathText path={path} />
        </h1>
        <p>
          {count(folder.modules.length)} modules. {FOLDER_WORDS[path] ?? ""}
        </p>
      </header>
      <ul className="lean-modules">
        {folder.modules.map((row) => (
          <li key={row.module}>
            <a href={routeHref({ view: "lean", module: row.module })}>
              <code>{lastPart(row.module)}</code>
              <span>
                {count(row.declarations)} declarations, {count(row.lines)} lines
              </span>
            </a>
          </li>
        ))}
      </ul>
    </>
  );
}

// ---------------------------------------------------------------- the papers' declarations

interface Resting {
  row: DeclRow;
  records: LinkedRecord[];
}

function restingGroups(shell: LeanShell): { folder: string; rows: Resting[] }[] {
  const groups = new Map<string, Resting[]>();
  for (const [name, records] of shell.linked) {
    const row = findDecl(shell.index, name);
    if (!row) continue;
    const folder = folderOf(shell, row.module)?.path ?? "";
    const rows = groups.get(folder);
    if (rows) rows.push({ row, records });
    else groups.set(folder, [{ row, records }]);
  }
  const order = shell.modules.folders.map((folder) => folder.path);
  return [...groups]
    .sort((a, b) => order.indexOf(a[0]) - order.indexOf(b[0]))
    .map(([folder, rows]) => ({ folder, rows: rows.sort((a, b) => a.row.module.localeCompare(b.row.module) || a.row.line - b.row.line) }));
}

function PapersIndex({ shell }: { shell: LeanShell }) {
  const groups = useMemo(() => restingGroups(shell), [shell]);
  return (
    <>
      <header className="lean-modhead">
        <Crumbs shell={shell} />
        <h1>The {count(shell.linked.size)} declarations the papers rest on</h1>
        <p>Each declaration a step of the argument links to, by folder, with where the papers state it. {LINK_CAVEAT}</p>
      </header>
      {groups.map(({ folder, rows }) => (
        <section className="lean-rest" key={folder} aria-label={folderLabel(folder)}>
          <h2>{folderLabel(folder)}</h2>
          <ul>
            {rows.map(({ row, records }) => {
              const statements = shell.statements?.get(row.name) ?? [];
              const papers = STAGE_ORDER.flatMap((stage) => statements.find((s) => s.statement.paper === stage) ?? []);
              return (
                <li key={`${row.module}:${row.name}`}>
                  <a className="lean-rest__name" href={declHref(row)}>
                    {shell.plain.get(row.name) && <strong>{shell.plain.get(row.name)}</strong>}
                    <Breakable name={row.short} />
                    <span>{kindWord(row.kind)}</span>
                  </a>
                  <span className="lean-rest__record">
                    <a href={routeHref({ view: "map", node: records[0].id })}>{records[0].title}</a>
                    {records.length > 1 ? ` and ${records.length - 1} more` : ""}
                  </span>
                  <span className="lean-rest__papers">
                    {papers.map((paper, k) => (
                      <span key={paper.statement.paper}>
                        {k > 0 && ", "}
                        <a href={statementHref(paper.statement)}>
                          {PAPER_NAMES[paper.statement.paper].short} {sectionPlace(paper.statement.section)}
                        </a>
                      </span>
                    ))}
                  </span>
                </li>
              );
            })}
          </ul>
        </section>
      ))}
    </>
  );
}

// ---------------------------------------------------------------------------- page

function Message({ children }: { children: ReactNode }) {
  return (
    <div className="lean-page lean-page--message">
      <p>{children}</p>
    </div>
  );
}

/** One quiet line for an address that names something this source does not hold. */
function missingWords(route: Extract<Route, { view: "lean" }>, hasDecl: boolean, hasModule: boolean, hasFolder: boolean): ReactNode {
  if (route.decl && !hasDecl) return <>No declaration named <code>{route.decl}</code> in this source{hasModule ? ". Here is the module." : ". Here is the index."}</>;
  if (route.module && !hasModule && !hasDecl) return <>No module named <code>{route.module}</code> in this source. Here is the index.</>;
  if (route.folder && !hasFolder) return <>No folder named <code>{route.folder}</code> in this source. Here is the index.</>;
  return null;
}

export function LeanPage({ route }: { route: Extract<Route, { view: "lean" }> }) {
  const state = useLeanShell();
  const shell = state.status === "ready" ? state.shell : null;
  // An address can name anything. Only what the index holds is shown, or named in the tab.
  const knownModule = shell && route.module && shell.paths.has(route.module) ? route.module : undefined;
  const knownFolder = shell?.modules.folders.some((folder) => folder.path === route.folder) ? route.folder : undefined;
  const row = shell && route.decl ? findDecl(shell.index, route.decl, knownModule) : undefined;
  const unknown = !shell ? null : missingWords(route, Boolean(row), Boolean(knownModule), Boolean(knownFolder));
  const opensHome = !route.index && !knownFolder && !row && !knownModule;
  const landing = opensHome;
  const mainRow = shell && landing ? findDecl(shell.index, MAIN_THEOREM) : undefined;
  const moduleName = row?.module ?? knownModule ?? mainRow?.module;
  const loaded = useLeanModule(moduleName);
  const hasTree = useMedia("(min-width: 760px)");
  const scroller = useRef<HTMLDivElement>(null);
  const slot = useBarLine();

  const module = loaded.status === "ready" ? loaded.module : undefined;
  const decl = module && row ? declIn(module, row.name) : undefined;

  useEffect(
    () =>
      namePlace(() => {
        if (decl) return shell?.plain.get(decl.name) ?? decl.short;
        if (knownModule) return lastPart(knownModule);
        if (knownFolder) return folderLabel(knownFolder);
        if (route.index) return "the declarations the papers rest on";
        return "the Lean index";
      }),
    [decl, knownModule, knownFolder, route.index, shell],
  );

  // PageTitle cannot see the index, so the page names its tab, and only by what exists.
  const tabTitle = decl ? (shell?.plain.get(decl.name) ?? decl.short) : knownModule ? lastPart(knownModule) : knownFolder ? folderLabel(knownFolder) : null;
  useEffect(() => {
    document.title = tabTitle ? `${tabTitle} · Lean Exposition` : "Lean index · Lean Exposition";
  }, [tabTitle]);

  // A new declaration starts at its head, unless Back is restoring a place.
  useEffect(() => {
    if (decl && arrivedBy() === "push") scroller.current?.scrollTo(0, 0);
  }, [decl]);

  if (state.status === "missing") return <Message>This edition does not include the Lean source.</Message>;
  if (!shell) return <Message>Loading the Lean source</Message>;

  let main: ReactNode;
  if (route.index) main = <PapersIndex shell={shell} />;
  else if (knownFolder && !knownModule) main = <FolderView shell={shell} path={knownFolder} />;
  else if (landing) main = <Landing shell={shell} slot={slot} />;
  else if (route.file && module && knownModule) main = <FileView module={module} shell={shell} slot={slot} file={route.file} scroller={scroller} />;
  else if (decl && module) main = <DeclPage decl={decl} module={module} shell={shell} slot={slot} />;
  else if (module) main = <ModuleView module={module} shell={shell} slot={slot} scroller={scroller} />;
  else if (loaded.status === "failed") main = <p className="lean-note">This module could not be loaded.</p>;
  else main = <p className="lean-note">Loading the module</p>;

  return (
    <div className="lean-page">
      {hasTree ? (
        <aside className="lean-left">
          <NameFilter shell={shell}>
            <TreeNav shell={shell} current={module?.module && !landing ? module.module : undefined} landing={landing} index={Boolean(route.index)} folder={knownFolder} />
          </NameFilter>
        </aside>
      ) : (
        <div className="lean-top">
          <ModuleSelect shell={shell} current={route.module} />
          <NameFilter shell={shell}>{null}</NameFilter>
        </div>
      )}
      <div className="lean-centre">
        <div className="lean-scroll" ref={scroller} tabIndex={-1}>
          {unknown && <p className="lean-address" role="status">{unknown}</p>}
          {main}
        </div>
      </div>
    </div>
  );
}

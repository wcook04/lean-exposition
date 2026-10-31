// The Lean source as a Lean user reads it. Every declaration has its own page and address:
// where the papers state it, then the Lean, then what it uses and what uses it. A module page
// lists its declarations in source order, a folder page its modules, and the first screen says
// what this tree is, what has been checked and where to begin.

import { memo, useCallback, useEffect, useId, useMemo, useRef, useState, type ReactNode } from "react";
import type { AlignedStatement, LeanDeclaration, LeanFolder, LeanModule } from "../api/lean";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { navigate, routeHref, type Route } from "../app/router";
import { namePlace } from "../app/trail";
import { useCheckedWords } from "./checked";
import { LazyStatementSlice } from "../compare/lazy";
import { statementHref } from "../reader/links";
import { CHALLENGE_FILE, declIn, kindWord, LINK_CAVEAT, MAIN_THEOREM, MINIMIZER, RELATION_WORDS, sectionPlace, useLeanModule, useLeanShell, VALUE_CHALLENGE_FILE, VALUE_THEOREM, type LeanShell, type LinkedRecord, type PaperStatement } from "./data";
import { rankNames } from "./find";
import { folderLabel, FOLDER_WORDS } from "./folders";
import { CopyName, DeclView, LeanBlock, SourceLink, usesOf } from "./LeanBlock";
import "./lean.css";
import { Neighbourhood } from "./Neighbourhood";
import { Breakable, Notation, PathText, Prose } from "./ReadingStrip";
import { findDecl, type DeclRow } from "./resolve";

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

function Start({ href, name, title, children }: { href: string; name: string; title: string; children: ReactNode }) {
  return (
    <li>
      <a href={href}>
        <code>{name}</code>
        <span className="lean-start__what">{title}</span>
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
        <h1>OpenAI's Lean source</h1>
        <p>
          This is OpenAI's Lean, unchanged, at commit{" "}
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
                {shell.linked.get(main.name)?.[0]?.title ?? "The full support theorem"}, in <code>SKSupport/Main.lean</code>.
              </Start>
            )}
            {minimizer && (
              <Start href={declHref(minimizer)} name={minimizer.short} title="Its hypothesis">
                {shell.terms.get(minimizer.name) ? <Prose text={shell.terms.get(minimizer.name)!.words} /> : "What it assumes of the order parameter."}
              </Start>
            )}
            {value && (
              <Start href={declHref(value)} name={value.short} title="The second main theorem">
                {shell.linked.get(value.name)?.[0]?.title ?? "The value result"}, in <code>SKValue/Main.lean</code>.
              </Start>
            )}
            <Start href={routeHref({ view: "lean", module: CHALLENGE_FILE })} name="SKFullSupport.lean" title="The Comparator challenge file">
              {FOLDER_WORDS.ComparatorChallenges} The other is{" "}
              <a href={routeHref({ view: "lean", module: VALUE_CHALLENGE_FILE })}>
                <code>SKValue.lean</code>
              </a>
              .
            </Start>
            <Start href={routeHref({ view: "lean", index: "papers" })} name={`The ${count(resting)} declarations the papers rest on`} title="">
              Each with the record that links it and where the papers state it.
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

function TreeNav({ shell, current, landing, index, folder }: { shell: LeanShell; current?: string; landing: boolean; index: boolean; folder?: string }) {
  const folders = shell.modules.folders;
  const currentFolder = folder ?? (current ? folders.find((f) => f.modules.some((m) => m.module === current))?.path : undefined);
  const [open, setOpen] = useState<Set<string>>(new Set(currentFolder ? [currentFolder] : []));
  useEffect(() => {
    if (currentFolder) setOpen((was) => (was.has(currentFolder) ? was : new Set(was).add(currentFolder)));
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
                onClick={() =>
                  setOpen((was) => {
                    const next = new Set(was);
                    if (!next.delete(entry.path)) next.add(entry.path);
                    return next;
                  })
                }
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
      <a href={routeHref({ view: "lean" })}>Lean source</a>
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
          <h3>Linked records</h3>
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
  return (
    <article className="lean-decl" data-decl={decl.name}>
      <header className="lean-decl__head">
        <Crumbs shell={shell} module={module.module} here={decl.short} />
        <p className="lean-block__kind">{kindWord(decl.kind)}</p>
        <div className="lean-decl__title">
          <h1>
            <Breakable name={decl.short} />
          </h1>
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
          <LeanBlock name={decl.name} module={module.module} noHead noPapers noDependencies lines={lit} previewSlot={slot} />
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
    scroller.current?.scrollTo(0, 0);
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
        <p>Each declaration a record of the argument links to, by folder, with where the papers state it. {LINK_CAVEAT}</p>
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

export function LeanPage({ route }: { route: Extract<Route, { view: "lean" }> }) {
  const state = useLeanShell();
  const shell = state.status === "ready" ? state.shell : null;
  const landing = !route.module && !route.decl && !route.folder && !route.index;
  const row = shell && !route.module && route.decl ? findDecl(shell.index, route.decl) : undefined;
  const mainRow = shell && landing ? findDecl(shell.index, MAIN_THEOREM) : undefined;
  const moduleName = route.module ?? row?.module ?? mainRow?.module;
  const loaded = useLeanModule(moduleName);
  const hasTree = useMedia("(min-width: 760px)");
  const scroller = useRef<HTMLDivElement>(null);
  const [slot, setSlot] = useState<HTMLElement | null>(null);

  const module = loaded.status === "ready" ? loaded.module : undefined;
  const decl = module && route.decl ? declIn(module, route.decl) : undefined;

  useEffect(
    () =>
      namePlace(() => {
        if (decl) return decl.short;
        if (route.module) return lastPart(route.module);
        if (route.folder) return folderLabel(route.folder);
        if (route.index) return "the declarations the papers rest on";
        return "the Lean source";
      }),
    [decl, route.module, route.folder, route.index],
  );

  // A new declaration starts at its head, unless Back is restoring a place.
  useEffect(() => {
    if (decl && !history.state?.lxEntry?.scroll) scroller.current?.scrollTo(0, 0);
  }, [decl]);

  if (state.status === "missing") return <Message>This edition does not include the Lean source.</Message>;
  if (!shell) return <Message>Loading the Lean source</Message>;

  let main: ReactNode;
  if (route.index) main = <PapersIndex shell={shell} />;
  else if (route.folder && !route.module) main = <FolderView shell={shell} path={route.folder} />;
  else if (landing) main = <Landing shell={shell} slot={slot} />;
  else if (route.decl && decl && module) main = <DeclPage decl={decl} module={module} shell={shell} slot={slot} />;
  else if (route.decl && module) main = <p className="lean-note">No declaration named <code>{route.decl}</code> in {module.module}.</p>;
  else if (module) main = <ModuleView module={module} shell={shell} slot={slot} scroller={scroller} />;
  else if (loaded.status === "failed") main = <p className="lean-note">This module could not be loaded.</p>;
  else main = <p className="lean-note">Loading the module</p>;

  const hasCode = !route.index && !(route.folder && !route.module);
  return (
    <div className="lean-page">
      {hasTree ? (
        <aside className="lean-left">
          <NameFilter shell={shell}>
            <TreeNav shell={shell} current={module?.module && !landing ? module.module : undefined} landing={landing} index={Boolean(route.index)} folder={route.folder} />
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
          {main}
        </div>
        {hasCode && <div className="lean-slot lean-slot--page" ref={setSlot} />}
      </div>
    </div>
  );
}

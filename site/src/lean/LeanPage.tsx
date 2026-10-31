import { memo, useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { LeanDeclaration, LeanFolder, LeanModule } from "../api/lean";
import { navigate, routeHref, type Route } from "../app/router";
import { declIn, kindWord, LINK_CAVEAT, MAIN_THEOREM, RELATION_WORDS, useLeanModule, useLeanShell, type LeanShell } from "./data";
import { folderLabel, FOLDER_WORDS } from "./folders";
import { DeclView, LeanBlock, SharedStrip, Terms, useStatementTargets } from "./LeanBlock";
import "./lean.css";
import { Neighbourhood } from "./Neighbourhood";
import { PathText, Prose, StripBody } from "./ReadingStrip";
import { findDecl, type DeclRow, type NameTarget } from "./resolve";

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

function folderHref(folder: LeanFolder): string {
  return routeHref({ view: "lean", module: folder.modules[0].module });
}

function Folders({ shell }: { shell: LeanShell }) {
  return (
    <section className="lean-folders" aria-labelledby="lean-folders">
      <h2 id="lean-folders">What each folder holds</h2>
      <ul>
        {shell.modules.folders.map((folder) => (
          <li key={folder.path}>
            <a href={folderHref(folder)}>{folderLabel(folder.path)}</a>
            <span className="lean-folders__count">{count(folder.modules.length)} modules</span>
            {FOLDER_WORDS[folder.path] && <p>{FOLDER_WORDS[folder.path]}</p>}
          </li>
        ))}
      </ul>
    </section>
  );
}

function Landing({ shell, wide, main }: { shell: LeanShell; wide: boolean; main?: LeanDeclaration }) {
  const { modules } = shell;
  const row = findDecl(shell.index, MAIN_THEOREM);
  const revisionUrl = modules.base_url.replace(/\/blob\//, "/tree/");
  return (
    <>
      <header className="lean-intro">
        <h1>OpenAI's Lean source for this result</h1>
        <p>
          OpenAI's proof, as written in the Lean language, at revision{" "}
          <a href={revisionUrl} target="_blank" rel="noreferrer">
            {modules.revision.slice(0, 7)}
          </a>
          : {count(modules.counts.modules)} modules holding {count(modules.counts.declarations)} declarations, of which {count(modules.counts.theorem + modules.counts.lemma)} are theorems and lemmas. The main theorem comes first.
        </p>
      </header>
      {row && (
        <LeanBlock
          name={row.name}
          module={row.module}
          noDependencies
          noTerms={wide}
          below={
            main && (
              <>
                {!wide && <Records decl={main} shell={shell} />}
                <Neighbourhood key={main.name} decl={main} module={row.module} shell={shell} />
              </>
            )
          }
        />
      )}
      <HowToRead />
      <Folders shell={shell} />
    </>
  );
}

function Tree({ shell, current, landing }: { shell: LeanShell; current?: string; landing: boolean }) {
  const folders = shell.modules.folders;
  const currentFolder = current ? folders.find((f) => f.modules.some((m) => m.module === current))?.path : undefined;
  const [open, setOpen] = useState<Set<string>>(new Set(currentFolder ? [currentFolder] : []));
  useEffect(() => {
    if (currentFolder) setOpen((was) => (was.has(currentFolder) ? was : new Set(was).add(currentFolder)));
  }, [currentFolder]);
  return (
    <nav className="lean-tree" aria-label="Folders and modules">
      <a className={`lean-tree__main${landing ? " is-current" : ""}`} href={routeHref({ view: "lean" })} aria-current={landing ? "page" : undefined}>
        The main theorem
      </a>
      <p className="lean-tree__key">
        <span>Folders and modules</span>
        <span>Declarations</span>
      </p>
      <ul>
        {folders.map((folder) => {
          const isOpen = open.has(folder.path);
          const total = folder.modules.reduce((sum, m) => sum + m.declarations, 0);
          return (
            <li key={folder.path}>
              <button
                type="button"
                className="lean-tree__folder"
                aria-expanded={isOpen}
                onClick={() =>
                  setOpen((was) => {
                    const next = new Set(was);
                    if (!next.delete(folder.path)) next.add(folder.path);
                    return next;
                  })
                }
              >
                <span>{folderLabel(folder.path)}</span>
                <span className="lean-tree__n">{count(total)}</span>
              </button>
              {isOpen && (
                <ul>
                  {folder.modules.map((row) => (
                    <li key={row.module}>
                      <a className={`lean-tree__module${row.module === current ? " is-current" : ""}`} href={routeHref({ view: "lean", module: row.module })} aria-current={row.module === current ? "page" : undefined}>
                        <span>{row.module.slice(row.module.lastIndexOf(".") + 1)}</span>
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

const FILTER_LIMIT = 80;

function filterNames(shell: LeanShell, query: string): { rows: DeclRow[]; total: number } {
  const parts = query.toLowerCase().split(/\s+/).filter(Boolean);
  const { rows, lower } = shell.index;
  const hits: { row: DeclRow; rank: number }[] = [];
  for (let i = 0; i < rows.length; i++) {
    if (!parts.every((part) => lower[i].includes(part))) continue;
    const short = rows[i].short.toLowerCase();
    hits.push({ row: rows[i], rank: short === parts[0] ? 0 : short.startsWith(parts[0]) ? 1 : short.includes(parts[0]) ? 2 : 3 });
  }
  hits.sort((a, b) => a.rank - b.rank || a.row.short.length - b.row.short.length || a.row.short.localeCompare(b.row.short));
  return { rows: hits.slice(0, FILTER_LIMIT).map((hit) => hit.row), total: hits.length };
}

function NameFilter({ shell, children }: { shell: LeanShell; children: ReactNode }) {
  const [query, setQuery] = useState("");
  const result = useMemo(() => (query.trim() ? filterNames(shell, query) : null), [shell, query]);
  return (
    <>
      <label className="lean-filter">
        <span>Find a declaration by name</span>
        <input
          type="search"
          value={query}
          placeholder={`${count(shell.modules.counts.declarations)} names`}
          autoComplete="off"
          spellCheck={false}
          onChange={(event) => setQuery(event.target.value)}
          onKeyDown={(event) => {
            if (event.key === "Escape") setQuery("");
          }}
        />
      </label>
      {result ? (
        <div className="lean-hits">
          <p role="status">
            {result.total > FILTER_LIMIT ? `First ${FILTER_LIMIT} of ${count(result.total)} names` : `${count(result.total)} ${result.total === 1 ? "name" : "names"}`}
          </p>
          <ul>
            {result.rows.map((row) => (
              <li key={`${row.module}:${row.name}`}>
                <a href={routeHref({ view: "lean", module: row.module, decl: row.name })}>
                  <code>{row.short}</code>
                  <span>
                    {kindWord(row.kind)} in {row.module.slice(row.module.lastIndexOf(".") + 1)}
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
        <option value="">The main theorem</option>
        {shell.modules.folders.map((folder) => (
          <optgroup key={folder.path} label={folderLabel(folder.path)}>
            {folder.modules.map((row) => (
              <option key={row.module} value={row.module}>
                {row.module.slice(row.module.lastIndexOf(".") + 1)} ({row.declarations})
              </option>
            ))}
          </optgroup>
        ))}
      </select>
    </label>
  );
}

function PageStrip({ shell, register }: { shell: LeanShell; register(set: (target: NameTarget) => void): void }) {
  const [target, setTarget] = useState<NameTarget | null>(null);
  useEffect(() => register(setTarget), [register]);
  return (
    <div className="lean-strip lean-strip--page" role="status" aria-label="Reading the name in focus">
      <StripBody target={target} shell={shell} />
    </div>
  );
}

const Rows = memo(function Rows({ module, shell, selected, inline }: { module: LeanModule; shell: LeanShell; selected?: string; inline: boolean }) {
  return (
    <>
      {module.declarations.map((decl, k) => (
        <div key={`${decl.name}:${decl.line}`} id={`lean-d-${k}`} data-decl={decl.name}>
          <DeclView
            decl={decl}
            module={module}
            shell={shell}
            noDependencies
            noTerms={!inline}
            below={
              decl.name === selected ? (
                <>
                  {inline && <Records decl={decl} shell={shell} />}
                  <Neighbourhood key={decl.name} decl={decl} module={module.module} shell={shell} />
                </>
              ) : undefined
            }
            row={{
              href: routeHref({ view: "lean", module: module.module, decl: decl.name }),
              selected: decl.name === selected,
              onSelect: () => navigate(routeHref({ view: "lean", module: module.module, decl: decl.name }), { replace: true }),
            }}
          />
        </div>
      ))}
    </>
  );
});

function ModuleView({ module, shell, selected, inline, scroller }: { module: LeanModule; shell: LeanShell; selected?: string; inline: boolean; scroller: React.RefObject<HTMLDivElement | null> }) {
  const row = shell.paths.get(module.module);
  useEffect(() => {
    if (!selected) {
      scroller.current?.scrollTo(0, 0);
      return;
    }
    const target = scroller.current?.querySelector<HTMLElement>(`[data-decl="${CSS.escape(selected)}"]`);
    if (!target) return;
    const box = target.getBoundingClientRect();
    const view = scroller.current?.getBoundingClientRect();
    if (!view || box.bottom < view.top || box.top > view.top + view.height * 0.6) target.scrollIntoView({ block: "start" });
  }, [module.module, selected, scroller]);
  return (
    <>
      <header className="lean-modhead">
        <h1>
          <PathText path={module.path} />
        </h1>
        <p>
          {count(module.declarations.length)} declarations in {count(row?.lines ?? 0)} lines. Statements are shown in source order, with proofs folded.
        </p>
      </header>
      <Rows module={module} shell={shell} selected={selected} inline={inline} />
    </>
  );
}

function Records({ decl, shell }: { decl: LeanDeclaration; shell: LeanShell }) {
  const records = shell.linked.get(decl.name) ?? [];
  return (
    <section className="lean-records" aria-label="Linked records of the argument">
      <p className="lean-terms__title">Linked records of the argument</p>
      {records.length === 0 ? (
        <p className="lean-side__hint">No record of the argument links to this declaration.</p>
      ) : (
        <>
          <ul>
            {records.map((record, k) => (
              <li key={`${record.id}:${k}`}>
                <a href={routeHref({ view: "compare", node: record.id })}>{record.title}</a>
                <p>
                  {RELATION_WORDS[record.relation]}. <Prose text={record.note} />
                </p>
              </li>
            ))}
          </ul>
          <p className="lean-block__caveat">{LINK_CAVEAT}</p>
        </>
      )}
    </section>
  );
}

function SideNames({ decl, module, shell }: { decl: LeanDeclaration; module: LeanModule; shell: LeanShell }) {
  const targets = useStatementTargets(decl, module, shell);
  return <Terms targets={targets} onOpen={(row) => navigate(routeHref({ view: "lean", module: row.module, decl: row.name }))} />;
}

function Selected({ decl, shell, module }: { decl: LeanDeclaration | undefined; shell: LeanShell; module?: LeanModule }) {
  if (!decl || !module) {
    return <p className="lean-side__hint">Select a declaration to see where the argument uses it and what its names mean.</p>;
  }
  return (
    <>
      <header>
        <p className="lean-block__kind">{kindWord(decl.kind)}</p>
        <h2 className="lean-block__name">
          <code>{decl.short}</code>
        </h2>
        <p className="lean-block__path">
          <PathText path={module.path} />
        </p>
      </header>
      <Records decl={decl} shell={shell} />
      <SideNames decl={decl} module={module} shell={shell} />
    </>
  );
}

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
  const landing = !route.module && !route.decl;
  const row = shell && !route.module ? findDecl(shell.index, route.decl ?? MAIN_THEOREM) : undefined;
  const moduleName = route.module ?? row?.module;
  const loaded = useLeanModule(moduleName);
  const threeZones = useMedia("(min-width: 1180px)");
  const hasTree = useMedia("(min-width: 760px)");
  const scroller = useRef<HTMLDivElement>(null);
  const setStrip = useRef<(target: NameTarget) => void>(() => undefined);
  const stripContext = useMemo(() => (target: NameTarget) => setStrip.current(target), []);
  const register = useMemo(
    () => (set: (target: NameTarget) => void) => {
      setStrip.current = set;
    },
    [],
  );

  if (state.status === "missing") return <Message>This edition does not include the Lean source.</Message>;
  if (!shell) return <Message>Loading the Lean source</Message>;

  const module = loaded.status === "ready" ? loaded.module : undefined;
  const decl = module ? declIn(module, route.decl ?? (landing ? MAIN_THEOREM : "")) : undefined;

  const main = landing ? (
    <Landing shell={shell} wide={threeZones} main={decl} />
  ) : module ? (
    <ModuleView module={module} shell={shell} selected={route.decl} inline={!threeZones} scroller={scroller} />
  ) : loaded.status === "failed" ? (
    <p className="lean-note">This module could not be loaded.</p>
  ) : (
    <p className="lean-note">Loading the module</p>
  );

  return (
    <div className="lean-page">
      {hasTree ? (
        <aside className="lean-left">
          <NameFilter shell={shell}>
            <Tree shell={shell} current={route.module} landing={landing} />
          </NameFilter>
        </aside>
      ) : (
        <div className="lean-top">
          <ModuleSelect shell={shell} current={route.module} />
          <NameFilter shell={shell}>{null}</NameFilter>
        </div>
      )}
      <div className="lean-centre">
        <SharedStrip.Provider value={landing ? null : stripContext}>
          <div className="lean-scroll" ref={scroller} tabIndex={-1}>
            {main}
          </div>
          {!landing && <PageStrip shell={shell} register={register} />}
        </SharedStrip.Provider>
      </div>
      {threeZones && (
        <aside className="lean-side" aria-label="The selected declaration">
          <Selected decl={decl} shell={shell} module={module} />
        </aside>
      )}
    </div>
  );
}

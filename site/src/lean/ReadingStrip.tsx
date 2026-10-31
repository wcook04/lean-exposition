// The one line where a name is read, like an editor's status bar. It lies over the foot of
// the scrolling column, so pointing at a name moves nothing; when idle it is empty and
// invisible. There is one for the whole page, however many blocks are on it, and when the
// name is near the foot it moves to the top of the column so it never covers that name.

import { useEffect, useLayoutEffect, useRef, useState, useSyncExternalStore } from "react";
import { createRoot } from "react-dom/client";
import { texHtml } from "../figures/tex";
import { declIn, fetchModule, kindWord, moduleIfLoaded, sourceLines, type LeanShell } from "./data";
import type { DeclRow, NameTarget } from "./resolve";
import type { DictionaryTerm } from "../api/lean";

/** Prose with the `backticked` names of the source notes set as code. */
export function Prose({ text }: { text: string }) {
  if (!text.includes("`")) return <>{text}</>;
  return <>{text.split("`").map((part, k) => (k % 2 ? <code key={k}>{part}</code> : part))}</>;
}

/** A source path that may break only after a slash. */
export function PathText({ path }: { path: string }) {
  return (
    <>
      {path.split("/").map((part, k, parts) => (
        <span key={k}>
          {part}
          {k < parts.length - 1 && (
            <>
              /<wbr />
            </>
          )}
        </span>
      ))}
    </>
  );
}

/** Notation typeset by KaTeX, or null when there is none to show. */
export function Notation({ term }: { term: DictionaryTerm | undefined }) {
  if (!term?.tex) return null;
  let html: string;
  try {
    html = texHtml(term.tex);
  } catch {
    return null;
  }
  return <span className="lean-notation" dangerouslySetInnerHTML={{ __html: html }} />;
}

function firstSignatureLine(row: DeclRow): string | null {
  const module = moduleIfLoaded(row.module);
  const decl = module && declIn(module, row.name);
  return module && decl ? (sourceLines(module)[decl.line - 1]?.trim() ?? null) : null;
}

/** Fetch the module after a rest of 150ms on a name, then show what arrived. */
function useModuleArrival(module: string | undefined): void {
  const [, refresh] = useState(0);
  useEffect(() => {
    if (!module || moduleIfLoaded(module)) return;
    let alive = true;
    const timer = window.setTimeout(() => {
      fetchModule(module).then(
        () => alive && refresh((n) => n + 1),
        () => undefined,
      );
    }, 150);
    return () => {
      alive = false;
      window.clearTimeout(timer);
    };
  }, [module]);
}

/** A long name may break after a dot or an underscore, and between camel-case words only when a part cannot fit. */
export function Breakable({ name }: { name: string }) {
  return (
    <code className="lean-break">
      {name.split(/(?<=[_.])/).map((part, k) => (
        <span key={k}>
          {part.split(/(?<=[a-z0-9])(?=[A-Z])/).flatMap((word, j) => (j ? [<wbr key={j} />, word] : [word]))}
        </span>
      ))}
    </code>
  );
}

function DeclReading({ row, term, shell }: { row: DeclRow; term?: DictionaryTerm; shell: LeanShell }) {
  useModuleArrival(row.module);
  const file = (shell.paths.get(row.module)?.path ?? row.module).split("/").pop();
  const signature = firstSignatureLine(row);
  return (
    <>
      <Breakable name={row.short} />
      {term?.words ? (
        <span className="lean-bar__words">
          <Notation term={term} />
          <Prose text={term.words} />
        </span>
      ) : (
        <>
          <span className="lean-bar__words lean-bar__words--sig">{signature && <code>{signature}</code>}</span>
          <span className="lean-bar__place">
            {kindWord(row.kind)} in {file}, line {row.line}
          </span>
        </>
      )}
    </>
  );
}

/** What the line says about a name. */
export function ReadingLine({ target, shell }: { target: NameTarget; shell: LeanShell }) {
  if (target.kind === "decl") return <DeclReading row={target.row} term={target.term} shell={shell} />;
  return (
    <>
      <Breakable name={target.name} />
      <span className="lean-bar__words">{target.words ?? "Defined outside OpenAI's source, in Mathlib or Lean's core library."}</span>
      <span className="lean-bar__place">From Mathlib</span>
    </>
  );
}

interface Reading {
  target: NameTarget;
  element: HTMLElement;
  shell: LeanShell;
}

/** Moving from one name to the next passes over nothing, so the line does not blink. */
const LINGER = 140;

let reading: Reading | null = null;
let timer = 0;
const listeners = new Set<() => void>();
const publish = (next: Reading | null) => {
  reading = next;
  listeners.forEach((listen) => listen());
};

export function readName(target: NameTarget, element: HTMLElement, shell: LeanShell): void {
  window.clearTimeout(timer);
  publish({ target, element, shell });
}

export function clearName(): void {
  window.clearTimeout(timer);
  timer = window.setTimeout(() => publish(null), LINGER);
}

/** The column the line belongs to: the name's nearest tall scroller, or else the page. */
function columnOf(element: HTMLElement): HTMLElement | null {
  for (let at = element.parentElement; at && at !== document.body; at = at.parentElement) {
    const { overflowY } = getComputedStyle(at);
    if ((overflowY === "auto" || overflowY === "scroll") && at.clientHeight >= 240) return at;
  }
  return null;
}

/** The line's place: along the column's foot, or its head when the foot would cover the name. */
export function barPlace(column: { left: number; top: number; width: number; bottom: number }, name: { bottom: number }, height: number, gap = 6) {
  const atTop = name.bottom + gap > column.bottom - height;
  return { left: column.left, width: column.width, top: atTop ? column.top : column.bottom - height, edge: atTop ? "top" : "bottom" };
}

function place(bar: HTMLElement, element: HTMLElement): void {
  const column = columnOf(element);
  const box = column?.getBoundingClientRect();
  const head = parseFloat(getComputedStyle(document.documentElement).getPropertyValue("--bar-h")) || 0;
  const frame = column && box
    ? { left: box.left + column.clientLeft, top: Math.max(box.top, 0), width: column.clientWidth, bottom: Math.min(box.top + column.clientTop + column.clientHeight, window.innerHeight) }
    : { left: 0, top: head, width: document.documentElement.clientWidth, bottom: window.innerHeight };
  const at = barPlace(frame, element.getBoundingClientRect(), bar.offsetHeight);
  bar.style.left = `${at.left}px`;
  bar.style.top = `${at.top}px`;
  bar.style.width = `${at.width}px`;
  bar.style.paddingInline = column ? getComputedStyle(column).paddingLeft : "";
  bar.dataset.edge = at.edge;
}

function ReadingBar() {
  const now = useSyncExternalStore(
    (listen) => {
      listeners.add(listen);
      return () => listeners.delete(listen);
    },
    () => reading,
  );
  const bar = useRef<HTMLDivElement>(null);
  useLayoutEffect(() => {
    const node = bar.current;
    if (!node || !now) return;
    const again = () => {
      if (now.element.isConnected) place(node, now.element);
    };
    again();
    window.addEventListener("scroll", again, { capture: true, passive: true });
    window.addEventListener("resize", again);
    const watcher = new ResizeObserver(again);
    watcher.observe(node);
    return () => {
      window.removeEventListener("scroll", again, { capture: true });
      window.removeEventListener("resize", again);
      watcher.disconnect();
    };
  }, [now]);
  return (
    <div className={`lean-bar${now ? " is-on" : ""}`} ref={bar} role="status" aria-label="The name being read">
      <div className="lean-bar__line">{now && <ReadingLine target={now.target} shell={now.shell} />}</div>
    </div>
  );
}

let mounted = false;

/** Put the one line on the page, ready and empty, the first time any code appears. */
export function ensureReadingBar(): void {
  if (mounted) return;
  mounted = true;
  const host = document.createElement("div");
  document.body.append(host);
  createRoot(host).render(<ReadingBar />);
}

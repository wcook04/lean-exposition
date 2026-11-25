// The line where a name is read, like an editor's status bar: signature, docstring and the
// paper's notation for the name under the pointer or keyboard focus. It sits in a row of its
// own at the foot of the block, or in a slot its host gives it, and that row keeps its height
// whether or not a name is being read. So pointing moves nothing and covers nothing.

import site from "@instance/site";
import { useEffect, useId, useLayoutEffect, useMemo, useRef, useState, useSyncExternalStore } from "react";
import { createPortal } from "react-dom";
import { texHtml } from "../figures/tex";
import { compiled, declIn, docLine, fetchModule, kindWord, moduleIfLoaded, signatureText, type LeanShell } from "./data";
import type { DeclRow, NameTarget } from "./resolve";
import type { DictionaryTerm } from "../api/lean";

/** Prose with the `backticked` names of the source notes set as code and $inline$ formulas typeset. */
export function Prose({ text }: { text: string }) {
  if (!text.includes("`") && !text.includes("$")) return <>{text}</>;
  return <>{text.split("`").map((part, k) => (k % 2 ? <code key={k}>{part}</code> : <Maths key={k} text={part} />))}</>;
}

/** Text with $inline$ formulas typeset by KaTeX; a formula KaTeX cannot read stays as its source. */
function Maths({ text }: { text: string }) {
  if (!text.includes("$")) return <>{text}</>;
  const parts = text.split(/(?<!\\)\$/);
  if (parts.length % 2 === 0) return <>{text}</>;
  return (
    <>
      {parts.map((part, k) => {
        if (k % 2 === 0) return part.replace(/\\\$/g, "$");
        try {
          return <span key={k} className="tex" dangerouslySetInnerHTML={{ __html: texHtml(part) }} />;
        } catch {
          return `$${part}$`;
        }
      })}
    </>
  );
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

/** What is known of a declaration once its module is here. */
function factsOf(row: DeclRow) {
  const module = moduleIfLoaded(row.module);
  const decl = module && declIn(module, row.name);
  if (!module || !decl) return null;
  const facts = compiled(decl);
  return { signature: facts.type ? `${row.short} : ${facts.type}` : signatureText(module, decl), doc: docLine(decl.doc), printed: Boolean(facts.type) };
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
  const facts = factsOf(row);
  const words = term?.words ?? facts?.doc;
  return (
    <>
      <p className="lean-read__top">
        <Breakable name={row.short} />
        <Notation term={term} />
        <span className="lean-read__place">
          {kindWord(row.kind)} in {file}, line {row.line}
          {facts?.printed ? ", as Lean prints it" : ""}
        </span>
      </p>
      {words && (
        <p className="lean-read__words">
          <Prose text={words} />
        </p>
      )}
      <code className="lean-read__sig">{facts?.signature ?? " "}</code>
    </>
  );
}

/** What the line says about a name. */
export function ReadingLine({ target, shell }: { target: NameTarget; shell: LeanShell }) {
  if (target.kind === "decl") return <DeclReading row={target.row} term={target.term} shell={shell} />;
  return (
    <>
      <p className="lean-read__top">
        <Breakable name={target.name} />
        <span className="lean-read__place">From Mathlib</span>
      </p>
      <p className="lean-read__words">{target.words ?? `Defined outside ${site.lean.ownerSource}, in Mathlib or Lean's core library.`}</p>
      <span className="lean-read__note">Click to find it in Mathlib's documentation, in a new tab.</span>
    </>
  );
}

export interface Reading {
  target: NameTarget;
  shell: LeanShell;
  anchor: HTMLElement;
}

/** Moving from one name to the next passes over nothing, so the line does not blink. */
const LINGER = 140;

export interface ReadingStore {
  now(): Reading | null;
  subscribe(listen: () => void): () => void;
  read(reading: Reading): void;
  clear(): void;
}

/** One block's reading, kept apart from the block so that pointing does not render the code again. */
export function readingStore(): ReadingStore {
  let reading: Reading | null = null;
  let timer = 0;
  const listeners = new Set<() => void>();
  const publish = (next: Reading | null) => {
    reading = next;
    listeners.forEach((listen) => listen());
  };
  return {
    now: () => reading,
    subscribe(listen) {
      listeners.add(listen);
      return () => listeners.delete(listen);
    },
    read(next) {
      window.clearTimeout(timer);
      publish(next);
    },
    clear() {
      window.clearTimeout(timer);
      timer = window.setTimeout(() => publish(null), LINGER);
    },
  };
}

/** Reuse the existing signature and module cache in a preview anchored to the linked token. */
function NamePreview({ reading, store }: { reading: Reading; store: ReadingStore }) {
  const id = useId();
  const ref = useRef<HTMLDivElement>(null);
  const { anchor } = reading;
  useLayoutEffect(() => {
    const tip = ref.current;
    if (!tip || !anchor.isConnected) return;
    const priorDescription = anchor.getAttribute("aria-describedby");
    anchor.setAttribute("aria-describedby", [priorDescription, id].filter(Boolean).join(" "));
    const place = () => {
      if (!anchor.isConnected) return hide();
      const token = anchor.getBoundingClientRect();
      const width = tip.offsetWidth;
      const height = tip.offsetHeight;
      const gap = 8;
      const left = Math.min(window.innerWidth - width - gap, Math.max(gap, token.left));
      const below = token.bottom + gap;
      const top = below + height <= window.innerHeight - gap ? below : Math.max(gap, token.top - height - gap);
      tip.style.transform = `translate(${Math.round(left)}px, ${Math.round(top)}px)`;
      tip.style.visibility = "visible";
    };
    function hide() {
      if (tip) tip.style.visibility = "hidden";
    }
    const key = (event: KeyboardEvent) => {
      if (event.key === "Escape" && tip.style.visibility === "visible") {
        hide();
        event.preventDefault();
        event.stopPropagation();
      }
    };
    place();
    const observer = new ResizeObserver(() => {
      if (tip.style.visibility === "visible") place();
    });
    observer.observe(tip);
    window.addEventListener("scroll", hide, { passive: true, capture: true });
    window.addEventListener("resize", hide, { passive: true });
    window.addEventListener("keydown", key, true);
    anchor.addEventListener("click", hide, { capture: true });
    return () => {
      observer.disconnect();
      window.removeEventListener("scroll", hide, true);
      window.removeEventListener("resize", hide);
      window.removeEventListener("keydown", key, true);
      anchor.removeEventListener("click", hide, true);
      if (priorDescription === null) anchor.removeAttribute("aria-describedby");
      else anchor.setAttribute("aria-describedby", priorDescription);
    };
  }, [anchor, id]);
  return createPortal(
    <div ref={ref} className="lean-name-preview lean-read" id={id} role="tooltip"
      onPointerEnter={() => store.read(reading)}
      onPointerLeave={() => { if (!anchor.matches(":focus-visible")) store.clear(); }}>
      <ReadingLine target={reading.target} shell={reading.shell} />
    </div>,
    document.body,
  );
}

function Line({ store, popupOnly }: { store: ReadingStore; popupOnly?: boolean }) {
  const now = useSyncExternalStore(store.subscribe, store.now);
  if (!now) return null;
  const desktop = window.matchMedia("(hover: hover) and (pointer: fine)").matches;
  if (desktop || now.anchor.matches(":focus-visible")) return <NamePreview reading={now} store={store} />;
  if (popupOnly) return null;
  return (
    <div className="lean-read" role="status">
      <ReadingLine target={now.target} shell={now.shell} />
    </div>
  );
}

/** The block's reading row, or the same line in the host's slot. */
export function ReadingFoot({ store, slot, popupOnly }: { store: ReadingStore; slot?: HTMLElement | null; popupOnly?: boolean }) {
  const line = useMemo(() => <Line store={store} popupOnly={popupOnly} />, [store, popupOnly]);
  if (popupOnly) return line;
  if (slot) return createPortal(line, slot);
  return <div className="lean-slot">{line}</div>;
}

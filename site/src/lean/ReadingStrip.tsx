// The fixed place under the code where a name is read. Its height is reserved, so
// pointing at a name moves nothing, and it never covers the code.

import { useEffect, useState } from "react";
import { texHtml } from "../figures/tex";
import { declIn, fetchModule, kindWord, moduleIfLoaded, sourceLines, type LeanShell } from "./data";
import { mathlibUrl, type DeclRow, type NameTarget } from "./resolve";
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

function DeclReading({ row, term, shell, compact }: { row: DeclRow; term?: DictionaryTerm; shell: LeanShell; compact?: boolean }) {
  useModuleArrival(row.module);
  const full = shell.paths.get(row.module)?.path ?? row.module;
  const path = compact ? full.slice(full.lastIndexOf("/") + 1) : full;
  const signature = term?.words ? null : firstSignatureLine(row);
  return (
    <>
      <p className="lean-strip__head">
        <code className="lean-strip__name">{row.short}</code>
        <span>
          {kindWord(row.kind)} in <PathText path={path} />, line {row.line}
        </span>
      </p>
      {term?.words ? (
        <p className="lean-strip__body">
          <Notation term={term} />
          <span>
            <Prose text={term.words} />
          </span>
        </p>
      ) : signature ? (
        <p className="lean-strip__sig">
          <code>{signature}</code>
        </p>
      ) : null}
    </>
  );
}

export function StripBody({ target, shell, compact }: { target: NameTarget | null; shell: LeanShell; compact?: boolean }) {
  if (!target) {
    return <p className="lean-strip__idle">Point at a name to read it here. Click to open it.</p>;
  }
  if (target.kind === "decl") return <DeclReading row={target.row} term={target.term} shell={shell} compact={compact} />;
  return (
    <>
      <p className="lean-strip__head">
        <code className="lean-strip__name">{target.name}</code>
        <span>From Mathlib</span>
      </p>
      <p className="lean-strip__body">
        <span>
          {target.words ?? "Defined outside OpenAI's source, in Mathlib or Lean's core library."}{" "}
          <a href={mathlibUrl(target.name)} target="_blank" rel="noreferrer">
            Look it up in the Mathlib documentation
          </a>
        </span>
      </p>
    </>
  );
}

export function ReadingStrip({ target, shell, sticky, compact }: { target: NameTarget | null; shell: LeanShell; sticky?: boolean; compact?: boolean }) {
  return (
    <div className={`lean-strip${sticky ? " lean-strip--sticky" : ""}`} role="status" aria-label="Reading the name in focus">
      <StripBody target={target} shell={shell} compact={compact} />
    </div>
  );
}

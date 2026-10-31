// Lean source as numbered lines, with every name that resolves as a real link. Pointer
// and keyboard report the name to the reading strip; nothing floats over the code.
// Tab reaches one name in a block and the arrow keys walk the rest, so a long proof does
// not cost a reader hundreds of tab stops.

import { memo, useRef, type FocusEvent, type KeyboardEvent, type MouseEvent, type PointerEvent } from "react";
import { routeHref } from "../app/router";
import { mathlibUrl, resolveName, type NameTarget, type Scope } from "./resolve";
import { tokenLines, type LeanToken } from "./tokenize";

export interface CodePart {
  text: string;
  className: string;
  /** Index into `targets`. */
  target?: number;
}

export interface CodeLine {
  n: number;
  indent: number;
  parts: CodePart[];
}

export interface BuiltCode {
  lines: CodeLine[];
  targets: NameTarget[];
  /** Whether a clause was found and marked. */
  marked: boolean;
}

/** Lay out tokens as source lines, resolve each name once and mark `clause` if it occurs. */
export function buildCode(tokens: LeanToken[], firstLine: number, scope: Scope, clause?: string): BuiltCode {
  const source = tokens.map((t) => t.text).join("");
  const from = clause ? source.indexOf(clause) : -1;
  const to = from < 0 ? -1 : from + (clause as string).length;
  const ends: number[] = [];
  tokens.reduce((at, t, k) => (ends[k] = at + t.text.length), 0);
  const inClause = (index: number) => from >= 0 && ends[index] > from && ends[index] - tokens[index].text.length < to;
  const targets: NameTarget[] = [];
  const known = new Map<string, number | null>();
  const resolve = (text: string): number | null => {
    const seen = known.get(text);
    if (seen !== undefined) return seen;
    const found = resolveName(text, scope);
    let at: number | null = null;
    if (found && !(found.kind === "decl" && found.row.name === scope.self)) at = targets.push(found) - 1;
    known.set(text, at);
    return at;
  };
  const lines = tokenLines(tokens).map((line, k) => ({
    n: firstLine + k,
    indent: line.indent,
    parts: line.pieces.map(({ token, text, index }): CodePart => {
      const part = piece(token, text);
      return inClause(index) ? { ...part, className: `${part.className} lean-clause`.trim() } : part;
    }),
  }));
  function piece(token: LeanToken, text: string): CodePart {
      if (token.kind === "space") return { text, className: "" };
      if (token.kind !== "name" && token.kind !== "type") return { text, className: `lean-t lean-t--${token.kind}` };
      const target = resolve(text);
      if (target !== null) {
        const found = targets[target];
        const shape = found.kind === "mathlib" ? "lean-n--lib" : found.term ? "lean-n--term" : "lean-n--decl";
        return { text, className: `lean-t lean-t--${token.kind} lean-n ${shape}`, target };
      }
      const local = scope.locals.has(text.split(".")[0]);
      return { text, className: `lean-t lean-t--${local ? "binder" : token.kind}` };
  }
  return { lines, targets, marked: from >= 0 };
}

export interface CodeViewProps {
  code: BuiltCode;
  label: string;
  onRead(target: NameTarget): void;
  /** Called on a plain click. Prevent the event's default to stay on the page. */
  onOpen(target: NameTarget, element: HTMLElement, event: MouseEvent): void;
}

function hrefOf(target: NameTarget): string {
  return target.kind === "decl" ? routeHref({ view: "lean", module: target.row.module, decl: target.row.name }) : mathlibUrl(target.name);
}

export const CodeView = memo(function CodeView({ code, label, onRead, onOpen }: CodeViewProps) {
  const root = useRef<HTMLDivElement>(null);
  const lit = useRef<HTMLElement | null>(null);

  const nameAt = (node: EventTarget | null) => {
    const element = (node as Element | null)?.closest?.("a[data-t]") as HTMLElement | null;
    return element ? { element, target: code.targets[Number(element.dataset.t)] } : null;
  };
  const read = (hit: { element: HTMLElement; target: NameTarget } | null) => {
    if (!hit || hit.element === lit.current) return;
    lit.current?.classList.remove("is-read");
    hit.element.classList.add("is-read");
    lit.current = hit.element;
    onRead(hit.target);
  };
  const onFocus = (event: FocusEvent) => {
    const hit = nameAt(event.target);
    if (!hit) return;
    root.current?.querySelector('a[data-t][tabindex="0"]')?.setAttribute("tabindex", "-1");
    hit.element.setAttribute("tabindex", "0");
    read(hit);
  };
  const onKeyDown = (event: KeyboardEvent) => {
    const hit = nameAt(event.target);
    if (!hit || event.metaKey || event.ctrlKey || event.altKey) return;
    const step = { ArrowRight: 1, ArrowDown: 1, ArrowLeft: -1, ArrowUp: -1 }[event.key];
    const names = Array.from(root.current?.querySelectorAll<HTMLElement>("a[data-t]") ?? []);
    let next: HTMLElement | undefined;
    if (step) next = names[names.indexOf(hit.element) + step];
    else if (event.key === "Home") next = names[0];
    else if (event.key === "End") next = names[names.length - 1];
    else return;
    event.preventDefault();
    next?.focus();
  };

  let first = true;
  return (
    <div className="lean-code" role="group" aria-label={label} ref={root} onPointerOver={(e: PointerEvent) => read(nameAt(e.target))} onFocus={onFocus} onKeyDown={onKeyDown}
      onClick={(event) => {
        const hit = nameAt(event.target);
        if (!hit || event.metaKey || event.ctrlKey || event.shiftKey) return;
        onOpen(hit.target, hit.element, event);
      }}
    >
      {code.lines.map((line) => (
        <div className="lean-line" key={line.n}>
          <span className="lean-line__n" aria-hidden="true">
            {line.n}
          </span>
          <code className="lean-line__c" style={{ "--i": line.indent } as React.CSSProperties}>
            {line.parts.map((part, k) => {
              if (part.target === undefined) {
                return part.className ? (
                  <span key={k} className={part.className}>
                    {part.text}
                  </span>
                ) : (
                  part.text
                );
              }
              const tabIndex = first ? 0 : -1;
              first = false;
              return (
                <a key={k} className={part.className} data-t={part.target} href={hrefOf(code.targets[part.target])} tabIndex={tabIndex} data-external={code.targets[part.target].kind === "mathlib" ? "" : undefined}>
                  {part.text}
                </a>
              );
            })}
            {line.parts.length === 0 && "​"}
          </code>
        </div>
      ))}
    </div>
  );
});

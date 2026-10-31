// Everything the Lean views load, each piece fetched once and only when first needed.
// A module is fetched alone and kept in memory. Nothing here runs at startup.

import { useEffect, useMemo, useState } from "react";
import {
  loadLeanModule,
  loadLeanModules,
  loadLeanNames,
  type Alignment,
  type AlignedStatement,
  type DictionaryTerm,
  type LeanDeclaration,
  type LeanKind,
  type LeanModule,
  type LeanModuleRow,
  type LeanModules,
  type LeanRelation,
} from "../api/lean";
import { alignmentResource, shortTitle, useAlignment } from "../compare/useAlignment";
import { buildIndex, type LeanIndex } from "./resolve";

export const MAIN_THEOREM = "OAI.ZeroTemperatureSK.full_support";
export const VALUE_THEOREM = "OAI.SKValue.value_consequences";
export const MINIMIZER = "OAI.ZeroTemperatureSK.IsMinimizer";
export const CHALLENGE_FILE = "ComparatorChallenges.SKFullSupport";
export const VALUE_CHALLENGE_FILE = "ComparatorChallenges.SKValue";

let shellPending: Promise<{ modules: LeanModules; index: LeanIndex }> | null = null;
let shell: { modules: LeanModules; index: LeanIndex } | undefined;

export function shellResource() {
  shellPending ??= Promise.all([loadLeanModules(), loadLeanNames()]).then(([modules, names]) => (shell = { modules, index: buildIndex(names) }));
  return shellPending;
}

export interface LinkedRecord {
  id: string;
  title: string;
  relation: LeanRelation;
  note: string;
  clause?: string;
}

/** Where a paper states a declaration: an exact slice, and the record that ties it. */
export interface PaperStatement {
  statement: AlignedStatement;
  /** The record whose slice this is; absent for a dictionary entry's quotation. */
  record?: string;
}

export interface LeanShell {
  modules: LeanModules;
  index: LeanIndex;
  paths: Map<string, LeanModuleRow>;
  terms: Map<string, DictionaryTerm>;
  linked: Map<string, LinkedRecord[]>;
  /** Most direct first. An empty map until the alignment arrives. */
  statements?: Map<string, PaperStatement[]>;
}

const pathsMemo = new WeakMap<LeanModules, Map<string, LeanModuleRow>>();
const termsMemo = new WeakMap<Alignment, { terms: Map<string, DictionaryTerm>; linked: Map<string, LinkedRecord[]>; statements: Map<string, PaperStatement[]> }>();
const emptyAlignment = { terms: new Map<string, DictionaryTerm>(), linked: new Map<string, LinkedRecord[]>(), statements: new Map<string, PaperStatement[]>() };

const RELATION_ORDER: LeanRelation[] = ["states", "defines", "contains", "part", "proof"];
const PAPER_ORDER = ["short", "long", "expository"];
const ROLE_ORDER = ["statement", "definition", "derivation", "explanation", "example", "mention"];

function statementsOf(alignment: Alignment): Map<string, PaperStatement[]> {
  const found = new Map<string, { row: PaperStatement; rank: number }[]>();
  const add = (name: string, row: PaperStatement, rank: number) => {
    const rows = found.get(name);
    if (!rows) found.set(name, [{ row, rank }]);
    else if (!rows.some((r) => r.row.statement.paper === row.statement.paper && r.row.statement.start_byte === row.statement.start_byte)) rows.push({ row, rank });
  };
  for (const [id, record] of Object.entries(alignment.records)) {
    for (const lean of record.lean) {
      for (const statement of record.statements) {
        // Where a slice says which Lean it means, it counts only for that Lean.
        if (statement.lean_source === "statement" && !statement.lean?.some((row) => row.name === lean.name)) continue;
        if (statement.role === "mention") continue;
        add(lean.name, { statement, record: id }, RELATION_ORDER.indexOf(lean.relation) * 10 + ROLE_ORDER.indexOf(statement.role));
      }
    }
  }
  for (const term of alignment.dictionary as (DictionaryTerm & { start_byte?: number; end_byte?: number; section?: string; heading_id?: string | null })[]) {
    if (!term.paper || !term.markdown || term.start_byte === undefined || term.end_byte === undefined) continue;
    const statement: AlignedStatement = { paper: term.paper, role: "definition", markdown: term.markdown, start_byte: term.start_byte, end_byte: term.end_byte, anchor: term.anchor ?? null, section: term.section ?? "", heading_id: term.heading_id ?? null } as AlignedStatement;
    add(term.name, { statement }, 5);
  }
  const out = new Map<string, PaperStatement[]>();
  for (const [name, rows] of found) out.set(name, rows.sort((a, b) => a.rank - b.rank || PAPER_ORDER.indexOf(a.row.statement.paper) - PAPER_ORDER.indexOf(b.row.statement.paper)).map((r) => r.row));
  return out;
}

function alignmentMaps(alignment: Alignment | null) {
  if (!alignment) return emptyAlignment;
  let maps = termsMemo.get(alignment);
  if (!maps) {
    const linked = new Map<string, LinkedRecord[]>();
    for (const [id, record] of Object.entries(alignment.records)) {
      for (const lean of record.lean) {
        const row = { id, title: shortTitle(id, record.short || id), relation: lean.relation, note: lean.note, clause: lean.clause };
        const rows = linked.get(lean.name);
        if (rows) rows.push(row);
        else linked.set(lean.name, [row]);
      }
    }
    maps = { terms: new Map(alignment.dictionary.map((term) => [term.name, term])), linked, statements: statementsOf(alignment) };
    termsMemo.set(alignment, maps);
  }
  return maps;
}

function pathsOf(modules: LeanModules) {
  let paths = pathsMemo.get(modules);
  if (!paths) {
    paths = new Map(modules.folders.flatMap((folder) => folder.modules.map((row) => [row.module, row] as const)));
    pathsMemo.set(modules, paths);
  }
  return paths;
}

export type ShellState = { status: "loading" } | { status: "missing" } | { status: "ready"; shell: LeanShell };

/** The index of names and modules, joined with the alignment when it has arrived. */
export function useLeanShell(): ShellState {
  const [state, setState] = useState<typeof shell | null>(shell ?? undefined);
  const alignment = useAlignment();
  useEffect(() => {
    if (shell) return;
    let alive = true;
    void alignmentResource();
    shellResource().then(
      (value) => alive && setState(value),
      () => alive && setState(null),
    );
    return () => {
      alive = false;
    };
  }, []);
  return useMemo((): ShellState => {
    if (state === null) return { status: "missing" };
    if (!state) return { status: "loading" };
    return { status: "ready", shell: { ...state, paths: pathsOf(state.modules), ...alignmentMaps(alignment) } };
  }, [state, alignment]);
}

const modules = new Map<string, LeanModule>();
const modulesPending = new Map<string, Promise<LeanModule>>();

export function fetchModule(name: string): Promise<LeanModule> {
  let pending = modulesPending.get(name);
  if (!pending) {
    pending = loadLeanModule(name).then(
      (value) => {
        modules.set(name, value);
        return value;
      },
      (error) => {
        modulesPending.delete(name);
        throw error;
      },
    );
    modulesPending.set(name, pending);
  }
  return pending;
}

export const moduleIfLoaded = (name: string | undefined) => (name ? modules.get(name) : undefined);

export type ModuleState = { status: "loading" } | { status: "failed" } | { status: "ready"; module: LeanModule };

export function useLeanModule(name: string | undefined): ModuleState {
  const [, refresh] = useState(0);
  const [failed, setFailed] = useState<string | null>(null);
  useEffect(() => {
    if (!name || modules.has(name)) return;
    let alive = true;
    fetchModule(name).then(
      () => alive && refresh((n) => n + 1),
      () => alive && setFailed(name),
    );
    return () => {
      alive = false;
    };
  }, [name]);
  const module = name ? modules.get(name) : undefined;
  if (module) return { status: "ready", module };
  return failed === name ? { status: "failed" } : { status: "loading" };
}

/** Several modules at once; the list holds those that have arrived. */
export function useLeanModules(names: readonly string[]): LeanModule[] {
  const [, refresh] = useState(0);
  const key = names.join(" ");
  useEffect(() => {
    let alive = true;
    for (const name of names) if (!modules.has(name)) fetchModule(name).then(() => alive && refresh((n) => n + 1), () => undefined);
    return () => {
      alive = false;
    };
    // The names are compared through their joined key.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [key]);
  return names.flatMap((name) => modules.get(name) ?? []);
}

const declMaps = new WeakMap<LeanModule, Map<string, LeanDeclaration>>();
const lineMaps = new WeakMap<LeanModule, string[]>();

export function declIn(module: LeanModule, name: string): LeanDeclaration | undefined {
  let map = declMaps.get(module);
  if (!map) {
    map = new Map(module.declarations.map((decl) => [decl.name, decl]));
    declMaps.set(module, map);
  }
  return map.get(name);
}

export function sourceLines(module: LeanModule): string[] {
  let lines = lineMaps.get(module);
  if (!lines) {
    lines = module.source.split("\n");
    lineMaps.set(module, lines);
  }
  return lines;
}

const KIND_WORDS: Record<LeanKind, string> = {
  theorem: "Theorem",
  lemma: "Lemma",
  def: "Definition",
  abbrev: "Abbreviation",
  structure: "Structure",
  class: "Class",
  instance: "Instance",
  inductive: "Inductive type",
  opaque: "Opaque definition",
  axiom: "Axiom",
};

export const kindWord = (kind: LeanKind) => KIND_WORDS[kind] ?? kind;

export const RELATION_WORDS: Record<LeanRelation, string> = {
  states: "States this result",
  contains: "A stronger statement, with this result as one part",
  part: "States one part of this result",
  proof: "Proves this step, in a different form",
  defines: "Defines this object",
};

/** Said once, near the link. */
export const LINK_CAVEAT = "People or agents read the two and linked them. No program has checked that they say the same thing.";

export function dependencyWords(source: string | undefined): string {
  return source === "elaborated" ? "Names from Lean's elaborated report" : "Names found in the source text";
}

/** "1. The result" as "§1", which is how a paper's own section is cited. */
export function sectionPlace(section: string): string {
  const number = /^(\d+(?:\.\d+)*)\.?\s/.exec(section)?.[1];
  return number ? `§${number}` : section;
}

/** What a compiled extraction adds to a declaration, read wherever it is present. */
export interface CompiledFacts {
  /** The pretty-printed type, as Lean prints it. */
  type?: string;
  /** Axioms as `#print axioms` reports them. */
  axioms?: string[];
  /** Whether Lean reports `sorryAx` among them. */
  sorry?: boolean;
  statement_uses?: string[];
  proof_uses?: string[];
  statement_used_by?: string[];
  proof_used_by?: string[];
}

export const compiled = (decl: LeanDeclaration) => decl as LeanDeclaration & CompiledFacts;

const LEADING = /^(?:\s*(?:@\[[^\]]*\]|noncomputable|private|protected|unsafe|partial)\s+)+/;

/** The statement as one line of source, without attributes and modifiers. */
export function signatureText(module: LeanModule, decl: LeanDeclaration): string {
  const text = sourceLines(module).slice(decl.line - 1, decl.signature_end_line).join(" ");
  return text.replace(/\s+/g, " ").replace(LEADING, "").replace(/\s*(?::=|where)\s*(?:by)?\s*$/, "").trim();
}

/** The first sentence or so of a docstring, for one line. */
export function docLine(doc: string | null | undefined): string | null {
  if (!doc) return null;
  const text = doc.replace(/\s+/g, " ").trim();
  return text || null;
}

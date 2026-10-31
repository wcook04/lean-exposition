// Everything the Lean views load, each piece fetched once and only when first needed.
// A module is fetched alone and kept in memory. Nothing here runs at startup.

import { useEffect, useMemo, useState } from "react";
import {
  loadLeanModule,
  loadLeanModules,
  loadLeanNames,
  type Alignment,
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

export interface LeanShell {
  modules: LeanModules;
  index: LeanIndex;
  paths: Map<string, LeanModuleRow>;
  terms: Map<string, DictionaryTerm>;
  linked: Map<string, LinkedRecord[]>;
}

const pathsMemo = new WeakMap<LeanModules, Map<string, LeanModuleRow>>();
const termsMemo = new WeakMap<Alignment, { terms: Map<string, DictionaryTerm>; linked: Map<string, LinkedRecord[]> }>();
const emptyAlignment = { terms: new Map<string, DictionaryTerm>(), linked: new Map<string, LinkedRecord[]>() };

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
    maps = { terms: new Map(alignment.dictionary.map((term) => [term.name, term])), linked };
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
  contains: "Contains this result as one part",
  part: "States one part of this result",
  proof: "Carries this proof step",
  defines: "Defines this object",
};

export const LINK_CAVEAT = "Linked by reading the source. Not checked as equivalent.";

export function dependencyWords(source: string | undefined): string {
  return source === "elaborated" ? "Names from Lean's elaborated report" : "Names found in the source text";
}

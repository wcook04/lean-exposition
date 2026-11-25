// What the graph pane draws around one subject, from data the reader already holds: the
// argument graph (its records and their `supports` and `assumes` links), the record alignment
// (each record's Lean declarations and their plain titles), the Lean index (each declaration's
// kind and the declarations it uses and is used by) and this paper's ties (the topic colour of
// each phrase and where the paper states each record). docs/graph-pane.md says what each part
// means; FocusGraph draws it.
//
// Lean expression, curated argument and citation stay apart. The argument's links are drawn as
// edges between records, each saying where it comes from: stated by the paper, derived from the
// Lean's dependencies (relationOf), or an assumption. A record's Lean declarations are named on its card and shown
// in the dock, never drawn as neighbours (`formalizes` is a correspondence, not a use). What
// those declarations use in the Lean is drawn as Lean declarations, in their own groups, with a
// dashed line where only the statement names the declaration. Citations are not dependencies.

import site from "@instance/site";
import type { Alignment, LeanDeclaration, LeanKind, LeanModule } from "../../api/lean";
import { compiled } from "../../lean/data";
import type { Stage } from "../../api/types";
import type { FGCard, FGEdge, FGRelation, FGRole, FGRoleWords } from "../../map/FocusGraph";
import type { LeanShell } from "../../lean/data";
import { findDecl } from "../../lean/resolve";
import { declTitle } from "../../model/declTitle";
import { onlyPaperLogic, type ArgEdge, type ArgGraph, type ArgNode } from "../../model/graph";
import { routeHref } from "../../app/router";
import { namedIn } from "../../model/leanGraph";
import { graphRecordTitle, shortTitle } from "../../compare/useAlignment";
import { isPhraseRecord, type TieModel } from "../ties";

/** The card id of a declaration with no record of its own. */
export const DECL = "decl:";

/** What the pane is about: records of the argument, or one Lean declaration. */
export type Subject = { kind: "records"; ids: readonly string[] } | { kind: "decl"; name: string };

export interface FocusInput {
  graph: ArgGraph;
  stage: Stage;
  /** The main result of the paper's argument. */
  home: string;
  /** This paper's selected goals, its own main result first. */
  selected?: readonly string[];
  /** Whether the paper's argument (the map) draws a record. */
  onMap(id: string): boolean;
  alignment: Alignment | null;
  shell: LeanShell | null;
  /** A Lean module, if it has been loaded. */
  module(name: string): LeanModule | undefined;
  places: PaperPlaces;
  /** Where the reader is in the paper, as a byte offset, when the reader knows. */
  readAt: number | null;
}

export interface Focus {
  subjects: string[];
  cards: Map<string, FGCard>;
  edges: FGEdge[];
  route: string[] | null;
  routeNote?: string;
  /** The words before the route's steps: how many links, and which kind each is. */
  routeLabel?: string;
  /** The Lean modules this drawing needs and has not loaded yet. */
  missing: string[];
  /** Words for the groups, where this paper's data asks for them. */
  roles: Partial<Record<FGRole, Partial<FGRoleWords>>>;
}

/** Where this paper states each record and each declaration, and the topic colour its phrases carry. */
export interface PaperPlaces {
  recordAt: Map<string, number>;
  declAt: Map<string, number>;
  recordTone: Map<string, string>;
  declTone: Map<string, string>;
  /** The name of that topic, as the paper's legend shows it. */
  recordTopic: Map<string, string>;
  declTopic: Map<string, string>;
  /** The paper's sections by their first byte, in order: a step's section is the last that starts before it. */
  sections: { start: number; title: string }[];
}

export const startOf = (at: string | null | undefined) => {
  const m = /^b(\d+)-/.exec(at ?? "");
  return m ? Number(m[1]) : null;
};

/** Read once per paper: the first place each record and declaration is stated, its topic and colour, and the sections. */
export function paperPlaces(ties: TieModel, sections: readonly { start: number; title: string }[] = []): PaperPlaces {
  const places: PaperPlaces = {
    recordAt: new Map(),
    declAt: new Map(),
    recordTone: new Map(),
    declTone: new Map(),
    recordTopic: new Map(),
    declTopic: new Map(),
    sections: [...sections].sort((a, b) => a.start - b.start),
  };
  const topicName = new Map((ties.index.topics ?? []).map((topic) => [topic.id, topic.name]));
  const first = <K>(map: Map<K, number>, key: K, at: number) => {
    if (!map.has(key) || map.get(key)! > at) map.set(key, at);
  };
  for (const tie of ties.index.ties) {
    const at = startOf(tie.at);
    const tone = tie.tone !== undefined ? `var(--tone-${tie.tone})` : null;
    const names = tie.rows?.map((row) => row.name) ?? (tie.name ? [tie.name] : []);
    const topic = tie.topic ? topicName.get(tie.topic) : undefined;
    if (tie.record && !isPhraseRecord(tie.record)) {
      if (at !== null) first(places.recordAt, tie.record, at);
      if (tone && !places.recordTone.has(tie.record)) places.recordTone.set(tie.record, tone);
      if (topic && !places.recordTopic.has(tie.record)) places.recordTopic.set(tie.record, topic);
    }
    for (const name of names) {
      if (at !== null) first(places.declAt, name, at);
      if (tone && !places.declTone.has(name)) places.declTone.set(name, tone);
      if (topic && !places.declTopic.has(name)) places.declTopic.set(name, topic);
    }
  }
  return places;
}

/** Where a passage starts, for `seen`, from this paper's ties. */
export function passageStart(ties: TieModel, anchor: string | null): number | null {
  if (!anchor) return null;
  const passage = ties.index.passages.find((p) => p[3] === anchor);
  return passage ? passage[0] : null;
}

const DEFINITION_KINDS: readonly LeanKind[] = ["def", "abbrev", "structure", "class", "inductive", "opaque"];

const lastName = (name: string) => name.slice(name.lastIndexOf(".") + 1);

/**
 * A Lean file by its name: `OAI.Probability.SKSupport.Model` is `Model.lean`. A zero-width space
 * before each inner capital lets a long name such as `GreedyAchievementSet.lean` wrap in a narrow column.
 */
export const leanFile = (module: string) => `${module.slice(module.lastIndexOf(".") + 1).replace(/([a-z0-9])(?=[A-Z])/g, "$1\u200b")}.lean`;

/** The section of the paper a byte lies in, by its title. */
export function sectionAt(places: PaperPlaces, at: number | undefined): string | undefined {
  if (at === undefined) return undefined;
  let title: string | undefined;
  for (const s of places.sections) {
    if (s.start > at) break;
    title = s.title;
  }
  return title;
}

/** "Theorem 4.1", "Long record, Lemma 6.55": the number the paper prints, said for this paper. */
export function printedNumber(label: string, stage: Stage): string | undefined {
  const m = /^(?:(Long record|Short paper|Exposition) )?(Theorem|Lemma|Corollary|Proposition|Problem|Definition|Remark|Conjecture|Question|Example|Claim) ([A-Z]?\d*(?:\.\d+)*[a-z]?)\b/.exec(label);
  if (!m || !m[3]) return undefined;
  const paper = m[1] ? ({ "Long record": "long", "Short paper": "short", Exposition: "expository" } as const)[m[1] as "Long record"] : null;
  const words = `${m[2]} ${m[3]}`;
  return paper && paper !== stage ? `${m[1]}, ${words}` : words;
}

/** A record's title in plain words, without the printed number its kicker carries. */
function recordTitle(node: ArgNode): string {
  const short = graphRecordTitle(node.id) ?? shortTitle(node.id, node.label);
  // "Theorem 4.1 (mixed weighted and cover supports)": the words in the brackets.
  const m = /^(?:(?:Long record|Short paper|Exposition) )?(?:Theorem|Lemma|Corollary|Proposition|Problem|Definition|Remark|Conjecture|Question|Example|Claim) [A-Z]?\d*(?:\.\d+)*[a-z]? \((.+)\)$/.exec(short);
  const words = m ? m[1] : short;
  return words.charAt(0).toUpperCase() + words.slice(1);
}

/** Lookups shared by neighbourhoods of the same graph and paper home. */
export function indexFocusGraph(graph: ArgGraph, home: string) {
  // Declaration identity: an argument record of kind declaration stands for its declaration.
  const nodeOfDecl = new Map<string, string>();
  const goals = new Set([home]);
  for (const node of graph.nodes.values()) {
    if (node.kind === "declaration" && node.declaration) nodeOfDecl.set(node.declaration, node.id);
    if (node.kind === "goal") goals.add(node.id);
  }
  return { nodeOfDecl, goals };
}

export function makeFocus(input: FocusInput, index = indexFocusGraph(input.graph, input.home)) {
  const { graph, stage, alignment, shell } = input;
  const { nodeOfDecl, goals } = index;
  const declCard = (name: string) => nodeOfDecl.get(name) ?? `${DECL}${name}`;
  /** The declaration a card stands for, if it stands for one. */
  const declOf = (id: string): string | null => {
    if (id.startsWith(DECL)) return id.slice(DECL.length);
    const node = graph.nodes.get(id);
    return node?.kind === "declaration" ? (node.declaration ?? node.label) : null;
  };
  const rowOf = (name: string) => (shell ? findDecl(shell.index, name) : undefined);
  /**
   * The topic of a Lean file: the topic most of the paper's phrases have whose declarations are in it.
   * A declaration no phrase names takes its file's topic; one in a file no phrase names is grouped under that file's name.
   */
  const fileTopic = new Map<string, string>();
  if (shell) {
    const counts = new Map<string, Map<string, number>>();
    for (const [name, topic] of input.places.declTopic) {
      const module = findDecl(shell.index, name)?.module;
      if (!module) continue;
      const row = counts.get(module) ?? new Map<string, number>();
      row.set(topic, (row.get(topic) ?? 0) + 1);
      counts.set(module, row);
    }
    for (const [module, row] of counts) fileTopic.set(module, [...row.entries()].sort((x, y) => y[1] - x[1] || x[0].localeCompare(y[0]))[0][0]);
  }
  const declTitleOf = (name: string) => shell?.plain.get(name) ?? declTitle(alignment as never, name) ?? lastName(name).replace(/_/g, " ");

  /** A record's declarations: those the alignment links it to, then those its `formalizes` links name. */
  const recordDecls = (id: string): string[] => {
    const names: string[] = [];
    for (const row of alignment?.records[id]?.lean ?? []) names.push(row.name);
    const node = graph.nodes.get(id);
    if (node?.declaration) names.push(node.declaration);
    for (const edge of graph.out.get(id) ?? []) {
      if (edge.kind !== "formalizes") continue;
      const to = graph.nodes.get(edge.to);
      if (to?.declaration) names.push(to.declaration);
    }
    return [...new Set(names)].filter((name) => !shell || rowOf(name));
  };
  /** The records whose statement a declaration is, most direct first. */
  const statedBy = (name: string): string[] => (shell?.linked.get(name) ?? []).filter((row) => row.relation === "states" && graph.nodes.has(row.id)).map((row) => row.id);

  const seen = (at: number | undefined): FGCard["seen"] => {
    if (input.readAt === null || at === undefined) return undefined;
    return at < input.readAt ? "before" : at > input.readAt + 1 ? "later" : "here";
  };

  const recordRole = (node: ArgNode): FGRole => {
    if (node.kind === "goal") return "result";
    if (node.kind === "declaration") return declRole(node.declaration ?? node.label);
    if (node.kind === "assumption") return "step";
    const kind = site.recordKind?.(node);
    if (kind === "declaration") return declRole(node.declaration ?? node.label);
    if (kind) return kind;
    if (node.status === "open") return "open";
    if (node.status === "external") return "cited";
    return "step";
  };
  const declRole = (name: string): FGRole => (DEFINITION_KINDS.includes(rowOf(name)?.kind as LeanKind) ? "definition" : "helper");

  const recordCard = (id: string): FGCard | undefined => {
    const node = graph.nodes.get(id);
    if (!node) return undefined;
    if (node.kind === "declaration") return declCardOf(node.declaration ?? node.label, id);
    const decls = recordDecls(id);
    return {
      id,
      title: recordTitle(node),
      name: decls[0] ? lastName(decls[0]) : undefined,
      role: recordRole(node),
      kicker: node.kind === "assumption" ? "Assumption" : node.kind === "goal" && !printedNumber(node.label, stage) ? "Main result" : printedNumber(node.label, stage),
      tone: input.places.recordTone.get(id) ?? (decls[0] ? input.places.declTone.get(decls[0]) : undefined),
      // A step no phrase of this paper names is grouped by the section of the paper that states it.
      topic: input.places.recordTopic.get(id) ?? (decls[0] ? (input.places.declTopic.get(decls[0]) ?? fileTopic.get(rowOf(decls[0])?.module ?? "")) : undefined) ?? sectionAt(input.places, input.places.recordAt.get(id)),
      section: sectionAt(input.places, input.places.recordAt.get(id)) ?? (decls[0] && rowOf(decls[0]) ? leanFile(rowOf(decls[0])!.module) : undefined),
      seen: seen(input.places.recordAt.get(id)),
    };
  };
  const declCardOf = (name: string, id = declCard(name)): FGCard => {
    const stated = statedBy(name)[0];
    const number = stated ? printedNumber(graph.nodes.get(stated)!.label, stage) : undefined;
    const row = rowOf(name);
    const file = row ? leanFile(row.module) : undefined;
    return {
      id,
      title: declTitleOf(name),
      name: lastName(name),
      role: declRole(name),
      // A declaration that states a record of the paper says which.
      kicker: stated ? `Lean of ${number ?? "a step"}` : undefined,
      tone: input.places.declTone.get(name),
      // A declaration no phrase of this paper names is grouped with its Lean file's phrases, else under its file's own name.
      topic: input.places.declTopic.get(name) ?? (row ? (fileTopic.get(row.module) ?? leanFile(row.module)) : undefined),
      section: file,
      seen: seen(input.places.declAt.get(name)),
    };
  };
  const card = (id: string): FGCard | undefined => (id.startsWith(DECL) ? declCardOf(id.slice(DECL.length), id) : recordCard(id));

  /** The shortest chain of uses from a record up to `to`, through the argument's own links. */
  const chainTo = (id: string, to: ReadonlySet<string>): string[] | null => {
    if (to.has(id)) return [];
    const back = new Map<string, string>([[id, ""]]);
    let wave = [id];
    while (wave.length) {
      const next: string[] = [];
      for (const at of wave) {
        for (const edge of graph.in.get(at) ?? []) {
          if (edge.kind !== "supports" && edge.kind !== "assumes") continue;
          if (back.has(edge.from)) continue;
          back.set(edge.from, at);
          if (to.has(edge.from)) {
            const chain = [edge.from];
            for (let step = at; step !== id; step = back.get(step)!) chain.unshift(step);
            return chain;
          }
          next.push(edge.from);
        }
      }
      wave = next;
    }
    return null;
  };
  /** The shortest chain down the argument's links (a step to what it uses) from `id` to `to`. */
  const chainDown = (id: string, to: string): string[] | null => {
    if (id === to) return [];
    const back = new Map<string, string>([[id, ""]]);
    let wave = [id];
    while (wave.length) {
      const next: string[] = [];
      for (const at of wave) {
        for (const edge of graph.out.get(at) ?? []) {
          if (edge.kind !== "supports" && edge.kind !== "assumes") continue;
          if (back.has(edge.to)) continue;
          back.set(edge.to, at);
          if (edge.to === to) {
            const chain = [edge.to];
            for (let step = at; step !== id; step = back.get(step)!) chain.unshift(step);
            return chain;
          }
          next.push(edge.to);
        }
      }
      wave = next;
    }
    return null;
  };
  /**
   * A route into the main result: up from `id` to a step that uses it, then down from that step to the
   * main result (Proposition B.14 is used by the cell-layer theorem, which uses Corollary 7.2, which
   * draws Theorem 1.1's conclusions). The shortest such chain, or null.
   */
  const routeInto = (id: string): string[] | null => {
    const up = new Map<string, string[]>([[id, []]]);
    let wave = [id];
    while (wave.length) {
      const next: string[] = [];
      for (const at of wave) {
        for (const edge of graph.in.get(at) ?? []) {
          if (edge.kind !== "supports" && edge.kind !== "assumes") continue;
          if (up.has(edge.from)) continue;
          up.set(edge.from, [...up.get(at)!, edge.from]);
          next.push(edge.from);
        }
      }
      wave = next;
    }
    let best: string[] | null = null;
    for (const [via, path] of up) {
      if (via === id) continue;
      const down = chainDown(via, input.home);
      if (down && (!best || path.length + down.length < best.length)) best = [...path, ...down];
    }
    return best;
  };
  /** To the paper's main result, else along a route into it, else to the nearest other result the argument ends in. */
  const routeFrom = (id: string): string[] | null => chainTo(id, new Set([input.home])) ?? routeInto(id) ?? chainTo(id, goals);

  return { declCard, declOf, recordDecls, statedBy, card, routeFrom, rowOf, declTitleOf };
}

export type FocusTools = ReturnType<typeof makeFocus>;

/** The evidence record the converter writes for links read off the Lean's dependencies. */
export const LEAN_DEPENDENCIES = "lean_dependencies";

/**
 * Where an argument link between two records comes from: the paper's own statement, the Lean's
 * dependencies (a `supports` link the edition derived, not one the paper states), or an assumption.
 */
export function relationOf(edge: Pick<ArgEdge, "from" | "to" | "kind" | "warrant">): Extract<FGRelation, "argument" | "derived" | "assumes"> {
  if (edge.kind === "assumes") return "assumes";
  // The link's own evidence ids, where the edition carries them on the map; else its warrant, else the build's list.
  const ids = (edge as { evidenceIds?: readonly string[] }).evidenceIds;
  if (ids?.length) return ids.every((id) => id === LEAN_DEPENDENCIES) ? "derived" : "argument";
  if (edge.warrant ? edge.warrant.evidenceId === LEAN_DEPENDENCIES : site.leanDerivedSupports?.has(`${edge.from}→${edge.to}`)) return "derived";
  return "argument";
}

/** The words before a route's steps, saying how many links it has and of which kind. */
export function routeWords(hops: readonly FGRelation[], toMain: boolean): string {
  const end = toMain ? "the main result" : "one of the paper’s main results";
  const lean = hops.filter((k) => k === "derived").length;
  const paper = hops.length - lean;
  if (hops.length === 1) return `${end.charAt(0).toUpperCase()}${end.slice(1)} uses this directly, by a link ${lean ? "derived from the Lean" : "the paper states"}:`;
  const how = lean === 0 ? "each stated by the paper" : paper === 0 ? "each derived from the Lean" : `${paper} stated by the paper and ${lean} derived from the Lean`;
  return `${hops.length} links to ${end}, ${how}:`;
}

const HELPER_WORDS: Partial<FGRoleWords> = { one: "Lean lemma", uses: "Lean lemmas it uses", usedBy: "Lean lemmas that use it" };
const LEAN_DEFINITION_WORDS: Partial<FGRoleWords> = { one: "Lean definition", uses: "Lean definitions it uses", usedBy: "Lean definitions that use it" };

/** Everything the graph draws around the subject. */
export function focusOn(subject: Subject, input: FocusInput, tools: FocusTools = makeFocus(input)): Focus {
  const { graph } = input;
  const cards = new Map<string, FGCard>();
  const edges: FGEdge[] = [];
  const missing = new Set<string>();
  /**
   * An edge of the paper's argument. One that rests only on the paper's own stated logic is drawn
   * dashed, with the sentence that states it and a link to where the using result is stated.
   */
  const argumentEdge = (edge: ArgEdge, from: string, to: string): FGEdge => {
    // A supports link resting only on the paper's stated logic is "paper"; any other link is
    // classified by relationOf: stated by the paper, derived from the Lean, or an assumption.
    if (edge.kind !== "supports" || !onlyPaperLogic(edge)) return { from, to, kind: relationOf(edge) };
    return { from, to, kind: "paper", why: edge.warrant?.details ?? edge.warrant?.text, href: routeHref({ view: "read", stage: input.stage, node: from }) };
  };
  const put = (id: string) => {
    if (cards.has(id)) return true;
    const c = tools.card(id);
    if (c) cards.set(id, c);
    return !!c;
  };
  const declaration = (name: string): LeanDeclaration | undefined => {
    const row = tools.rowOf(name);
    if (!row) return undefined;
    const module = input.module(row.module);
    if (!module) {
      missing.add(row.module);
      return undefined;
    }
    return module.declarations.find((d) => d.name === name);
  };
  const statementText = (decl: LeanDeclaration) => {
    const module = input.module(tools.rowOf(decl.name)!.module)!;
    return module.source.split("\n").slice(decl.line - 1, decl.signature_end_line).join("\n");
  };
  /** What a declaration uses in the Lean, drawn below the subject card `from`. */
  const leanUses = (from: string, decl: LeanDeclaration, skip: ReadonlySet<string>) => {
    // Lean's own split (type dependencies are the statement's) where the edition has it, else
    // whether the statement's text names the declaration.
    const facts = compiled(decl);
    const inStatement = facts.statement_uses ? new Set(facts.statement_uses) : null;
    const text = inStatement ? "" : statementText(decl);
    for (const name of new Set(decl.uses)) {
      if (name === decl.name || skip.has(name) || !tools.rowOf(name)) continue;
      const id = tools.declCard(name);
      if (id === from || !put(id)) continue;
      edges.push({ from, to: id, kind: (inStatement ? inStatement.has(name) : namedIn(text, name)) ? "statement" : "proof" });
    }
  };
  /** The kinds of each link along a route, from `start` up through `chain`. */
  const hopsOf = (start: string, chain: readonly string[]): FGRelation[] =>
    chain.map((consumer, i) => {
      const prerequisite = i ? chain[i - 1] : start;
      const edge = (graph.out.get(consumer) ?? []).find((e) => e.to === prerequisite && (e.kind === "supports" || e.kind === "assumes"));
      return edge ? (argumentEdge(edge, consumer, prerequisite).kind ?? "argument") : "argument";
    });
  let routeLabel: string | undefined;
  let route: string[] | null = null;
  let routeNote: string | undefined;
  let subjects: string[];
  const leanWords = { helper: HELPER_WORDS, definition: LEAN_DEFINITION_WORDS };

  if (subject.kind === "decl") {
    const id = tools.declCard(subject.name);
    subjects = put(id) ? [id] : [];
    const decl = declaration(subject.name);
    if (decl) {
      leanUses(id, decl, new Set());
      // Lean's own split says whether each user names this one in its statement or its proof; without
      // it (a text scan), only the user's own statement could say, and its module is not loaded.
      const facts = compiled(decl);
      const inStatement = new Set(facts.statement_used_by ?? []);
      const inProof = new Set(facts.proof_used_by ?? []);
      const split = !!facts.statement_used_by && !!facts.proof_used_by;
      for (const name of new Set(decl.used_by)) {
        if (name === decl.name || !tools.rowOf(name)) continue;
        const user = tools.declCard(name);
        if (user === id || !put(user)) continue;
        if (!split) edges.push({ from: user, to: id, kind: "use" });
        else {
          if (inStatement.has(name)) edges.push({ from: user, to: id, kind: "statement" });
          if (inProof.has(name)) edges.push({ from: user, to: id, kind: "proof" });
          if (!inStatement.has(name) && !inProof.has(name)) edges.push({ from: user, to: id, kind: "use" });
        }
      }
    }
    // The main theorem's own Lean (site.lean.mainTheorem) is stated by the main result, even where
    // no statement of the alignment names it.
    const stated = tools.statedBy(subject.name)[0] ?? (subject.name === site.lean.mainTheorem && site.mainGoal ? site.mainGoal : undefined);
    const chain = stated ? tools.routeFrom(stated) : null;
    if (stated && chain) {
      route = [stated, ...chain];
      for (const r of route) put(r);
      // The first crumb is the result this declaration states: a correspondence, not a link of the argument.
      const toMain = (chain.length ? chain[chain.length - 1] : stated) === input.home;
      routeLabel = chain.length
        ? `This declaration states the first of these. From it, ${routeWords(hopsOf(stated, chain), toMain).replace(/^./, (c) => c.toLowerCase())}`
        : `This declaration states ${toMain ? "the main result" : "one of the paper’s main results"}:`;
    } else
      routeNote = stated
        ? "No paper-argument route is recorded for this declaration: no recorded link joins the result it states to the main result."
        : "No paper-argument route is recorded for this declaration: it is not linked to a result of the paper.";
  } else {
    subjects = subject.ids.filter((id) => put(id));
    const here = new Set(subjects);
    for (const s of subjects) {
      for (const edge of graph.out.get(s) ?? []) {
        if (edge.kind !== "supports" && edge.kind !== "assumes") continue;
        if (put(edge.to)) edges.push(argumentEdge(edge, s, edge.to));
      }
      for (const edge of graph.in.get(s) ?? []) {
        if (edge.kind !== "supports" && edge.kind !== "assumes") continue;
        if (put(edge.from)) edges.push(argumentEdge(edge, edge.from, s));
      }
    }
    // What the subjects' own declarations use in the Lean, beside what the paper's argument uses.
    for (const s of subjects) {
      const own = new Set(tools.recordDecls(s));
      // A declaration that states a record already drawn as an argument neighbour is that neighbour.
      for (const other of cards.keys()) for (const name of tools.recordDecls(other)) if (other !== s && !here.has(other)) own.add(name);
      for (const name of tools.recordDecls(s)) {
        const decl = declaration(name);
        if (decl) leanUses(s, decl, own);
      }
    }
    // The route: from whichever subject is nearest the main result.
    let start: string | null = null;
    for (const s of subjects) {
      const chain = tools.routeFrom(s);
      if (chain && (route === null || chain.length < route.length)) {
        route = chain;
        start = s;
      }
    }
    if (route) for (const r of route) put(r);
    if (route && route.length && start) routeLabel = routeWords(hopsOf(start, route), route[route.length - 1] === input.home);
    if (route && route.length === 0) {
      // The paper's own main result is its first selected goal; the others are among its main results.
      const first = input.selected?.[0] ?? input.home;
      const main = subjects.includes(first);
      routeNote = subjects.length > 1
        ? `${main ? "The paper’s main result" : "One of the paper’s main results"} is stated here.`
        : main ? "This is the paper’s main result." : "This is one of the paper’s main results.";
      route = null;
    } else if (!route && subjects.length) {
      const main = tools.card(input.home)?.title ?? "the main result";
      routeNote = `No recorded link joins ${subjects.length > 1 ? "these steps" : "this step"} to the main result, ${main}, so no route to it is recorded.`;
    }
  }
  // Where the paper states the subject is the reading position itself.
  for (const id of subjects) cards.set(id, { ...cards.get(id)!, seen: undefined });
  return { subjects, cards, edges, route, routeNote, routeLabel, missing: [...missing], roles: leanWords };
}

/** The modules a subject's drawing reads, so they can be fetched before it is drawn. */
export function modulesFor(subject: Subject, tools: FocusTools): string[] {
  const names = subject.kind === "decl" ? [subject.name] : subject.ids.flatMap((id) => tools.recordDecls(id));
  return [...new Set(names.map((name) => tools.rowOf(name)?.module).filter((m): m is string => !!m))];
}

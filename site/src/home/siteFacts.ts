// The numbers and outcomes the front page, Checks, About and llms.txt state, read once at
// build time from the files the site serves. vite.config.ts runs this; no browser code
// imports it, only the plain result as "virtual:site-facts". A file that is absent gives a
// null, and the page then leaves that sentence out rather than state an old number.

import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, resolve } from "node:path";

const STAGES = ["short", "long", "expository"] as const;
type Stage = (typeof STAGES)[number];

export interface SiteFacts {
  /**
   * From the edition's tie indexes. A statement is one marked place in a paper, as the reader's
   * stepper counts it. A tie joins a statement to one step, so one statement can have several.
   */
  ties: { total: number; statements: number; withLean: number; papers: Record<Stage, { statements: number; withLean: number }> } | null;
  /** All the steps on the site. */
  steps: number | null;
  /** Links from a step to a Lean declaration, and the distinct declarations they reach. */
  leanLinks: { links: number; declarations: number } | null;
  /** The latest audit of the ties, from its summary file. */
  audit: { date: string; read: number; changed: number; absencesChecked: number; absencesChanged: number; sampled: number; right: number; loose: number; wrong: number; reader: string } | null;
  /** Links in the papers to theorems, equations, sections and citations, from the reference tables. */
  references: number | null;
  /** Declarations with a plain title. */
  plainTitles: number | null;
  lean: { modules: number; declarations: number; revision: string; toolchain: string; dependencySource: string; dependencyNote: string } | null;
  /** Theorem 1 of the short paper, as the alignment places it. */
  theorem1: { at: string; anchor: string | null } | null;
  build: { module: string; command: string; returncode: number; finalLine: string; date: string; toolchain: string; revision: string } | null;
  extraction: { root: string; axioms: string[]; hasSorry: boolean; declarations: number; externalDependencies: number; date: string; status: string } | null;
  /** Word matches in the vendored Lean, outside comments. */
  scan: { sorry: { file: string; count: number }[]; axiomDeclarations: number; files: number } | null;
}

const json = (path: string) => JSON.parse(readFileSync(path, "utf8"));
const MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"];
const dateWords = (iso: string) => {
  const [y, m, d] = iso.slice(0, 10).split("-").map(Number);
  return `${d} ${MONTHS[m - 1]} ${y}`;
};

type TieRows = { segments: [number, number, number[]][]; ties: { lean: boolean }[] };

/** The reader's stops (tieModel in reader/ties.ts): one statement for each place a statement starts. */
export function tieStops(index: TieRows): { statements: number; withLean: number } {
  const first = new Map<number, number>();
  index.segments.forEach(([, , members], segment) => members.forEach((tie) => first.has(tie) || first.set(tie, segment)));
  let statements = 0;
  let withLean = 0;
  index.segments.forEach(([, , members], segment) => {
    const opening = members.filter((tie) => first.get(tie) === segment);
    if (!opening.length) return;
    statements += 1;
    if (opening.some((tie) => index.ties[tie]?.lean)) withLean += 1;
  });
  return { statements, withLean };
}

function editionFacts(dir: string) {
  const index = resolve(dir, "index.json");
  if (!existsSync(index)) return null;
  const responses: Record<string, string> = json(index).responses ?? {};
  const read = (route: string) => {
    const file = responses[route];
    if (!file) return null;
    const body = json(resolve(dir, file));
    return body.data ?? body;
  };
  return { read };
}

/** Lean source with its comments taken out, so a word in a comment is not counted. */
export function withoutComments(source: string): string {
  return source.replace(/\/-[\s\S]*?-\//g, " ").replace(/--.*$/gm, " ");
}

function scanLean(root: string): SiteFacts["scan"] {
  if (!existsSync(root)) return null;
  const files: string[] = [];
  const walk = (dir: string) => {
    for (const name of readdirSync(dir)) {
      const path = join(dir, name);
      if (statSync(path).isDirectory()) walk(path);
      else if (name.endsWith(".lean") && name !== "lakefile.lean") files.push(path);
    }
  };
  walk(root);
  const sorry: { file: string; count: number }[] = [];
  let axiomDeclarations = 0;
  for (const path of files) {
    const text = withoutComments(readFileSync(path, "utf8"));
    const count = text.match(/(?<![\w.'])sorry(?![\w'])/g)?.length ?? 0;
    if (count) sorry.push({ file: path.slice(root.length + 1), count });
    axiomDeclarations += text.match(/^\s*(?:private\s+|protected\s+)?axiom\s/gm)?.length ?? 0;
  }
  return { sorry: sorry.sort((a, b) => a.file.localeCompare(b.file)), axiomDeclarations, files: files.length };
}

export function siteFacts(root = "..", edition = "public/edition"): SiteFacts {
  const alignmentDir = resolve(root, "examples/qaoa-sk/alignment");
  const served = editionFacts(resolve(edition));
  const alignment = served?.read("/alignment") as { records?: Record<string, { lean?: { name: string }[]; statements: { paper: string; role: string; markdown: string; at?: string; start_byte: number; end_byte: number; anchor: string | null }[] }>; names?: Record<string, string> } | null | undefined;

  const perPaper = STAGES.map((stage) => [stage, served?.read(`/ties/${stage}`) as TieRows | null | undefined] as const);
  const stops = perPaper.map(([stage, index]) => [stage, index ? tieStops(index) : null] as const);
  const ties: SiteFacts["ties"] = perPaper.every(([, index]) => index)
    ? {
        total: perPaper.reduce((n, [, index]) => n + index!.ties.length, 0),
        statements: stops.reduce((n, [, row]) => n + row!.statements, 0),
        withLean: stops.reduce((n, [, row]) => n + row!.withLean, 0),
        papers: Object.fromEntries(stops) as Record<Stage, { statements: number; withLean: number }>,
      }
    : null;

  const overview = served?.read("/overview") as { record_counts?: { nodes?: number } } | null | undefined;
  const rows = alignment?.records ? Object.values(alignment.records).flatMap((record) => record.lean ?? []) : null;
  const leanLinks = rows ? { links: rows.length, declarations: new Set(rows.map((row) => row.name)).size } : null;

  const auditPath = resolve(root, "examples/qaoa-sk/verification/tie-audit.json");
  const audit = existsSync(auditPath) ? json(auditPath) : null;

  const tables = existsSync(alignmentDir) ? readdirSync(alignmentDir).filter((name) => /^references-.*\.json$/.test(name)) : [];
  const references = tables.length ? tables.reduce((n, name) => n + (json(resolve(alignmentDir, name)).references?.length ?? 0), 0) : null;

  const modules = served?.read("/lean/modules") as { counts?: { modules: number; declarations: number }; revision: string; toolchain: string; dependency_source: string; dependency_note: string } | null | undefined;
  const lean: SiteFacts["lean"] = modules?.counts
    ? { ...modules.counts, revision: modules.revision, toolchain: modules.toolchain, dependencySource: modules.dependency_source, dependencyNote: modules.dependency_note }
    : null;

  // Found by its own words, so a change in the order of the alignment's rows cannot move the link.
  const statement = alignment?.records?.full_support?.statements.find((s) => s.paper === "short" && /^\*\*Theorem 1\b/.test(s.markdown));
  const theorem1 = statement ? { at: statement.at ?? `b${statement.start_byte}-${statement.end_byte}`, anchor: statement.anchor } : null;

  const observationPath = resolve(root, "examples/qaoa-sk/verification/full-support-build-extraction-observation-20261026.json");
  let build: SiteFacts["build"] = null;
  let extraction: SiteFacts["extraction"] = null;
  if (existsSync(observationPath)) {
    const seen = json(observationPath);
    const native = seen.native_build;
    build = {
      module: native.graph_receipt.module,
      command: native.graph_receipt.command.join(" "),
      returncode: native.graph_receipt.returncode,
      finalLine: native.stdout_final_line,
      date: dateWords(seen.observed_at),
      toolchain: seen.source_binding.lean_toolchain,
      revision: seen.source_revision,
    };
    const v2 = seen.v2_extraction;
    extraction = {
      root: v2.selected_root.name,
      axioms: v2.selected_root.axioms,
      hasSorry: v2.selected_root.has_sorry,
      declarations: v2.declarations_count,
      externalDependencies: v2.external_dependencies_count,
      date: dateWords(seen.observed_at),
      status: seen.retained_extracted_graph_validation.extraction_status,
    };
  }

  return {
    ties,
    steps: overview?.record_counts?.nodes ?? null,
    leanLinks,
    audit: audit ? {
      date: dateWords(audit.date), read: audit.read, changed: audit.changed, absencesChecked: audit.absences_checked, absencesChanged: audit.absences_changed,
      sampled: audit.sampled, right: audit.right, loose: audit.correct_but_loose, wrong: audit.wrong, reader: audit.reader,
    } : null,
    references,
    plainTitles: alignment?.names ? Object.keys(alignment.names).length : null,
    lean,
    theorem1,
    build,
    extraction,
    scan: scanLean(resolve(root, "examples/qaoa-sk/upstream/lean")),
  };
}

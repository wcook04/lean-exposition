import { createServer, defineConfig, loadEnv, type Plugin } from "vite";
import react from "@vitejs/plugin-react";
import katex from "katex";
import { copyFileSync, createReadStream, existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { dirname, resolve } from "node:path";
import { inflateSync } from "node:zlib";
import { frameHtml } from "./src/home/heroMarkup.ts";
import { readerFirstScreenHtml, readerSkeletonHtml } from "./src/reader/skeleton.ts";
import { siteFacts, type SiteFacts } from "./src/home/siteFacts.ts";
import { copyTodos, selectInstance } from "./src/instances/registry.ts";
import { buildRunLedger, type EvidenceInput, type RunLedger } from "./src/checks/runLedger.ts";

// The example this build is for: LX_INSTANCE, default qaoa-sk (src/instances/registry.ts).
// Every path, title and published text below comes from it.
export const INSTANCE = selectInstance(process.env.LX_INSTANCE);
const REPO = "..";
const EXAMPLE = `${REPO}/${INSTANCE.example}`;
const PAPERS_DIR = `${REPO}/${INSTANCE.papers}`;
/** True while vitest runs: an absent input then gives an empty value, where a build stops. */
const TESTING = Boolean(process.env.VITEST);

// The accounts (and for SK the architectural companion), as the repository renders them.
// Download links use page counts read from the same files at build time.
export const PAPER_PDFS: Record<string, { file: string; name: string; alias?: string }> = Object.fromEntries(
  Object.entries(INSTANCE.pdfs).map(([stage, pdf]) => [stage, { ...pdf, file: `${REPO}/${pdf.file}` }]),
);

/** An input the site needs, or a clear stop naming it (a warning only while tests run). */
function missingInput(path: string, what: string): string {
  return `${INSTANCE.id}: ${what} is missing: ${resolve(path)}. The ${INSTANCE.id} data (${INSTANCE.example}/ and ${INSTANCE.papers}/) must be in place before the site builds.`;
}

// Intentionally published observations. Keep this an explicit file list; verification
// directories also contain artifacts that the website does not use. An instance that
// publishes its receipts adds every file an evidence record names (runLedgerModule).
const PUBLIC_OBSERVATIONS = INSTANCE.publicObservations.map((item) => ({ ...item, file: `${REPO}/${item.file}` }));

/** The graph's evidence records, for the run table; empty when the graph is absent. */
function graphEvidence(): EvidenceInput[] {
  const path = resolve(EXAMPLE, "evidence-graph.json");
  if (!existsSync(path)) return [];
  return (JSON.parse(readFileSync(path, "utf8")).evidence ?? []) as EvidenceInput[];
}

/** Receipt paths are relative to the example folder; they are published under verification/ with the same path below it. */
const receiptPublished = (path: string) => `verification/${path.replace(/^verification\//, "")}`;

function readReceipt(path: string): unknown {
  const file = resolve(EXAMPLE, path);
  if (!/^[\w./-]+$/.test(path) || path.includes("..") || !existsSync(file)) return null;
  try {
    return JSON.parse(readFileSync(file, "utf8"));
  } catch {
    return null;
  }
}

export function runLedger(): RunLedger {
  if (!INSTANCE.publishReceipts) return { groups: [], missing: [] };
  return buildRunLedger(graphEvidence(), readReceipt, receiptPublished);
}

/** Every receipt the ledger publishes: its source file and its path under dist/. */
function ledgerFiles(ledger: RunLedger): { file: string; name: string }[] {
  const seen = new Map<string, string>();
  for (const group of ledger.groups) {
    for (const row of group.rows) {
      if (!row.receipt) continue;
      const rel = row.receipt.replace(/^verification\//, "");
      const source = existsSync(resolve(EXAMPLE, rel)) ? resolve(EXAMPLE, rel) : resolve(EXAMPLE, "verification", rel);
      seen.set(rel, source);
    }
  }
  return [...seen].map(([name, file]) => ({ file, name }));
}

function runLedgerModule(ledger: RunLedger): Plugin {
  const id = "virtual:run-ledger";
  return {
    name: "run-ledger",
    resolveId: (source) => (source === id ? `\0${id}` : null),
    load: (resolved) => (resolved === `\0${id}` ? `export const RUN_LEDGER = ${JSON.stringify(ledger)};` : null),
  };
}

function publicObservations(build = false, extra: { file: string; name: string }[] = []): Plugin {
  const files = [...PUBLIC_OBSERVATIONS, ...extra];
  return {
    name: "public-observations",
    configureServer(server) {
      server.middlewares.use((req, res, next) => {
        const name = req.url?.match(/\/verification\/([^?]+\.json)(?:\?.*)?$/)?.[1];
        const observation = files.find((item) => item.name === name);
        if (!observation) return next();
        res.setHeader("Content-Type", "application/json");
        createReadStream(resolve(observation.file)).pipe(res);
      });
    },
    closeBundle() {
      if (!build) return;
      const out = resolve("dist", "verification");
      mkdirSync(out, { recursive: true });
      for (const item of files) {
        mkdirSync(dirname(resolve(out, item.name)), { recursive: true });
        copyFileSync(resolve(item.file), resolve(out, item.name));
      }
    },
  };
}

/** Pages in a PDF: page objects in the file and in its compressed object streams. */
export function pdfPageCount(buf: Buffer): number {
  const text = buf.toString("latin1");
  const count = (t: string) => t.match(/\/Type\s*\/Page(?![a-zA-Z])/g)?.length ?? 0;
  let pages = count(text.replace(/stream\r?\n[\s\S]*?endstream/g, ""));
  const streams = /<<([^>]*?\/Length\s+(\d+)(?!\s+\d+\s+R)[^>]*?)>>\s*stream\r?\n/g;
  for (let m = streams.exec(text); m; m = streams.exec(text)) {
    if (!/FlateDecode/.test(m[1])) continue;
    const start = m.index + m[0].length;
    try {
      pages += count(inflateSync(buf.subarray(start, start + Number(m[2]))).toString("latin1"));
    } catch {
      // A stream that is not zlib data holds no page objects.
    }
  }
  return pages;
}

/** Each PDF's first page as the papers shelf shows it, from scripts/render-paper-pages.py. */
export const PAPER_PAGES = "public/paper-pages";

interface FirstPage {
  src: string;
  srcSet: string;
  width: number;
  height: number;
}

/**
 * The first-page picture of a PDF, while it still matches the PDF's bytes; null when
 * the PDF has changed since the picture was rendered, so the shelf never shows a stale page.
 */
export function firstPage(stage: string, pdf: Buffer, instance = INSTANCE.id): FirstPage | null {
  const manifestPath = resolve(PAPER_PAGES, "manifest.json");
  if (!existsSync(manifestPath)) return null;
  // An instance's own rows ("erdos257/long") come first; the SK site's rows are keyed by stage alone.
  const manifest = JSON.parse(readFileSync(manifestPath, "utf8"));
  const row = (manifest[`${instance}/${stage}`] ?? manifest[stage]) as
    | { pdf_sha256: string; files: Record<string, string>; width: number; height: number }
    | undefined;
  const digest = `sha256:${createHash("sha256").update(pdf).digest("hex")}`;
  if (!row || row.pdf_sha256 !== digest) return null;
  const files = Object.entries(row.files).sort(([a], [b]) => Number(a) - Number(b));
  if (!files.length || !files.every(([, file]) => existsSync(resolve(PAPER_PAGES, file)))) return null;
  return {
    src: `paper-pages/${files[files.length - 1][1]}`,
    srcSet: files.map(([width, file]) => `paper-pages/${file} ${width}w`).join(", "),
    width: row.width,
    height: row.height,
  };
}

/** Serves the PDFs under /pdf/ in development, copies them into every build, and exports their page counts and first pages. */
function paperPdfs(build = false): Plugin {
  const id = "virtual:paper-pdfs";
  return {
    name: "paper-pdfs",
    resolveId: (source) => (source === id ? `\0${id}` : null),
    load(resolved) {
      if (resolved !== `\0${id}`) return null;
      const entries = Object.entries(PAPER_PDFS).map(([stage, p]) => {
        if (!existsSync(resolve(p.file))) {
          if (!TESTING) this.error(missingInput(p.file, `the ${stage} PDF`));
          return [stage, { path: `pdf/${p.name}`, pages: 0 }];
        }
        const buf = readFileSync(resolve(p.file));
        const page = firstPage(stage, buf);
        if (!page) this.warn(`${p.file} has no current first-page picture; run python site/scripts/render-paper-pages.py`);
        return [stage, { path: `pdf/${p.name}`, pages: pdfPageCount(buf), ...(page ? { firstPage: page } : {}) }];
      });
      return `export const PAPER_PDFS = ${JSON.stringify(Object.fromEntries(entries))};`;
    },
    configureServer(server) {
      server.middlewares.use((req, res, next) => {
        const path = req.url?.split("?", 1)[0];
        const pdf = Object.values(PAPER_PDFS).find((p) =>
          path?.endsWith(`/pdf/${p.name}`) || (p.alias && path?.endsWith(`/${p.alias}`)));
        if (!pdf) return next();
        res.setHeader("Content-Type", "application/pdf");
        createReadStream(resolve(pdf.file)).pipe(res);
      });
    },
    closeBundle() {
      if (!build) return;
      const out = resolve("dist");
      for (const p of Object.values(PAPER_PDFS)) {
        // The aliases retain the papers' relative cross-PDF targets without
        // modifying their bytes or changing the site's existing download URLs.
        for (const publicPath of [`pdf/${p.name}`, ...(p.alias ? [p.alias] : [])]) {
          const destination = resolve(out, publicPath);
          mkdirSync(dirname(destination), { recursive: true });
          copyFileSync(resolve(p.file), destination);
        }
      }
    },
  };
}

// The authored alignment (docs/record-alignment.md), read once at build time. The page
// needs only a line per record to title its tiles and mark its levels, so that line ships
// in the bundle and the full alignment stays an on-demand file.
const ALIGNMENT = `${EXAMPLE}/alignment`;
const ROLE_STRENGTH = ["mention", "example", "explanation", "derivation", "definition", "statement"];

interface AuthoredRecord {
  short?: string;
  lean?: { relation?: string }[];
  statements?: { paper: string; role: string }[];
}

/** The folder also holds the dictionary, the theorem's clauses, plain names, per-paper ties and reference tables. */
const NOT_A_BATCH = /^(dictionary|main-theorem|names|ties-.*|references-.*|phrases-.*)\.json$/;

export function recordIndex(dir = ALIGNMENT): Record<string, { short: string; lean: number; relations: string[]; levels: Record<string, string> }> {
  const out: ReturnType<typeof recordIndex> = {};
  if (!existsSync(resolve(dir))) return out;
  const names = readdirSync(resolve(dir)).sort();
  const level = (levels: Record<string, string>, paper: string, role: string) => {
    if (ROLE_STRENGTH.indexOf(role) > ROLE_STRENGTH.indexOf(levels[paper] ?? "")) levels[paper] = role;
  };
  for (const name of names) {
    if (!name.endsWith(".json") || NOT_A_BATCH.test(name)) continue;
    const { records } = JSON.parse(readFileSync(resolve(dir, name), "utf8")) as { records: Record<string, AuthoredRecord> };
    // Other authored companions (results.json, aliases.json) share the folder; only batch files hold records.
    for (const [id, row] of Object.entries(records ?? {})) {
      const levels: Record<string, string> = {};
      for (const { paper, role } of row.statements ?? []) level(levels, paper, role);
      const relations = [...new Set((row.lean ?? []).flatMap((lean) => lean.relation ?? []))];
      out[id] = { short: row.short ?? "", lean: row.lean?.length ?? 0, relations, levels };
    }
  }
  // A declaration's own record ("lean.<name>") takes the declaration's plain title, where the
  // alignment gives one and no batch file titles the record: a card never shows a raw name
  // where plain words exist.
  const namesPath = resolve(dir, "names.json");
  if (existsSync(namesPath)) {
    const { names: plain } = JSON.parse(readFileSync(namesPath, "utf8")) as { names: Record<string, string> };
    for (const [name, title] of Object.entries(plain ?? {})) {
      const id = `lean.${name}`;
      if (!out[id]) out[id] = { short: title, lean: 0, relations: [], levels: {} };
    }
  }
  // Statements added paper by paper count towards their records' levels.
  for (const name of names) {
    if (!/^ties-.*\.json$/.test(name)) continue;
    const { statements } = JSON.parse(readFileSync(resolve(dir, name), "utf8")) as { statements: { record: string; paper: string; role: string }[] };
    for (const { record, paper, role } of statements) if (out[record]) level(out[record].levels, paper, role);
  }
  return out;
}

function recordIndexModule(): Plugin {
  const id = "virtual:record-index";
  return {
    name: "record-index",
    resolveId: (source) => (source === id ? `\0${id}` : null),
    load: (resolved) => (resolved === `\0${id}` ? `export const RECORD_INDEX = ${JSON.stringify(recordIndex())};` : null),
  };
}

function siteFactsModule(facts: SiteFacts): Plugin {
  const id = "virtual:site-facts";
  return {
    name: "site-facts",
    resolveId: (source) => (source === id ? `\0${id}` : null),
    load: (resolved) => (resolved === `\0${id}` ? `export const SITE_FACTS = ${JSON.stringify(facts)};` : null),
  };
}

/** The fields of the reviewed reference tables a reader's page uses. */
export function referenceModule(stage: string): string {
  const path = resolve(ALIGNMENT, `references-${stage}.json`);
  if (!existsSync(path)) {
    if (TESTING) return `export default ${JSON.stringify({ paper: stage, targets: {}, sources: {}, references: [] })};`;
    throw new Error(missingInput(path, `the ${stage} paper's reference table`));
  }
  const table = JSON.parse(readFileSync(path, "utf8"));
  const references = (table.references as Record<string, unknown>[])
    .filter((row) => row.kind !== "plain")
    .map(({ before: _before, cited_as: _cited, ...row }) => row);
  const used = (field: string, all: Record<string, unknown>) =>
    Object.fromEntries(Object.entries(all).filter(([key]) => references.some((row) => row[field] === key && row.kind !== "other_paper")));
  return `export default ${JSON.stringify({ paper: table.paper, targets: used("target", table.targets), sources: used("source", table.sources), references })};`;
}

function referenceTables(): Plugin {
  const prefix = "virtual:paper-references/";
  return {
    name: "paper-references",
    resolveId: (source) => (source.startsWith(prefix) ? `\0${source}` : null),
    load: (resolved) => (resolved.startsWith(`\0${prefix}`) ? referenceModule(resolved.slice(prefix.length + 1)) : null),
  };
}

/** The chunks each route opens with. What they import starts with them. */
const ROUTE_CODE: Record<string, string[]> = {
  map: ["MapPage"],
  compare: ["ComparePage", "StatementSlice", "LeanBlock"],
  lean: ["LeanPage"],
  checks: ["ChecksPage"],
  about: ["AboutPage"],
  // Each paper's reference table is its own chunk, named for the paper, and the paper waits for it.
  "read/long": ["ReaderPage", "long"],
  "read/short": ["ReaderPage", "short"],
  "read/expository": ["ReaderPage", "expository"],
};

interface BuiltChunk {
  file: string;
  entry: boolean;
  imports: string[];
  css: string[];
}
const chunksByName = new Map<string, BuiltChunk>();
const chunksByFile = new Map<string, BuiltChunk>();

/**
 * A route's code, with everything it imports and their stylesheets. Without these links the
 * page's chunks would start only once the edition has arrived, one wait after the other;
 * with them, code and data download together.
 */
function routeCode(route: string, base: string): string[] {
  const seen = new Set<BuiltChunk>();
  const css = new Set<string>();
  const visit = (chunk: BuiltChunk | undefined) => {
    if (!chunk || chunk.entry || seen.has(chunk)) return;
    seen.add(chunk);
    chunk.css.forEach((file) => css.add(file));
    chunk.imports.forEach((file) => visit(chunksByFile.get(file)));
  };
  (ROUTE_CODE[route] ?? []).forEach((name) => visit(chunksByName.get(name)));
  // A chunk that holds only CSS loses its script when the bundle is written. Its stylesheet stays.
  const scripts = [...seen].filter((chunk) => existsSync(resolve("dist", chunk.file)));
  return [
    ...scripts.map((chunk) => `<link rel="modulepreload" crossorigin href="${base}${chunk.file}" />`),
    ...[...css].map((file) => `<link rel="preload" as="style" crossorigin href="${base}${file}" />`),
  ];
}

/** The edition files a route asks for first, named by the edition's own index. */
function routeData(route: string, base: string): string[] {
  const path = resolve("public/edition/index.json");
  if (!existsSync(path)) return [];
  const index = JSON.parse(readFileSync(path, "utf8"));
  const responses: Record<string, string> = index.responses ?? {};
  const graph = Object.keys(responses).find((key) => key.startsWith("/graph?") && key.includes("representation=reader_map"));
  const stage = route.match(/^read\/(.+)$/)?.[1];
  const files = [
    responses[""],
    responses["/overview?representation=reader"],
    graph && responses[graph],
    index.summaries_by_table?.nodes,
    ...(stage ? ["nodes", "sources"] : ["nodes", "sources", "edges", "evidence"]).map((table) => index.records_by_table?.[table]),
    ...(stage ? [index.documents?.[stage], responses[`/papers/${stage}/structure?representation=reader`], responses[`/ties/${stage}`]] : []),
    ...(route === "compare" ? [responses["/alignment"]] : []),
    ...(route === "lean" ? [responses["/lean/modules"], responses["/lean/names"]] : []),
  ];
  return files.filter(Boolean).map((file) => `<link rel="preload" href="${base}edition/${file}" as="fetch" crossorigin />`);
}

/**
 * Each paper's first screen, through the page's own engine. It needs a DOM to sanitise, and the
 * bundler's handling of `import.meta.env` and the virtual modules, so it runs in a dev server
 * of its own. An edition that is not there leaves the empty shape.
 */
async function paperFirstScreens(base: string, facts: SiteFacts): Promise<Record<string, string>> {
  const path = resolve("public/edition/index.json");
  if (!existsSync(path)) return {};
  const index = JSON.parse(readFileSync(path, "utf8"));
  const edition = (name: string) => readFileSync(resolve("public/edition", name));
  const body = (name: string | undefined) => (name ? JSON.parse(edition(name).toString("utf8")) : null);
  // @ts-expect-error jsdom has no types here, and these two lines are all that touch it.
  const { JSDOM } = await import("jsdom");
  const { window } = new JSDOM("<!doctype html>");
  const globals = globalThis as { window?: unknown; document?: unknown };
  globals.window = window;
  globals.document = window.document;
  const { closeBundle: _pdfs, configureServer: _serve, ...pdfs } = paperPdfs();
  const server = await createServer({
    configFile: false,
    base,
    logLevel: "error",
    appType: "custom",
    server: { middlewareMode: true, hmr: false, ws: false },
    optimizeDeps: { noDiscovery: true },
    resolve: { alias: [{ find: /^@instance\//, replacement: `${resolve("src/instances", INSTANCE.id)}/` }] },
    plugins: [pdfs, recordIndexModule(), referenceTables(), siteFactsModule(facts)],
  });
  try {
    const { firstScreen } = await server.ssrLoadModule("/src/reader/firstScreen.ts");
    const screens: Record<string, string> = {};
    for (const stage of Object.keys(index.documents).filter((s) => !INSTANCE.stages || INSTANCE.stages.includes(s as never))) {
      const references = JSON.parse(referenceModule(stage).replace(/^export default /, "").replace(/;$/, ""));
      const { account, parts } = firstScreen(stage, edition(index.documents[stage]), body(index.responses[`/papers/${stage}/structure?representation=reader`]), body(index.responses[`/ties/${stage}`]), references);
      screens[stage] = readerFirstScreenHtml(account, parts, base);
    }
    return screens;
  } finally {
    await server.close();
    delete globals.window;
    delete globals.document;
  }
}

const typeset = (source: string) => katex.renderToString(source, { throwOnError: true, output: "html", strict: "error" });

/**
 * The first screen and the frame, built once. They go straight into the HTML, so the title,
 * the theorem and the bar paint before any script or data arrives, and they reach readers
 * and crawlers that run no script. Pages other than the front page get the frame only.
 */
function firstScreen(base: string, facts: SiteFacts, build = false): Plugin {
  const id = "virtual:front-hero";
  const hero = INSTANCE.hero(base, facts, typeset);
  const frame = frameHtml(base, INSTANCE.siteName);
  const shell = (main: string) => `<div class="app">${frame}<main id="main" class="app__main">${main}</main></div>`;
  return {
    name: "first-screen",
    resolveId: (source) => (source === id ? `\0${id}` : null),
    load: (resolved) => (resolved === `\0${id}` ? `export const HERO_HTML = ${JSON.stringify(hero)};` : null),
    transformIndexHtml: {
      order: "post",
      handler(html, context) {
        // Keep the fonts of the first screen from swapping in late: the text faces, and the KaTeX
        // faces most formulas are drawn in (every route and address, 404.html included, starts here).
        const fonts = Object.keys(context.bundle ?? {}).filter((name) =>
          /stix-two-text-latin-(400|500)-normal.*\.woff2$|source-sans-3-latin-wght-normal.*\.woff2$|KaTeX_(Main-Regular|Math-Italic|Size1-Regular|Size2-Regular)-.*\.woff2$/.test(name),
        );
        const preload = [
          ...fonts.map((name) => `<link rel="preload" href="${base}${name}" as="font" type="font/woff2" crossorigin />`),
          // Every page starts from the edition's index.
          ...(process.env.VITE_STATIC_EDITION === "true" ? [`<link rel="preload" href="${base}edition/index.json" as="fetch" crossorigin />`] : []),
        ].join("");
        return html
          .replace('<html lang="en">', '<html lang="en" data-view="home">')
          .replace("</head>", `${preload}</head>`)
          .replace('<div id="root"></div>', `<div id="root"><!--first-screen-->${shell(`<div class="front">${hero}</div>`)}<!--/first-screen--></div>`);
      },
    },
    generateBundle(_options, bundle) {
      for (const [file, item] of Object.entries(bundle)) {
        if (item.type !== "chunk") continue;
        const chunk = { file, entry: item.isEntry, imports: item.imports, css: [...(item.viteMetadata?.importedCss ?? [])] };
        chunksByName.set(item.name, chunk);
        chunksByFile.set(file, chunk);
      }
    },
    closeBundle() {
      if (!build) return;
      const home = resolve("dist/index.html");
      if (!existsSync(home)) return;
      const html = readFileSync(home, "utf8");
      writeFileSync(
        resolve("dist/.route-shell.html"),
        html.replace(' data-view="home"', "").replace(/<!--first-screen-->[\s\S]*<!--\/first-screen-->/, shell("")),
      );
    },
  };
}

// The published README, llms.txt, sitemap and route titles are the instance's own.
const SITE_URL = process.env.LX_SITE_URL ?? INSTANCE.defaultSiteUrl ?? "";
const SITE_PAGES = INSTANCE.sitePages;
/** What a browser tab says before the page's script takes over, the same words as PageTitle. */
const ROUTE_TITLES = INSTANCE.routeTitles;
const titled = (html: string, title: string) => html.replace(/<title>[^<]*<\/title>/, `<title>${title} · ${INSTANCE.siteName}</title>`);

/** index.html's head and noscript, from the instance: the SK values are the page's words before instances. */
function instanceHtml(): Plugin {
  const escape = (text: string) => text.replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;");
  return {
    name: "instance-html",
    transformIndexHtml: {
      order: "pre",
      handler(html) {
        const og = SITE_URL
          ? `<meta property="og:url" content="${SITE_URL}" />${INSTANCE.html.ogImage ? `\n    <meta property="og:image" content="${SITE_URL}og.png" />\n    <meta property="og:image:width" content="1200" />\n    <meta property="og:image:height" content="630" />` : ""}`
          : "";
        return html
          .replace("%LX_TITLE%", escape(INSTANCE.editionTitle))
          .replace("%LX_DESCRIPTION%", escape(INSTANCE.html.description))
          .replace("%LX_OG_TITLE%", escape(INSTANCE.html.ogTitle))
          .replace("%LX_OG_DESCRIPTION%", escape(INSTANCE.html.ogDescription))
          .replace("%LX_OG_URL%", og)
          .replace("%LX_NOSCRIPT%", INSTANCE.html.noscript);
      },
    },
  };
}

/** Before a build: the inputs the site cannot do without, each named if absent. */
function requireInputs(): void {
  const needed: [string, string][] = [
    [`${EXAMPLE}/evidence-graph.json`, "the evidence graph"],
    [ALIGNMENT, "the alignment folder"],
    ...["long", "short", "expository"].map((stage): [string, string] => [`${ALIGNMENT}/references-${stage}.json`, `the ${stage} paper's reference table`]),
    ...Object.entries(PAPER_PDFS).map(([stage, pdf]): [string, string] => [pdf.file, `the ${stage} PDF`]),
  ];
  const absent = needed.filter(([path]) => !existsSync(resolve(path)));
  if (absent.length) throw new Error(absent.map(([path, what]) => missingInput(path, what)).join("\n"));
}

/** The paper figures shipped as image files (papers/<name>/<stage>/figures/), served and copied under paper-figures/<stage>/. */
function paperFigures(build = false): Plugin {
  const stages = ["long", "short", "expository"].filter((stage) => existsSync(resolve(PAPERS_DIR, stage, "figures")));
  const types: Record<string, string> = { svg: "image/svg+xml", png: "image/png", jpg: "image/jpeg", jpeg: "image/jpeg", webp: "image/webp" };
  return {
    name: "paper-figures",
    configureServer(server) {
      server.middlewares.use((req, res, next) => {
        const m = req.url?.split("?", 1)[0].match(/\/paper-figures\/(long|short|expository)\/([\w.-]+\.(svg|png|jpe?g|webp))$/);
        const file = m && resolve(PAPERS_DIR, m[1], "figures", m[2]);
        if (!m || !file || !existsSync(file)) return next();
        res.setHeader("Content-Type", types[m[3]]);
        createReadStream(file).pipe(res);
      });
    },
    closeBundle() {
      if (!build) return;
      for (const stage of stages) {
        const from = resolve(PAPERS_DIR, stage, "figures");
        const out = resolve("dist", "paper-figures", stage);
        mkdirSync(out, { recursive: true });
        for (const name of readdirSync(from)) if (/\.(svg|png|jpe?g|webp)$/.test(name)) copyFileSync(resolve(from, name), resolve(out, name));
      }
    },
  };
}

/** The test files that read the SK edition, its fixtures or its source: they run for the SK instance only. */
export const SK_ONLY_TESTS: string[] = JSON.parse(readFileSync(resolve("tests/sk-only.json"), "utf8")).tests;

// The site reads one captured edition from the read-only web API.
// During development and preview, /api is proxied to a local
// `lean-exposition serve` process so the page and the API share an origin.
export default defineConfig(({ mode, command }) => {
  const env = loadEnv(mode, process.cwd(), "");
  const api = env.LEAN_EXPOSITION_API ?? "http://127.0.0.1:8000";
  const proxy = { "/api": { target: api, changeOrigin: false } };
  const base = env.VITE_BASE_PATH ?? "/";
  const facts = siteFacts(REPO, "public/edition", INSTANCE);
  const build = command === "build";
  const todos = copyTodos(INSTANCE.copySlots);
  if (todos.length && !TESTING) console.warn(`\n${INSTANCE.id}: ${todos.length} copy slot(s) still hold TODO(copy) (src/instances/${INSTANCE.id}/copy.ts):\n${todos.map((slot) => `  - ${slot}`).join("\n")}\n`);
  if (!SITE_URL && !TESTING) console.warn(`${INSTANCE.id}: LX_SITE_URL is unset, so llms.txt and the README use relative links and no sitemap.xml is written.`);
  if (build) requireInputs();
  const ledger = runLedger();
  if (ledger.missing.length && !TESTING) console.warn(`${INSTANCE.id}: receipts named by evidence records are missing:\n${ledger.missing.map((path) => `  - ${INSTANCE.example}/${path}`).join("\n")}`);
  const instanceDir = resolve("src/instances", INSTANCE.id);
  return {
    base,
    resolve: { alias: [{ find: /^@instance\//, replacement: `${instanceDir}/` }] },
    plugins: [react(), instanceHtml(), paperPdfs(build), publicObservations(build, ledgerFiles(ledger)), paperFigures(build), runLedgerModule(ledger), recordIndexModule(), referenceTables(), siteFactsModule(facts), firstScreen(base, facts, build), ...(build && env.VITE_STATIC_EDITION === "true" ? [{
      name: "static-reading-routes",
      async closeBundle() {
        const out = resolve("dist");
        const shell = resolve(out, ".route-shell.html");
        const screens = await paperFirstScreens(base, facts);
        for (const route of ["map", "compare", "lean", "checks", "about", "search", ...(INSTANCE.stages ?? ["long", "short", "expository"]).map((stage) => `read/${stage}`)]) {
          mkdirSync(resolve(out, route), { recursive: true });
          const preload = [...routeCode(route, base), ...routeData(route, base)].join("");
          // A paper's first paint is already its text, in the shape of the page, so nothing moves when the page arrives.
          const stage = route.match(/^read\/(.+)$/)?.[1];
          const page = stage
            ? readFileSync(shell, "utf8").replace("<html ", '<html data-view="read" ').replace('class="app__main"></main>', () => `class="app__main">${screens[stage] ?? readerSkeletonHtml()}</main>`)
            : readFileSync(shell, "utf8");
          writeFileSync(resolve(out, route, "index.html"), titled(page, ROUTE_TITLES[route]).replace("</head>", `${preload}</head>`));
        }
        writeFileSync(resolve(out, "404.html"), titled(readFileSync(shell, "utf8"), "Page not found"));
        rmSync(shell);
        copyFileSync(resolve("../LICENSE"), resolve(out, "LICENSE.txt"));
        copyFileSync(resolve("../NOTICE"), resolve(out, "NOTICE.txt"));
        copyFileSync(resolve("THIRD_PARTY_NOTICES.md"), resolve(out, "THIRD_PARTY_NOTICES.md"));
        writeFileSync(resolve(out, "README.md"), INSTANCE.readme(SITE_URL, facts));
        writeFileSync(resolve(out, ".nojekyll"), "");
        writeFileSync(resolve(out, "llms.txt"), INSTANCE.llms(SITE_URL, facts));
        if (SITE_URL)
          writeFileSync(
            resolve(out, "sitemap.xml"),
            `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n${SITE_PAGES.map((page) => `  <url><loc>${SITE_URL}${page}</loc></url>`).join("\n")}\n</urlset>\n`,
          );
      },
    }] : [])],
    server: { port: 5173, strictPort: true, proxy },
    preview: { port: 4173, strictPort: true, proxy },
    // A font is fetched only if a page uses its characters. Inlined, its bytes would sit in the
    // stylesheet that every page waits for.
    build: { target: "es2022", sourcemap: true, chunkSizeWarningLimit: 900, assetsInlineLimit: (file) => (/\.(woff2?|ttf)$/.test(file) ? false : undefined) },
    test: {
      environment: "jsdom",
      include: ["tests/**/*.test.ts", "tests/**/*.test.tsx"],
      // The SK suites read the SK edition, its fixtures and its source; another instance runs the rest.
      exclude: INSTANCE.id === "qaoa-sk" ? [] : SK_ONLY_TESTS.map((name) => `tests/${name}`),
      // Several tests render all three papers and parse every part into a DOM;
      // on a shared CI runner that can take longer than Vitest's 5 s default.
      testTimeout: 30000,
    },
  };
});

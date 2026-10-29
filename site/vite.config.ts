import { defineConfig, loadEnv, type Plugin } from "vite";
import react from "@vitejs/plugin-react";
import { copyFileSync, createReadStream, existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { dirname, resolve } from "node:path";
import { inflateSync } from "node:zlib";

// The three accounts and architectural companion, as the repository renders them.
// Download links use page counts read from the same files at build time.
export const PAPER_PDFS: Record<string, { file: string; name: string; alias?: string }> = {
  long: { file: "../papers/qaoa-sk/long/reasoning-record.pdf", name: "long-record.pdf", alias: "long/reasoning-record.pdf" },
  short: { file: "../papers/qaoa-sk/short/paper.pdf", name: "short-paper.pdf", alias: "short/paper.pdf" },
  expository: { file: "../papers/qaoa-sk/expository/main.pdf", name: "exposition.pdf", alias: "expository/main.pdf" },
  architecture: { file: "../papers/architecture/paper.pdf", name: "architecture.pdf" },
};

// One intentionally published observation. Keep this an explicit file list;
// verification directories also contain artifacts that the website does not use.
const PUBLIC_OBSERVATIONS = [{
  file: "../examples/qaoa-sk/verification/full-support-build-extraction-observation-20261026.json",
  name: "full-support-build-extraction-observation-20261026.json",
}];

function publicObservations(): Plugin {
  return {
    name: "public-observations",
    configureServer(server) {
      server.middlewares.use((req, res, next) => {
        const name = req.url?.match(/\/verification\/([^/?]+\.json)(?:\?.*)?$/)?.[1];
        const observation = PUBLIC_OBSERVATIONS.find((item) => item.name === name);
        if (!observation) return next();
        res.setHeader("Content-Type", "application/json");
        createReadStream(resolve(observation.file)).pipe(res);
      });
    },
    closeBundle() {
      const out = resolve("dist", "verification");
      mkdirSync(out, { recursive: true });
      for (const item of PUBLIC_OBSERVATIONS) copyFileSync(resolve(item.file), resolve(out, item.name));
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
export function firstPage(stage: string, pdf: Buffer): FirstPage | null {
  const manifestPath = resolve(PAPER_PAGES, "manifest.json");
  if (!existsSync(manifestPath)) return null;
  const row = JSON.parse(readFileSync(manifestPath, "utf8"))[stage] as
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
function paperPdfs(): Plugin {
  const id = "virtual:paper-pdfs";
  return {
    name: "paper-pdfs",
    resolveId: (source) => (source === id ? `\0${id}` : null),
    load(resolved) {
      if (resolved !== `\0${id}`) return null;
      const entries = Object.entries(PAPER_PDFS).map(([stage, p]) => {
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

// The public repository that receives the static build has no other README.
const SITE_README = `# Why the SK order parameter has no gaps

This repository holds the built reading website published at
https://wcook04.github.io/lean-exposition-site/.

The website presents one theorem about the zero-temperature
Sherrington–Kirkpatrick spin glass: every minimising Parisi order parameter
increases across every interval in [0, 1). It has three written accounts of
the proof (an exposition, a short paper and a long record), each readable on
the site or as a PDF in \`pdf/\`, an argument map of the records the proof
uses, and the checks recorded for them. The architectural companion explains
why these accounts share one record; read it on the About page or in
\`pdf/architecture.pdf\`.

The mathematics comes from OpenAI's mathematics release, family 281:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md

Plectis Atlas has a page for the same family:
https://wcook04.github.io/plectis-atlas/families/281.html

Will Cook made this website as part of Plectis, his projects on researching
mathematics with AI and on tools that help people follow what AI produces:
https://wcook04.github.io/practical-formal-verification/
His videos are on YouTube: https://www.youtube.com/@willcook2004

Source, papers, tools and contribution instructions:
https://github.com/wcook04/lean-exposition

This repository receives the generated website from the source repository’s
main-branch build workflow. Make changes in the source repository; the workflow
publishes the resulting files here.
`;

// The site reads one captured edition from the read-only web API.
// During development and preview, /api is proxied to a local
// `lean-exposition serve` process so the page and the API share an origin.
export default defineConfig(({ mode }) => {
  const env = loadEnv(mode, process.cwd(), "");
  const api = env.LEAN_EXPOSITION_API ?? "http://127.0.0.1:8000";
  const proxy = { "/api": { target: api, changeOrigin: false } };
  return {
    base: env.VITE_BASE_PATH ?? "/",
    plugins: [react(), paperPdfs(), publicObservations(), ...(env.VITE_STATIC_EDITION === "true" ? [{
      name: "static-reading-routes",
      closeBundle() {
        const out = resolve("dist");
        for (const route of ["map", "checks", "about", "search", "read/long", "read/short", "read/expository"]) {
          mkdirSync(resolve(out, route), { recursive: true });
          copyFileSync(resolve(out, "index.html"), resolve(out, route, "index.html"));
        }
        copyFileSync(resolve(out, "index.html"), resolve(out, "404.html"));
        copyFileSync(resolve("../LICENSE"), resolve(out, "LICENSE.txt"));
        copyFileSync(resolve("../NOTICE"), resolve(out, "NOTICE.txt"));
        copyFileSync(resolve("THIRD_PARTY_NOTICES.md"), resolve(out, "THIRD_PARTY_NOTICES.md"));
        writeFileSync(resolve(out, "README.md"), SITE_README);
        writeFileSync(resolve(out, ".nojekyll"), "");
      },
    }] : [])],
    server: { port: 5173, strictPort: true, proxy },
    preview: { port: 4173, strictPort: true, proxy },
    build: { target: "es2022", sourcemap: true, chunkSizeWarningLimit: 900 },
    test: {
      environment: "jsdom",
      include: ["tests/**/*.test.ts", "tests/**/*.test.tsx"],
      // Several tests render all three papers and parse every part into a DOM;
      // on a shared CI runner that can take longer than Vitest's 5 s default.
      testTimeout: 30000,
    },
  };
});

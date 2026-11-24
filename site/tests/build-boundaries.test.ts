// @vitest-environment node
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { promisify } from "node:util";
import { expect, it } from "vitest";
import { recordIndex } from "../vite.config";
import { recordLine, shortTitle } from "../src/compare/useAlignment";

it("keeps the authored record lines and plain titles available synchronously", () => {
  const lines = Object.entries(recordIndex());
  expect(lines.length).toBeGreaterThan(0);
  // Read titles before expanding title-only entries into full lines.
  expect(lines.map(([id]) => shortTitle(id, id))).toEqual(lines.map(([id, line]) => line.short || id));
  expect(lines.map(([id]) => recordLine(id))).toEqual(lines.map(([, line]) => line));
  expect(recordLine("missing-record-index-test")).toBeUndefined();
  expect(shortTitle("missing-record-index-test", "Graph label")).toBe("Graph label");
});

it("keeps an argument title separate from its numbered record label", () => {
  const root = mkdtempSync(join(tmpdir(), "argument-title-"));
  const alignment = join(root, "alignment");
  try {
    mkdirSync(alignment);
    writeFileSync(join(root, "evidence-graph.json"), JSON.stringify({ nodes: [{ id: "paper.lemma-2" }] }));
    writeFileSync(join(alignment, "m1.json"), JSON.stringify({ records: { "paper.lemma-2": { short: "Lemma 2" } } }));
    const names = join(alignment, "names.json");
    writeFileSync(names, JSON.stringify({ names: {}, record_titles: { "paper.lemma-2": "Finite Fourier expansion" } }));
    expect(recordIndex(alignment)["paper.lemma-2"]).toMatchObject({ short: "Lemma 2", graphTitle: "Finite Fourier expansion" });
    writeFileSync(names, JSON.stringify({ names: {}, record_titles: { "paper.wrong": "Finite Fourier expansion" } }));
    expect(() => recordIndex(alignment)).toThrow("no graph record paper.wrong");
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

function outputTree(root: string): Record<string, { bytes: string; modified: number }> {
  const files: ReturnType<typeof outputTree> = {};
  if (!existsSync(root)) return files;
  function visit(dir: string) {
    for (const row of readdirSync(dir, { withFileTypes: true })) {
      const file = join(dir, row.name);
      if (row.isDirectory()) visit(file);
      else files[file.slice(root.length)] = { bytes: createHash("sha256").update(readFileSync(file)).digest("hex"), modified: statSync(file).mtimeMs };
    }
  }
  visit(root);
  return files;
}

it("closing a development server leaves build output unchanged", async () => {
  const dist = resolve("dist");
  const before = outputTree(dist);
  const existed = existsSync(dist);
  await promisify(execFile)(process.execPath, ["--input-type=module", "-e", `
    import { createServer } from "vite";
    const server = await createServer({
      server: { middlewareMode: true, hmr: false, ws: false },
      optimizeDeps: { noDiscovery: true },
    });
    await server.close();
  `]);
  expect(existsSync(dist)).toBe(existed);
  expect(outputTree(dist)).toEqual(before);
});

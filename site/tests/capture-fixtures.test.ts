// @vitest-environment node
import { execFile } from "node:child_process";
import { mkdtemp, readFile, readdir, rm, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { promisify } from "node:util";
import { expect, it } from "vitest";

const execute = promisify(execFile);

async function capture(missingTies: boolean) {
  const out = await mkdtemp(join(tmpdir(), "lean-exposition-capture-"));
  await writeFile(join(out, "keep.txt"), "existing fixture bytes");
  const server = createServer((req, res) => {
    const url = new URL(req.url!, "http://localhost");
    const route = url.pathname.replace(/^\/api\/v1/, "");
    if (missingTies && route === "/ties/long") {
      res.writeHead(404).end("alignment unavailable");
      return;
    }
    if (route.endsWith("/document")) {
      res.end(`paper-${route.split("/")[2]}`);
      return;
    }
    let data: unknown;
    if (!route) {
      res.end(JSON.stringify({ snapshot: { manifest_sha256: "captured-edition" } }));
      return;
    }
    if (route === "/graph") data = { selected_goals: [], records: { nodes: [], evidence: [] }, links: [], components: [], coverage: {} };
    else if (route === "/records") data = { items: [], total: 0 };
    else if (route === "/overview") data = { papers: ["long", "short", "expository"].map((stage) => ({ stage })) };
    else if (route.endsWith("/structure")) data = { stage: route.split("/")[2], paper: {} };
    else if (route.startsWith("/ties/")) data = { segments: [], ties: [], passages: [], meaning: route };
    else {
      res.writeHead(404).end(route);
      return;
    }
    // Every response after discovery must belong to that captured edition.
    if (url.searchParams.get("manifest") !== "captured-edition") {
      res.writeHead(409).end("missing manifest");
      return;
    }
    res.end(JSON.stringify({ data }));
  });
  await new Promise<void>((done) => server.listen(0, "127.0.0.1", done));
  const address = server.address() as { port: number };
  try {
    let error: unknown;
    try {
      await execute(process.execPath, [resolve("scripts/capture-fixtures.mjs"), `http://127.0.0.1:${address.port}`, "--out", out]);
    } catch (caught) {
      error = caught;
    }
    return { files: await readdir(out), keep: await readFile(join(out, "keep.txt"), "utf8"),
      ties: !error ? await Promise.all(["long", "short", "expository"].map(async (stage) => JSON.parse(await readFile(join(out, `ties-${stage}.json`), "utf8")))) : [], error };
  } finally {
    await new Promise<void>((done) => server.close(() => done()));
    await rm(out, { recursive: true, force: true });
  }
}

it("captures all three paper tie projections with the pinned edition", async () => {
  const result = await capture(false);
  expect(result.error).toBeUndefined();
  expect(result.ties.map((ties) => ties.meaning)).toEqual(["/ties/long", "/ties/short", "/ties/expository"]);
  expect(result.files).toContain("document-long.md");
  expect(result.keep).toBe("existing fixture bytes");
});

it("leaves existing fixture files untouched when an alignment route is missing", async () => {
  const result = await capture(true);
  expect(String(result.error)).toContain("404");
  expect(result.files).toEqual(["keep.txt"]);
  expect(result.keep).toBe("existing fixture bytes");
});

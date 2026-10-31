// @vitest-environment node
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, resolve } from "node:path";
import { promisify } from "node:util";
import { expect, it } from "vitest";

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

import { defineConfig, loadEnv } from "vite";
import react from "@vitejs/plugin-react";
import { copyFileSync, mkdirSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";

// The site reads one captured edition from the read-only web API.
// During development and preview, /api is proxied to a local
// `lean-exposition serve` process so the page and the API share an origin.
export default defineConfig(({ mode }) => {
  const env = loadEnv(mode, process.cwd(), "");
  const api = env.LEAN_EXPOSITION_API ?? "http://127.0.0.1:8000";
  const proxy = { "/api": { target: api, changeOrigin: false } };
  return {
    base: env.VITE_BASE_PATH ?? "/",
    plugins: [react(), ...(env.VITE_STATIC_EDITION === "true" ? [{
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
        writeFileSync(resolve(out, ".nojekyll"), "");
      },
    }] : [])],
    server: { port: 5173, strictPort: true, proxy },
    preview: { port: 4173, strictPort: true, proxy },
    build: { target: "es2022", sourcemap: true, chunkSizeWarningLimit: 900 },
    test: {
      environment: "jsdom",
      include: ["tests/**/*.test.ts", "tests/**/*.test.tsx"],
    },
  };
});

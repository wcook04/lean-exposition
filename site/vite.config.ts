import { defineConfig, loadEnv } from "vite";
import react from "@vitejs/plugin-react";

// The site reads one captured edition from the read-only web API.
// During development and preview, /api is proxied to a local
// `lean-exposition serve` process so the page and the API share an origin.
export default defineConfig(({ mode }) => {
  const env = loadEnv(mode, process.cwd(), "");
  const api = env.LEAN_EXPOSITION_API ?? "http://127.0.0.1:8000";
  const proxy = { "/api": { target: api, changeOrigin: false } };
  return {
    plugins: [react()],
    server: { port: 5173, strictPort: true, proxy },
    preview: { port: 4173, strictPort: true, proxy },
    build: { target: "es2022", sourcemap: true, chunkSizeWarningLimit: 900 },
    test: {
      environment: "jsdom",
      include: ["tests/**/*.test.ts", "tests/**/*.test.tsx"],
    },
  };
});

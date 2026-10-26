// The authored PDFs, served under pdf/ with page counts read at build time (vite.config.ts).
declare module "virtual:paper-pdfs" {
  export const PAPER_PDFS: Record<"long" | "short" | "expository" | "architecture", { path: string; pages: number }>;
}

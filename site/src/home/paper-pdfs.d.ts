// The authored PDFs, served under pdf/ with page counts read at build time (vite.config.ts),
// and each one's first page as a picture while it matches the PDF (scripts/render-paper-pages.py).
declare module "virtual:paper-pdfs" {
  export interface FirstPage {
    /** Paths relative to the site's base, like `path`. */
    src: string;
    srcSet: string;
    width: number;
    height: number;
  }
  export const PAPER_PDFS: Record<
    "long" | "short" | "expository" | "architecture",
    { path: string; pages: number; firstPage?: FirstPage }
  >;
}

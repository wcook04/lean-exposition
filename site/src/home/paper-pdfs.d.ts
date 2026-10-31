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

// One line per record, from the authored alignment, built into the bundle (vite.config.ts).
declare module "virtual:record-index" {
  export interface RecordLine {
    /** Two to five plain words for a tile. */
    short: string;
    /** How many Lean declarations are linked to the record. */
    lean: number;
    /** How those declarations relate to the record: "states", "part" and so on, each once. */
    relations: string[];
    /** The strongest thing each paper does with the record: "statement", "mention" and so on. */
    levels: Partial<Record<"long" | "short" | "expository", string>>;
  }
  export const RECORD_INDEX: Record<string, RecordLine>;
}

// The first screen's HTML, typeset at build time.
declare module "virtual:front-hero" {
  export const HERO_HTML: string;
}

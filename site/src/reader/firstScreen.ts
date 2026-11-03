// The opening of each paper as HTML, made once when the site is built and written into that
// paper's page, so the words appear with the stylesheet and before any script has run. It goes
// through the page's own engine, so what the page draws later is the same text in the same
// place. Nothing in a browser imports this file; `vite.config.ts` runs it under a DOM.

import type { TieIndex } from "../api/lean";
import type { PaperStructure, Stage } from "../api/types";
import { PAPER_NAMES } from "../app/papers";
import { PAPER_PDFS } from "virtual:paper-pdfs";
import { preparePaper } from "./documents";
import { statusWords } from "./page/model";
import type { ReferenceTable } from "./references";
import { accountLineHtml } from "./skeleton";

/** Bytes of Markdown that fill a tall window. The last part may run past this. */
const FIRST_SCREEN_BYTES = 4000;

export interface FirstScreen {
  account: string;
  parts: string;
}

export function firstScreen(stage: Stage, bytes: Uint8Array, structure: PaperStructure, ties: TieIndex | null, references: ReferenceTable | null): FirstScreen {
  const doc = preparePaper({ stage, structure, bytes: bytes as Uint8Array<ArrayBuffer> }, ties, references);
  let parts = "";
  let taken = 0;
  for (const part of doc.parts) {
    if (part.blank) continue;
    const { html } = doc.render(part.index);
    // A figure is drawn by script, so its place cannot be held here.
    if (html.includes("data-figure-slot")) break;
    parts += `<section class="part"><div class="part__text">${html}</div></section>`;
    taken += part.span.end - part.span.start;
    if (taken >= FIRST_SCREEN_BYTES) break;
  }
  const names = PAPER_NAMES[stage];
  const status = statusWords(structure.state, structure.review_state);
  const pdf = PAPER_PDFS[stage];
  const account = [names.job, names.reader, status].filter(Boolean).join(" ");
  return { account: accountLineHtml(account, `${import.meta.env.BASE_URL}${pdf.path}`, pdf.pages), parts };
}

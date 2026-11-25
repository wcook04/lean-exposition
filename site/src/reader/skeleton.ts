// A paper before it arrives, the same shape as the page it becomes: the strip, the paper's
// column, the sidecar. Each paper's HTML opens with the paper's own first screen in this
// shape; a page that opens further down, or a paper reached from inside the site, shows the
// empty shape instead. React keeps showing either until the text is ready, so the first paint
// does not move. Its stylesheet comes with it, because the reader's own arrives with the
// reader. No script, no import: the build reads this too.

const STYLE = `.reader-shape{display:grid;grid-template-columns:minmax(0,var(--reader-measure));justify-content:center;column-gap:var(--reader-gap);align-items:start;padding-inline:var(--space-6)}
.reader-shape__outline,.reader-shape__side{display:none}
.reader-shape__strip{height:45px;margin-bottom:var(--space-5);margin-left:-22px;border-bottom:1px solid var(--rule)}
.reader-shape__text{display:flex;flex-direction:column;gap:14px}
.reader-shape__text i{display:block;height:13px;background:var(--rule);opacity:.55}
.reader-shape__text i:first-child{width:62%;height:30px;margin-bottom:var(--space-4)}
.reader-shape__words{margin:0;font-family:var(--font-sans);font-size:var(--fs-sm);color:var(--ink-3)}
.reader-shape .account-line{margin:var(--space-4) 0 var(--space-6);font-family:var(--font-sans);font-size:var(--fs-sm);line-height:var(--lh-ui);color:var(--ink-3);text-wrap:pretty}
.reader-shape .reader-hint{margin:0 0 var(--space-5);padding:var(--space-2) var(--space-3);border-left:2px solid var(--rule-control);font-family:var(--font-sans);font-size:var(--fs-ui);line-height:var(--lh-ui);color:var(--ink-2);text-wrap:pretty}
.reader-shape .paper.prose{max-width:var(--reader-measure)}
.reader-shape .part{position:relative;display:flow-root;padding-bottom:var(--space-4)}
.reader-shape .part__text{content-visibility:visible;contain-intrinsic-block-size:none}
.reader-shape .part__text>:last-child{margin-bottom:0}
@media (max-width:700px){.reader-shape{padding-inline:20px}.reader-shape__strip{margin-left:-15px}.reader-shape .account-line{margin:var(--space-3) 0 var(--space-4)}}
@media (min-width:1024px){.reader-shape{grid-template-columns:minmax(0,1fr) minmax(0,1fr);justify-content:start;column-gap:24px;padding-left:32px;padding-right:0}.reader-shape .paper.prose{max-width:100%}
.reader-shape__side{display:block;position:sticky;top:var(--topbar-h);height:calc(100vh - var(--topbar-h));border-left:1px solid var(--rule)}}
@media (min-width:1280px){.reader-shape{column-gap:var(--reader-gap)}.reader-shape__side{margin-left:16px}}
@media (min-width:1680px){.reader-shape{grid-template-columns:var(--reader-outline) minmax(0,1fr) minmax(0,1fr)}
.reader-shape__outline{display:block}.reader-shape__strip{margin-bottom:var(--space-6)}}
@media (min-width:1921px){.reader-shape{--fs-read:clamp(18px,calc(18px + (100vw - 1920px)/320),20px);--reader-measure:clamp(680px,calc(680px + (100vw - 1920px)*.117),755px)}}`;

const LINES = [100, 96, 98, 92, 60, 0, 100, 94, 97, 88, 99, 45];

const shape = (column: string, busy: string) =>
  `<div class="reader-shape"${busy}><div class="reader-shape__outline"></div><div><div class="reader-shape__strip"></div>${column}</div><div class="reader-shape__side"></div></div>`;

/** The shape as HTML. `words` is said to assistive technology and shown at the column's head. */
export function readerSkeletonHtml(words = "Loading the paper…"): string {
  const lines = LINES.map((w) => (w ? `<i style="width:${w}%"></i>` : `<i style="visibility:hidden"></i>`)).join("");
  return `<style>${STYLE}</style>${shape(`<p class="reader-shape__words" role="status">${words}</p><div class="reader-shape__text"><i></i>${lines}</div>`, ' aria-busy="true"')}`;
}

/** The line under the strip, in the words and with the link the page gives it. */
export function accountLineHtml(words: string, pdf: string | null, pages: number): string {
  // A document with no PDF of its own (a library paper's guide) has no Open PDF link.
  if (!pdf) return `<p class="account-line">${words}</p>`;
  return `<p class="account-line">${words} <a class="pdf-link" href="${pdf}" target="_blank" rel="noopener">Open PDF, ${pages} ${pages === 1 ? "page" : "pages"}</a></p>`;
}

/** What to do with a linked phrase: shown whole at every width, at the head of a paper with linked phrases. */
export const READER_HINT = "Auto select follows the paper as you scroll. Hover over a marked phrase to preview its Lean and see how the two compare. Click a phrase to keep it selected in Manual.";

/** The hint as the first screen sets it; the page renders the same element (ReaderPage). */
export function readerHintHtml(): string {
  return `<p class="reader-hint">${READER_HINT}</p>`;
}

const FIRST_ATTRIBUTE = "data-first-paper";

/**
 * A paper's first screen. A page that opens anywhere but the top (an address with a place in it,
 * or a reload or Back that restores one) swaps it for the empty shape before anything paints.
 * With `base`, an address whose path names a place (a numbered result such as theorem-1.1/,
 * which is served this same page) opens further down too. The site root, its read/ routes and
 * an optional public document opening are the top.
 */
export function readerFirstScreenHtml(account: string, parts: string, base?: string, openingPath?: string): string {
  const opening = openingPath ? `||p===${JSON.stringify(openingPath)}||p===${JSON.stringify(openingPath + "index.html")}` : "";
  const top = base
    ? `var p=location.pathname,b=${JSON.stringify(base)};if(p===b||p===b+"index.html"||p.indexOf(b+"read/")===0${opening})`
    : "";
  const swap = `(function(){${top}if(!location.hash&&!location.search&&!history.state)return;var f=document.querySelector("[${FIRST_ATTRIBUTE}]");f.replaceWith(f.nextElementSibling.content)})()`;
  return `<div ${FIRST_ATTRIBUTE} style="display:contents"><style>${STYLE}</style>${shape(`${account}<div class="paper prose">${parts}</div>`, "")}</div><template>${readerSkeletonHtml()}</template><script>${swap}</script>`;
}

/** The first screen the page opened with, if it did, read before React replaces it. */
export function openedFirstScreen(root: ParentNode): string | null {
  return root.querySelector(`[${FIRST_ATTRIBUTE}]`)?.outerHTML ?? null;
}

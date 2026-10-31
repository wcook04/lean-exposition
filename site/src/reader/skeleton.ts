// A paper before it arrives, the same shape as the page it becomes: the strip, the paper's
// column, the sidecar. It goes straight into each paper's HTML and is what React shows until
// the text is ready, so the first paint does not move. Its stylesheet comes with it, because
// the reader's own arrives with the reader. No script, no import: the build reads this too.

const STYLE = `.reader-shape{display:grid;grid-template-columns:minmax(0,var(--reader-measure));justify-content:center;column-gap:var(--reader-gap);align-items:start;padding-inline:var(--space-6)}
.reader-shape__outline,.reader-shape__side{display:none}
.reader-shape__strip{height:44px;margin-bottom:var(--space-5);border-bottom:1px solid var(--rule)}
.reader-shape__text{display:flex;flex-direction:column;gap:14px}
.reader-shape__text i{display:block;height:13px;background:var(--rule);opacity:.55}
.reader-shape__text i:first-child{width:62%;height:30px;margin-bottom:var(--space-4)}
.reader-shape__words{margin:0;font-family:var(--font-sans);font-size:var(--fs-sm);color:var(--ink-3)}
@media (max-width:700px){.reader-shape{padding-inline:20px}}
@media (min-width:1280px){.reader-shape{grid-template-columns:minmax(0,min(var(--reader-measure),50vw)) minmax(0,1fr);justify-content:start;padding-left:32px;padding-right:0}
.reader-shape__side{display:block;position:sticky;top:var(--topbar-h);height:calc(100vh - var(--topbar-h));margin-left:16px;border-left:1px solid var(--rule)}}
@media (min-width:1501px){.reader-shape{grid-template-columns:var(--reader-outline) minmax(0,var(--reader-measure)) minmax(600px,1fr)}
.reader-shape__outline{display:block}}
@media (min-width:1921px){.reader-shape{--reader-measure:clamp(680px,calc(680px + (100vw - 1920px)*.117),755px)}}
@media (min-width:2100px){.reader-shape{grid-template-columns:var(--reader-outline) minmax(0,var(--reader-measure)) minmax(600px,1040px);justify-content:center}}`;

const LINES = [100, 96, 98, 92, 60, 0, 100, 94, 97, 88, 99, 45];

/** The shape as HTML. `words` is said to assistive technology and shown at the column's head. */
export function readerSkeletonHtml(words = "Loading the paper…"): string {
  const lines = LINES.map((w) => (w ? `<i style="width:${w}%"></i>` : `<i style="visibility:hidden"></i>`)).join("");
  return `<style>${STYLE}</style><div class="reader-shape" aria-busy="true"><div class="reader-shape__outline"></div><div><div class="reader-shape__strip"></div><p class="reader-shape__words" role="status">${words}</p><div class="reader-shape__text"><i></i>${lines}</div></div><div class="reader-shape__side"></div></div>`;
}

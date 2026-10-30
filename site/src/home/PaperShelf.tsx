// The architectural companion stands apart from the three mathematical accounts.
// Each stands as its real first page (rendered from the PDF the link opens, by
// scripts/render-paper-pages.py), with its name, one line on who it is for from the
// site's own descriptions, and two actions: read it on this site, or open its PDF in a
// new tab. A paper whose picture no longer matches its PDF is shown without one.

import { PAPER_PDFS } from "virtual:paper-pdfs";
import { routeHref } from "../app/router";

type PaperKey = keyof typeof PAPER_PDFS;

interface ShelfPaper {
  key: PaperKey;
  name: string;
  /** Who it is for, as the site describes each paper elsewhere. */
  who: string;
  read: string;
  companion?: boolean;
}

const SHELF: ShelfPaper[] = [
  {
    key: "architecture",
    name: "Architectural companion",
    who: "Written for readers who want to know why the result is written up as three accounts linked to one set of records, and how those records and links are made.",
    read: routeHref({ view: "about", anchor: "companion" }),
    companion: true,
  },
];

const base = import.meta.env.BASE_URL;
const plural = (n: number, one: string) => `${n} ${one}${n === 1 ? "" : "s"}`;

export function ArchitectureCompanion() {
  return (
    <aside className="companion" aria-labelledby="companion-heading">
      <div>
        <h3 id="companion-heading">About the three accounts</h3>
        <p>A separate paper on how the accounts and their shared records are made.</p>
      </div>
    <ul className="shelf">
      {SHELF.map((paper) => {
        const pdf = PAPER_PDFS[paper.key];
        const page = pdf.firstPage;
        const href = `${base}${pdf.path}`;
        return (
          <li key={paper.key} className={`shelf__paper${paper.companion ? " shelf__paper--companion" : ""}`}>
            <div className="shelf__stand">
              {page ? (
                // The page and the PDF action open the same file, so only the action is in the Tab order.
                <a className="shelf__sheet" href={href} target="_blank" rel="noopener" aria-hidden="true" tabIndex={-1}>
                  <img
                    src={`${base}${page.src}`}
                    srcSet={page.srcSet.split(", ").map((entry) => `${base}${entry}`).join(", ")}
                    sizes="(min-width: 1100px) 168px, 128px"
                    alt=""
                    width={page.width}
                    height={page.height}
                    loading="lazy"
                    decoding="async"
                  />
                </a>
              ) : null}
            </div>
            <h3 className="shelf__name">{paper.name}</h3>
            <p className="shelf__who">{paper.who}</p>
            <p className="shelf__actions">
              <a href={paper.read}>
                Read it here<span className="sr-only">: {paper.name}</span>
              </a>
              <a href={href} target="_blank" rel="noopener">
                Open PDF, {plural(pdf.pages, "page")}
                <span className="sr-only">: {paper.name}</span>
              </a>
            </p>
          </li>
        );
      })}
    </ul>
    </aside>
  );
}

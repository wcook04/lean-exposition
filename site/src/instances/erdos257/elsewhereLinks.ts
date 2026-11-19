// Where else the #257 work lives: the plain links the old problem page offered
// (practical-formal-verification/maths/problems/erdos_257.html), kept on the front page and
// About. No browser API and no import.meta. Every address is in this file.

/** The papers' repository at the revision this site pins. */
const REVISION = "3368d1e69467aec111eb3244843ad3542171ff96";
const REPO = "https://github.com/wcook04/plectis-erdos";
const PAPER = `${REPO}/blob/${REVISION}/paper/257`;

/**
 * The present problem page, to be kept at this new address when the old one forwards here.
 * It does not exist yet; change this one constant if it moves.
 */
export const OVERVIEW_URL = "https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_257_overview.html";

export interface ElsewhereLink {
  label: string;
  href: string;
}

export interface ElsewhereRow {
  label: string;
  links: ElsewhereLink[];
}

export const ELSEWHERE: ElsewhereRow[] = [
  { label: "The problem", links: [{ label: "Erdős problem #257 on erdosproblems.com", href: "https://www.erdosproblems.com/257" }] },
  {
    label: "The Lean",
    links: [
      { label: "The Lean directory on GitHub", href: `${REPO}/tree/main/lean/ErdosProblems/Erdos257` },
      { label: `The pinned revision, ${REVISION.slice(0, 7)}`, href: `${REPO}/tree/${REVISION}` },
    ],
  },
  {
    label: "Short paper",
    links: [
      { label: "PDF", href: `${PAPER}/erdos-257-mersenne-support-subseries.pdf` },
      { label: ".tex source", href: `${PAPER}/erdos-257-mersenne-support-subseries.tex` },
    ],
  },
  {
    label: "Exposition",
    links: [
      { label: "PDF", href: `${PAPER}/erdos257-expository-sums-never-fractions.pdf` },
      { label: ".tex source", href: `${PAPER}/erdos257-expository-sums-never-fractions.tex` },
    ],
  },
  {
    label: "Long record",
    links: [
      { label: "PDF", href: `${PAPER}/erdos257-mersenne-reasoning-surface.pdf` },
      { label: ".tex source", href: `${PAPER}/erdos257-mersenne-reasoning-surface.tex` },
    ],
  },
  { label: "Maths Map", links: [{ label: "Erdős #257 on the Maths Map", href: "https://wcook04.github.io/practical-formal-verification/maths/universe.html#o=problem%3Aerdos_257" }] },
  { label: "Overview page", links: [{ label: "Worked figures, the 189/388 calculation and the full list of results", href: OVERVIEW_URL }] },
];

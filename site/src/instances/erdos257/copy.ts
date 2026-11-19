// Every sentence of the Erdős #257 site that its author writes himself. Each slot holds the
// literal placeholder "TODO(copy): <slot name>" until he does; the build prints a warning
// naming every slot still holding one (copyTodos in ../registry.ts). Inline TeX between
// single dollar signs is typeset. No count or identifier belongs in this file: every number
// the pages show is read from the edition or the PDFs, and a sentence that needs a number
// is written by the page around this text, never typed here.
// No browser API and no import.meta: vite.config.ts reads this file too.

export type Verdict = "same" | "stronger" | "weaker";

/** A slot not yet written. */
type Todo = `TODO(copy): ${string}`;

export interface ClauseRow {
  /** Exact text of a clause of the Lean statement. */
  lean: string;
  /** The same clause in the short paper's notation, as TeX. */
  tex: string;
  /** What a reader who knows no Lean needs in order to match the two. */
  note: string;
  /** What the Lean clause says against the paper's. */
  verdict: Verdict | Todo;
  /** The step Compare opens for this clause, a graph id; null opens the main theorem. */
  record: string | null;
}

export interface AskedEntry {
  /** The question, as the problem or the papers ask it. */
  asked: string;
  /** What the papers prove about it. */
  proved: string;
  /** What stays open. */
  open: string;
  /** The goal the map opens for this entry, a graph id; null leaves the link out. */
  goal: string | null;
}

export interface ProofStep {
  title: string;
  text: string;
}

export interface LevelWords {
  /** The account's name in the bar and the shelf. */
  short: string;
  /** What it does. */
  job: string;
  /** Who it is written for. */
  reader: string;
}

export const COPY = {
  /** The website's name in the bar and the browser tab, as the family registry will list it. */
  siteName: "Erdős 257 Reader",
  /** The edition's title: the front page's heading, the browser tab and the link preview. */
  title: "Which sums of 1/(2ⁿ − 1) are irrational?",
  /** The line above the title, saying what the site is in one breath. */
  strapline: "Three papers on Erdős problem #257, read beside their Lean proofs and a graph of the argument",
  /** The first paragraph under the title. */
  opening: String.raw`Erdős asked whether $\sum_{a\in A}1/(2^a-1)$ is irrational for every infinite set $A$ of positive integers. The question is open. The papers here prove that the sum is irrational when $A$ satisfies a weighted summability condition, when $A$ has a summable divisor cover, and when $A$ lies in the union of a set of each kind. Each result holds with any integer $b\ge2$ in place of $2$. The simplest case is the one Erdős stated in 1968: every infinite $A$ with $\sum_{a\in A}1/a<\infty$.`,
  /** Who proved what, who formalised it and who made the site. */
  credit: "Made by Will Cook using AI. He built and directed the research; AI agents did most of the research, the drafting and the Lean, and no independent mathematician has reviewed the papers. Erdős proved the case of all positive integers in 1948, and in 1968 the case of pairwise coprime sets with finite reciprocal sum, remarking without details that coprimality could be removed. Duverney and Tachiya proved the squarefree case, and Tao and Teräväinen the case of the primes. Lean is a programming language whose compiler rejects a proof with a wrong step.",
  /** What was asked, what was proved and what stays open: one entry per question. */
  asked: [
    {
      asked: String.raw`Is $X_A(2)=\sum_{a\in A}1/(2^a-1)$ irrational for every infinite set $A$ of positive integers? This is Erdős problem #257.`,
      proved: String.raw`Yes when $\sum_{a\in A}1/a$ is finite, at every integer base $b\ge2$ (short paper, Theorem A.1). Erdős stated this in 1968 without details. More generally, yes when $\sum_{a\in A}h(a)/\bigl(a(2^{h(a)}-1)\bigr)$ is finite, where $h(a)$ is the part of $a$ built from a fixed finite set of primes (Theorem 1.2). Some sets with finite weighted sum have divergent $\sum_{a\in A}1/a$.`,
      open: String.raw`Arbitrary infinite $A$. The conditions are sufficient, and none of them characterises the sets in the problem.`,
      goal: "short.res-weighted-support",
    },
    {
      asked: "Does the joint divisibility of the exponents give irrationality where the weighted condition fails?",
      proved: String.raw`Yes. If $A$ lies in a union of finite sets $F_j$ for which fractional powers of the divisor counts are bounded by positive divisor sums of summable total cost, then $X_A(b)$ is irrational for every integer $b\ge2$ (Theorem 3.1). Neither condition implies the other (Proposition 5.1), and they combine: every infinite subset of $E\cup V$, with $E$ of the first kind and $V$ of the second, has an irrational sum (Theorem 4.1).`,
      open: "Corollary 5.2 exhibits a set that lies in neither class and needs the combined theorem. It has no Lean proof at the revision this site pins.",
      goal: "short.res-mixed-supports",
    },
    {
      asked: String.raw`Is a prescribed rational number, such as $1/2$ or $1/21$, equal to $X_A(2)$ for some set $A$?`,
      proved: String.raw`For a finite set $F$, the multiplicative order of $b$ modulo the reduced denominator of $X_F(b)$ equals the least common multiple of $F$ (Theorem B.1), so $1/21$ is the sum of no finite set. Theorems C.1 and D.1 to D.3 give tests for membership.`,
      open: String.raw`The tests decide neither $1/2$ nor $1/21$ for infinite sets.`,
      goal: "short.res-period",
    },
  ] as AskedEntry[],
  /** How the proof goes, in order. */
  proofSteps: [
    {
      title: "Compare a multiple of the sum with an integer",
      text: String.raw`For a positive integer $N$, the displacement $\Delta_{b,A}(N)=\sum_{a\in A}(b^{N\bmod a}-1)/(b^a-1)$ equals $(b^N-1)X_A(b)$ minus an integer, and it is positive when $A$ is infinite. If $X_A(b)=p/q$, then $q\,\Delta_{b,A}(N)$ is a positive integer, so $\Delta_{b,A}(N)\ge1/q$. It therefore suffices to find displacements that tend to zero.`,
    },
    {
      title: "Take N to be a multiple of a modulus",
      text: String.raw`When $N$ is a multiple of $Q$, each exponent dividing $Q$ contributes nothing. An exponent that shares a large common divisor with $Q$ has a small mean over a complete period of its residues.`,
    },
    {
      title: "Average over dyadic lengths",
      text: String.raw`The bound for an incomplete period lacks the factor $1/a$. Averaging over the lengths $2^j$ restores it: an exponent enters the truncated error only once the sampled range reaches it, and the reciprocals of the later lengths form a geometric tail bounded by a multiple of $1/a$.`,
    },
    {
      title: "Choose one index",
      text: String.raw`The mean of the displacements over the sampled indices is then small, so some sampled $N$ has $\Delta_{b,A}(N)$ below any prescribed $\varepsilon$. This contradicts $\Delta_{b,A}(N)\ge1/q$. Both criteria use the same average, so for a union one index makes both errors small.`,
    },
  ] as ProofStep[],
  /** Each level of the argument: the Lean, then the three papers. */
  levels: {
    lean: { who: "Statements and proofs written for the Lean compiler, from Will Cook's public repository." },
    long: { short: "Long record", job: "Detailed proofs, computations, attempted approaches and the obstructions they met.", reader: "Written so that a reader can examine any single step." },
    short: { short: "Short paper", job: "The three criteria with their proofs, the comparison of their classes, and the limits of the method.", reader: "Written for readers who know analytic number theory." },
    expository: { short: "Exposition", job: "The reciprocal-summable case at base two, built from a worked example with doubling exponents.", reader: "Written for readers new to irrationality proofs. It starts from fractions." },
  } satisfies { lean: { who: string } } & Record<"long" | "short" | "expository", LevelWords>,
  /** The main theorem, clause by clause, beside its Lean statement. */
  clauses: {
    /** The table's heading. */
    heading: "Theorem A.1, clause by clause",
    /** The paragraph beside the table. */
    intro: "Theorem A.1 of the short paper is the statement Erdős gave in 1968. Its Lean statement is irrational_erdosSupportSeries_of_summable_reciprocal, which also allows the set to contain 0. The exposition proves the theorem at base two only, so the Lean statement says more than the exposition's Theorem 1 in the base as well. An AI agent compared the clauses, and no independent mathematician has reviewed the comparison.",
    rows: [
      {
        lean: "(b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)",
        tex: String.raw`\text{every integer } b\ge2,\quad A\subseteq\mathbb{N}_{>0}\ \text{infinite}`,
        note: "The base and the set. The Lean allows A to contain 0, which the paper excludes. Lean's division by 0 gives 0, so the exponent 0 adds 0 to both sums, and on sets of positive integers the two statements agree. The exposition's Theorem 1 fixes b = 2.",
        verdict: "stronger",
        record: "short.res-reciprocal-support",
      },
      {
        lean: "(hsum : Summable (reciprocalSupportTerm A))",
        tex: String.raw`\sum_{a\in A}\frac1a<\infty`,
        note: "reciprocalSupportTerm A takes the value 1/a at a in A and 0 elsewhere.",
        verdict: "same",
        record: "short.res-reciprocal-support",
      },
      {
        lean: "Irrational (erdosSupportSeries b A)",
        tex: String.raw`X_A(b)=\sum_{a\in A}\frac1{b^a-1}\ \text{is irrational}`,
        note: "erdosSupportSeries b A is the sum over all natural numbers a of 1/(b^a − 1) for a in A and 0 elsewhere.",
        verdict: "same",
        record: "short.res-reciprocal-support",
      },
    ] as ClauseRow[],
  },
  /** The About page: sections in order, each a heading and its paragraphs. */
  about: [
    {
      heading: "What this site is",
      paragraphs: [
        "Three papers on Erdős problem #257 at three levels of detail, each read beside the Lean statements of its results. A statement with a tick in the margin opens its Lean. A graph of the argument follows the passage on screen, Compare sets each step side by side at every level, and What ran lists every recorded run with its outcome.",
        "The problem is open. The papers prove sufficient conditions for irrationality and say where the method stops.",
      ],
    },
    {
      heading: "Where the papers and the Lean come from",
      paragraphs: [
        "The papers and the Lean are Will Cook's, from the public repository wcook04/plectis-erdos at one pinned revision. The reading copies are transcribed from the published text by a program, which compares every word with the source and typesets every formula. The PDFs are the published files, unchanged.",
        "Will Cook built and directed the research and reviewed the claims when he could. AI agents did most of the research, the drafting and the Lean. No independent mathematician has reviewed the papers.",
      ],
    },
    {
      heading: "What a link between a paper and the Lean means",
      paragraphs: [
        "Most links from a printed result to its Lean declaration are copied from the evidence record that the papers themselves publish. The others were written for this site by an AI agent that read both sides. The site says which kind each link is.",
        "A link says where to look. A program confirms that both ends exist in the pinned files. Whether the paper's sentence and the Lean statement mean the same is a reading, recorded with the name of who made it, and no independent mathematician has reviewed these readings.",
      ],
    },
    {
      heading: "What was run",
      paragraphs: [
        "The Lean was compiled and compared by public GitHub Actions runs in the source repositories, and this site records those runs with their outcomes, failures included. Nothing was compiled again for this site, and the statuses it shows are the ones those runs recorded.",
      ],
    },
  ] as { heading: string; paragraphs: string[] }[],
  /** llms.txt: the summary line under its title. The rest of the file is written from the data. */
  llms: "Erdős problem #257 asks whether the sum of 1/(2^a - 1) over every infinite set A of positive integers is irrational. It is open. This site holds three papers that prove irrationality under sufficient conditions on A, beside the Lean proofs of their statements and a graph of the argument.",
};

export type Copy = typeof COPY;

/** True while a slot is unwritten, so a page can show it as plain text rather than typeset it. */
export const isTodo = (text: string) => text.includes("TODO(copy)");

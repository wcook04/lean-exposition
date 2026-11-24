// Reader identity marks simplified from the papers’ figures, notation and constructions.
// The same inline SVG is rendered by the static shell and the interactive header.
const marks = {
  // Euler, Figure 1: k turns from E₃ toward E₁ under a strong shear.
  euler: '<path d="M7 20V4m-3 3 3-3 3 3" opacity=".6"/><path d="m7 20 13-9m-4-.5 4 .5-.9 3.9"/><path d="M7 12a8 8 0 0 1 6.5 3.5"/>',
  // Navier–Stokes, §5.1: the radial cutoff is one near the origin and falls to zero outside.
  "navier-stokes": '<path d="M3 19h18M12 19V4" opacity=".4"/><path d="M3 18c4 0 3-10 7-10h4c4 0 3 10 7 10"/><path d="M9 19V9m6 10V9" opacity=".33" stroke-dasharray="1 3"/>',
  // PCP, Theorem 1.1: the verifier reads only a few bits of a proof.
  pcp: '<path d="M3 11h18v7H3zM7.5 11v7m4.5-7v7m4.5-7v7" opacity=".55"/><path d="M5.3 5v3m13.4-3v3"/><path d="M5.3 14.5h.1m13.3 0h.1" stroke-width="2.8"/>',
  // PCP guide: the Lean verifier definition is reached through the guide’s module/file tree.
  "pcp-reading-guide": '<path d="M6 4h9l4 4v12H6zM15 4v5h4" opacity=".58"/><path d="M9 10v6h6m-6-3h4"/><path d="M9 10h.1m4 3h.1m2 3h.1" stroke-width="2.6"/>',
  // SK, main theorem: the zero-temperature order parameter has full support on [0,1).
  "qaoa-sk": '<path d="M2.5 12h19M5.5 9v6m13-6v6" opacity=".45"/><path d="M5.5 12h11.3" stroke-width="2.8"/><circle cx="18.5" cy="12" r="2" fill="var(--ground, white)"/>',
  // Contextual Embeddings, §2: a reference in the inner scope resolves to the outer binder.
  "contextual-embeddings": '<path d="M7 4c-4 3-4 13 0 16m10-16c4 3 4 13 0 16M11 7c-2.5 2-2.5 8 0 10" opacity=".63"/><path d="M14 14c0-5-4-6-7-5m1 3-1-3 3-1"/><path d="M14 14h.1" stroke-width="2.7"/>',
  // Coupled spring, the paper’s oscillator schematic: two masses with a shared middle spring.
  "coupled-spring": '<path d="M2 6v12m20-12v12M2 12h2l1.5-2 1.5 2m10 0 1.5-2 1.5 2h2M10 12l1-2 2 4 1-2"/><path d="M7 9h3v6H7zm7 0h3v6h-3z" fill="currentColor" stroke="none"/>',
  // Erdős #257, the first four reciprocal terms at base two: 1, 1/3, 1/7 and 1/15.
  "erdos-257": '<path d="M3 20h18" opacity=".48"/><path d="M5 20V4m5 16v-5.3m5 5.3v-2.3m5 2.3v-1.1" stroke-width="2.2"/>',
  // Quartic, the hidden zero in a column of the hard distribution (short paper, §2).
  quartic: '<path d="M4 4h16v16H4zM9.3 4v16m5.4-16v16M4 9.3h16M4 14.7h16" opacity=".52"/><circle cx="12" cy="12" r="1.5"/><path d="M10 4h4m-4 16h4" stroke-width="2.5"/>',
  // SMT-LIB, §3.9: commands are applications, written between parentheses.
  smtlib: '<path d="M7 4c-4 3-4 13 0 16m10-16c4 3 4 13 0 16"/><path d="M9 9h6m-6 3h4m-4 3h6" opacity=".72"/>',
  // RH, Statement 2.1: the real part of each nontrivial zero is 1/2.
  "riemann-hypothesis": '<path d="M3 12h18M6 4v16m12-16v16" opacity=".41"/><path d="M12 3v18"/><circle cx="12" cy="7" r="1.6" fill="currentColor" stroke="none"/><circle cx="12" cy="17" r="1.6" fill="currentColor" stroke="none"/>',
} as const;

export function paperMarkHtml(id: string): string {
  const key = id === "erdos257" ? "erdos-257" : id;
  if (!Object.hasOwn(marks, key)) return "";
  return `<svg class="paper-mark" data-paper-mark="${key}" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width="22" height="22" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round" stroke-linecap="round">${marks[key as keyof typeof marks]}</svg>`;
}

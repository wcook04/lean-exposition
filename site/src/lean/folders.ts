// One plain sentence on each folder of OpenAI's Lean source, written from reading the
// module names and the theorems inside each folder at the pinned revision.

export const FOLDER_WORDS: Record<string, string> = {
  ComparatorChallenges: "The definitions and the two main statements copied out alone, with sorry in place of each proof, as challenge files for a Comparator run.",
  "OAI/Probability/SKSupport": "The definitions of the model and the final full support theorem.",
  "OAI/Probability/SKSupport/Backward": "Solutions of the backward equation: their shape, comparison, gradient bounds and what happens on a terminal plateau.",
  "OAI/Probability/SKSupport/Control": "The control problem behind the value function: payoffs, grid approximations, and the value's Lipschitz and convexity properties.",
  "OAI/Probability/SKSupport/Density": "Densities on finite grids, Gaussian tails and the ratio comparisons that give coercivity.",
  "OAI/Probability/SKSupport/Diffusion": "The diffusion driven by the gradient: its construction by Picard iteration, feedback verification and uniqueness.",
  "OAI/Probability/SKSupport/Foundations": "Groundwork used throughout: the cascade, semigroups, variance heat curves, step data and finite values.",
  "OAI/Probability/SKSupport/Moments": "The square moment and curvature moment along the diffusion, and the equations they satisfy.",
  "OAI/Probability/SKSupport/Parabolic": "Comparison principles for parabolic inequalities, and Burgers, forward and tilted evolutions.",
  "OAI/Probability/SKSupport/Regularity": "Smoothness of the value function: its derivatives, their bounds and their limits.",
  "OAI/Probability/SKSupport/Support": "The final argument: contact, the variational inequality and the exclusion of gaps.",
  "OAI/Probability/SKValue": "The definitions and the main statement of the ground-state value result.",
  "OAI/Probability/SKValue/Coercivity": "Coercivity estimates, pointwise and integrated, including the zero-gap case.",
  "OAI/Probability/SKValue/Control": "Controls and verification for the value: progressive controls, stability and regularity on strips.",
  "OAI/Probability/SKValue/Equations": "Estimates for the equations: comparison principles, polynomial moments, forced generators and strip bounds.",
  "OAI/Probability/SKValue/Evolution": "The Parisi evolution: Cole-Hopf, heat kernel bounds, grid convergence and assembly of the Parisi value.",
  "OAI/Probability/SKValue/Gaussian": "Gaussian building blocks: Brownian coordinates, density derivatives and split profile estimates.",
  "OAI/Probability/SKValue/GroundState": "The passage to the ground state: Guerra bounds, tree and cascade laws, Gumbel maxima and rounding to spins.",
  "OAI/Probability/SKValue/Processes": "Diffusion processes for the value: existence, Euler meshes, martingale facts and gradient isometries.",
  "OAI/Probability/SKValue/Variation": "First variations, contact at a minimiser and the ground-state value derived from contact.",
};

/** The folder's name for a reader: its path below `OAI/Probability`. */
export const folderLabel = (path: string) => path.replace(/^OAI\/Probability\//, "");

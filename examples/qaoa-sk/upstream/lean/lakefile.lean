-- Derived for the qaoa-sk example from the Apache-2.0 OpenAI package.
-- Modified: retain mathlib, the two selected roots, and ComparatorChallenges;
-- omit unrelated dependencies and compatibility-patch hooks.
-- Original configuration: ../provenance/lakefile.lean.

import Lake

open Lake DSL

package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib OAI where
  roots := #[`OAI.Probability.SKSupport.Main, `OAI.Probability.SKValue.Main]

lean_lib ComparatorChallenges where
  globs := #[`ComparatorChallenges.+]

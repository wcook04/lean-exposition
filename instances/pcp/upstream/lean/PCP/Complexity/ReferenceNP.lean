/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file `vendor/LICENSE`.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.NP

/-!
# Polynomial normal form for the reference NP class

The imported definitions are the unmodified ComplexityLib definitions from commit
`add0aca8ee0d71e68969f2cb45cf91554a50f787`. This small adapter repeats the proof of
`Complexity.mem_NP_iff_decidesInTime_polynomial_internal` from upstream
`Classes/NP/Internal/Closure.lean`, without importing its unrelated machine
composition dependency. It does not redefine `Complexity.NP` or its machine model.
-/

namespace PCP.ReferenceNP

/-- Reference NP uses exactly the languages decided within an everywhere-valid
natural-polynomial bound by one of its finite nondeterministic machines. -/
theorem mem_iff_polynomial {L : Complexity.Language} :
    L ∈ Complexity.NP ↔ ∃ (k : ℕ) (N : Complexity.NTM k) (p : Polynomial ℕ),
      N.DecidesInTime L p.eval := by
  constructor
  · intro hL
    obtain ⟨d, k, N, T, hdec, hbig⟩ := Set.mem_iUnion.mp hL
    obtain ⟨p, hp⟩ := Complexity.BigO.pow_polynomial_bound hbig
    exact ⟨k, N, p, hdec.mono hp⟩
  · rintro ⟨k, N, p, hdec⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p.natDegree, k, N, p.eval, hdec, ?_⟩
    exact Complexity.BigO.of_polynomial_bound p fun _ => le_rfl

end PCP.ReferenceNP

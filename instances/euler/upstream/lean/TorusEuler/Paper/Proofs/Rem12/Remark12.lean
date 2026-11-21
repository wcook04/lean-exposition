import TorusEuler.Paper.Auxiliary.Statements
import TorusEuler.AuxiliaryTerminalSmoothness
import TorusEuler.PeriodicEulerUniqueness

/-! # Proof of Remark 1.2 (library) -/

open Filter Set

namespace TorusEuler.Paper

namespace Lib.Rem12

/-- **Glue.** A smooth periodic-lift extension through `T` away from the origin gives the
extension of the statement (`SmoothTerminalExtension`), with the neighbourhood
`O = ℝ × offOrigin`. -/
theorem smoothTerminalExtension_of_hasSmoothOffOriginExtension {T : ℝ} {u : Velocity}
    (h : HasSmoothOffOriginExtension T u) : SmoothTerminalExtension T u := by
  obtain ⟨g, hg, hper, heq⟩ := h
  refine ⟨univ ×ˢ offOrigin, g, isOpen_univ.prod isOpen_offOrigin,
    prod_mono (subset_univ _) le_rfl, ?_, hper, heq⟩
  exact hg.mono (union_subset (prod_mono (subset_univ _) le_rfl) le_rfl)

/-- **Uniqueness of the maximal solution** (periodic Euler uniqueness, `velocity_eq_on_common_interval`,
and maximality on both sides): two maximal Euler solutions with the same initial datum have the
same lifetime and agree on `[0,T)`. -/
theorem maximal_unique {T T' : ℝ} {u v : Velocity} {p q : Pressure}
    (hu : IsMaximalEulerSolution T u p) (hv : IsMaximalEulerSolution T' v q) (h0 : v 0 = u 0) :
    T' = T ∧ EqOn v u (Ico 0 T) := by
  have hEq := hv.1.velocity_eq_on_common_interval hu.1 h0
  have h1 : T ≤ T' := by
    by_contra! hSmall
    apply hv.2 T hSmall
    refine ⟨u, p, hu.1, fun t ht => ?_⟩
    exact (hEq t (by simpa only [min_eq_left hSmall.le] using ht)).symm
  have h2 : T' ≤ T := by
    by_contra! hSmall
    apply hu.2 T' hSmall
    refine ⟨v, q, hv.1, fun t ht => ?_⟩
    exact (hEq t (by simpa only [min_eq_right hSmall.le] using ht))
  have hT : T' = T := le_antisymm h2 h1
  exact ⟨hT, fun t ht => hEq t (by simpa only [hT, min_self] using ht)⟩

end Lib.Rem12

/-- Proof of **Remark 1.2** (sections/01_problem.tex:80-84), proved from the library, not
one-to-one with the auxiliary note (decision D28): the Lean statements of the note's
results (still compiled in `Paper.Aux.Statement`, unproved and outside the spine) (Theorem 1.1, Lemmas 1.2 and 1.3) quantified over every cutoff symbol, every admissible
threshold and every construction satisfying the conclusions of Theorem 7.1, while the library
results are existential (the dyadic cutoff symbol, `b` large, the library's own scheduled
construction), so they could not be transferred to those statements. The remark only
asserts existence of a solution, and the library's `auxiliaryTerminalSmoothness` supplies one:
a velocity `u` with `EulerSingularityWitness (u 0) T u p` (all conclusions of Theorem 1.1,
(1.1)-(1.3)) and a smooth periodic extension through `T` away from the origin
(`HasSmoothOffOriginExtension`, converted to `SmoothTerminalExtension` with `O = ℝ × offOrigin`).
The uniqueness clause is derived from the maximality conjunct of the witness and periodic Euler
uniqueness (`IsEulerSolution.velocity_eq_on_common_interval`): a second maximal solution with the
same initial datum agrees with `u` on the common interval, and maximality of both forces equal
lifetimes. -/
theorem Proof.remark_1_2 : Statement.remark_1_2 := by
  obtain ⟨b, threshold, N₁, -, hSchedule⟩ := auxiliaryTerminalSmoothness
  obtain ⟨P, c, -, -, -, -, -, T, u, p, -, -, -, hW, hExt⟩ := hSchedule N₁ le_rfl
  exact ⟨u 0, T, u, p, hW, fun T' v q hv hv0 => Lib.Rem12.maximal_unique hW.2.2.2.2.1 hv hv0,
    Lib.Rem12.smoothTerminalExtension_of_hasSmoothOffOriginExtension hExt⟩

end TorusEuler.Paper

import TorusEuler.Paper.Proofs.S2a.Library.Angle

/-! # Proof of Lemma 2.5

The conditional proof `TorusEuler.Paper.Proof.lemma_2_5` of
`TorusEuler.Paper.Statement.lemma_2_5` (`cc:lem:model`,
`sections/03_amplification.tex:452-535`). Lemma 2.5 cites no numbered result. -/

open Set

namespace TorusEuler.Paper

open Lib.S2a ReferenceRiccati

/-- Proof of **Lemma 2.5** (`cc:lem:model`) following
`sections/03_amplification.tex:471-535`. The row cites no numbered result, so there are no
hypotheses; the proof uses the library theory of the Riccati problem (2.12)
(`TorusEuler.ReferenceRiccati`, the carrier of the row's own content
`PaperAffine.referenceModel`), after translating `φ` of (2.4) by `cos φ = s`,
`tan φ = x`, `ετ sin 2φ = damping` (`Lib.S2a.referenceSlope_iff`).

* Ansatz (2.13) (`:472-486`): every solution `Y` is `referenceY ε e` with
  `e = deviation ε Y` (`referenceY_deviation`), which is (2.13) since
  `(1/4)ετ sin 2φ = damping/4`.
* (2.14) (`:488-489`): integrating (2.13) with `(log cos φ)' = -(1/2)ετ sin 2φ`,
  `referenceV_ratio_decomposition`.
* `0 ≤ e ≤ ε/8` and global existence (`:490-499`): `riccati_deviation_bounds_Ici`
  (barriers for `e' = cos φ(-2e - e² + (ε/2) sin φ cos φ)`) and `riccati_exists_Ici`;
  uniqueness of the solution, which the text uses in "the solution `Y`", is
  `riccati_unique_Ici`.
* `|Y| ≤ 1` (`:501-509`): `riccati_abs_le_one`.
* The unique zero `τ_m` with `2 ≤ ετ_m ≤ 3` and the signs (`:511-522`):
  `riccati_turning_time`; hence `a_ref` is largest at `τ_m`
  (`referenceV_le_at_turning_time`).
* `log a_ref(τ_m) ≥ ε^{-1/2} - 1` (`:524-534`): `riccati_gain_bound`. -/
theorem Proof.lemma_2_5 : Statement.lemma_2_5 := by
  intro ε hε hε₁
  refine ⟨?_, ?_⟩
  · obtain ⟨Y, e, -, hY0, hY, -⟩ := riccati_exists_Ici hε hε₁
    exact ⟨Y, referenceSlope_iff.2 ⟨hY0, hY⟩⟩
  · intro Y hYs
    obtain ⟨hY0, hY⟩ := referenceSlope_iff.1 hYs
    have hYc : ContinuousOn Y (Ici 0) := fun τ hτ => (hY τ hτ).continuousWithinAt
    have hform : Y = referenceY ε (deviation ε Y) := (referenceY_deviation ε Y).symm
    have he : MapsTo (deviation ε Y) (Ici 0) (Icc 0 (ε / 8)) :=
      riccati_deviation_bounds_Ici hε hY0 hY
    obtain ⟨τm, hm, hz, hpos, hneg⟩ := riccati_turning_time hε hε₁ hY hform he
    have hτm : 0 ≤ τm := (div_nonneg (by norm_num) hε.le).trans hm.1
    have hnonneg : ∀ τ ∈ Icc 0 τm, 0 ≤ Y τ := by
      intro τ hτ
      rcases hτ.2.lt_or_eq with hlt | rfl
      · exact (hpos τ ⟨hτ.1, hlt⟩).le
      · exact hz.ge
    refine ⟨fun Z hZ => riccati_unique_Ici hε hε₁ hY0 (referenceSlope_iff.1 hZ).1 hY
        (referenceSlope_iff.1 hZ).2, riccati_abs_le_one hε hε₁ hY0 hY, deviation ε Y,
      fun τ hτ => he hτ, ?_, ?_, τm, ?_, ?_, ?_, hpos, hneg, ?_, ?_⟩
    · intro τ _
      conv_lhs => rw [hform]
      rw [referenceY, cos_referenceAngle, sin_two_referenceAngle]
      ring
    · intro τ hτ
      have h := referenceV_ratio_decomposition hform hYc le_rfl (show (0 : ℝ) ≤ τ from hτ)
      rw [referenceV_zero, div_one, s_zero, div_one] at h
      change referenceV Y τ = _
      rw [h, cos_referenceAngle]
      congr 2
      apply intervalIntegral.integral_congr
      intro u _
      simp only [cos_referenceAngle, mul_comm]
    · intro τ hτ
      constructor
      · intro hZero
        rcases lt_trichotomy τ τm with ht | ht | ht
        · exact ((hpos τ ⟨hτ, ht⟩).ne' hZero).elim
        · exact ht
        · exact ((hneg τ ht).ne hZero).elim
      · rintro rfl
        exact hz
    · simpa only [mul_comm ε] using (div_le_iff₀ hε).mp hm.1
    · simpa only [mul_comm ε] using (le_div_iff₀ hε).mp hm.2
    · intro τ hτ
      exact referenceV_le_at_turning_time hτm hYc hnonneg (fun t ht => by
        rcases (show τm ≤ t from ht).lt_or_eq with hlt | rfl
        · exact (hneg t hlt).le
        · exact hz.le) τ hτ
    · change _ ≤ Real.log (Real.exp _)
      rw [Real.log_exp]
      exact riccati_gain_bound hε hε₁ hm.1 hform he hYc hnonneg

end TorusEuler.Paper

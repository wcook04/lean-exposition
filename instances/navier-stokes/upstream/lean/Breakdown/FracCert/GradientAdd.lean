import Breakdown.FracCert.StGradientAdd

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.SteadyCert

namespace GradientAddInternal

lemma abs_le_one_add_sq (a : ℝ) : |a| ≤ 1 + a ^ 2 := by
  nlinarith [sq_abs a, abs_nonneg a, sq_nonneg (|a| - 1)]

lemma locInt_of_bound {f g : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : IsLocalSquareIntegrable (fun y => g y ^ 2)) (hb : ∀ y, |f y| ≤ |g y|) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hfin : volume K < ⊤ := hK.measure_lt_top
  have h1 : IntegrableOn (fun _ : Space => (1 : ℝ)) K volume := integrableOn_const hfin.ne
  refine Integrable.mono' (h1.add (hg K hK)) hf.restrict (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  calc |f y| ≤ |g y| := hb y
    _ ≤ 1 + g y ^ 2 := abs_le_one_add_sq _

lemma pair_integrable {f : Space → ℝ} (hf : LocallyIntegrable f volume) {φ : Space → ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) : Integrable (fun y => φ y * f y) volume := by
  simpa [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hφ hs

lemma comp_locInt {Q : Space → Space} (hQ : AEStronglyMeasurable Q volume)
    (h2 : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2)) (j : Fin 3) :
    LocallyIntegrable (fun y => inner ℝ (Q y) (unitVector j)) volume := by
  refine locInt_of_bound (g := fun y => ‖Q y‖) (hQ.inner aestronglyMeasurable_const) h2 ?_
  intro y
  rw [abs_norm]
  calc |inner ℝ (Q y) (unitVector j)| ≤ ‖Q y‖ * ‖unitVector j‖ := abs_real_inner_le_norm _ _
    _ = ‖Q y‖ := by simp [unitVector]

lemma deriv_continuous {φ : Space → ℝ} (hφ : IsTestScalar φ) (v : Space) :
    Continuous fun y => fderiv ℝ φ y v :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma deriv_support {φ : Space → ℝ} (hφ : IsTestScalar φ) (v : Space) :
    HasCompactSupport fun y => fderiv ℝ φ y v :=
  (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L v) (by simp)

lemma aesm_of_pairings {q : Space → ℝ} (j : Fin 3)
    (h : ∀ φ : Space → ℝ, IsTestScalar φ →
      AEStronglyMeasurable (fun y => fderiv ℝ φ y (unitVector j) * q y) volume) :
    AEStronglyMeasurable q volume := by
  let ℓ : Space →L[ℝ] ℝ := EuclideanSpace.proj j
  have key : ∀ n : ℕ, AEStronglyMeasurable q (volume.restrict (Metric.ball (0 : Space) (n + 1))) := by
    intro n
    let χ : ContDiffBump (0 : Space) := ⟨(n : ℝ) + 1, n + 2, by positivity, by linarith⟩
    let φ : Space → ℝ := fun y => ℓ y * χ y
    have hφ : IsTestScalar φ := ⟨ℓ.contDiff.mul χ.contDiff, χ.hasCompactSupport.mul_left⟩
    have hd : ∀ y ∈ Metric.ball (0 : Space) (n + 1), fderiv ℝ φ y (unitVector j) = 1 := by
      intro y hy
      have hev : φ =ᶠ[nhds y] ⇑ℓ := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
        have hz' : z ∈ Metric.closedBall (0 : Space) χ.rIn := Metric.ball_subset_closedBall hz
        simp only [φ]
        rw [χ.one_of_mem_closedBall hz', mul_one]
      rw [hev.fderiv_eq, ContinuousLinearMap.fderiv]
      simp [ℓ, unitVector]
    refine (h φ hφ).restrict.congr ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
    rw [hd y hy, one_mul]
  have := (aestronglyMeasurable_iUnion_iff (μ := volume) (f := q)).2 key
  rwa [Metric.iUnion_ball_nat_succ, Measure.restrict_univ] at this

lemma pairing_zero {Q : Space → Space} {q : Space → ℝ} (hQ : AEStronglyMeasurable Q volume)
    (h2 : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2))
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j))
    (hq : ¬ AEStronglyMeasurable q volume) (ψ : Space → ℝ) (hψ : IsTestScalar ψ) (j : Fin 3) :
    ∫ y, ψ y * inner ℝ (Q y) (unitVector j) = 0 := by
  have hbad : ∃ φ, IsTestScalar φ ∧
      ¬ AEStronglyMeasurable (fun y => fderiv ℝ φ y (unitVector j) * q y) volume := by
    by_contra hc
    push Not at hc
    exact hq (aesm_of_pairings j hc)
  obtain ⟨φ, hφ, hφb⟩ := hbad
  have zero_of_bad : ∀ θ : Space → ℝ, IsTestScalar θ →
      ¬ AEStronglyMeasurable (fun y => fderiv ℝ θ y (unitVector j) * q y) volume →
      ∫ y, θ y * inner ℝ (Q y) (unitVector j) = 0 := by
    intro θ hθ hb
    have h0 : ∫ y, fderiv ℝ θ y (unitVector j) * q y = 0 :=
      integral_undef (fun hi => hb hi.aestronglyMeasurable)
    have := hw θ hθ j
    rw [h0] at this
    linarith
  by_cases hg : AEStronglyMeasurable (fun y => fderiv ℝ ψ y (unitVector j) * q y) volume
  · have hs : IsTestScalar (fun y => ψ y + φ y) := ⟨hψ.1.add hφ.1, hψ.2.add hφ.2⟩
    have hsb : ¬ AEStronglyMeasurable
        (fun y => fderiv ℝ (fun y => ψ y + φ y) y (unitVector j) * q y) volume := by
      intro hm
      apply hφb
      refine (hm.sub hg).congr (Filter.Eventually.of_forall fun y => ?_)
      have hadd : fderiv ℝ (fun y => ψ y + φ y) y = fderiv ℝ ψ y + fderiv ℝ φ y :=
        (((hψ.1.differentiable (by simp)) y).hasFDerivAt.add
          ((hφ.1.differentiable (by simp)) y).hasFDerivAt).fderiv
      simp only [Pi.sub_apply]
      rw [hadd, add_apply]
      ring
    have e1 := zero_of_bad _ hs hsb
    have e2 := zero_of_bad φ hφ hφb
    have hiQ := comp_locInt hQ h2 j
    have i1 := pair_integrable hiQ hψ.1.continuous hψ.2
    have i2 := pair_integrable hiQ hφ.1.continuous hφ.2
    have hsum : ∫ y, (ψ y + φ y) * inner ℝ (Q y) (unitVector j) =
        (∫ y, ψ y * inner ℝ (Q y) (unitVector j)) + ∫ y, φ y * inner ℝ (Q y) (unitVector j) := by
      rw [← integral_add i1 i2]
      congr 1
      ext y
      ring
    linarith
  · exact zero_of_bad ψ hψ hg

end GradientAddInternal

open GradientAddInternal

theorem gradientAdd : GradientAddStatement := by
  intro Q R ⟨q, hq2, hQ2, hQm, hqw⟩ ⟨r, hr2, hR2, hRm, hrw⟩
  have hSm : AEStronglyMeasurable (fun y => Q y + R y) volume := hQm.add hRm
  have hS2 : IsLocalSquareIntegrable (fun y => ‖Q y + R y‖ ^ 2) := by
    intro K hK
    refine Integrable.mono' (((hQ2 K hK).const_mul 2).add ((hR2 K hK).const_mul 2))
      ((hSm.norm.pow 2).restrict) (Filter.Eventually.of_forall fun y => ?_)
    have := norm_add_le (Q y) (R y)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) this 2, sq_nonneg (‖Q y‖ - ‖R y‖)]
  have split : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, φ y * inner ℝ (Q y + R y) (unitVector j) =
        (∫ y, φ y * inner ℝ (Q y) (unitVector j)) + ∫ y, φ y * inner ℝ (R y) (unitVector j) := by
    intro φ hφ j
    rw [← integral_add (pair_integrable (comp_locInt hQm hQ2 j) hφ.1.continuous hφ.2)
      (pair_integrable (comp_locInt hRm hR2 j) hφ.1.continuous hφ.2)]
    congr 1
    ext y
    rw [inner_add_left]
    ring
  by_cases hqm : AEStronglyMeasurable q volume
  · by_cases hrm : AEStronglyMeasurable r volume
    · refine ⟨fun y => q y + r y, ?_, hS2, hSm, ?_⟩
      · intro K hK
        refine Integrable.mono' (((hq2 K hK).const_mul 2).add ((hr2 K hK).const_mul 2))
          (((hqm.add hrm).pow 2).restrict) (Filter.Eventually.of_forall fun y => ?_)
        simp only [Pi.add_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (q y - r y)]
      · intro φ hφ j
        have hqi := locInt_of_bound (g := q) hqm hq2 (fun y => le_rfl)
        have hri := locInt_of_bound (g := r) hrm hr2 (fun y => le_rfl)
        have hd := deriv_continuous hφ (unitVector j)
        have hds := deriv_support hφ (unitVector j)
        have hexp : (fun y => fderiv ℝ φ y (unitVector j) * (q y + r y)) =
            fun y => fderiv ℝ φ y (unitVector j) * q y + fderiv ℝ φ y (unitVector j) * r y := by
          ext y
          ring
        rw [hexp, integral_add (pair_integrable hqi hd hds) (pair_integrable hri hd hds),
          hqw φ hφ j, hrw φ hφ j, split φ hφ j]
        ring
    · refine ⟨q, hq2, hS2, hSm, fun φ hφ j => ?_⟩
      rw [split φ hφ j, pairing_zero hRm hR2 hrw hrm φ hφ j, hqw φ hφ j]
      ring
  · refine ⟨r, hr2, hS2, hSm, fun φ hφ j => ?_⟩
    rw [split φ hφ j, pairing_zero hQm hQ2 hqw hqm φ hφ j, hrw φ hφ j]
    ring

end Breakdown.SteadyCert

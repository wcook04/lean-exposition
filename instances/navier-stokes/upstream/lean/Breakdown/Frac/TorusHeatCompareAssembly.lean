import Breakdown.Frac.StTorusShell
import Breakdown.Torus.HeatComparisonAssembly
import Breakdown.Torus.HeatComparisonFreeAssembly

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracHeatCompare.Internal

theorem simScale_pos {α μ : ℝ} (hμ : 0 < μ) : 0 < simScale α μ := Real.rpow_pos_of_pos hμ _

theorem simScale_lt {α μ m : ℝ} (hα : 0 < α) (hμ : 0 < μ) (hm : 0 < m) (h : μ < m ^ α) :
    simScale α μ < m := by
  unfold simScale
  have h1 : μ ^ (1 / α) < (m ^ α) ^ (1 / α) := Real.rpow_lt_rpow hμ.le h (by positivity)
  rw [one_div, Real.rpow_rpow_inv hm.le hα.ne'] at h1
  rw [one_div]
  exact h1

theorem fracGradDensity_eq (α : ℝ) (j : Fin 3) (τ : ℝ) (A : Space → Space) (y : Space) :
    fracGradDensity α j τ A y = fun ξ => expChar y ξ •
      ((2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec A ξ))) := by
  funext ξ
  simp only [fracGradDensity, fracValueDensity, smul_smul, mul_comm]

theorem continuous_value (α h τ : ℝ) (A : Space → Space) :
    Continuous fun y => latticeSum h (fracValueDensity α τ A y) :=
  SourceComparison.Internal.continuous_latticeSum h _

theorem continuous_grad (α h τ : ℝ) (A : Space → Space) (j : Fin 3) :
    Continuous fun y => latticeSum h (fracGradDensity α j τ A y) := by
  have e : (fun y => latticeSum h (fracGradDensity α j τ A y)) = fun y => latticeSum h (fun ξ => expChar y ξ •
      ((2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec A ξ)))) :=
    funext fun y => by rw [fracGradDensity_eq]
  rw [e]
  exact SourceComparison.Internal.continuous_latticeSum h _

def familyDensity (α : ℝ) (q : Freq.L2R × Space × ℝ) : Option (Fin 3) → Space → Coef
  | none => fracValueDensity α q.2.2 (⇑q.1) q.2.1
  | some j => fracGradDensity α j q.2.2 (⇑q.1) q.2.1

theorem difference_smul (α μ b τ c : ℝ) (A : Freq.L2R) :
    restrictTorus (simScale α μ) b ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ (c • A)) -
        restrictR3 b (Freq.fracHeatSolenoidal α τ (c • A)) =
      c • (restrictTorus (simScale α μ) b ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) -
        restrictR3 b (Freq.fracHeatSolenoidal α τ A)) := by
  have e1 : fracSourceOp α μ τ (c • A) = c • fracSourceOp α μ τ A := map_smul _ _ _
  have e2 : Freq.fracHeatSolenoidal α τ (c • A) = c • Freq.fracHeatSolenoidal α τ A := map_smul _ _ _
  have e3 : (μ ^ (-(1 / (4 * α)))) • (c • fracSourceOp α μ τ A) =
      c • ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) := by
    rw [smul_smul, smul_smul, mul_comm]
  have e4 : restrictTorus (simScale α μ) b (c • ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A)) =
      c • restrictTorus (simScale α μ) b ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) := map_smul _ _ _
  have e5 : restrictR3 b (c • Freq.fracHeatSolenoidal α τ A) = c • restrictR3 b (Freq.fracHeatSolenoidal α τ A) :=
    map_smul _ _ _
  rw [e1, e2, e3]
  exact (congrArg₂ (· - ·) e4 e5).trans (smul_sub _ _ _).symm

set_option maxHeartbeats 1000000 in
theorem comparison_of_normalized {α : ℝ} (hα : 1 < α) (h1 : PartitionSumBound) (h2 : FracTorusSourceSeries α)
    (h3 : FracR3ValueFormula α) (h4 : FracSourceDensityBounds α) (h5 : FracSourceDensityIncrement α)
    {b b' ε δ : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (hε : 0 < ε) (hδ : 0 < δ) : ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
    ∀ τ ∈ Icc ε ε⁻¹, ∀ A : Freq.L2R, (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
      (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 →
      ‖restrictTorus (simScale α μ) b ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) -
        restrictR3 b (Freq.fracHeatSolenoidal α τ A)‖ ≤ δ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  obtain ⟨K, hK⟩ := h4 b b' ε hε
  set W := (volume (Metric.closedBall (0 : Space) b)).toReal with hW
  have hM1 : 0 < max 1 W := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set δ' := δ / max 1 W with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ hM1
  have hδ'M : δ' * max 1 W ≤ δ := by rw [hδ', div_mul_cancel₀ δ hM1.ne']
  obtain ⟨h₀, hh₀, hR⟩ := h1 {q : (Freq.L2R × Space × ℝ) × Option (Fin 3) //
      (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → (q.1.1 : Space → Space) y = 0) ∧
      (eLpNorm (q.1.1 : Space → Space) (3 / 2) volume).toReal ≤ 1 ∧ ‖q.1.2.1‖ ≤ b ∧ q.1.2.2 ∈ Icc ε ε⁻¹}
    (fun i => familyDensity α i.1.1 i.1.2) K
    (by
      rintro ⟨⟨⟨A, y, τ⟩, o⟩, hA, hA1, hy, hτ⟩ ξ
      cases o with
      | none => exact (hK A hA hA1 y hy τ hτ ξ).1
      | some j => exact (hK A hA hA1 y hy τ hτ ξ).2 j)
    (by
      intro r R hr
      obtain ⟨L, hL⟩ := h5 b b' ε r R hε hr
      refine ⟨L, ?_⟩
      rintro ⟨⟨⟨A, y, τ⟩, o⟩, hA, hA1, hy, hτ⟩ ξ ξ' hξ1 hξ2 hξ3 hξ4
      cases o with
      | none => exact (hL A hA hA1 y hy τ hτ ξ ξ' hξ1 hξ2 hξ3 hξ4).1
      | some j => exact (hL A hA hA1 y hy τ hτ ξ ξ' hξ1 hξ2 hξ3 hξ4).2 j)
    δ' hδ'0
  set m := min (min 1 (h₀ ^ 2)) (min ((1 / (8 * b)) ^ 2) ((1 / (4 * b')) ^ 2)) with hm
  have hm0 : 0 < m := by positivity
  refine ⟨min 1 (m ^ α), lt_min zero_lt_one (Real.rpow_pos_of_pos hm0 _), ?_⟩
  intro μ hμ hμ₀ τ hτ A hA hA1
  have hμ1 : μ < 1 := lt_of_lt_of_le hμ₀ (min_le_left _ _)
  have hμm : simScale α μ < m := simScale_lt hα0 hμ (hm0) (lt_of_lt_of_le hμ₀ (min_le_right _ _))
  have hμ'0 : 0 < simScale α μ := simScale_pos hμ
  set μ' := simScale α μ with hμ'
  have hμ'1 : μ' < 1 := lt_of_lt_of_le hμm ((min_le_left _ _).trans (min_le_left _ _))
  have hμh : μ' < h₀ ^ 2 := lt_of_lt_of_le hμm ((min_le_left _ _).trans (min_le_right _ _))
  have hμb : μ' < (1 / (8 * b)) ^ 2 := lt_of_lt_of_le hμm ((min_le_right _ _).trans (min_le_left _ _))
  have hμb' : μ' < (1 / (4 * b')) ^ 2 := lt_of_lt_of_le hμm ((min_le_right _ _).trans (min_le_right _ _))
  have hsh : Real.sqrt μ' < h₀ := (Real.sqrt_lt' hh₀).2 hμh
  have hsb : Real.sqrt μ' * (8 * b) < 1 := by
    have := (Real.sqrt_lt' (by positivity : (0 : ℝ) < 1 / (8 * b))).2 hμb
    rwa [lt_div_iff₀ (by positivity)] at this
  have hsb' : Real.sqrt μ' * (4 * b') < 1 := by
    have := (Real.sqrt_lt' (by positivity : (0 : ℝ) < 1 / (4 * b'))).2 hμb'
    rwa [lt_div_iff₀ (by positivity)] at this
  have hsqpos : 0 < Real.sqrt μ' := Real.sqrt_pos.2 hμ'0
  have hshell : IsShellScale μ' b := by
    refine ⟨hμ'0, hμ'1.le, hb, ?_⟩
    have e : Real.sqrt μ' * b = (Real.sqrt μ' * (8 * b)) / 8 := by ring
    rw [e]
    linarith
  have hsc' : Real.sqrt μ' * b' ≤ 1 / 4 := by
    have e : Real.sqrt μ' * b' = (Real.sqrt μ' * (4 * b')) / 4 := by ring
    rw [e]
    linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le hε hτ.1
  obtain ⟨hv, hg⟩ := h2 b b' μ τ hμ hμ1.le hshell hsc' hτ0 A hA
  obtain ⟨hv3, hg3⟩ := h3 b' τ hτ0 A hA
  have hRg : ∀ (j : Fin 3) (y : Space), ‖y‖ ≤ b →
      ‖latticeSum (Real.sqrt μ') (fracGradDensity α j τ (⇑A) y) - ∫ ξ, fracGradDensity α j τ (⇑A) y ξ‖ ≤ δ' :=
    fun j y hy => hR (Real.sqrt μ') hsqpos hsh ⟨((A, y, τ), some j), hA, hA1, hy, hτ⟩
  have hRv : ∀ y : Space, ‖y‖ ≤ b →
      ‖latticeSum (Real.sqrt μ') (fracValueDensity α τ (⇑A) y) - ∫ ξ, fracValueDensity α τ (⇑A) y ξ‖ ≤ δ' :=
    fun y hy => hR (Real.sqrt μ') hsqpos hsh ⟨((A, y, τ), none), hA, hA1, hy, hτ⟩
  have hs : MeasurableSet (Metric.closedBall (0 : Space) b) := measurableSet_closedBall
  set C0 := ∫ ξ : Space, (1 + ‖ξ‖) ^ (-4 : ℝ) with hC0
  set z := (μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A with hz
  have hgrad : ∀ j : Fin 3, ‖Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ' ^ (3 / 4 : ℝ)) •
          Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ' • y)))) -
      cutLp 2 b (Freq.partialX j (Freq.fracHeatSolenoidal α τ A))‖ ≤ δ := by
    intro j
    refine SourceComparison.Internal.component_norm_le (p := 2) (C := δ' + K * C0)
      (L := fun y => latticeSum (Real.sqrt μ') (fracGradDensity α j τ (⇑A) y))
      (I := fun y => ∫ ξ, fracGradDensity α j τ (⇑A) y ξ) (by norm_num) hδ'0.le hδ'M
      (continuous_grad _ _ _ _ j) ?_ (fun y hy => hRg j y (mem_closedBall_zero_iff.1 hy)) ?_ ?_
    · intro y hy
      have hy' := mem_closedBall_zero_iff.1 hy
      have e1 := hRg j y hy'
      have e2 := SourceComparison.Internal.integral_bound (fun ξ => (hK A hA hA1 y hy' τ hτ ξ).2 j)
      have e3 := norm_sub_norm_le (latticeSum (Real.sqrt μ') (fracGradDensity α j τ (⇑A) y))
        (∫ ξ, fracGradDensity α j τ (⇑A) y ξ)
      linarith
    · refine (ae_eq_restrict_iff_indicator_ae_eq hs).1 ?_
      filter_upwards [hg j] with y hy
      rw [← map_smul]
      exact congrArg _ hy
    · exact (cutLp_apply 2 b _).trans ((ae_eq_restrict_iff_indicator_ae_eq hs).1 (ae_restrict_of_ae (hg3 j)))
  have hval : ‖Freq.toLpOrZero 6 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ' ^ (1 / 4 : ℝ)) •
          Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ' • y)))) -
      cutLp 6 b (Freq.velocity (Freq.fracHeatSolenoidal α τ A))‖ ≤ δ := by
    refine SourceComparison.Internal.component_norm_le (p := 6) (C := δ' + K * C0)
      (L := fun y => latticeSum (Real.sqrt μ') (fracValueDensity α τ (⇑A) y))
      (I := fun y => ∫ ξ, fracValueDensity α τ (⇑A) y ξ) (by norm_num) hδ'0.le hδ'M
      (continuous_value _ _ _ _) ?_ (fun y hy => hRv y (mem_closedBall_zero_iff.1 hy)) ?_ ?_
    · intro y hy
      have hy' := mem_closedBall_zero_iff.1 hy
      have e1 := hRv y hy'
      have e2 := SourceComparison.Internal.integral_bound (fun ξ => (hK A hA hA1 y hy' τ hτ ξ).1)
      have e3 := norm_sub_norm_le (latticeSum (Real.sqrt μ') (fracValueDensity α τ (⇑A) y))
        (∫ ξ, fracValueDensity α τ (⇑A) y ξ)
      linarith
    · refine (ae_eq_restrict_iff_indicator_ae_eq hs).1 ?_
      filter_upwards [hv] with y hy
      rw [← map_smul]
      exact congrArg _ hy
    · exact (cutLp_apply 6 b _).trans ((ae_eq_restrict_iff_indicator_ae_eq hs).1 (ae_restrict_of_ae hv3))
  rw [norm_prod_le_iff]
  simp only [SourceComparison.Internal.restrictTorus_apply, restrictTorusFun, if_pos hshell,
    SourceComparison.Internal.restrictR3_apply, Prod.fst_sub, Prod.snd_sub]
  refine ⟨(pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_, hval⟩
  rw [Pi.sub_apply]
  exact hgrad j

end FracHeatCompare.Internal

theorem fracHeatSolenoidalComparison_of (α : ℝ) (hα : 1 < α) (h1 : PartitionSumBound) (h2 : FracTorusSourceSeries α)
    (h3 : FracR3ValueFormula α) (h4 : FracSourceDensityBounds α) (h5 : FracSourceDensityIncrement α) :
    FracHeatSolenoidalComparison α := by
  intro b b' ε δ hb hb' hε hδ
  obtain ⟨μ₀, hμ₀, hunit⟩ :=
    FracHeatCompare.Internal.comparison_of_normalized hα h1 h2 h3 h4 h5 hb hb' hε hδ
  refine ⟨μ₀, hμ₀, fun μ hμ hμμ₀ τ hτ A hA => ?_⟩
  set s := (eLpNorm (A : Space → Space) (3 / 2) volume).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hc : ∀ t : ℝ, 0 < t → s ≤ t →
      ‖restrictTorus (simScale α μ) b ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) -
        restrictR3 b (Freq.fracHeatSolenoidal α τ A)‖ ≤ δ * t := by
    intro t ht hst
    have hA' : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' →
        ((t⁻¹ • A : Freq.L2R) : Space → Space) y = 0 := by
      filter_upwards [hA, Lp.coeFn_smul t⁻¹ A] with y hy hsm hyn
      rw [hsm, Pi.smul_apply, hy hyn, smul_zero]
    have hn' : (eLpNorm ((t⁻¹ • A : Freq.L2R) : Space → Space) (3 / 2) volume).toReal ≤ 1 := by
      rw [eLpNorm_congr_ae (Lp.coeFn_smul t⁻¹ A), eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm,
        ← hs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]
      calc t⁻¹ * s ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hst (inv_pos.2 ht).le
        _ = 1 := inv_mul_cancel₀ ht.ne'
    have key := hunit μ hμ hμμ₀ τ hτ _ hA' hn'
    have e := FracHeatCompare.Internal.difference_smul α μ b τ t (t⁻¹ • A)
    have hAeq : t • (t⁻¹ • A) = A := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    rw [hAeq] at e
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_comm δ]
    exact mul_le_mul_of_nonneg_left key ht.le
  rcases hs0.lt_or_eq with hpos | hzero
  · exact hc s hpos le_rfl
  · rw [← hzero, mul_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have := hc (η / δ) (div_pos hη hδ) (by rw [← hzero]; exact (div_pos hη hδ).le)
    rw [mul_div_cancel₀ η hδ.ne'] at this
    linarith

open FreeComparison.Internal in
theorem fracFreeHeatComparison_of (α : ℝ) (hα : 1 < α) (h1 : PartitionSumBound) (h2 : FracTorusFreeSeries α)
    (h3 : FracR3FreeFormula α) (h4 : FracFreeDensityBounds α) (h5 : FracFreeDensityIncrement α) :
    FracFreeHeatComparison α := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  intro φ hφ b ε δ hb hε hδ
  obtain ⟨b₁, hb₁⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : Space)
  have hb' : (0 : ℝ) < max b₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.closedBall 0 (max b₁ 1) :=
    hb₁.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hvol : 0 ≤ (volume (Metric.closedBall (0 : Space) b)).toReal := ENNReal.toReal_nonneg
  have hδ' : 0 < δ / (1 + (volume (Metric.closedBall (0 : Space) b)).toReal) := by positivity
  have hδeq : δ / (1 + (volume (Metric.closedBall (0 : Space) b)).toReal) *
      (1 + (volume (Metric.closedBall (0 : Space) b)).toReal) = δ :=
    div_mul_cancel₀ δ (by positivity)
  obtain ⟨K, hK⟩ := h4 φ hφ b ε hε
  let G : ({q : Space × ℝ // ‖q.1‖ ≤ b ∧ q.2 ∈ Icc 0 ε⁻¹} × Option (Fin 3)) → Space → Coef :=
    fun i => i.2.elim (fracFreeDensity α i.1.1.2 φ i.1.1.1) (fun j => fracFreeGradDensity α j i.1.1.2 φ i.1.1.1)
  have hGK : ∀ i ξ, ‖G i ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
    rintro ⟨⟨⟨y, τ⟩, hy, hτ⟩, _ | j⟩ ξ
    · exact (hK y hy τ hτ ξ).1
    · exact (hK y hy τ hτ ξ).2 j
  have hGL : ∀ r R : ℝ, 0 < r → ∃ L : ℝ, ∀ i ξ ξ', r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖G i ξ - G i ξ'‖ ≤ L * ‖ξ - ξ'‖ := by
    intro r R hr
    obtain ⟨L, hL⟩ := h5 φ hφ b ε r R hε hr
    refine ⟨L, ?_⟩
    rintro ⟨⟨⟨y, τ⟩, hy, hτ⟩, _ | j⟩ ξ ξ' a1 a2 a3 a4
    · exact (hL y hy τ hτ ξ ξ' a1 a2 a3 a4).1
    · exact (hL y hy τ hτ ξ ξ' a1 a2 a3 a4).2 j
  obtain ⟨h₀, hh₀, hh⟩ := h1 _ G K hGK hGL _ hδ'
  set m := min (min 1 (h₀ ^ 2)) (min ((1 / (8 * b)) ^ 2) ((1 / (8 * max b₁ 1)) ^ 2)) with hm
  have hm0 : 0 < m := by positivity
  refine ⟨min 1 (m ^ α), lt_min zero_lt_one (Real.rpow_pos_of_pos hm0 _), ?_⟩
  intro μ hμ hlt0 τ hτ
  have hμ1 : μ < 1 := lt_of_lt_of_le hlt0 (min_le_left _ _)
  have hlt : simScale α μ < m :=
    FracHeatCompare.Internal.simScale_lt hα0 hμ hm0 (lt_of_lt_of_le hlt0 (min_le_right _ _))
  have hμ'0 : 0 < simScale α μ := FracHeatCompare.Internal.simScale_pos hμ
  set μ' := simScale α μ with hμ'
  simp only [hm, lt_min_iff] at hlt
  have hsc := shellScale_of_lt hμ'0 hlt.1.1 hb hlt.2.1
  have hsc' := shellScale_of_lt hμ'0 hlt.1.1 hb' hlt.2.2
  have hsq : Real.sqrt μ' < h₀ := (Real.sqrt_lt' hh₀).2 hlt.1.2
  have hsq0 : 0 < Real.sqrt μ' := Real.sqrt_pos.2 hμ'0
  obtain ⟨hT0, hTj⟩ := h2 φ hφ b (max b₁ 1) μ τ hμ hμ1.le hsc hsc' hτ.1 hsupp
  obtain ⟨hR0, hRj⟩ := h3 φ hφ τ hτ.1
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_
    rw [Prod.fst_sub, Pi.sub_apply]
    refine (component_le (p := 2) (by norm_num) (by norm_num) (by norm_num) hδ'.le _ _ _ _
      (torus_grad_ae hsc _ j) (cutLp_apply 2 b _) ?_).trans_eq hδeq
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).1 (hTj j), hRj j] with y hy1 hy2 hyB
    erw [hy2]
    rw [← map_smul Freq.realVec, hy1 hyB, ← map_sub]
    refine (ShellDefs.Internal.norm_realVec_le _).trans ?_
    exact hh (Real.sqrt μ') hsq0 hsq (⟨(y, τ), mem_closedBall_zero_iff.1 hyB, hτ⟩, some j)
  · rw [Prod.snd_sub]
    refine (component_le (p := 6) (by norm_num) (by norm_num) (by norm_num) hδ'.le _ _ _ _
      (torus_value_ae hsc _) (cutLp_apply 6 b _) ?_).trans_eq hδeq
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).1 hT0, hR0] with y hy1 hy2 hyB
    erw [hy2]
    rw [← map_smul Freq.realVec, hy1 hyB, ← map_sub]
    refine (ShellDefs.Internal.norm_realVec_le _).trans ?_
    exact hh (Real.sqrt μ') hsq0 hsq (⟨(y, τ), mem_closedBall_zero_iff.1 hyB, hτ⟩, none)

end Breakdown.Periodic

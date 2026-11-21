import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace SourceComparison.Internal

theorem norm_realVec_le (z : Coef) : ‖Freq.realVec z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have h : ‖Freq.realVec z i‖ ≤ ‖z i‖ := by
    simp only [Freq.realVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      PiLp.toLp_apply, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem rpow_le_max {W e : ℝ} (hW : 0 ≤ W) (he : 0 ≤ e) (he1 : e ≤ 1) : W ^ e ≤ max 1 W := by
  rcases le_total W 1 with h | h
  · exact (Real.rpow_le_one hW h he).trans (le_max_left _ _)
  · calc W ^ e ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h he1
      _ = W := Real.rpow_one W
      _ ≤ max 1 W := le_max_right _ _

theorem component_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ⊤) {b δ δ' C : ℝ} (hδ' : 0 ≤ δ')
    (hδ : δ' * max 1 (volume (Metric.closedBall (0 : Space) b)).toReal ≤ δ)
    {F : Space → Space} {u : Lp Space p (volume : Measure Space)} {L I : Space → Coef} (hL : Continuous L)
    (hC : ∀ y ∈ Metric.closedBall (0 : Space) b, ‖L y‖ ≤ C)
    (hLI : ∀ y ∈ Metric.closedBall (0 : Space) b, ‖L y - I y‖ ≤ δ')
    (hF : F =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator (fun y => Freq.realVec (L y)))
    (hu : (u : Space → Space) =ᵐ[volume]
      (Metric.closedBall (0 : Space) b).indicator (fun y => Freq.realVec (I y))) :
    ‖Freq.toLpOrZero p F - u‖ ≤ δ := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hs : MeasurableSet (Metric.closedBall (0 : Space) b) := measurableSet_closedBall
  have hfin : volume (Metric.closedBall (0 : Space) b) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hM : MemLp ((Metric.closedBall (0 : Space) b).indicator (fun y => Freq.realVec (L y))) p volume := by
    rw [memLp_indicator_iff_restrict hs]
    have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) b)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
    refine MemLp.of_bound (Freq.realVec.continuous.comp hL).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hs] with y hy
    exact (norm_realVec_le _).trans (hC y hy)
  have hMF : MemLp F p volume := hM.ae_eq hF.symm
  have h1 : (Freq.toLpOrZero p F : Space → Space) =ᵐ[volume] F := by
    unfold Freq.toLpOrZero
    rw [dif_pos hMF]
    exact hMF.coeFn_toLp
  have hd : ∀ᵐ y ∂volume, ‖((Freq.toLpOrZero p F - u : Lp Space p (volume : Measure Space)) : Space → Space) y‖ ≤
      (Metric.closedBall (0 : Space) b).indicator (fun _ => δ') y := by
    filter_upwards [Lp.coeFn_sub (Freq.toLpOrZero p F) u, h1, hF, hu] with y hsub h1y hFy huy
    rw [hsub, Pi.sub_apply, h1y, hFy, huy]
    by_cases hy : y ∈ Metric.closedBall (0 : Space) b
    · simp only [indicator_of_mem hy]
      rw [← map_sub]
      exact (norm_realVec_le _).trans (hLI y hy)
    · simp [indicator_of_notMem hy]
  have he := eLpNorm_mono_ae_real (p := p) hd
  rw [eLpNorm_indicator_const hs hp0 hpt, Real.enorm_of_nonneg hδ'] at he
  set W := (volume (Metric.closedBall (0 : Space) b)).toReal with hW
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hpr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  have he0 : 0 ≤ 1 / p.toReal := by positivity
  have he1 : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hpr
  have hV : volume (Metric.closedBall (0 : Space) b) = ENNReal.ofReal W := (ENNReal.ofReal_toReal hfin).symm
  rw [hV, ENNReal.ofReal_rpow_of_nonneg hW0 he0, ← ENNReal.ofReal_mul hδ'] at he
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal ((mul_nonneg hδ' (le_trans zero_le_one (le_max_left _ _))).trans hδ)
    (he.trans (ENNReal.ofReal_le_ofReal ?_))
  exact (mul_le_mul_of_nonneg_left (rpow_le_max hW0 he0 he1) hδ').trans hδ

theorem norm_expChar (y ξ : Space) : ‖expChar y ξ‖ = 1 := by
  have h : 2 * π * Complex.I * ((inner ℝ ξ y : ℝ) : ℂ) = ((2 * π * inner ℝ ξ y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [expChar, h, Complex.norm_exp_ofReal_mul_I]

theorem continuous_expChar (ξ : Space) : Continuous fun y => expChar y ξ := by
  unfold expChar
  fun_prop

theorem continuous_latticeSum (h : ℝ) (w : Space → Coef) :
    Continuous fun y => latticeSum h (fun ξ => expChar y ξ • w ξ) := by
  unfold latticeSum
  suffices hT : Continuous fun y => ∑' k : Lattice, expChar y (h • freq k) • w (h • freq k) from
    hT.const_smul (h ^ 3)
  by_cases hs : Summable (fun k : Lattice => ‖w (h • freq k)‖)
  · exact continuous_tsum (fun k => (continuous_expChar _).smul continuous_const) hs
      (fun k y => by rw [norm_smul, norm_expChar, one_mul])
  · have hz : (fun y => ∑' k : Lattice, expChar y (h • freq k) • w (h • freq k)) = fun _ => 0 := by
      funext y
      apply tsum_eq_zero_of_not_summable
      intro hs'
      apply hs
      exact (summable_norm_iff.2 hs').congr (fun k => by rw [norm_smul, norm_expChar, one_mul])
    rw [hz]
    exact continuous_const

theorem gradDensity_eq (j : Fin 3) (τ : ℝ) (A : Space → Space) (y : Space) :
    gradDensity j τ A y = fun ξ => expChar y ξ •
      ((2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ))) := by
  funext ξ
  simp only [gradDensity, valueDensity, smul_smul, mul_comm]

theorem continuous_value (h τ : ℝ) (A : Space → Space) :
    Continuous fun y => latticeSum h (valueDensity τ A y) :=
  continuous_latticeSum h _

theorem continuous_grad (h τ : ℝ) (A : Space → Space) (j : Fin 3) :
    Continuous fun y => latticeSum h (gradDensity j τ A y) := by
  have e : (fun y => latticeSum h (gradDensity j τ A y)) = fun y => latticeSum h (fun ξ => expChar y ξ •
      ((2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ)))) :=
    funext fun y => by rw [gradDensity_eq]
  rw [e]
  exact continuous_latticeSum h _

def familyDensity (q : Freq.L2R × Space × ℝ) : Option (Fin 3) → Space → Coef
  | none => valueDensity q.2.2 (⇑q.1) q.2.1
  | some j => gradDensity j q.2.2 (⇑q.1) q.2.1

theorem restrictTorus_apply (μ b : ℝ) (z : V) : restrictTorus μ b z = restrictTorusFun μ b z := rfl

theorem integral_bound {G : Space → Coef} {K : ℝ} (hG : ∀ ξ, ‖G ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)) :
    ‖∫ ξ, G ξ‖ ≤ K * ∫ ξ : Space, (1 + ‖ξ‖) ^ (-4 : ℝ) := by
  have hi : Integrable (fun ξ : Space => (1 + ‖ξ‖) ^ (-4 : ℝ)) volume := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace_fin]
    norm_num
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hi.const_mul K) (Filter.Eventually.of_forall hG)

theorem difference_smul (μ b τ c : ℝ) (A : Freq.L2R) :
    restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ (c • A)) - restrictR3 b (Freq.heatDivFree τ (c • A)) =
      c • (restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) - restrictR3 b (Freq.heatDivFree τ A)) := by
  have e1 : sourceOp μ τ (c • A) = c • sourceOp μ τ A := map_smul _ _ _
  have e2 : Freq.heatDivFree τ (c • A) = c • Freq.heatDivFree τ A := map_smul _ _ _
  have e3 : (μ ^ (-(1 / 4 : ℝ))) • (c • sourceOp μ τ A) = c • ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) := by
    rw [smul_smul, smul_smul, mul_comm]
  have e4 : restrictTorus μ b (c • ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A)) =
      c • restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) := map_smul _ _ _
  have e5 : restrictR3 b (c • Freq.heatDivFree τ A) = c • restrictR3 b (Freq.heatDivFree τ A) := map_smul _ _ _
  rw [e1, e2, e3]
  exact (congrArg₂ (· - ·) e4 e5).trans (smul_sub _ _ _).symm

theorem restrictR3_apply (b : ℝ) (v : Freq.X) :
    restrictR3 b v = (fun j => cutLp 2 b (Freq.partialX j v), cutLp 6 b (Freq.velocity v)) := rfl

set_option maxHeartbeats 1000000 in
theorem comparison_of_normalized (h1 : PartitionSumBound) (h2 : TorusSourceSeries) (h3 : R3ValueFormula)
    (h4 : SourceDensityBounds) (h5 : SourceDensitySlope) {b b' ε δ : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (hε : 0 < ε) (hδ : 0 < δ) : ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
    ∀ τ ∈ Icc ε ε⁻¹, ∀ A : Freq.L2R, (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
      (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 →
      ‖restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) - restrictR3 b (Freq.heatDivFree τ A)‖ ≤ δ := by
  obtain ⟨K, hK⟩ := h4 b b' ε hε
  set W := (volume (Metric.closedBall (0 : Space) b)).toReal with hW
  have hM1 : 0 < max 1 W := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set δ' := δ / max 1 W with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ hM1
  have hδ'M : δ' * max 1 W ≤ δ := by rw [hδ', div_mul_cancel₀ δ hM1.ne']
  obtain ⟨h₀, hh₀, hR⟩ := h1 {q : (Freq.L2R × Space × ℝ) × Option (Fin 3) //
      (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → (q.1.1 : Space → Space) y = 0) ∧
      (eLpNorm (q.1.1 : Space → Space) (3 / 2) volume).toReal ≤ 1 ∧ ‖q.1.2.1‖ ≤ b ∧ q.1.2.2 ∈ Icc ε ε⁻¹}
    (fun i => familyDensity i.1.1 i.1.2) K
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
  refine ⟨min (min 1 (h₀ ^ 2)) (min ((1 / (8 * b)) ^ 2) ((1 / (4 * b')) ^ 2)), by positivity, ?_⟩
  intro μ hμ hμ₀ τ hτ A hA hA1
  have hμ1 : μ < 1 := lt_of_lt_of_le hμ₀ ((min_le_left _ _).trans (min_le_left _ _))
  have hμh : μ < h₀ ^ 2 := lt_of_lt_of_le hμ₀ ((min_le_left _ _).trans (min_le_right _ _))
  have hμb : μ < (1 / (8 * b)) ^ 2 := lt_of_lt_of_le hμ₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hμb' : μ < (1 / (4 * b')) ^ 2 := lt_of_lt_of_le hμ₀ ((min_le_right _ _).trans (min_le_right _ _))
  have hsh : Real.sqrt μ < h₀ := (Real.sqrt_lt' hh₀).2 hμh
  have hsb : Real.sqrt μ * (8 * b) < 1 := by
    have := (Real.sqrt_lt' (by positivity : (0 : ℝ) < 1 / (8 * b))).2 hμb
    rwa [lt_div_iff₀ (by positivity)] at this
  have hsb' : Real.sqrt μ * (4 * b') < 1 := by
    have := (Real.sqrt_lt' (by positivity : (0 : ℝ) < 1 / (4 * b'))).2 hμb'
    rwa [lt_div_iff₀ (by positivity)] at this
  have hsqpos : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hshell : IsShellScale μ b := by
    refine ⟨hμ, hμ1.le, hb, ?_⟩
    have e : Real.sqrt μ * b = (Real.sqrt μ * (8 * b)) / 8 := by ring
    rw [e]
    linarith
  have hsc' : Real.sqrt μ * b' ≤ 1 / 4 := by
    have e : Real.sqrt μ * b' = (Real.sqrt μ * (4 * b')) / 4 := by ring
    rw [e]
    linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le hε hτ.1
  obtain ⟨hv, hg⟩ := h2 b b' μ τ hshell hsc' hτ0 A hA
  obtain ⟨hv3, hg3⟩ := h3 b' τ hτ0 A hA
  have hRg : ∀ (j : Fin 3) (y : Space), ‖y‖ ≤ b →
      ‖latticeSum (Real.sqrt μ) (gradDensity j τ (⇑A) y) - ∫ ξ, gradDensity j τ (⇑A) y ξ‖ ≤ δ' :=
    fun j y hy => hR (Real.sqrt μ) hsqpos hsh ⟨((A, y, τ), some j), hA, hA1, hy, hτ⟩
  have hRv : ∀ y : Space, ‖y‖ ≤ b →
      ‖latticeSum (Real.sqrt μ) (valueDensity τ (⇑A) y) - ∫ ξ, valueDensity τ (⇑A) y ξ‖ ≤ δ' :=
    fun y hy => hR (Real.sqrt μ) hsqpos hsh ⟨((A, y, τ), none), hA, hA1, hy, hτ⟩
  have hs : MeasurableSet (Metric.closedBall (0 : Space) b) := measurableSet_closedBall
  set C0 := ∫ ξ : Space, (1 + ‖ξ‖) ^ (-4 : ℝ) with hC0
  set z := (μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A with hz
  have hgrad : ∀ j : Fin 3, ‖Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (3 / 4 : ℝ)) •
          Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y)))) -
      cutLp 2 b (Freq.partialX j (Freq.heatDivFree τ A))‖ ≤ δ := by
    intro j
    refine component_norm_le (p := 2) (C := δ' + K * C0)
      (L := fun y => latticeSum (Real.sqrt μ) (gradDensity j τ (⇑A) y))
      (I := fun y => ∫ ξ, gradDensity j τ (⇑A) y ξ) (by norm_num) hδ'0.le hδ'M
      (continuous_grad _ _ _ j) ?_ (fun y hy => hRg j y (mem_closedBall_zero_iff.1 hy)) ?_ ?_
    · intro y hy
      have hy' := mem_closedBall_zero_iff.1 hy
      have e1 := hRg j y hy'
      have e2 := integral_bound (fun ξ => (hK A hA hA1 y hy' τ hτ ξ).2 j)
      have e3 := norm_sub_norm_le (latticeSum (Real.sqrt μ) (gradDensity j τ (⇑A) y))
        (∫ ξ, gradDensity j τ (⇑A) y ξ)
      linarith
    · refine (ae_eq_restrict_iff_indicator_ae_eq hs).1 ?_
      filter_upwards [hg j] with y hy
      rw [← map_smul]
      exact congrArg _ hy
    · exact (cutLp_apply 2 b _).trans ((ae_eq_restrict_iff_indicator_ae_eq hs).1 (ae_restrict_of_ae (hg3 j)))
  have hval : ‖Freq.toLpOrZero 6 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (1 / 4 : ℝ)) •
          Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y)))) -
      cutLp 6 b (Freq.velocity (Freq.heatDivFree τ A))‖ ≤ δ := by
    refine component_norm_le (p := 6) (C := δ' + K * C0)
      (L := fun y => latticeSum (Real.sqrt μ) (valueDensity τ (⇑A) y))
      (I := fun y => ∫ ξ, valueDensity τ (⇑A) y ξ) (by norm_num) hδ'0.le hδ'M
      (continuous_value _ _ _) ?_ (fun y hy => hRv y (mem_closedBall_zero_iff.1 hy)) ?_ ?_
    · intro y hy
      have hy' := mem_closedBall_zero_iff.1 hy
      have e1 := hRv y hy'
      have e2 := integral_bound (fun ξ => (hK A hA hA1 y hy' τ hτ ξ).1)
      have e3 := norm_sub_norm_le (latticeSum (Real.sqrt μ) (valueDensity τ (⇑A) y))
        (∫ ξ, valueDensity τ (⇑A) y ξ)
      linarith
    · refine (ae_eq_restrict_iff_indicator_ae_eq hs).1 ?_
      filter_upwards [hv] with y hy
      rw [← map_smul]
      exact congrArg _ hy
    · exact (cutLp_apply 6 b _).trans ((ae_eq_restrict_iff_indicator_ae_eq hs).1 (ae_restrict_of_ae hv3))
  rw [norm_prod_le_iff]
  simp only [restrictTorus_apply, restrictTorusFun, if_pos hshell, restrictR3_apply, Prod.fst_sub,
    Prod.snd_sub]
  refine ⟨(pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_, hval⟩
  rw [Pi.sub_apply]
  exact hgrad j

end SourceComparison.Internal

theorem heatDivFreeComparison_of (h1 : PartitionSumBound) (h2 : TorusSourceSeries) (h3 : R3ValueFormula)
    (h4 : SourceDensityBounds) (h5 : SourceDensitySlope) : HeatDivFreeComparison := by
  intro b b' ε δ hb hb' hε hδ
  obtain ⟨μ₀, hμ₀, hunit⟩ := SourceComparison.Internal.comparison_of_normalized h1 h2 h3 h4 h5 hb hb' hε hδ
  refine ⟨μ₀, hμ₀, fun μ hμ hμμ₀ τ hτ A hA => ?_⟩
  set s := (eLpNorm (A : Space → Space) (3 / 2) volume).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hc : ∀ t : ℝ, 0 < t → s ≤ t →
      ‖restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) - restrictR3 b (Freq.heatDivFree τ A)‖ ≤
        δ * t := by
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
    have e := SourceComparison.Internal.difference_smul μ b τ t (t⁻¹ • A)
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

end Breakdown.Periodic

import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FreeComparison.Internal

theorem rpow_le_one_add {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : x ^ q ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_le_one hx h hq0]
  · have := Real.rpow_le_rpow_of_exponent_le h hq1
    rw [Real.rpow_one] at this
    linarith

theorem norm_le_of_ae_ball {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) (b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ᵐ y ∂volume, ‖F y‖ ≤ (Metric.closedBall (0 : Space) b).indicator (fun _ => c) y) :
    ‖F‖ ≤ c * (volume (Metric.closedBall (0 : Space) b)).toReal ^ (1 / p.toReal) := by
  rw [Lp.norm_def]
  have h1 := eLpNorm_mono_ae_real (p := p) h
  rw [eLpNorm_indicator_const measurableSet_closedBall hp0 hpt] at h1
  have hfin : volume (Metric.closedBall (0 : Space) b) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hne : ‖c‖ₑ * volume (Metric.closedBall (0 : Space) b) ^ (1 / p.toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin)
  refine (ENNReal.toReal_mono hne h1).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, toReal_enorm, Real.norm_of_nonneg hc]

theorem component_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hq : 1 / p.toReal ≤ 1)
    {b c : ℝ} (hc : 0 ≤ c) (T R : Lp Space p (volume : Measure Space)) (f g : Space → Space)
    (hT : (T : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator f)
    (hR : (R : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator g)
    (hfg : ∀ᵐ y ∂volume, y ∈ Metric.closedBall (0 : Space) b → ‖f y - g y‖ ≤ c) :
    ‖T - R‖ ≤ c * (1 + (volume (Metric.closedBall (0 : Space) b)).toReal) := by
  refine (norm_le_of_ae_ball hp0 hpt (T - R) b c hc ?_).trans ?_
  · filter_upwards [Lp.coeFn_sub T R, hT, hR, hfg] with y h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3]
    by_cases hy : y ∈ Metric.closedBall (0 : Space) b
    · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy]
      exact h4 hy
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy, sub_zero, norm_zero]
  · exact mul_le_mul_of_nonneg_left (rpow_le_one_add ENNReal.toReal_nonneg (by positivity) hq) hc

theorem shellScale_of_lt {μ b : ℝ} (hμ : 0 < μ) (h1 : μ < 1) (hb : 0 < b) (h : μ < (1 / (8 * b)) ^ 2) :
    IsShellScale μ b := by
  refine ⟨hμ, h1.le, hb, ?_⟩
  have hs : Real.sqrt μ < 1 / (8 * b) := (Real.sqrt_lt' (by positivity)).2 h
  rw [lt_div_iff₀ (by positivity)] at hs
  nlinarith

theorem torus_grad_ae {μ b : ℝ} (h : IsShellScale μ b) (z : V) (j : Fin 3) :
    ((restrictTorus μ b z).1 j : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
      (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))) := by
  have e : restrictTorus μ b z = restrictTorusFun μ b z := by
    simp only [restrictTorus, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [e]
  unfold restrictTorusFun
  rw [if_pos h]
  dsimp only
  rw [ShellDefs.Internal.toLpOrZero_eq
    (ShellDefs.Internal.norm_shell_le 2 (by norm_num) h ShellDefs.Internal.exp_two (torusSeries 2 (gradCoef j z))).1]
  exact MemLp.coeFn_toLp _

theorem torus_value_ae {μ b : ℝ} (h : IsShellScale μ b) (z : V) :
    ((restrictTorus μ b z).2 : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
      (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))) := by
  have e : restrictTorus μ b z = restrictTorusFun μ b z := by
    simp only [restrictTorus, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [e]
  unfold restrictTorusFun
  rw [if_pos h]
  dsimp only
  rw [ShellDefs.Internal.toLpOrZero_eq
    (ShellDefs.Internal.norm_shell_le 6 (by norm_num) h ShellDefs.Internal.exp_six (torusSeries 6 (coeff z))).1]
  exact MemLp.coeFn_toLp _

end FreeComparison.Internal

open FreeComparison.Internal in
theorem freeHeatComparison_of (h1 : PartitionSumBound) (h2 : TorusFreeSeries) (h3 : R3FreeFormula)
    (h4 : FreeDensityBounds) (h5 : FreeDensitySlope) : FreeHeatComparison := by
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
    fun i => i.2.elim (freeDensity i.1.1.2 φ i.1.1.1) (fun j => freeGradDensity j i.1.1.2 φ i.1.1.1)
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
  refine ⟨min (min 1 (h₀ ^ 2)) (min ((1 / (8 * b)) ^ 2) ((1 / (8 * max b₁ 1)) ^ 2)), by positivity, ?_⟩
  intro μ hμ hlt τ hτ
  simp only [lt_min_iff] at hlt
  have hsc := shellScale_of_lt hμ hlt.1.1 hb hlt.2.1
  have hsc' := shellScale_of_lt hμ hlt.1.1 hb' hlt.2.2
  have hsq : Real.sqrt μ < h₀ := (Real.sqrt_lt' hh₀).2 hlt.1.2
  have hsq0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  obtain ⟨hT0, hTj⟩ := h2 φ hφ b (max b₁ 1) μ τ hsc hsc' hτ.1 hsupp
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
    exact hh (Real.sqrt μ) hsq0 hsq (⟨(y, τ), mem_closedBall_zero_iff.1 hyB, hτ⟩, some j)
  · rw [Prod.snd_sub]
    refine (component_le (p := 6) (by norm_num) (by norm_num) (by norm_num) hδ'.le _ _ _ _
      (torus_value_ae hsc _) (cutLp_apply 6 b _) ?_).trans_eq hδeq
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).1 hT0, hR0] with y hy1 hy2 hyB
    erw [hy2]
    rw [← map_smul Freq.realVec, hy1 hyB, ← map_sub]
    refine (ShellDefs.Internal.norm_realVec_le _).trans ?_
    exact hh (Real.sqrt μ) hsq0 hsq (⟨(y, τ), mem_closedBall_zero_iff.1 hyB, hτ⟩, none)

end Breakdown.Periodic

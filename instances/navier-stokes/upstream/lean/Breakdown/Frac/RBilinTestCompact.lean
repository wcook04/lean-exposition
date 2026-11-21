import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracInternal

open Breakdown.Freq Breakdown.Freq.Internal.BilinCompact

theorem fracPhiFactor_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor; positivity

theorem fracPhiFactor_tail {α τ R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hR : 1 ≤ R) {ξ : Space}
    (hξ : R ≤ ‖ξ‖) : fracPhiFactor α τ ξ ≤ 1 / (τ * R) := by
  unfold fracPhiFactor
  set s := 2 * π * ‖ξ‖ with hs
  have hs1 : R ≤ s := by
    have : ‖ξ‖ ≤ 2 * π * ‖ξ‖ := by nlinarith [Real.pi_gt_three, norm_nonneg ξ]
    linarith
  have hs0 : 1 ≤ s := hR.trans hs1
  have hpow : s ^ 2 ≤ s ^ (2 * α) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hs0 (by norm_num; linarith)
  have hE := Real.add_one_le_exp (τ * s ^ (2 * α))
  have hpos := Real.exp_pos (τ * s ^ (2 * α))
  have hτR : 0 < τ * R := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hpos hτR]
  have h0 : 0 ≤ τ * s := by positivity
  calc s * (τ * R) = (τ * s) * R := by ring
    _ ≤ (τ * s) * s := mul_le_mul_of_nonneg_left hs1 h0
    _ = τ * s ^ 2 := by ring
    _ ≤ τ * s ^ (2 * α) := mul_le_mul_of_nonneg_left hpow hτ.le
    _ ≤ 1 * Real.exp (τ * s ^ (2 * α)) := by linarith

theorem fracPhiFactor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    fracPhiFactor α τ ξ ≤ 2 * π + 1 / τ := by
  rcases le_or_gt 1 ‖ξ‖ with h | h
  · have := fracPhiFactor_tail hα hτ le_rfl h
    rw [mul_one] at this
    linarith [Real.pi_pos]
  · unfold fracPhiFactor
    have h1 : Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ τ * (2 * π * ‖ξ‖) ^ (2 * α) := by positivity
      linarith
    have h2 : 0 < 1 / τ := by positivity
    have h3 : 2 * π * ‖ξ‖ ≤ 2 * π := by
      have := norm_nonneg ξ; nlinarith [Real.pi_pos]
    calc 2 * π * ‖ξ‖ * Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) ≤ 2 * π * ‖ξ‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * π + 1 / τ := by linarith

theorem continuous_fracPhiFactor {α : ℝ} (hα : 1 < α) (τ : ℝ) : Continuous (fracPhiFactor α τ) := by
  have hc : Continuous (fun x : ℝ => x ^ (2 * α)) := Real.continuous_rpow_const (by linarith)
  unfold fracPhiFactor
  have hn : Continuous (fun ξ : Space => 2 * π * ‖ξ‖) := by fun_prop
  exact hn.mul (Real.continuous_exp.comp ((continuous_const.mul (hc.comp hn)).neg))

def fracPhiMul (α τ : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)

theorem norm_fracPhiFactor_smul_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 2 * π + 1 / τ := by
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (fracPhiFactor_nonneg α τ ξ)]
  calc fracPhiFactor α τ ξ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ fracPhiFactor α τ ξ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (fracPhiFactor_nonneg α τ ξ)
    _ ≤ _ := by rw [mul_one]; exact fracPhiFactor_le hα hτ ξ

theorem fracPhiMul_ae {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (u : L2C) :
    (fracPhiMul α τ u : Space → CSpace) =ᵐ[volume]
      fun ξ => fracPhiFactor α τ ξ • (u : Space → CSpace) ξ := by
  have hmeas : AEStronglyMeasurable
      (fun ξ : Space => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    ((continuous_fracPhiFactor hα τ).smul continuous_const).aestronglyMeasurable
  have := fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) _ _ hmeas
    (norm_fracPhiFactor_smul_le hα hτ) u
  simpa [fracPhiMul] using this

theorem inner_complexifyVec_real (a : Space) (b : CSpace) :
    inner ℝ (complexifyVec a) b = inner ℝ a (realVec b) := by
  simp [complexifyVec, realVec, PiLp.inner_apply, Complex.inner]

theorem inner_complexify_real (g : L2R) (z : L2C) :
    inner ℝ (complexify g) z = inner ℝ g (realPart z) := by
  have hx : (complexify g : Space → CSpace) =ᵐ[volume] fun a => complexifyVec (g a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hy : (realPart z : Space → Space) =ᵐ[volume] fun a => realVec (z a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx, hy] with x hx hy
  rw [hx, hy, inner_complexifyVec_real]

def transformRealIsometry : L2C ≃ₗᵢ[ℝ] L2C :=
  { freqTrL2.toLinearEquiv.restrictScalars ℝ with norm_map' := freqTrL2.norm_map }

theorem inner_transformR (a b : L2C) :
    inner ℝ (freqTrR a) b = inner ℝ a (freqTrInvR b) :=
  transformRealIsometry.inner_map_eq_flip a b

theorem fracHeatProject_inner {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (g : L2R) (ψ : X) :
    inner ℝ (fracHeatSolenoidal α τ g) ψ = inner ℝ g (fracPhiX α τ ψ) := by
  have hsa : ∀ a b : L2C, inner ℝ (fracPhiMul α τ a) b = inner ℝ a (fracPhiMul α τ b) := by
    intro a b
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [fracPhiMul_ae hα hτ a, fracPhiMul_ae hα hτ b] with x ha hb
    rw [ha, hb, real_inner_smul_left, real_inner_smul_right]
  have hproj : ∀ w : L2C, inner ℝ (projX w) ψ = inner ℝ w (ψ : L2C) := fun w =>
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right ψ w
  show inner ℝ (projX (fracPhiMul α τ (freqTrR (complexify g)))) ψ =
    inner ℝ g (realPart (freqTrInvR (fracPhiMul α τ ψ)))
  rw [hproj, hsa, inner_transformR, inner_complexify_real]

theorem fracBilinX_spec {α τ : ℝ} (h1 : FracBilinExists α) (hτ : 0 < τ) :
    FracBilinSpec α τ (fracBilinX α τ) := by
  have h : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, h1 τ hτ⟩
  unfold fracBilinX
  rw [dif_pos h]
  exact h.2.choose_spec

end Breakdown.FracInternal

namespace Breakdown.Freq

theorem fracBilinTestFormula (α : ℝ) (hα : 1 < α) (h1 : FracBilinExists α) :
    FracBilinTestFormula α := by
  intro φ hφ τ hτ v
  apply ext_inner_right ℝ
  intro ψ
  rw [FracInternal.fracBilinX_spec h1 hτ, real_inner_smul_left,
    FracInternal.fracHeatProject_inner hα hτ, fracBilinForm,
    Internal.BilinTestFormula.trilinear_sum velocity_holds fieldOpRealized_holds hφ v]

end Breakdown.Freq

namespace Breakdown.FracInternal

open Breakdown.Freq Breakdown.Freq.Internal.BilinCompact
open scoped BoundedContinuousFunction Classical

def fracExtend (α τ R : ℝ) (f : ballR R →ᵇ CSpace) : Space → CSpace :=
  fun ξ => if h : ξ ∈ ballR R then fracPhiFactor α τ ξ • f ⟨ξ, h⟩ else 0

theorem fracExtend_eq (α τ R : ℝ) (f : ballR R →ᵇ CSpace) :
    fracExtend α τ R f = (ballR R).indicator (fracExtend α τ R f) := by
  funext ξ
  by_cases h : ξ ∈ ballR R
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]; simp [fracExtend, h]

theorem continuousOn_fracExtend {α : ℝ} (hα : 1 < α) (τ R : ℝ) (f : ballR R →ᵇ CSpace) :
    ContinuousOn (fracExtend α τ R f) (ballR R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (ballR R).domRestrict (fracExtend α τ R f) =
      fun x : ballR R => fracPhiFactor α τ x • f x := by
    funext x; simp [fracExtend, x.2]
  rw [this]
  exact ((continuous_fracPhiFactor hα τ).comp continuous_subtype_val).smul f.continuous

theorem norm_fracExtend_le {α τ R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (f : ballR R →ᵇ CSpace)
    (ξ : Space) : ‖fracExtend α τ R f ξ‖ ≤ (2 * π + 1 / τ) * ‖f‖ := by
  unfold fracExtend
  split_ifs with h
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fracPhiFactor_nonneg _ _ _)]
    exact mul_le_mul (fracPhiFactor_le hα hτ ξ) (f.norm_coe_le_norm _) (norm_nonneg _)
      (by positivity)
  · rw [norm_zero]; positivity

theorem memLp_fracExtend {α τ R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (f : ballR R →ᵇ CSpace) :
    MemLp (fracExtend α τ R f) 2 volume := by
  rw [fracExtend_eq, memLp_indicator_iff_restrict measurableSet_closedBall]
  have : IsFiniteMeasure (volume.restrict (ballR R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  exact MemLp.of_bound ((continuousOn_fracExtend hα τ R f).aestronglyMeasurable
    measurableSet_closedBall) _ (Filter.Eventually.of_forall (norm_fracExtend_le hα hτ f))

def fracCutLp (α τ R : ℝ) (f : ballR R →ᵇ CSpace) : L2C := toLpOrZero 2 (fracExtend α τ R f)

theorem fracCutLp_ae {α τ R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (f : ballR R →ᵇ CSpace) :
    (fracCutLp α τ R f : Space → CSpace) =ᵐ[volume] fracExtend α τ R f := by
  unfold fracCutLp toLpOrZero
  rw [dif_pos (memLp_fracExtend hα hτ f)]
  exact (memLp_fracExtend hα hτ f).coeFn_toLp

theorem dist_fracCutLp_le {α τ R : ℝ} (hα : 1 < α) (hτ : 0 < τ) :
    ∃ c : ℝ, ∀ f f' : ballR R →ᵇ CSpace,
      dist (fracCutLp α τ R f) (fracCutLp α τ R f') ≤ c * dist f f' := by
  have hχ : MemLp ((ballR R).indicator (fun _ => (1 : ℝ))) 2 volume :=
    memLp_indicator_const 2 measurableSet_closedBall (1 : ℝ) (Or.inr measure_closedBall_lt_top.ne)
  refine ⟨(2 * π + 1 / τ) * ‖hχ.toLp _‖, fun f f' => ?_⟩
  rw [dist_eq_norm]
  have key : ‖fracCutLp α τ R f - fracCutLp α τ R f'‖ ≤
      ((2 * π + 1 / τ) * dist f f') * ‖hχ.toLp _‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (fracCutLp α τ R f) (fracCutLp α τ R f'), fracCutLp_ae hα hτ f,
      fracCutLp_ae hα hτ f', hχ.coeFn_toLp] with ξ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
    by_cases h : ξ ∈ ballR R
    · rw [indicator_of_mem h, norm_one, mul_one]
      simp only [fracExtend, dif_pos h]
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (fracPhiFactor_nonneg _ _ _)]
      have hd : ‖f ⟨ξ, h⟩ - f' ⟨ξ, h⟩‖ ≤ dist f f' := by
        rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist _
      exact mul_le_mul (fracPhiFactor_le hα hτ ξ) hd (norm_nonneg _) (by positivity)
    · simp only [fracExtend, dif_neg h, indicator_of_notMem h, sub_zero, norm_zero, mul_zero,
        le_refl]
  exact key.trans (le_of_eq (by ring))

theorem fracTail_le {α τ R : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hR : 1 ≤ R)
    {K : Set Space} (hK : IsCompact K) {g : L2R}
    (hg : ∀ᵐ x ∂volume, x ∉ K → (g : Space → Space) x = 0) :
    ‖fracPhiMul α τ (freqTrR (complexify g)) - fracCutLp α τ R (fcut hK R g)‖ ≤
      1 / (τ * R) * ‖freqTrR (complexify g)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (fracPhiMul α τ (freqTrR (complexify g)))
      (fracCutLp α τ R (fcut hK R g)),
    fracPhiMul_ae hα hτ (freqTrR (complexify g)), fracCutLp_ae hα hτ (fcut hK R g),
    freqTrR_complexify_ae freqTrL1L2.1 hK hg] with ξ h1 h3 h5 h6
  rw [h1, Pi.sub_apply, h3, h5]
  by_cases h : ξ ∈ ballR R
  · simp only [fracExtend, dif_pos h]
    rw [fcut_apply, ← h6, sub_self, norm_zero]
    have : 0 < τ * R := by positivity
    positivity
  · simp only [fracExtend, dif_neg h, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fracPhiFactor_nonneg _ _ _)]
    have hξ : R ≤ ‖ξ‖ := by
      simp only [ballR, Metric.mem_closedBall, dist_zero_right, not_le] at h
      exact h.le
    exact mul_le_mul_of_nonneg_right (fracPhiFactor_tail hα hτ hR hξ) (norm_nonneg _)

theorem fracTotallyBounded_image {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ)
    {K : Set Space} (hK : IsCompact K) {C : ℝ} (hC : 0 ≤ C) :
    TotallyBounded ((fun g : L2R => fracPhiMul α τ (freqTrR (complexify g))) '' supSet K C) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hD : 0 ≤ ‖complexify‖ * C := by positivity
  obtain ⟨R, hR, htail⟩ : ∃ R : ℝ, 1 ≤ R ∧ 1 / (τ * R) * (‖complexify‖ * C) < ε / 2 := by
    refine ⟨4 * (‖complexify‖ * C) / (τ * ε) + 1, by
      have : 0 ≤ 4 * (‖complexify‖ * C) / (τ * ε) := by positivity
      linarith, ?_⟩
    have hRe : τ * (4 * (‖complexify‖ * C) / (τ * ε) + 1) * ε =
        4 * (‖complexify‖ * C) + τ * ε := by
      field_simp
    have hRpos : 0 < 4 * (‖complexify‖ * C) / (τ * ε) + 1 := by positivity
    rw [one_div, inv_mul_eq_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hτ hε]
  obtain ⟨c, hc⟩ := dist_fracCutLp_le (R := R) hα hτ
  have hcomp : IsCompact (fracCutLp α τ R '' closure (fcut hK R '' supSet K C)) :=
    (isCompact_closure_fcut hK R C).image (LipschitzWith.of_dist_le' hc).continuous
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hcomp.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hm : fracCutLp α τ R (fcut hK R g) ∈ fracCutLp α τ R '' closure (fcut hK R '' supSet K C) :=
    ⟨_, subset_closure ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨y, hy, hdist⟩ := mem_iUnion₂.1 (hcov hm)
  refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
  rw [Metric.mem_ball] at hdist ⊢
  have hu : ‖freqTrR (complexify g)‖ ≤ ‖complexify‖ * C := by
    have : ‖freqTrR (complexify g)‖ = ‖complexify g‖ := freqTrL2.norm_map (complexify g)
    rw [this]
    exact (complexify.le_opNorm g).trans (mul_le_mul_of_nonneg_left hg.1 (norm_nonneg _))
  have ht' := fracTail_le hα hτ hR hK hg.2
  have hRpos : 0 < τ * R := by positivity
  have hfirst : dist (fracPhiMul α τ (freqTrR (complexify g))) (fracCutLp α τ R (fcut hK R g)) <
      ε / 2 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (ht'.trans (mul_le_mul_of_nonneg_left hu (by positivity))) htail
  calc dist (fracPhiMul α τ (freqTrR (complexify g))) y
      ≤ dist (fracPhiMul α τ (freqTrR (complexify g))) (fracCutLp α τ R (fcut hK R g)) +
        dist (fracCutLp α τ R (fcut hK R g)) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hdist
    _ = ε := by ring

end Breakdown.FracInternal

namespace Breakdown.Freq

theorem fracBilinCompact (α : ℝ) (hα : 1 < α) (h1 : FracBilinTestFormula α)
    (_h2 : FracBilinBound α) : FracBilinCompact α := by
  intro x hx τ hτ
  obtain ⟨φ, hφ, rfl⟩ := testSpan_holds x hx
  have hfun : ⇑(fracBilinX α τ (embedX φ)) = fun v =>
      (-(1 / 2 : ℝ)) • projX (FracInternal.fracPhiMul α τ (freqTrR (complexify (advectTest φ v)))) := by
    funext v
    rw [h1 φ hφ τ hτ v]
    rfl
  rw [hfun, isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  obtain ⟨C, hC, hmem⟩ := Internal.BilinCompact.advect_mem hφ
  have hK : IsCompact (tsupport φ) := hφ.2.1
  have htb := FracInternal.fracTotallyBounded_image hα hτ hK hC
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos,
    (fun y => (-(1 / 2 : ℝ)) • projX y) ''
      closure ((fun g : L2R => FracInternal.fracPhiMul α τ (freqTrR (complexify g))) ''
        Internal.BilinCompact.supSet (tsupport φ) C),
    (htb.closure.isCompact_of_isClosed isClosed_closure).image
      (by fun_prop), ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨_, subset_closure ⟨_, hmem v (mem_closedBall_zero_iff.1 hv), rfl⟩, rfl⟩

end Breakdown.Freq

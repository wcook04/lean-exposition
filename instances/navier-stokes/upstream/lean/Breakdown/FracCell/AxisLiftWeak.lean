import Breakdown.FracCell.AxisLiftParts

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.AxisLiftWeak

theorem entry_le (G : Space →L[ℝ] Space) : entrySq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold entrySq
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    intro i
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      have := G.le_opNorm (unitVector i)
      rwa [unitVector, PiLp.norm_single, norm_one, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖G‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖G‖ ^ 2 := by simp

theorem entry_cont : Continuous (fun G : Space →L[ℝ] Space => entrySq G) := by
  unfold entrySq
  fun_prop

theorem comp_line {ψ : Space → Space} {y : Space} (h : DifferentiableAt ℝ ψ y) (i : Fin 3) (v : Space) :
    lineDeriv ℝ (fun x => ψ x i) y v = fderiv ℝ ψ y v i := by
  have h2 := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h.hasFDerivAt).hasLineDerivAt v
  exact h2.lineDeriv

end Internal.AxisLiftWeak

open Internal.AxisLiftWeak in
theorem weak_of_slopeBound {ψ : Space → Space} {K : NNReal} (hL : LipschitzWith K ψ) (hc : HasCompactSupport ψ)
    {D : Space → (Space →L[ℝ] Space)} (hD : ∀ᵐ y, DifferentiableAt ℝ ψ y → fderiv ℝ ψ y = D y) :
    MemLp ψ 2 volume ∧ AEStronglyMeasurable D volume ∧ Integrable (fun y => entrySq (D y)) ∧
      IsWeakGradientOf ψ D := by
  have hdiff := hL.ae_differentiableAt (μ := volume)
  have hDe : (fun y => fderiv ℝ ψ y) =ᵐ[volume] D := by
    filter_upwards [hdiff, hD] with y h1 h2 using h2 h1
  have hfm : AEStronglyMeasurable (fderiv ℝ ψ) volume := (measurable_fderiv ℝ ψ).aestronglyMeasurable
  have hDm : AEStronglyMeasurable D volume := hfm.congr hDe
  have hbd : ∀ y, ‖fderiv ℝ ψ y‖ ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hL
  have hDbd : ∀ᵐ y, ‖D y‖ ≤ K := by
    filter_upwards [hDe] with y hy
    rw [← hy]
    exact hbd y
  refine ⟨hL.continuous.memLp_of_hasCompactSupport hc, hDm, ?_, ?_⟩
  · have hT : MeasurableSet (tsupport ψ) := (isClosed_tsupport ψ).measurableSet
    have hfin : volume (tsupport ψ) ≠ ⊤ := hc.isCompact.measure_lt_top.ne
    have hg : Integrable ((tsupport ψ).indicator (fun _ => 3 * (K : ℝ) ^ 2)) :=
      (integrable_indicator_iff hT).2 (integrableOn_const hfin)
    have hm : AEStronglyMeasurable (fun y => entrySq (fderiv ℝ ψ y)) volume :=
      entry_cont.comp_aestronglyMeasurable hfm
    have hI : Integrable (fun y => entrySq (fderiv ℝ ψ y)) := by
      refine Integrable.mono' hg hm (Filter.Eventually.of_forall fun y => ?_)
      have hnn : 0 ≤ entrySq (fderiv ℝ ψ y) := Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [Real.norm_of_nonneg hnn]
      by_cases hy : y ∈ tsupport ψ
      · rw [Set.indicator_of_mem hy]
        calc entrySq (fderiv ℝ ψ y) ≤ 3 * ‖fderiv ℝ ψ y‖ ^ 2 := entry_le _
          _ ≤ 3 * (K : ℝ) ^ 2 := by
            have := pow_le_pow_left₀ (norm_nonneg _) (hbd y) 2
            linarith
      · rw [Set.indicator_of_notMem hy]
        have h0 : fderiv ℝ ψ y = 0 := by
          by_contra hne
          exact hy (support_fderiv_subset ℝ hne)
        rw [h0]
        simp [entrySq]
    exact hI.congr (by filter_upwards [hDe] with y hy; rw [hy])
  · intro φ hφ j
    obtain ⟨hφs, hφc⟩ := hφ
    obtain ⟨Cφ, hφL⟩ := hφs.lipschitzWith_of_hasCompactSupport hφc (by simp)
    have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => (hφs.differentiable (by simp)).differentiableAt
    have hφi : Integrable φ := hφs.continuous.integrable_of_hasCompactSupport hφc
    have hI1 : Integrable (fun y => (fderiv ℝ φ y (unitVector j)) • ψ y) := by
      have hcs : HasCompactSupport (fun y => (fderiv ℝ φ y (unitVector j)) • ψ y) :=
        hc.mono (Function.support_smul_subset_right (fun y => fderiv ℝ φ y (unitVector j)) ψ)
      refine Continuous.integrable_of_hasCompactSupport ?_ hcs
      exact ((hφs.continuous_fderiv (by simp)).clm_apply continuous_const).smul hL.continuous
    have hDj : AEStronglyMeasurable (fun y => D y (unitVector j)) volume :=
      (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hDm
    have hI2 : Integrable (fun y => φ y • D y (unitVector j)) := by
      have hm2 : AEStronglyMeasurable (fun y => φ y • D y (unitVector j)) volume :=
        hφs.continuous.aestronglyMeasurable.smul hDj
      have hb : Integrable (fun y => ‖φ y‖ * (K : ℝ)) := hφi.norm.mul_const (K : ℝ)
      refine Integrable.mono' hb hm2 ?_
      filter_upwards [hDbd] with y hy
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := (D y).le_opNorm (unitVector j)
      rw [unitVector, PiLp.norm_single, norm_one, mul_one] at this
      exact this.trans hy
    have key : ∀ i : Fin 3, ∫ y, fderiv ℝ φ y (unitVector j) * ψ y i = -∫ y, φ y * D y (unitVector j) i := by
      intro i
      have hψi : LipschitzWith (‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖₊ * K) (fun y => ψ y i) :=
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).lipschitz.comp hL
      have M := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) hψi hφL hφc (unitVector j)
      have e1 : ∀ y, lineDeriv ℝ φ y (-unitVector j) * ψ y i = -(fderiv ℝ φ y (unitVector j) * ψ y i) := by
        intro y
        rw [(hφd y).lineDeriv_eq_fderiv, map_neg, neg_mul]
      have e2 : (fun y => lineDeriv ℝ (fun x => ψ x i) y (unitVector j) * φ y)
          =ᵐ[volume] fun y => φ y * D y (unitVector j) i := by
        filter_upwards [hdiff, hD] with y h1 h2
        rw [comp_line h1, h2 h1, mul_comm]
      simp only [e1, integral_neg] at M
      rw [integral_congr_ae e2] at M
      linarith
    ext i
    have a1 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hI1
    have a2 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hI2
    simp only [PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] at a1 a2
    rw [PiLp.neg_apply, ← a1, ← a2, key i]

def LiftSlopeStatement : Prop :=
  ∀ (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (ψ : Space → Space),
    g.innerRadius = 0 → g.mode = 0 → 0 < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    χ 1 = 0 → (∃ K, LipschitzWith K χ) → (∀ s c j, ContDiff ℝ 1 (u s c j)) →
    (∀ s c j, u s c j (if s = 0 then g.lowerHeight else -g.upperHeight) = 0 ∧
      u s c j (if s = 0 then g.upperHeight else -g.lowerHeight) = 0) →
    (∀ s c, c ≠ 2 → u s c 0 = 0) →
    (∀ y, ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y) →
    (∃ K, LipschitzWith K ψ) ∧ HasCompactSupport ψ

def LiftDerivStatement : Prop :=
  ∀ (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (ψ : Space → Space),
    g.innerRadius = 0 → g.mode = 0 → 0 < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    χ 1 = 0 → (∃ K, LipschitzWith K χ) → (∀ s c j, ContDiff ℝ 1 (u s c j)) →
    (∀ s c j, u s c j (if s = 0 then g.lowerHeight else -g.upperHeight) = 0 ∧
      u s c j (if s = 0 then g.upperHeight else -g.lowerHeight) = 0) →
    (∀ s c, c ≠ 2 → u s c 0 = 0) →
    (∀ y, ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y) →
    ∀ᵐ y, DifferentiableAt ℝ ψ y → fderiv ℝ ψ y = liftGrad g χ u y

theorem liftGrad_of_parts (hL : LiftSlopeStatement) (hD : LiftDerivStatement) : LiftGradStatement := by
  intro g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ
  obtain ⟨⟨K, hK⟩, hc⟩ := hL g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ
  exact weak_of_slopeBound hK hc (hD g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ)

end Spectral

end CellCert

end Breakdown

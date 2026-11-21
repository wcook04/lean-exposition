import Breakdown.Frac.StTorusForce
import Breakdown.Torus.Forced

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusForcedModes.Internal

open TimeCoef.Internal

theorem mode_deriv {α : ℝ} (hC : CoefFractional α) {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    {F : ℝ → Space → Space} {a b : ℝ} (hab : a < b) (h : IsFracForcedPeriodicSolution α u p F a b)
    (k : Lattice) {τ : ℝ} (hτ : τ ∈ Ioo a b) :
    HasDerivAt (fun σ => freqTrCoef (u σ) k)
      ((-((2 * π * ‖freq k‖) ^ (2 * α))) • freqTrCoef (u τ) k
        - (divFree k (advCoef (toV (u τ)) (toV (u τ)) k) - divFree k (freqTrCoef (F τ) k))) τ := by
  obtain ⟨hu, hp, hFc, hper, hdiv, hmom⟩ := h
  have hτ' : τ ∈ Icc a b := Ioo_subset_Icc_self hτ
  have hφ : ContDiff ℝ ∞ (u τ) :=
    Forced.Internal.sliceContDiff (g := fun z : ℝ × Space => u z.1 z.2) hu hτ'
  have hq : ContDiff ℝ ∞ (p τ) :=
    Forced.Internal.sliceContDiff (g := fun z : ℝ × Space => p z.1 z.2) hp hτ'
  have hFτ : Continuous (F τ) :=
    Forced.Internal.sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc hτ'
  have hd : HasDerivAt (fun σ => freqTrCoef (u σ) k)
      (freqTrCoef (fun x => deriv (fun σ => u σ x) τ) k) τ :=
    Forced.Internal.hasDerivAt_freqTrCoef_slab (g := fun z : ℝ × Space => u z.1 z.2) hu hab k hτ
  have hD : Continuous (fun x => deriv (fun σ => u σ x) τ) := by
    have hU : UniqueDiffOn ℝ (Icc a b ×ˢ (univ : Set Space)) :=
      (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
    have hDc : ContinuousOn (fun z => fderivWithin ℝ (fun z : ℝ × Space => u z.1 z.2)
        (Icc a b ×ˢ (univ : Set Space)) z (1, 0)) (Icc a b ×ˢ univ) :=
      ((hu.fderivWithin hU infty_add_one_le).clm_apply contDiffOn_const).continuousOn
    have e : (fun x => deriv (fun σ => u σ x) τ) = fun x => fderivWithin ℝ
        (fun z : ℝ × Space => u z.1 z.2) (Icc a b ×ˢ (univ : Set Space)) (τ, x) (1, 0) :=
      funext fun x => (Forced.Internal.timeDeriv (g := fun z : ℝ × Space => u z.1 z.2) hu hτ x).deriv
    rw [e]
    exact Forced.Internal.sliceContinuous hDc hτ'
  have hadv : Continuous (advectionAt (u τ)) := Internal.Mild.continuous_advectionAt hφ
  have hgr : Continuous (gradientAt (p τ)) := Internal.Mild.continuous_gradientAt hq
  have hA : Continuous (fractionalPowerAt α (u τ)) := by
    have e : fractionalPowerAt α (u τ) = fun x =>
        F τ x - deriv (fun σ => u σ x) τ - advectionAt (u τ) x - gradientAt (p τ) x := by
      funext x
      rw [← hmom τ hτ x]
      abel
    rw [e]
    exact ((hFτ.sub hD).sub hadv).sub hgr
  have hm : (fun x => deriv (fun σ => u σ x) τ) =
      fun x => ((F τ x - advectionAt (u τ) x) - gradientAt (p τ) x) - fractionalPowerAt α (u τ) x := by
    funext x
    rw [← hmom τ hτ x]
    abel
  have hFa : Continuous (fun x => F τ x - advectionAt (u τ) x) := hFτ.sub hadv
  have hFag : Continuous (fun x => (F τ x - advectionAt (u τ) x) - gradientAt (p τ) x) := hFa.sub hgr
  rw [hm, Internal.Mild.freqTrCoef_sub hFag hA, Internal.Mild.freqTrCoef_sub hFa hgr,
    Internal.Mild.freqTrCoef_sub hFτ hadv, hC _ hφ (hper τ hτ').1,
    coefGradient _ (hq.of_le ENat.LEInfty.out) (hper τ hτ').2.1,
    coefAdvection coefDeriv (freqTrSeriesSpec coefDeriv) _ hφ (hper τ hτ').1 (hdiv τ hτ')] at hd
  have hfix : ∀ σ ∈ Icc a b, divFree k (freqTrCoef (u σ) k) = freqTrCoef (u σ) k := by
    intro σ hσ
    rw [← (freqTrSeriesSpec coefDeriv _
      (Forced.Internal.sliceContDiff (g := fun z : ℝ × Space => u z.1 z.2) hu hσ)
      (hper σ hσ).1 (hdiv σ hσ)).1 k, Internal.Mild.divFree_coeff]
  set LR : Coef →L[ℝ] Coef := (Internal.Mild.divFreeL k).restrictScalars ℝ with hLR
  have hL' := LR.hasFDerivAt.comp_hasDerivAt τ hd
  have hev : (fun σ => freqTrCoef (u σ) k) =ᶠ[𝓝 τ] (LR ∘ fun σ => freqTrCoef (u σ) k) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ
    exact (hfix σ (Ioo_subset_Icc_self hσ)).symm
  refine (hL'.congr_of_eventuallyEq hev).congr_deriv ?_
  have e2 : LR ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0 := by
    show Internal.Mild.divFreeL k ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0
    rw [map_smul, Internal.Mild.divFreeL_apply, Internal.Mild.divFree_latVec, smul_zero]
  rw [map_sub, map_sub, map_sub, e2, sub_zero, map_smul]
  show divFree k _ - divFree k _ - _ • divFree k _ = _
  rw [hfix τ hτ', neg_smul]
  abel

theorem mode_identity {α : ℝ} (hK : FracTorusKernelAlgebra α)
    (hC : CoefFractional α) (hF : FracTorusForceAlgebra α) {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} {F : ℝ → Space → Space} {a b : ℝ}
    (hab : a < b) (h : IsFracForcedPeriodicSolution α u p F a b)
    (hUc : ContinuousOn (fun t => toV (u t)) (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    (hI : IntervalIntegrable (fun s => fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) volume a t)
    (hJ : IntervalIntegrable (fun s => fracTorusForce α (t - s) (F s)) volume a t) (k : Lattice) :
    coeff (toV (u t)) k = fracLatticeFactor α (t - a) k • coeff (toV (u a)) k +
      (∫ s in a..t, coeff (fracTorusKernel α (t - s) (toV (u s)) (toV (u s))) k) +
      ∫ s in a..t, coeff (fracTorusForce α (t - s) (F s)) k := by
  have hu := h.1
  have hFc := h.2.2.1
  have hper := h.2.2.2.1
  have hdiv := h.2.2.2.2.1
  have hcU : ∀ s ∈ Icc a b, coeff (toV (u s)) k = freqTrCoef (u s) k := fun s hs =>
    (freqTrSeriesSpec coefDeriv _
      (Forced.Internal.sliceContDiff (g := fun z : ℝ × Space => u z.1 z.2) hu hs)
      (hper s hs).1 (hdiv s hs)).1 k
  have hpos : 0 < fracLatticeFactor α 1 k := Real.exp_pos _
  have hB : ∀ s, divFree k (advCoef (toV (u s)) (toV (u s)) k) =
      (-(fracLatticeFactor α 1 k)⁻¹) • coeff (fracTorusKernel α 1 (toV (u s)) (toV (u s))) k := by
    intro s
    rw [hK.1, fracTorusKernelCoef, if_pos one_pos, Internal.Mild.divFree_add, ← two_smul ℝ (divFree k _),
      smul_smul, smul_smul,
      show -(fracLatticeFactor α 1 k)⁻¹ * (-(1 / 2) * fracLatticeFactor α 1 k) * 2 = 1 by
        field_simp, one_smul]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hUt : ContinuousOn (fun s => toV (u s)) (Icc a t) := hUc.mono hsub
  have hAc : ContinuousOn (fun s => divFree k (advCoef (toV (u s)) (toV (u s)) k)) (Icc a t) := by
    simp only [hB]
    exact ((Internal.Mild.coeffL k).continuous.comp_continuousOn
      (((fracTorusKernel α 1).continuous.comp_continuousOn hUt).clm_apply hUt)).const_smul
        (-(fracLatticeFactor α 1 k)⁻¹)
  have hFk : ContinuousOn (fun s => freqTrCoef (F s) k) (Icc a b) :=
    Forced.Internal.continuousOn_freqTrCoef_slab (g := fun z : ℝ × Space => F z.1 z.2) hFc k
  have hFl : ContinuousOn (fun s => divFree k (freqTrCoef (F s) k)) (Icc a t) :=
    (Internal.Mild.divFreeL k).continuous.comp_continuousOn (hFk.mono hsub)
  have hcc : ContinuousOn (fun s => freqTrCoef (u s) k) (Icc a t) :=
    ((Internal.Mild.coeffL k).continuous.comp_continuousOn hUt).congr
      (fun s hs => (hcU s (hsub hs)).symm)
  have hv := Forced.Internal.variation_of_constants ht.1 hcc (hAc.sub hFl)
    (fun s hs => mode_deriv hC hab h k ⟨hs.1, hs.2.trans_le ht.2⟩)
  beta_reduce at hv
  have hh : fracLatticeFactor α (t - a) k =
      Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * (t - a))) := by
    simp only [fracLatticeFactor, max_eq_left (sub_nonneg.2 ht.1)]
  rw [hcU t ht, hcU a ⟨le_rfl, hab.le⟩, hv, hh, add_assoc]
  congr 1
  rw [← intervalIntegral.integral_add (Forced.Internal.intervalIntegrable_coeff hI k)
    (Forced.Internal.intervalIntegrable_coeff hJ k)]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with s hs hmem
  rw [uIoc_of_le ht.1] at hmem
  have hst : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hmem.2 hs)
  rw [hK.1, fracTorusKernelCoef, if_pos hst, hF.1, fracTorusForceCoef, if_pos hst,
    Internal.Mild.divFree_add, ← two_smul ℝ (divFree k _), smul_smul,
    fracLatticeFactor, max_eq_left hst.le, Pi.sub_apply, smul_sub,
    show ∀ z : ℝ, -(1 / 2) * z * 2 = -z from fun z => by ring, neg_smul, neg_smul, sub_neg_eq_add]

end FracTorusForcedModes.Internal

end Breakdown.Periodic

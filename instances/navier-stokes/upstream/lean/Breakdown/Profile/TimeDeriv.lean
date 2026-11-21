import Breakdown.Profile.StatementsPhysical

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma hasDerivAt_physicalScale {t : ℝ} (ht : t < 1) :
    HasDerivAt physicalScale (physicalScale t ^ 3 / 2) t := by
  have h1 : (1 - t) ≠ 0 := by linarith
  have hc : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have hi : HasDerivAt (fun τ : ℝ => (1 - τ)⁻¹) (-(-1) / (1 - t) ^ 2) t := hc.fun_inv h1
  have hpos : (1 - t)⁻¹ ≠ 0 := inv_ne_zero h1
  have hs := hi.sqrt hpos
  refine hs.congr_deriv ?_
  have hp : 0 < 1 - t := by linarith
  have ha : physicalScale t ^ 2 = (1 - t)⁻¹ := by
    unfold physicalScale
    exact Real.sq_sqrt (inv_nonneg.mpr hp.le)
  have hne : physicalScale t ≠ 0 := by
    unfold physicalScale
    exact (Real.sqrt_pos.mpr (inv_pos.mpr hp)).ne'
  change -(-1) / (1 - t) ^ 2 / (2 * physicalScale t) = physicalScale t ^ 3 / 2
  field_simp
  have : (1 - t) = (physicalScale t ^ 2)⁻¹ := by rw [ha, inv_inv]
  rw [this]
  field_simp

private lemma hasDerivAt_physicalTime (s₀ : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (physicalTime s₀) (physicalScale t ^ 2) t := by
  have h1 : (1 - t) ≠ 0 := by linarith
  have hc : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have hl := (hc.log h1).const_sub s₀
  refine hl.congr_deriv ?_
  have hp : 0 < 1 - t := by linarith
  have ha : physicalScale t ^ 2 = (1 - t)⁻¹ := by
    unfold physicalScale
    exact Real.sq_sqrt (inv_nonneg.mpr hp.le)
  rw [ha]
  field_simp

theorem physicalTimeDeriv_holds : PhysicalTimeDeriv := by
  intro W hW s₀ t ht x
  set Φ : ℝ × Space → Space := fun z => W z.1 z.2 with hΦdef
  have hdiff : Differentiable ℝ Φ := hW.differentiable (by simp)
  set a := physicalScale t with hadef
  set σ := physicalTime s₀ t with hσdef
  set y := a • x with hydef
  set D := fderiv ℝ Φ (σ, y) with hDdef
  have hD : HasFDerivAt Φ D (σ, y) := (hdiff (σ, y)).hasFDerivAt
  have hD1 : D (1, 0) = deriv (fun s => W s y) σ := by
    have hg : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : Space)) σ :=
      (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
    have := hD.comp_hasDerivAt σ hg
    exact this.deriv.symm
  have hD2 : ∀ h : Space, D (0, h) = fderiv ℝ (W σ) y h := by
    intro h
    have := hD.comp y (hasFDerivAt_prodMk_right σ y)
    have e := this.fderiv
    have e2 : fderiv ℝ (W σ) y = D.comp (ContinuousLinearMap.inr ℝ ℝ Space) := e
    rw [e2]
    rfl
  have hpath : HasDerivAt (fun τ => (physicalTime s₀ τ, physicalScale τ • x))
      (a ^ 2, (a ^ 3 / 2) • x) t :=
    (hasDerivAt_physicalTime s₀ ht).prodMk ((hasDerivAt_physicalScale ht).smul_const x)
  have hcomp := hD.comp_hasDerivAt t hpath
  have hprod := (hasDerivAt_physicalScale ht).smul hcomp
  have hfun : (fun τ => physicalField W s₀ τ x) =
      (physicalScale • (Φ ∘ fun τ => (physicalTime s₀ τ, physicalScale τ • x))) := by
    funext τ
    rfl
  rw [hfun]
  refine hprod.congr_deriv ?_
  have hsplit : ((a ^ 2, (a ^ 3 / 2) • x) : ℝ × Space) = a ^ 2 • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), (a ^ 3 / 2) • x) := by
    ext <;> simp
  have hW0 : (Φ ∘ fun τ => (physicalTime s₀ τ, physicalScale τ • x)) t = W σ y := rfl
  rw [hW0, hsplit, map_add, map_smul, hD1, hD2, map_smul, hydef, map_smul]
  module

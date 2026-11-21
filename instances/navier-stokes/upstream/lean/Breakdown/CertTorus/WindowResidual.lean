import Breakdown.CertTorus.RegularStatements
import Breakdown.Profile.Dilate

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.FarField

private lemma field_of_scale (W : ℝ → Space → Space) (s₀ σ r : ℝ) (hr : 0 < r)
    (hlog : Real.log (r ^ 2) = -(σ - s₀)) (y : Space) :
    W σ y = r • physicalField W s₀ (1 - r ^ 2) (r • y) := by
  have h1 : (1 : ℝ) - (1 - r ^ 2) = r ^ 2 := by ring
  have hT : physicalTime s₀ (1 - r ^ 2) = σ := by
    unfold physicalTime
    rw [h1, hlog]
    ring
  have hS : Real.sqrt ((1 - (1 - r ^ 2))⁻¹) = r⁻¹ := by
    rw [h1, ← inv_pow, Real.sqrt_sq (inv_nonneg.mpr hr.le)]
  simp only [physicalField, dilateField]
  rw [hT, hS, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', inv_mul_cancel₀ hr.ne']
  simp only [one_smul]

private lemma pressure_of_scale (q : ℝ → Space → ℝ) (s₀ σ r : ℝ) (hr : 0 < r)
    (hlog : Real.log (r ^ 2) = -(σ - s₀)) (y : Space) :
    q σ y = r ^ 2 * ((1 - (1 - r ^ 2))⁻¹ * q (s₀ - Real.log (1 - (1 - r ^ 2)))
      ((Real.sqrt (1 - (1 - r ^ 2)))⁻¹ • (r • y))) := by
  have h1 : (1 : ℝ) - (1 - r ^ 2) = r ^ 2 := by ring
  rw [h1, hlog, Real.sqrt_sq hr.le, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
    show s₀ - -(σ - s₀) = σ by ring, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]

private lemma window_mem {s₀ a b s r : ℝ} (hab : a < b) (hb : b < 1) (hr : 0 < r)
    (hlog : Real.log (r ^ 2) = -(s - s₀))
    (hs : s ∈ Ioo (s₀ - Real.log (1 - a)) (s₀ - Real.log (1 - b))) : 1 - r ^ 2 ∈ Ioo a b := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  obtain ⟨h1, h2⟩ := hs
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  constructor
  · have : r ^ 2 < 1 - a := by
      rw [← Real.log_lt_log_iff hr2 h1a, hlog]
      linarith
    linarith
  · have : 1 - b < r ^ 2 := by
      rw [← Real.log_lt_log_iff h1b hr2, hlog]
      linarith
    linarith

private lemma log_scale_sq (s₀ σ : ℝ) : Real.log (Real.exp (-(σ - s₀) / 2) ^ 2) = -(σ - s₀) := by
  rw [Real.log_pow, Real.log_exp]
  push_cast
  ring

private lemma scale_hasDerivAt (s₀ s : ℝ) :
    HasDerivAt (fun σ : ℝ => Real.exp (-(σ - s₀) / 2)) (-(1 / 2) * Real.exp (-(s - s₀) / 2)) s := by
  have h0 : HasDerivAt (fun σ : ℝ => -(1 / 2) * (σ - s₀)) (-(1 / 2) * 1) s :=
    ((hasDerivAt_id' s).sub_const s₀).const_mul _
  have hf : (fun σ : ℝ => Real.exp (-(σ - s₀) / 2)) = fun σ => Real.exp (-(1 / 2) * (σ - s₀)) :=
    funext fun σ => by congr 1; ring
  rw [hf]
  refine h0.exp.congr_deriv ?_
  rw [show -(1 / 2) * (s - s₀) = -(s - s₀) / 2 by ring]
  ring

private lemma window_hasDerivAt (W : ℝ → Space → Space) (s₀ s r : ℝ) (y : Space)
    (hr : Real.exp (-(s - s₀) / 2) = r)
    (hU : ContDiffAt ℝ ∞ (fun z : ℝ × Space => physicalField W s₀ z.1 z.2) (1 - r ^ 2, r • y))
    (g : Space)
    (hmom : HasDerivAt (fun τ => physicalField W s₀ τ (r • y)) g (1 - r ^ 2)) :
    HasDerivAt (fun σ => W σ y)
      (r • ((r ^ 2) • g + fderiv ℝ (physicalField W s₀ (1 - r ^ 2)) (r • y) ((-(1 / 2) * r) • y))
        + (-(1 / 2) * r) • physicalField W s₀ (1 - r ^ 2) (r • y)) s := by
  subst hr
  have hD : HasFDerivAt (fun z : ℝ × Space => physicalField W s₀ z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => physicalField W s₀ z.1 z.2)
        (1 - Real.exp (-(s - s₀) / 2) ^ 2, Real.exp (-(s - s₀) / 2) • y))
      (1 - Real.exp (-(s - s₀) / 2) ^ 2, Real.exp (-(s - s₀) / 2) • y) :=
    (hU.differentiableAt (by simp)).hasFDerivAt
  have hρ := scale_hasDerivAt s₀ s
  have hγ : HasDerivAt (fun σ : ℝ => ((1 : ℝ) - Real.exp (-(σ - s₀) / 2) ^ 2,
      Real.exp (-(σ - s₀) / 2) • y))
      ((Real.exp (-(s - s₀) / 2) ^ 2, (-(1 / 2) * Real.exp (-(s - s₀) / 2)) • y) : ℝ × Space) s := by
    have h := ((hρ.pow 2).const_sub 1).prodMk (hρ.smul_const y)
    refine h.congr_deriv (Prod.ext ?_ rfl)
    norm_num
    ring
  have hcomp := hD.comp_hasDerivAt s hγ
  have hprod := hρ.smul hcomp
  have hfun : (fun σ => W σ y) = fun σ => Real.exp (-(σ - s₀) / 2) •
      ((fun z : ℝ × Space => physicalField W s₀ z.1 z.2) ∘
        (fun σ : ℝ => ((1 : ℝ) - Real.exp (-(σ - s₀) / 2) ^ 2, Real.exp (-(σ - s₀) / 2) • y))) σ :=
    funext fun σ => field_of_scale W s₀ σ _ (Real.exp_pos _) (log_scale_sq s₀ σ) y
  rw [hfun]
  refine hprod.congr_deriv ?_
  set e := Real.exp (-(s - s₀) / 2) with he
  set D := fderiv ℝ (fun z : ℝ × Space => physicalField W s₀ z.1 z.2) (1 - e ^ 2, e • y) with hDdef
  have hD1 : D ((1 : ℝ), (0 : Space)) = g := by
    have h1 : HasDerivAt (fun τ => physicalField W s₀ τ (e • y)) (D ((1 : ℝ), (0 : Space))) (1 - e ^ 2) :=
      hD.comp_hasDerivAt (1 - e ^ 2) ((hasDerivAt_id' (1 - e ^ 2)).prodMk (hasDerivAt_const (1 - e ^ 2) (e • y)))
    exact h1.unique hmom
  have hD2 : ∀ v : Space, D ((0 : ℝ), v) = fderiv ℝ (physicalField W s₀ (1 - e ^ 2)) (e • y) v := by
    intro v
    have h2 : HasFDerivAt (physicalField W s₀ (1 - e ^ 2)) (D.comp (ContinuousLinearMap.inr ℝ ℝ Space)) (e • y) :=
      hD.comp (e • y) (hasFDerivAt_prodMk_right (1 - e ^ 2) (e • y))
    rw [h2.fderiv]
    rfl
  have hsplit : ((e ^ 2, (-(1 / 2) * e) • y) : ℝ × Space) =
      e ^ 2 • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), (-(1 / 2) * e) • y) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, hD1, hD2]
  rfl

theorem windowResidual_holds : WindowResidual := by
  intro W q s₀ a b ha hab hb hU hP hmom hdiv s hs y
  have hUat : ∀ τ ∈ Ioo a b, ∀ x : Space,
      ContDiffAt ℝ ∞ (fun z : ℝ × Space => physicalField W s₀ z.1 z.2) (τ, x) :=
    fun τ hτ x => hU.contDiffAt (prod_mem_nhds (Icc_mem_nhds hτ.1 hτ.2) univ_mem)
  have hPat : ∀ τ ∈ Ioo a b, ∀ x : Space,
      ContDiffAt ℝ ∞ (fun z : ℝ × Space =>
        (1 - z.1)⁻¹ * q (s₀ - Real.log (1 - z.1)) ((Real.sqrt (1 - z.1))⁻¹ • z.2)) (τ, x) :=
    fun τ hτ x => hP.contDiffAt (prod_mem_nhds (Icc_mem_nhds hτ.1 hτ.2) univ_mem)
  obtain ⟨r, hr⟩ : ∃ r, Real.exp (-(s - s₀) / 2) = r := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ Real.exp_pos _
  have hlogr : Real.log (r ^ 2) = -(s - s₀) := hr ▸ log_scale_sq s₀ s
  have ht : 1 - r ^ 2 ∈ Ioo a b := window_mem hab hb hr0 hlogr hs
  have hE : ContDiff ℝ ∞ (fun z : ℝ × Space => Real.exp (-(z.1 - s₀) / 2)) := by
    fun_prop
  have hΨ : ContDiff ℝ ∞ (fun z : ℝ × Space =>
      ((1 : ℝ) - Real.exp (-(z.1 - s₀) / 2) ^ 2, Real.exp (-(z.1 - s₀) / 2) • z.2)) :=
    (contDiff_const.sub (hE.pow 2)).prodMk (hE.smul contDiff_snd)
  have hUΨ : ContDiffAt ℝ ∞ (fun z : ℝ × Space => physicalField W s₀ z.1 z.2)
      ((1 : ℝ) - Real.exp (-(s - s₀) / 2) ^ 2, Real.exp (-(s - s₀) / 2) • y) := by
    rw [hr]
    exact hUat _ ht (r • y)
  have hPΨ : ContDiffAt ℝ ∞ (fun z : ℝ × Space =>
        (1 - z.1)⁻¹ * q (s₀ - Real.log (1 - z.1)) ((Real.sqrt (1 - z.1))⁻¹ • z.2))
      ((1 : ℝ) - Real.exp (-(s - s₀) / 2) ^ 2, Real.exp (-(s - s₀) / 2) • y) := by
    rw [hr]
    exact hPat _ ht (r • y)
  have hWfun : (fun z : ℝ × Space => W z.1 z.2) = fun z => Real.exp (-(z.1 - s₀) / 2) •
      ((fun w : ℝ × Space => physicalField W s₀ w.1 w.2) ∘ (fun z : ℝ × Space =>
        ((1 : ℝ) - Real.exp (-(z.1 - s₀) / 2) ^ 2, Real.exp (-(z.1 - s₀) / 2) • z.2))) z :=
    funext fun z => field_of_scale W s₀ z.1 _ (Real.exp_pos _) (log_scale_sq s₀ z.1) z.2
  have hqfun : (fun z : ℝ × Space => q z.1 z.2) = fun z => Real.exp (-(z.1 - s₀) / 2) ^ 2 *
      ((fun w : ℝ × Space => (1 - w.1)⁻¹ * q (s₀ - Real.log (1 - w.1)) ((Real.sqrt (1 - w.1))⁻¹ • w.2)) ∘
        (fun z : ℝ × Space =>
          ((1 : ℝ) - Real.exp (-(z.1 - s₀) / 2) ^ 2, Real.exp (-(z.1 - s₀) / 2) • z.2))) z :=
    funext fun z => pressure_of_scale q s₀ z.1 _ (Real.exp_pos _) (log_scale_sq s₀ z.1) z.2
  have hUt : ContDiff ℝ ∞ (physicalField W s₀ (1 - r ^ 2)) :=
    contDiff_iff_contDiffAt.2 fun x => (hUat _ ht x).comp x (contDiff_prodMk_right (1 - r ^ 2)).contDiffAt
  have hPt : ContDiff ℝ ∞ (fun x : Space => (1 - (1 - r ^ 2))⁻¹ *
      q (s₀ - Real.log (1 - (1 - r ^ 2))) ((Real.sqrt (1 - (1 - r ^ 2)))⁻¹ • x)) :=
    contDiff_iff_contDiffAt.2 fun x => (hPat _ ht x).comp x (contDiff_prodMk_right (1 - r ^ 2)).contDiffAt
  have hWs : W s = dilateField (r ^ 2) (physicalField W s₀ (1 - r ^ 2)) := by
    funext y'
    simp only [dilateField]
    rw [Real.sqrt_sq hr0.le]
    exact field_of_scale W s₀ s r hr0 hlogr y'
  have hqs : q s = fun y' => r ^ 2 * ((1 - (1 - r ^ 2))⁻¹ *
      q (s₀ - Real.log (1 - (1 - r ^ 2))) ((Real.sqrt (1 - (1 - r ^ 2)))⁻¹ • (r • y'))) :=
    funext fun y' => pressure_of_scale q s₀ s r hr0 hlogr y'
  obtain ⟨hfd, hlap, hadv⟩ := dilateCalculus_holds (r ^ 2) _ hUt y
  rw [Real.sqrt_sq hr0.le] at hfd hlap hadv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hWfun]
    exact hE.contDiffAt.smul (hUΨ.comp (s, y) hΨ.contDiffAt)
  · rw [hqfun]
    exact (hE.contDiffAt.pow 2).mul (hPΨ.comp (s, y) hΨ.contDiffAt)
  · have hderiv := window_hasDerivAt W s₀ s r y hr (hUat _ ht (r • y)) _ (hmom _ ht (r • y))
    have hgrad : gradientAt (q s) y = r ^ 3 • gradientAt (fun x : Space => (1 - (1 - r ^ 2))⁻¹ *
        q (s₀ - Real.log (1 - (1 - r ^ 2))) ((Real.sqrt (1 - (1 - r ^ 2)))⁻¹ • x)) (r • y) := by
      have hsc := gradientScale_holds r _ hPt y
      have hdc : DifferentiableAt ℝ (fun y' : Space => (1 - (1 - r ^ 2))⁻¹ *
          q (s₀ - Real.log (1 - (1 - r ^ 2))) ((Real.sqrt (1 - (1 - r ^ 2)))⁻¹ • (r • y'))) y :=
        ((hPt.comp (contDiff_const_smul r)).differentiable (by simp)) y
      rw [hqs]
      unfold gradientAt at hsc ⊢
      rw [fderiv_const_mul hdc]
      have hstep : ∀ (c : ℝ) (F : Space →L[ℝ] ℝ),
          ∑ i : Fin 3, (c • F) (unitVector i) • unitVector i = c • ∑ i : Fin 3, F (unitVector i) • unitVector i := by
        intro c F
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_apply, smul_eq_mul, mul_smul]
      rw [hstep, hsc, smul_smul]
      congr 1
    have hWy : W s y = r • physicalField W s₀ (1 - r ^ 2) (r • y) :=
      field_of_scale W s₀ s r hr0 hlogr y
    unfold SimilarityResidual
    rw [hderiv.deriv, hgrad, hWy, hWs, hfd, hlap, hadv, ContinuousLinearMap.map_smul,
      smul_apply]
    module
  · rw [hWs]
    unfold divergenceAt
    rw [hfd]
    simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have h0 := hdiv _ (Ioo_subset_Icc_self ht) (r • y)
    unfold divergenceAt at h0
    rw [h0, mul_zero]

end Breakdown.FarField

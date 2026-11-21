import Breakdown.Frac.StSpace
import Breakdown.Frac.OpExports

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FracInternal.Localization

theorem remS_add {f g : Space → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x z : Space) :
    scalarSecondOrderRemainder (fun y => f y + g y) x z =
      scalarSecondOrderRemainder f x z + scalarSecondOrderRemainder g x z := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
  have hg1 : DifferentiableAt ℝ g x := hg.differentiable (by norm_num) x
  unfold scalarSecondOrderRemainder
  have h2 : iteratedFDeriv ℝ 2 (fun y => f y + g y) x =
      iteratedFDeriv ℝ 2 f x + iteratedFDeriv ℝ 2 g x :=
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt
  rw [fderiv_fun_add hf1 hg1, h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  ring

theorem remS_const_mul {f : Space → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x z : Space) :
    scalarSecondOrderRemainder (fun y => c * f y) x z = c * scalarSecondOrderRemainder f x z := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
  unfold scalarSecondOrderRemainder
  have h2 : iteratedFDeriv ℝ 2 (fun y => c * f y) x = c • iteratedFDeriv ℝ 2 f x := by
    have := iteratedFDeriv_const_smul_apply' (a := c) hf.contDiffAt (i := 2) (x := x)
    simpa [smul_eq_mul] using this
  rw [fderiv_const_mul hf1, h2]
  simp only [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem remS_const (c : ℝ) (x z : Space) :
    scalarSecondOrderRemainder (fun _ => c) x z = 0 := by
  unfold scalarSecondOrderRemainder
  rw [fderiv_const_apply, iteratedFDeriv_const_of_ne (by norm_num)]
  simp

theorem remS_comp (L : Space →L[ℝ] ℝ) {f : Space → Space} (hf : ContDiff ℝ 2 f) (x z : Space) :
    scalarSecondOrderRemainder (fun y => L (f y)) x z = L (secondOrderRemainder f x z) := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
  unfold scalarSecondOrderRemainder secondOrderRemainder
  have h1 : fderiv ℝ (fun y => L (f y)) x = L.comp (fderiv ℝ f x) :=
    (L.hasFDerivAt.comp x hf1.hasFDerivAt).fderiv
  have h2 : iteratedFDeriv ℝ 2 (fun y => L (f y)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 f x) :=
    L.iteratedFDeriv_comp_left hf.contDiffAt le_rfl
  rw [h1, h2]
  simp [map_sub, map_smul]

theorem remS_comb {f1 f2 f3 f4 : Space → ℝ} (h1 : ContDiff ℝ 2 f1) (h2 : ContDiff ℝ 2 f2)
    (h3 : ContDiff ℝ 2 f3) (h4 : ContDiff ℝ 2 f4) (c2 c3 c4 d : ℝ) (x z : Space) :
    scalarSecondOrderRemainder (fun y => f1 y + c2 * f2 y + c3 * f3 y + c4 * f4 y + d) x z =
      scalarSecondOrderRemainder f1 x z + c2 * scalarSecondOrderRemainder f2 x z
        + c3 * scalarSecondOrderRemainder f3 x z + c4 * scalarSecondOrderRemainder f4 x z := by
  rw [remS_add (by fun_prop) contDiff_const, remS_const, add_zero,
    remS_add (by fun_prop) (by fun_prop), remS_add (by fun_prop) (by fun_prop),
    remS_add (by fun_prop) (by fun_prop), remS_const_mul h2, remS_const_mul h3, remS_const_mul h4]

def pairTerm (φ : Space → ℝ) (w : Space → Space) (x y : Space) : ℝ :=
  φ y * (φ y - φ x) * inner ℝ (w x) (w y) - (1 / 2) * (φ y - φ x) ^ 2 * ‖w x‖ ^ 2

def pairRemainderIntegral (α : ℝ) (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z

theorem two_le_top : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem scalar_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (x : Space) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder g x z) := by
  set e : Space := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  set P : Space →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 3)
  have hG : ContDiff ℝ ∞ (fun y => g y • e) := hg.smul contDiff_const
  have hGc : HasCompactSupport (fun y => g y • e) := HasCompactSupport.smul_right (f := g) hgc
  have iG := remainderIntegrable α hα1 hα2 _ hG (Or.inl (hG.continuous.memLp_of_hasCompactSupport (μ := volume) hGc)) x
  have hPg : (fun y => P (g y • e)) = g := by
    funext y; simp [P, e]
  refine (P.integrable_comp iG).congr (Filter.Eventually.of_forall fun z => ?_)
  have := remS_comp P (hG.of_le two_le_top) x z
  rw [hPg] at this
  simp only [Function.comp_apply, map_smul, smul_eq_mul, this]

theorem vector_scalar_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hfc : MemLp f 2 volume) (v x : Space) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      scalarSecondOrderRemainder (fun y => inner ℝ v (f y)) x z) := by
  have iF := remainderIntegrable α hα1 hα2 f hf (Or.inl hfc) x
  refine ((innerSL ℝ v).integrable_comp iF).congr (Filter.Eventually.of_forall fun z => ?_)
  have := remS_comp (innerSL ℝ v) (hf.of_le two_le_top) x z
  simp only [innerSL_apply_apply] at this
  simp only [Function.comp_apply, map_smul, smul_eq_mul, this, innerSL_apply_apply]

theorem vector_pairing {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hfc : MemLp f 2 volume) (v x : Space) :
    inner ℝ v (fractionalPowerAt α f x) = (fractionalNormalizer α)⁻¹ *
      ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (fun y => inner ℝ v (f y)) x z := by
  have iF := remainderIntegrable α hα1 hα2 f hf (Or.inl hfc) x
  unfold fractionalPowerAt
  rw [inner_smul_right, ← integral_inner iF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have := remS_comp (innerSL ℝ v) (hf.of_le two_le_top) x z
  simp only [innerSL_apply_apply] at this
  simp only [inner_smul_right, this]

theorem pointwise_split {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : Space) :
    inner ℝ (w x) (fractionalPowerAt α (fun y => φ y ^ 2 • w y) x)
      - inner ℝ (φ x • w x) (fractionalPowerAt α (fun y => φ y • w y) x)
      - (1 / 2) * ((scalarPowerAt α (fun y => φ y ^ 2) x - 2 * φ x * scalarPowerAt α φ x) *
          ‖w x‖ ^ 2) =
      (fractionalNormalizer α)⁻¹ * pairRemainderIntegral α φ w x := by
  have hA : ContDiff ℝ ∞ (fun y => φ y ^ 2 • w y) := (hφ.pow 2).smul hw
  have hφ2c : HasCompactSupport (fun y => φ y ^ 2) := hφc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hAc : HasCompactSupport (fun y => φ y ^ 2 • w y) :=
    HasCompactSupport.smul_right (f := fun y => φ y ^ 2) hφ2c
  have hB : ContDiff ℝ ∞ (fun y => φ y • w y) := hφ.smul hw
  have hBc : HasCompactSupport (fun y => φ y • w y) := HasCompactSupport.smul_right (f := φ) hφc
  have mA := hA.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hAc
  have mB := hB.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hBc
  have jA := vector_scalar_integrable hα1 hα2 hA mA (w x) x
  have jB := vector_scalar_integrable hα1 hα2 hB mB (w x) x
  have jC := scalar_integrable hα1 hα2 (hφ.pow 2) hφ2c x
  have jD := scalar_integrable hα1 hα2 hφ hφc x
  rw [vector_pairing hα1 hα2 hA mA, real_inner_smul_left, vector_pairing hα1 hα2 hB mB]
  unfold scalarPowerAt pairRemainderIntegral
  have hpt : pairTerm φ w x = fun y => inner ℝ (w x) (φ y ^ 2 • w y)
      + (-φ x) * inner ℝ (w x) (φ y • w y) + (-(1 / 2) * ‖w x‖ ^ 2) * φ y ^ 2
      + (φ x * ‖w x‖ ^ 2) * φ y + (-(1 / 2) * φ x ^ 2 * ‖w x‖ ^ 2) := by
    funext y
    simp only [pairTerm, inner_smul_right]
    ring
  have hcomb : ∀ z, ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z =
      ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (fun y => inner ℝ (w x) (φ y ^ 2 • w y)) x z
      + (-φ x) * (‖z‖ ^ (-(3 + 2 * α)) *
          scalarSecondOrderRemainder (fun y => inner ℝ (w x) (φ y • w y)) x z)
      + (-(1 / 2) * ‖w x‖ ^ 2) * (‖z‖ ^ (-(3 + 2 * α)) *
          scalarSecondOrderRemainder (fun y => φ y ^ 2) x z)
      + (φ x * ‖w x‖ ^ 2) * (‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder φ x z) := by
    intro z
    rw [hpt, remS_comb ((contDiff_const.inner ℝ hA).of_le two_le_top)
      ((contDiff_const.inner ℝ hB).of_le two_le_top)
      ((hφ.pow 2).of_le two_le_top) (hφ.of_le two_le_top)]
    ring
  have e1 := integral_add ((jA.add (jB.const_mul (-φ x))).add (jC.const_mul (-(1 / 2) * ‖w x‖ ^ 2)))
    (jD.const_mul (φ x * ‖w x‖ ^ 2))
  have e2 := integral_add (jA.add (jB.const_mul (-φ x))) (jC.const_mul (-(1 / 2) * ‖w x‖ ^ 2))
  have e3 := integral_add jA (jB.const_mul (-φ x))
  simp only [Pi.add_apply] at e1 e2 e3
  rw [integral_congr_ae (Filter.Eventually.of_forall hcomb), e1, e2, e3,
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

theorem pair_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : Space) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      scalarSecondOrderRemainder (pairTerm φ w x) x z) := by
  have hA : ContDiff ℝ ∞ (fun y => φ y ^ 2 • w y) := (hφ.pow 2).smul hw
  have hφ2c : HasCompactSupport (fun y => φ y ^ 2) := hφc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hAc : HasCompactSupport (fun y => φ y ^ 2 • w y) :=
    HasCompactSupport.smul_right (f := fun y => φ y ^ 2) hφ2c
  have hB : ContDiff ℝ ∞ (fun y => φ y • w y) := hφ.smul hw
  have hBc : HasCompactSupport (fun y => φ y • w y) := HasCompactSupport.smul_right (f := φ) hφc
  have mA := hA.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hAc
  have mB := hB.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hBc
  have jA := vector_scalar_integrable hα1 hα2 hA mA (w x) x
  have jB := vector_scalar_integrable hα1 hα2 hB mB (w x) x
  have jC := scalar_integrable hα1 hα2 (hφ.pow 2) hφ2c x
  have jD := scalar_integrable hα1 hα2 hφ hφc x
  have hpt : pairTerm φ w x = fun y => inner ℝ (w x) (φ y ^ 2 • w y)
      + (-φ x) * inner ℝ (w x) (φ y • w y) + (-(1 / 2) * ‖w x‖ ^ 2) * φ y ^ 2
      + (φ x * ‖w x‖ ^ 2) * φ y + (-(1 / 2) * φ x ^ 2 * ‖w x‖ ^ 2) := by
    funext y
    simp only [pairTerm, inner_smul_right]
    ring
  refine (((jA.add (jB.const_mul (-φ x))).add (jC.const_mul (-(1 / 2) * ‖w x‖ ^ 2))).add
    (jD.const_mul (φ x * ‖w x‖ ^ 2))).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  rw [hpt, remS_comb ((contDiff_const.inner ℝ hA).of_le two_le_top)
    ((contDiff_const.inner ℝ hB).of_le two_le_top)
    ((hφ.pow 2).of_le two_le_top) (hφ.of_le two_le_top)]
  ring

def pairSquare (α : ℝ) (φ : Space → ℝ) (w : Space → Space) (z : Space × Space) : ℝ :=
  (φ z.1 - φ z.2) ^ 2 * ‖w z.1 - w z.2‖ ^ 2 * ‖z.1 - z.2‖ ^ (-(3 + 2 * α))

def farSet (δ : ℝ) : Set Space := {z | δ < ‖z‖}

def farPairs (δ : ℝ) : Set (Space × Space) := {z | δ < ‖z.1 - z.2‖}

def tailIntegral (α : ℝ) (φ : Space → ℝ) (w : Space → Space) (δ : ℝ) (x : Space) : ℝ :=
  ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z


theorem farSet_measurable (δ : ℝ) : MeasurableSet (farSet δ) :=
  measurableSet_lt measurable_const measurable_norm

theorem farPairs_measurable (δ : ℝ) : MeasurableSet (farPairs δ) :=
  measurableSet_lt measurable_const (measurable_norm.comp (measurable_fst.sub measurable_snd))

theorem farSet_rpow_integrable {s δ : ℝ} (hs : s < -3) (hδ : 0 < δ) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) (farSet δ) := by
  have hint : Integrable (fun z : Space => (δ / (1 + δ)) ^ s * (1 + ‖z‖) ^ (-(-s))) :=
    (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)).const_mul _
  refine hint.integrableOn.mono' (measurable_norm.pow_const s).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem (farSet_measurable δ) fun z hz => ?_)
  have hz : δ < ‖z‖ := hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg,
    ← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith : s ≤ 0)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

def linPart (φ : Space → ℝ) (w : Space → Space) (x z : Space) : ℝ :=
  fderiv ℝ (pairTerm φ w x) x z

def quadPart (φ : Space → ℝ) (w : Space → Space) (x z : Space) : ℝ :=
  (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 (pairTerm φ w x) x ![z, z]

theorem lin_far_integrable {α δ : ℝ} (hα1 : 1 < α) (hδ : 0 < δ) (φ : Space → ℝ)
    (w : Space → Space) (x : Space) :
    IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * linPart φ w x z) (farSet δ) := by
  have hI := (farSet_rpow_integrable (s := -(3 + 2 * α) + 1) (by linarith) hδ).const_mul
    ‖fderiv ℝ (pairTerm φ w x) x‖
  refine hI.mono' ?_ (ae_restrict_of_forall_mem (farSet_measurable δ) fun z hz => ?_)
  · exact ((measurable_norm.pow_const _).mul
      (fderiv ℝ (pairTerm φ w x) x).continuous.measurable).aestronglyMeasurable
  · have hz : δ < ‖z‖ := hz
    have hz0 : ‖z‖ ≠ 0 := by linarith
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.rpow_add_one hz0, linPart]
    have := (fderiv ℝ (pairTerm φ w x) x).le_opNorm z
    have h0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
    calc ‖z‖ ^ (-(3 + 2 * α)) * ‖(fderiv ℝ (pairTerm φ w x) x) z‖
        ≤ ‖z‖ ^ (-(3 + 2 * α)) * (‖fderiv ℝ (pairTerm φ w x) x‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring

theorem quad_far_integrable {α δ : ℝ} (hα1 : 1 < α) (hδ : 0 < δ) (φ : Space → ℝ)
    (w : Space → Space) (x : Space) :
    IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * quadPart φ w x z) (farSet δ) := by
  have hI := (farSet_rpow_integrable (s := -(3 + 2 * α) + 1 + 1) (by linarith) hδ).const_mul
    ((1 / 2) * ‖iteratedFDeriv ℝ 2 (pairTerm φ w x) x‖)
  refine hI.mono' ?_ (ae_restrict_of_forall_mem (farSet_measurable δ) fun z hz => ?_)
  · have hc : Continuous fun z : Space => iteratedFDeriv ℝ 2 (pairTerm φ w x) x ![z, z] :=
      (iteratedFDeriv ℝ 2 (pairTerm φ w x) x).cont.comp
        (continuous_pi fun i => by fin_cases i <;> simp <;> exact continuous_id)
    exact ((measurable_norm.pow_const _).mul
      (continuous_const.mul hc).measurable).aestronglyMeasurable
  · have hz : δ < ‖z‖ := hz
    have hz0 : ‖z‖ ≠ 0 := by linarith
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.rpow_add_one hz0, Real.rpow_add_one hz0, quadPart]
    have := (iteratedFDeriv ℝ 2 (pairTerm φ w x) x).le_opNorm ![z, z]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    have h0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc ‖z‖ ^ (-(3 + 2 * α)) * (1 / 2 * ‖(iteratedFDeriv ℝ 2 (pairTerm φ w x) x) ![z, z]‖)
        ≤ ‖z‖ ^ (-(3 + 2 * α)) * (1 / 2 * (‖iteratedFDeriv ℝ 2 (pairTerm φ w x) x‖ * (‖z‖ * ‖z‖))) := by
          gcongr
      _ = _ := by ring

theorem lin_vanish {α δ : ℝ} (hα1 : 1 < α) (hδ : 0 < δ) (φ : Space → ℝ)
    (w : Space → Space) (x : Space) :
    ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * linPart φ w x z = 0 := by
  rw [← integral_indicator (farSet_measurable δ)]
  set g := (farSet δ).indicator (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * linPart φ w x z)
  have hodd : ∀ z, g (-z) = -g z := by
    intro z
    simp only [g, Set.indicator, farSet, Set.mem_setOf_eq, norm_neg, linPart, map_neg]
    split_ifs <;> ring
  have h := integral_neg_eq_self g volume
  simp only [hodd, integral_neg] at h
  linarith

theorem pairTerm_self (φ : Space → ℝ) (w : Space → Space) (x : Space) : pairTerm φ w x x = 0 := by
  simp [pairTerm]

theorem pairTerm_symm (φ : Space → ℝ) (w : Space → Space) (x y : Space) :
    pairTerm φ w x y + pairTerm φ w y x = -(1 / 2) * ((φ x - φ y) ^ 2 * ‖w x - w y‖ ^ 2) := by
  simp only [pairTerm]
  rw [norm_sub_sq_real, real_inner_comm (w y) (w x)]
  ring

theorem pairTerm_bound {φ : Space → ℝ} {C : ℝ} (hC : ∀ y, |φ y| ≤ C) (w : Space → Space) (x y : Space) :
    |pairTerm φ w x y| ≤ 3 * C ^ 2 * (‖w x‖ ^ 2 + ‖w y‖ ^ 2) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  have hba : |φ y - φ x| ≤ 2 * C := (abs_sub _ _).trans (by linarith [hC x, hC y])
  have hi : |inner ℝ (w x) (w y)| ≤ ‖w x‖ * ‖w y‖ := abs_real_inner_le_norm _ _
  have hsq : (φ y - φ x) ^ 2 ≤ (2 * C) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hba 2
  have h1 : |φ y * (φ y - φ x) * inner ℝ (w x) (w y)| ≤ C * (2 * C) * (‖w x‖ * ‖w y‖) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC y) hba (abs_nonneg _) hC0) hi (abs_nonneg _) (by positivity)
  have h2 : |(1 / 2) * (φ y - φ x) ^ 2 * ‖w x‖ ^ 2| ≤ (1 / 2) * (2 * C) ^ 2 * ‖w x‖ ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    gcongr
  have h3 : ‖w x‖ * ‖w y‖ ≤ (‖w x‖ ^ 2 + ‖w y‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖w x‖ - ‖w y‖)]
  unfold pairTerm
  calc |φ y * (φ y - φ x) * inner ℝ (w x) (w y) - 1 / 2 * (φ y - φ x) ^ 2 * ‖w x‖ ^ 2|
      ≤ |φ y * (φ y - φ x) * inner ℝ (w x) (w y)| + |(1 / 2) * (φ y - φ x) ^ 2 * ‖w x‖ ^ 2| :=
        abs_sub _ _
    _ ≤ C * (2 * C) * ((‖w x‖ ^ 2 + ‖w y‖ ^ 2) / 2) + (1 / 2) * (2 * C) ^ 2 * ‖w x‖ ^ 2 := by
        gcongr
        exact h1.trans (by gcongr)
    _ ≤ 3 * C ^ 2 * (‖w x‖ ^ 2 + ‖w y‖ ^ 2) := by nlinarith [sq_nonneg (‖w y‖), sq_nonneg C]

theorem far_pair_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun p : Space × Space => ‖p.1 - p.2‖ ^ (-(3 + 2 * α)) * pairTerm φ w p.1 p.2)
      (farPairs δ) (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hC' : ∀ y, |φ y| ≤ C := fun y => by simpa [Real.norm_eq_abs] using hC y
  set k : Space → ℝ := (farSet δ).indicator (fun z => ‖z‖ ^ (-(3 + 2 * α)))
  have hkm : Measurable k := (measurable_norm.pow_const _).indicator (farSet_measurable δ)
  have hk : Integrable k :=
    (farSet_rpow_integrable (s := -(3 + 2 * α)) (by linarith) hδ).integrable_indicator
      (farSet_measurable δ)
  have hk0 : ∀ z, 0 ≤ k z := fun z =>
    Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z
  have hw2i : Integrable (fun x => ‖w x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hw2.1).1 hw2
  have hwm : Measurable w := hw.continuous.measurable
  have g1 : Integrable (fun p : Space × Space => ‖w p.1‖ ^ 2 * k (p.1 - p.2)) (volume.prod volume) := by
    have hm : AEStronglyMeasurable (fun p : Space × Space => ‖w p.1‖ ^ 2 * k (p.1 - p.2))
        (volume.prod volume) := by
      have := hkm.comp (measurable_fst.sub measurable_snd)
      exact (((hwm.comp measurable_fst).norm.pow_const 2).mul this).aestronglyMeasurable
    refine (integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · simp only
      exact (hk.comp_sub_left x).const_mul _
    · refine (hw2i.mul_const (∫ z, k z)).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      have : ∀ y, ‖‖w x‖ ^ 2 * k (x - y)‖ = ‖w x‖ ^ 2 * k (x - y) := fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hk0 _))]
      simp_rw [this]
      rw [integral_const_mul, integral_sub_left_eq_self k volume x]
  have g2 : Integrable (fun p : Space × Space => ‖w p.2‖ ^ 2 * k (p.1 - p.2)) (volume.prod volume) := by
    have hm : AEStronglyMeasurable (fun p : Space × Space => ‖w p.2‖ ^ 2 * k (p.1 - p.2))
        (volume.prod volume) := by
      have := hkm.comp (measurable_fst.sub measurable_snd)
      exact (((hwm.comp measurable_snd).norm.pow_const 2).mul this).aestronglyMeasurable
    refine (integrable_prod_iff' hm).2 ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · simp only
      exact (hk.comp_sub_right y).const_mul _
    · refine (hw2i.mul_const (∫ z, k z)).congr (Filter.Eventually.of_forall fun y => ?_)
      simp only
      have : ∀ x, ‖‖w y‖ ^ 2 * k (x - y)‖ = ‖w y‖ ^ 2 * k (x - y) := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hk0 _))]
      simp_rw [this]
      rw [integral_const_mul, integral_sub_right_eq_self k y]
  have hind : (farPairs δ).indicator
      (fun p : Space × Space => ‖p.1 - p.2‖ ^ (-(3 + 2 * α)) * pairTerm φ w p.1 p.2) =
      fun p => k (p.1 - p.2) * pairTerm φ w p.1 p.2 := by
    funext p
    simp only [k, Set.indicator, farPairs, farSet, Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [← integrable_indicator_iff (farPairs_measurable δ), hind]
  have hGm : Measurable (fun p : Space × Space => pairTerm φ w p.1 p.2) := by
    unfold pairTerm
    have hφm := hφ.continuous.measurable
    fun_prop
  refine ((g1.add g2).const_mul (3 * C ^ 2)).mono'
    ((hkm.comp (measurable_fst.sub measurable_snd)).mul hGm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 _)]
  calc k (p.1 - p.2) * |pairTerm φ w p.1 p.2|
      ≤ k (p.1 - p.2) * (3 * C ^ 2 * (‖w p.1‖ ^ 2 + ‖w p.2‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (pairTerm_bound hC' w p.1 p.2) (hk0 _)
    _ = _ := by ring

def quadExplicit (φ : Space → ℝ) (w : Space → Space) (x z : Space) : ℝ :=
  (1 / 2 : ℝ) * (fderiv ℝ φ x z ^ 2 * ‖w x‖ ^ 2 + φ x * fderiv ℝ (fderiv ℝ φ) x z z * ‖w x‖ ^ 2
    + φ x * fderiv ℝ φ x z * fderiv ℝ (fun y => ‖w y‖ ^ 2) x z)

theorem quad_formula {w : Space → Space} (hw : ContDiff ℝ ∞ w) {φ : Space → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x z : Space) : quadPart φ w x z = quadExplicit φ w x z := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le two_le_top
  have hw2 : ContDiff ℝ 2 w := hw.of_le two_le_top
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (by norm_num)
  have hWD : ContDiff ℝ 1 (fderiv ℝ w) := hw2.fderiv_right (by norm_num)
  have dφ : ∀ y, DifferentiableAt ℝ φ y := fun y => hφ.differentiable (by simp) y
  have dw : ∀ y, DifferentiableAt ℝ w y := fun y => hw.differentiable (by simp) y
  have dD : DifferentiableAt ℝ (fderiv ℝ φ) x := hD.differentiable (by norm_num) x
  have dψ : DifferentiableAt ℝ (fun y => fderiv ℝ φ y z) x :=
    dD.clm_apply (differentiableAt_const z)
  have dJ : DifferentiableAt ℝ (fun y => inner ℝ (w x) (fderiv ℝ w y z)) x :=
    ((innerSL ℝ (w x)).differentiableAt).comp x
      ((hWD.differentiable (by norm_num) x).clm_apply (differentiableAt_const z))
  have hψx : fderiv ℝ (fun y => fderiv ℝ φ y z) x z = fderiv ℝ (fderiv ℝ φ) x z z := by
    rw [fderiv_clm_apply dD (differentiableAt_const z)]
    simp
  have hN : fderiv ℝ (fun y => ‖w y‖ ^ 2) x z = 2 * inner ℝ (w x) (fderiv ℝ w x z) := by
    rw [((dw x).hasFDerivAt.norm_sq).fderiv]
    simp
  have hI : ∀ y, HasFDerivAt (fun y => inner ℝ (w x) (w y))
      ((innerSL ℝ (w x)).comp (fderiv ℝ w y)) y := fun y =>
    (innerSL ℝ (w x)).hasFDerivAt.comp y (dw y).hasFDerivAt
  have hgC : ContDiff ℝ 2 (pairTerm φ w x) := by
    unfold pairTerm
    have h1 : ContDiff ℝ 2 (fun y => inner ℝ (w x) (w y)) := contDiff_const.inner ℝ hw2
    fun_prop
  have step1 : ∀ y, fderiv ℝ (pairTerm φ w x) y z =
      (fderiv ℝ φ y z * (φ y - φ x) + φ y * fderiv ℝ φ y z) * inner ℝ (w x) (w y)
        + φ y * (φ y - φ x) * inner ℝ (w x) (fderiv ℝ w y z)
        - (1 / 2) * (2 * (φ y - φ x) * fderiv ℝ φ y z) * ‖w x‖ ^ 2 := by
    intro y
    have key : HasFDerivAt (pairTerm φ w x) _ y :=
      (((dφ y).hasFDerivAt.mul ((dφ y).hasFDerivAt.sub_const (φ x))).mul (hI y)).sub
        ((((dφ y).hasFDerivAt.sub_const (φ x)).pow 2).const_mul (1 / 2) |>.mul_const (‖w x‖ ^ 2))
    rw [key.fderiv]
    simp
    ring
  have step2 : fderiv ℝ (fun y => fderiv ℝ (pairTerm φ w x) y z) x z =
      fderiv ℝ (fun y => (fderiv ℝ φ y z * (φ y - φ x) + φ y * fderiv ℝ φ y z) * inner ℝ (w x) (w y)
        + φ y * (φ y - φ x) * inner ℝ (w x) (fderiv ℝ w y z)
        - (1 / 2) * (2 * (φ y - φ x) * fderiv ℝ φ y z) * ‖w x‖ ^ 2) x z := by
    rw [funext step1]
  have dx := (dφ x).hasFDerivAt
  have key2 : HasFDerivAt (fun y => (fderiv ℝ φ y z * (φ y - φ x) + φ y * fderiv ℝ φ y z) *
        inner ℝ (w x) (w y) + φ y * (φ y - φ x) * inner ℝ (w x) (fderiv ℝ w y z)
        - (1 / 2) * (2 * (φ y - φ x) * fderiv ℝ φ y z) * ‖w x‖ ^ 2) _ x :=
    ((((dψ.hasFDerivAt.mul (dx.sub_const (φ x))).add (dx.mul dψ.hasFDerivAt)).mul (hI x)).add
      ((dx.mul (dx.sub_const (φ x))).mul dJ.hasFDerivAt)).sub
      ((((dx.sub_const (φ x)).const_mul 2).mul dψ.hasFDerivAt).const_mul (1 / 2) |>.mul_const (‖w x‖ ^ 2))
  have hDg : DifferentiableAt ℝ (fderiv ℝ (pairTerm φ w x)) x :=
    (hgC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have step0 : quadPart φ w x z = (1 / 2) * fderiv ℝ (fun y => fderiv ℝ (pairTerm φ w x) y z) x z := by
    unfold quadPart
    rw [iteratedFDeriv_two_apply, fderiv_clm_apply hDg (differentiableAt_const z)]
    simp
  rw [step0, step2, key2.fderiv]
  unfold quadExplicit
  simp only [sub_self, real_inner_self_eq_norm_sq] at *
  simp [hψx, hN]
  ring

def quadField (φ : Space → ℝ) (w : Space → Space) (z x : Space) : ℝ :=
  φ x * fderiv ℝ φ x z * ‖w x‖ ^ 2

theorem quadField_deriv {w : Space → Space} (hw : ContDiff ℝ ∞ w) {φ : Space → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x z : Space) :
    quadExplicit φ w x z = (1 / 2) * fderiv ℝ (quadField φ w z) x z := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le two_le_top
  have d1 : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (by norm_num)
  have d2 : DifferentiableAt ℝ (fderiv ℝ φ) x := hD.differentiable (by norm_num) x
  have d2' : DifferentiableAt ℝ (fun y => fderiv ℝ φ y z) x :=
    d2.clm_apply (differentiableAt_const z)
  have d3 : DifferentiableAt ℝ (fun y => ‖w y‖ ^ 2) x :=
    ((hw.norm_sq ℝ).differentiable (by simp)) x
  have h2 : fderiv ℝ (fun y => fderiv ℝ φ y z) x z = fderiv ℝ (fderiv ℝ φ) x z z := by
    rw [fderiv_clm_apply d2 (differentiableAt_const z)]
    simp
  unfold quadExplicit quadField
  have d12 : DifferentiableAt ℝ (fun y => φ y * fderiv ℝ φ y z) x := d1.mul d2'
  rw [fderiv_fun_mul d12 d3, fderiv_fun_mul d1 d2']
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, h2]
  ring

theorem quad_vanish {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * quadPart φ w x z) ∧
    ∫ x, ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * quadPart φ w x z = 0 := by
  simp_rw [quad_formula hw hφ]
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le two_le_top
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (by norm_num)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ φ)) := hD.continuous_fderiv (by norm_num)
  have hN : ContDiff ℝ 1 (fun y => ‖w y‖ ^ 2) := (hw.norm_sq ℝ).of_le (by simp)
  have hND : Continuous (fderiv ℝ (fun y => ‖w y‖ ^ 2)) := hN.continuous_fderiv (by norm_num)
  set c : Space → ℝ := fun x => (1 / 2) * (‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖ ^ 2
    + ‖φ x‖ * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ ^ 2
    + ‖φ x‖ * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ (fun y => ‖w y‖ ^ 2) x‖)
  have hcc : Continuous c := by
    have := hφ.continuous; have := hD.continuous; have := hw.continuous
    fun_prop
  have hDc : HasCompactSupport (fderiv ℝ φ) := hφc.fderiv (𝕜 := ℝ)
  have hcs : HasCompactSupport c := by
    have t1 : HasCompactSupport (fun x => ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖ ^ 2) :=
      (hDc.comp_left (g := fun L => ‖L‖ ^ 2) (by simp)).mul_right
    have t2 : HasCompactSupport (fun x => ‖φ x‖ * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ ^ 2) :=
      ((hφc.comp_left (g := fun t => ‖t‖) (by simp)).mul_right).mul_right
    have t3 : HasCompactSupport (fun x => ‖φ x‖ * ‖fderiv ℝ φ x‖ *
        ‖fderiv ℝ (fun y => ‖w y‖ ^ 2) x‖) :=
      ((hφc.comp_left (g := fun t => ‖t‖) (by simp)).mul_right).mul_right
    exact ((t1.add t2).add t3).mul_left
  have hci : Integrable c := hcc.integrable_of_hasCompactSupport hcs
  set k : Space → ℝ := (farSet δ).indicator (fun z => ‖z‖ ^ (-(3 + 2 * α) + 1 + 1))
  have hk : Integrable k :=
    (farSet_rpow_integrable (s := -(3 + 2 * α) + 1 + 1) (by linarith) hδ).integrable_indicator
      (farSet_measurable δ)
  have hEc : Continuous (fun p : Space × Space => quadExplicit φ w p.1 p.2) := by
    unfold quadExplicit
    have := hφ.continuous; have := hD.continuous; have := hw.continuous
    fun_prop
  have hEb : ∀ x z, |quadExplicit φ w x z| ≤ c x * ‖z‖ ^ 2 := by
    intro x z
    have e1 := (fderiv ℝ φ x).le_opNorm z
    have e2 : ‖fderiv ℝ (fderiv ℝ φ) x z z‖ ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖z‖ * ‖z‖ :=
      ((fderiv ℝ (fderiv ℝ φ) x z).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ φ) x).le_opNorm z) (norm_nonneg _))
    have e3 := (fderiv ℝ (fun y => ‖w y‖ ^ 2) x).le_opNorm z
    simp only [Real.norm_eq_abs] at e1 e2 e3
    unfold quadExplicit
    simp only [c, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 : |fderiv ℝ φ x z ^ 2 * ‖w x‖ ^ 2| ≤ ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖ ^ 2 * ‖z‖ ^ 2 := by
      rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)]
      calc |fderiv ℝ φ x z| ^ 2 * ‖w x‖ ^ 2 ≤ (‖fderiv ℝ φ x‖ * ‖z‖) ^ 2 * ‖w x‖ ^ 2 := by
            gcongr
        _ = _ := by ring
    have h2 : |φ x * fderiv ℝ (fderiv ℝ φ) x z z * ‖w x‖ ^ 2| ≤
        |φ x| * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ ^ 2 * ‖z‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)]
      calc |φ x| * |fderiv ℝ (fderiv ℝ φ) x z z| * ‖w x‖ ^ 2
          ≤ |φ x| * (‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖z‖ * ‖z‖) * ‖w x‖ ^ 2 := by gcongr
        _ = _ := by ring
    have h3 : |φ x * fderiv ℝ φ x z * fderiv ℝ (fun y => ‖w y‖ ^ 2) x z| ≤
        |φ x| * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ (fun y => ‖w y‖ ^ 2) x‖ * ‖z‖ ^ 2 := by
      rw [abs_mul, abs_mul]
      calc |φ x| * |fderiv ℝ φ x z| * |fderiv ℝ (fun y => ‖w y‖ ^ 2) x z|
          ≤ |φ x| * (‖fderiv ℝ φ x‖ * ‖z‖) * (‖fderiv ℝ (fun y => ‖w y‖ ^ 2) x‖ * ‖z‖) := by
            gcongr
        _ = _ := by ring
    have h4 := abs_add_three (fderiv ℝ φ x z ^ 2 * ‖w x‖ ^ 2)
      (φ x * fderiv ℝ (fderiv ℝ φ) x z z * ‖w x‖ ^ 2)
      (φ x * fderiv ℝ φ x z * fderiv ℝ (fun y => ‖w y‖ ^ 2) x z)
    nlinarith
  set k' : Space → ℝ := (farSet δ).indicator (fun z => ‖z‖ ^ (-(3 + 2 * α)))
  have hk'm : Measurable k' := (measurable_norm.pow_const _).indicator (farSet_measurable δ)
  set F : Space × Space → ℝ := fun p => k' p.2 * quadExplicit φ w p.1 p.2
  have hFi : Integrable F (volume.prod volume) := by
    refine (hci.mul_prod hk).mono' ((hk'm.comp measurable_snd).mul hEc.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [F, k', k, Set.indicator]
    split_ifs with hp
    · have hp' : δ < ‖p.2‖ := hp
      have hz0 : ‖p.2‖ ≠ 0 := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        Real.rpow_add_one hz0, Real.rpow_add_one hz0]
      calc ‖p.2‖ ^ (-(3 + 2 * α)) * |quadExplicit φ w p.1 p.2|
          ≤ ‖p.2‖ ^ (-(3 + 2 * α)) * (c p.1 * ‖p.2‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hEb _ _) (Real.rpow_nonneg (norm_nonneg _) _)
        _ = _ := by ring
    · simp
  have hrow : ∀ x, ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * quadExplicit φ w x z = ∫ z, F (x, z) := by
    intro x
    rw [← integral_indicator (farSet_measurable δ)]
    congr 1
    funext z
    simp only [F, k', Set.indicator]
    split_ifs <;> simp
  simp_rw [hrow]
  refine ⟨hFi.integral_prod_left, ?_⟩
  rw [integral_integral_swap hFi]
  have hcol : ∀ z, ∫ x, F (x, z) = 0 := by
    intro z
    simp only [F]
    rw [integral_const_mul]
    have hψ : ContDiff ℝ 1 (fun y => fderiv ℝ φ y z) := hD.clm_apply contDiff_const
    have hg : ContDiff ℝ 1 (quadField φ w z) :=
      ((hφ.of_le (by simp)).mul hψ).mul hN
    have hgc : HasCompactSupport (quadField φ w z) := by
      change HasCompactSupport ((φ * fun y => fderiv ℝ φ y z) * fun y => ‖w y‖ ^ 2)
      exact hφc.mul_right.mul_right
    have hgd : Continuous (fun x => fderiv ℝ (quadField φ w z) x z) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hgdc : HasCompactSupport (fun x => fderiv ℝ (quadField φ w z) x z) :=
      (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L z) (by simp)
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ : Space => (1 : ℝ)) (g := quadField φ w z) (v := z)
      (by simp) (by simpa using hgd.integrable_of_hasCompactSupport hgdc)
      (by simpa using hg.continuous.integrable_of_hasCompactSupport hgc)
      (fun x _ => differentiableAt_const _) (fun x _ => hg.differentiable (by norm_num) x)
    simp only [one_mul, fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, zero_mul,
      integral_zero, neg_zero] at hibp
    simp_rw [quadField_deriv hw hφ, integral_const_mul, hibp]
    simp
  simp [hcol]

theorem rem_uniform {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x z, ‖secondOrderRemainder f x z‖ ≤ M * ‖z‖ ^ 3 ∧
      ‖secondOrderRemainder f x z‖ ≤ M * (1 + ‖z‖ + ‖z‖ ^ 2) := by
  obtain ⟨B0, hB0⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨B1, hB1⟩ := (hf.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hfc.fderiv (𝕜 := ℝ))
  obtain ⟨B2, hB2⟩ := (hf.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 2)
  obtain ⟨B3, hB3⟩ := (hf.continuous_iteratedFDeriv (m := 3) (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 3)
  have h0 : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  have h1 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have h2 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have h3 : 0 ≤ B3 := (norm_nonneg _).trans (hB3 0)
  refine ⟨2 * B0 + B1 + B2 + B3, by positivity, fun x z => ⟨?_, ?_⟩⟩
  · have := remainderBound f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) x z B3 (fun y _ => hB3 y)
    refine this.trans ?_
    gcongr
    linarith
  · unfold secondOrderRemainder
    have e1 := (fderiv ℝ f x).le_opNorm z
    have e2 := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at e2
    have e3 : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ B2 * ‖z‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      nlinarith [hB2 x, norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z]), norm_nonneg z,
        mul_le_mul_of_nonneg_right (hB2 x) (mul_nonneg (norm_nonneg z) (norm_nonneg z))]
    have e4 : ‖fderiv ℝ f x z‖ ≤ B1 * ‖z‖ :=
      e1.trans (mul_le_mul_of_nonneg_right (hB1 x) (norm_nonneg _))
    calc ‖f (x + z) - f x - fderiv ℝ f x z - (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖
        ≤ ‖f (x + z)‖ + ‖f x‖ + ‖fderiv ℝ f x z‖ + ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ B0 + B0 + B1 * ‖z‖ + B2 * ‖z‖ ^ 2 := by
          gcongr
          · exact hB0 _
          · exact hB0 _
      _ ≤ (2 * B0 + B1 + B2 + B3) * (1 + ‖z‖ + ‖z‖ ^ 2) := by
          have := norm_nonneg z
          nlinarith [sq_nonneg ‖z‖, mul_nonneg h0 this, mul_nonneg h1 this, mul_nonneg h2 this,
            mul_nonneg h3 this, mul_nonneg h0 (sq_nonneg ‖z‖), mul_nonneg h1 (sq_nonneg ‖z‖),
            mul_nonneg h3 (sq_nonneg ‖z‖)]

def kernelProfile (α : ℝ) (z : Space) : ℝ :=
  (Metric.ball (0 : Space) 1).indicator (fun z => ‖z‖ ^ (-(3 + 2 * α) + 3)) z
    + 3 * (Metric.ball (0 : Space) 1)ᶜ.indicator (fun z => ‖z‖ ^ (-(3 + 2 * α) + 2)) z

theorem kernelProfile_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) :
    Integrable (kernelProfile α) := by
  have i1 := (integrableOn_ball_norm_rpow (s := -(3 + 2 * α) + 3) (by linarith)).integrable_indicator
    Metric.isOpen_ball.measurableSet
  have i2 := (integrableOn_compl_ball_norm_rpow (s := -(3 + 2 * α) + 2) (by linarith)).integrable_indicator
    Metric.isOpen_ball.measurableSet.compl
  exact i1.add (i2.const_mul 3)

theorem kernel_le_profile {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {M r : ℝ} (hM : 0 ≤ M) (z : Space)
    (h3 : r ≤ M * ‖z‖ ^ 3) (h2 : r ≤ M * (1 + ‖z‖ + ‖z‖ ^ 2)) :
    ‖z‖ ^ (-(3 + 2 * α)) * r ≤ M * kernelProfile α z := by
  have hK := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
  by_cases hz : z = 0
  · subst hz
    simp only [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0), zero_mul, kernelProfile]
    rw [Set.indicator_of_mem (Metric.mem_ball_self one_pos), Set.indicator_of_notMem (by simp)]
    simp only [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) + 3 ≠ 0)]
    simp
  have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  unfold kernelProfile
  by_cases hb : z ∈ Metric.ball (0 : Space) 1
  · rw [Set.indicator_of_mem hb, Set.indicator_of_notMem (by simpa using hb), mul_zero, add_zero,
      show -(3 + 2 * α) + 3 = -(3 + 2 * α) + 1 + 1 + 1 by ring, Real.rpow_add_one hz0,
      Real.rpow_add_one hz0, Real.rpow_add_one hz0]
    calc ‖z‖ ^ (-(3 + 2 * α)) * r ≤ ‖z‖ ^ (-(3 + 2 * α)) * (M * ‖z‖ ^ 3) :=
          mul_le_mul_of_nonneg_left h3 hK
      _ = _ := by ring
  · have hz1 : 1 ≤ ‖z‖ := by simpa using hb
    rw [Set.indicator_of_notMem hb, Set.indicator_of_mem (by exact hb), zero_add,
      show -(3 + 2 * α) + 2 = -(3 + 2 * α) + 1 + 1 by ring, Real.rpow_add_one hz0,
      Real.rpow_add_one hz0]
    have : 1 + ‖z‖ + ‖z‖ ^ 2 ≤ 3 * (‖z‖ * ‖z‖) := by nlinarith
    calc ‖z‖ ^ (-(3 + 2 * α)) * r ≤ ‖z‖ ^ (-(3 + 2 * α)) * (M * (1 + ‖z‖ + ‖z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hK
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * (M * (3 * (‖z‖ * ‖z‖))) := by gcongr
      _ = _ := by ring

theorem remainder_dominated {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∃ D : Space → ℝ, Integrable D ∧ ∀ x, ∫ z : Space, |‖z‖ ^ (-(3 + 2 * α)) *
      scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤ D x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hC' : ∀ y, |φ y| ≤ C := fun y => by simpa [Real.norm_eq_abs] using hC y
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC' 0)
  set e : Space := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hA : ContDiff ℝ ∞ (fun y => φ y ^ 2 • w y) := (hφ.pow 2).smul hw
  have hφ2c : HasCompactSupport (fun y => φ y ^ 2) := hφc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hAc : HasCompactSupport (fun y => φ y ^ 2 • w y) :=
    HasCompactSupport.smul_right (f := fun y => φ y ^ 2) hφ2c
  have hB : ContDiff ℝ ∞ (fun y => φ y • w y) := hφ.smul hw
  have hBc : HasCompactSupport (fun y => φ y • w y) := HasCompactSupport.smul_right (f := φ) hφc
  have hCf : ContDiff ℝ ∞ (fun y => φ y ^ 2 • e) := (hφ.pow 2).smul contDiff_const
  have hCc : HasCompactSupport (fun y => φ y ^ 2 • e) := HasCompactSupport.smul_right (f := fun y => φ y ^ 2) hφ2c
  have hDf : ContDiff ℝ ∞ (fun y => φ y • e) := hφ.smul contDiff_const
  have hDc : HasCompactSupport (fun y => φ y • e) := HasCompactSupport.smul_right (f := φ) hφc
  obtain ⟨MA, hMA0, hMA⟩ := rem_uniform hA hAc
  obtain ⟨MB, hMB0, hMB⟩ := rem_uniform hB hBc
  obtain ⟨MC, hMC0, hMC⟩ := rem_uniform hCf hCc
  obtain ⟨MD, hMD0, hMD⟩ := rem_uniform hDf hDc
  set c1 : Space → ℝ := fun x => ‖w x‖ * (MA + C * MB) + ‖w x‖ ^ 2 * ((1 / 2) * MC + C * MD)
  have hc1 : Continuous c1 := by
    have := hw.continuous
    fun_prop
  have hc10 : ∀ x, 0 ≤ c1 x := fun x => by positivity
  have hdec : ∀ x z, scalarSecondOrderRemainder (pairTerm φ w x) x z =
      inner ℝ (w x) (secondOrderRemainder (fun y => φ y ^ 2 • w y) x z)
      + (-φ x) * inner ℝ (w x) (secondOrderRemainder (fun y => φ y • w y) x z)
      + (-(1 / 2) * ‖w x‖ ^ 2) * inner ℝ e (secondOrderRemainder (fun y => φ y ^ 2 • e) x z)
      + (φ x * ‖w x‖ ^ 2) * inner ℝ e (secondOrderRemainder (fun y => φ y • e) x z) := by
    intro x z
    have hpt : pairTerm φ w x = fun y => inner ℝ (w x) (φ y ^ 2 • w y)
        + (-φ x) * inner ℝ (w x) (φ y • w y) + (-(1 / 2) * ‖w x‖ ^ 2) * φ y ^ 2
        + (φ x * ‖w x‖ ^ 2) * φ y + (-(1 / 2) * φ x ^ 2 * ‖w x‖ ^ 2) := by
      funext y
      simp only [pairTerm, inner_smul_right]
      ring
    have hCe : (fun y => inner ℝ e (φ y ^ 2 • e)) = fun y => φ y ^ 2 := by
      funext y; rw [inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
    have hDe : (fun y => inner ℝ e (φ y • e)) = φ := by
      funext y; rw [inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
    have r1 := remS_comp (innerSL ℝ (w x)) (hA.of_le two_le_top) x z
    have r2 := remS_comp (innerSL ℝ (w x)) (hB.of_le two_le_top) x z
    have r3 := remS_comp (innerSL ℝ e) (hCf.of_le two_le_top) x z
    have r4 := remS_comp (innerSL ℝ e) (hDf.of_le two_le_top) x z
    simp only [innerSL_apply_apply] at r1 r2 r3 r4
    rw [hCe] at r3
    rw [hDe] at r4
    rw [hpt, remS_comb ((contDiff_const.inner ℝ hA).of_le two_le_top)
      ((contDiff_const.inner ℝ hB).of_le two_le_top)
      ((hφ.pow 2).of_le two_le_top) (hφ.of_le two_le_top), r1, r2, r3, r4]
  have hpw : ∀ x z, |scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤ c1 x * ‖z‖ ^ 3 ∧
      |scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤ c1 x * (1 + ‖z‖ + ‖z‖ ^ 2) := by
    intro x z
    have key : ∀ t : ℝ, 0 ≤ t →
        (‖secondOrderRemainder (fun y => φ y ^ 2 • w y) x z‖ ≤ MA * t) →
        (‖secondOrderRemainder (fun y => φ y • w y) x z‖ ≤ MB * t) →
        (‖secondOrderRemainder (fun y => φ y ^ 2 • e) x z‖ ≤ MC * t) →
        (‖secondOrderRemainder (fun y => φ y • e) x z‖ ≤ MD * t) →
        |scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤ c1 x * t := by
      intro t ht a1 a2 a3 a4
      rw [hdec]
      have i1 := abs_real_inner_le_norm (w x) (secondOrderRemainder (fun y => φ y ^ 2 • w y) x z)
      have i2 := abs_real_inner_le_norm (w x) (secondOrderRemainder (fun y => φ y • w y) x z)
      have i3 := abs_real_inner_le_norm e (secondOrderRemainder (fun y => φ y ^ 2 • e) x z)
      have i4 := abs_real_inner_le_norm e (secondOrderRemainder (fun y => φ y • e) x z)
      rw [he, one_mul] at i3 i4
      have hw0 := norm_nonneg (w x)
      have hφx := hC' x
      set u1 := inner ℝ (w x) (secondOrderRemainder (fun y => φ y ^ 2 • w y) x z)
      set u2 := inner ℝ (w x) (secondOrderRemainder (fun y => φ y • w y) x z)
      set u3 := inner ℝ e (secondOrderRemainder (fun y => φ y ^ 2 • e) x z)
      set u4 := inner ℝ e (secondOrderRemainder (fun y => φ y • e) x z)
      have b1 : |u1| ≤ ‖w x‖ * (MA * t) := i1.trans (mul_le_mul_of_nonneg_left a1 hw0)
      have b2 : |(-φ x) * u2| ≤ C * (‖w x‖ * (MB * t)) := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hφx (i2.trans (mul_le_mul_of_nonneg_left a2 hw0)) (abs_nonneg _) hC0
      have b3 : |(-(1 / 2) * ‖w x‖ ^ 2) * u3| ≤ (1 / 2) * ‖w x‖ ^ 2 * (MC * t) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)]
        exact mul_le_mul_of_nonneg_left (i3.trans a3) (by positivity)
      have b4 : |(φ x * ‖w x‖ ^ 2) * u4| ≤ C * ‖w x‖ ^ 2 * (MD * t) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hφx (by positivity)) (i4.trans a4)
          (abs_nonneg _) (by positivity)
      have := (abs_add_le (u1 + (-φ x) * u2 + (-(1 / 2) * ‖w x‖ ^ 2) * u3) ((φ x * ‖w x‖ ^ 2) * u4)).trans
        (add_le_add_left (abs_add_three u1 ((-φ x) * u2) ((-(1 / 2) * ‖w x‖ ^ 2) * u3)) _)
      simp only [c1]
      nlinarith
    exact ⟨key _ (by positivity) (hMA x z).1 (hMB x z).1 (hMC x z).1 (hMD x z).1,
      key _ (by positivity) (hMA x z).2 (hMB x z).2 (hMC x z).2 (hMD x z).2⟩
  have hprof := kernelProfile_integrable hα1 hα2
  have hFb : ∀ x z, |‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤
      c1 x * kernelProfile α z := by
    intro x z
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact kernel_le_profile hα1 hα2 (hc10 x) z (hpw x z).1 (hpw x z).2
  have hnear : ∀ x, ∫ z : Space, |‖z‖ ^ (-(3 + 2 * α)) *
      scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤ c1 x * ∫ z, kernelProfile α z := by
    intro x
    rw [← integral_const_mul]
    exact integral_mono (pair_integrable hα1 hα2 hw hφ hφc x).abs (hprof.const_mul _) (hFb x)
  set N := Metric.cthickening 2 (tsupport φ)
  have hNc : IsCompact N := IsCompact.cthickening hφc
  have hNm : MeasurableSet N := Metric.isClosed_cthickening.measurableSet
  set k : Space → ℝ := (farSet 1).indicator (fun z => ‖z‖ ^ (-(3 + 2 * α)))
  have hkm : Measurable k := (measurable_norm.pow_const _).indicator (farSet_measurable 1)
  have hk : Integrable k :=
    (farSet_rpow_integrable (s := -(3 + 2 * α)) (by linarith) one_pos).integrable_indicator
      (farSet_measurable 1)
  have hk0 : ∀ z, 0 ≤ k z := fun z =>
    Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z
  have hk1 : ∀ z, k z ≤ 1 := by
    intro z
    simp only [k, Set.indicator]
    split_ifs with hz
    · exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hz) (by linarith)
    · norm_num
  have hw2i : Integrable (fun x => ‖w x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hw2.1).1 hw2
  have hkw : ∀ x, Integrable (fun z => k z * ‖w (x + z)‖ ^ 2) := by
    intro x
    refine (hw2i.comp_add_left x).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (hkm.mul ((hw.continuous.comp (continuous_const.add continuous_id)).norm.pow 2).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 z) (by positivity))]
      exact mul_le_of_le_one_left (by positivity) (hk1 z)
  set G : Space → ℝ := fun x => ∫ z, k z * ‖w (x + z)‖ ^ 2
  have hGi : Integrable G := by
    have hm : AEStronglyMeasurable (fun p : Space × Space => k p.2 * ‖w (p.1 + p.2)‖ ^ 2)
        (volume.prod volume) :=
      ((hkm.comp measurable_snd).mul
        ((hw.continuous.comp (continuous_fst.add continuous_snd)).norm.pow 2).measurable).aestronglyMeasurable
    have hΦ : Integrable (fun p : Space × Space => k p.2 * ‖w (p.1 + p.2)‖ ^ 2) (volume.prod volume) := by
      refine (integrable_prod_iff' hm).2 ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
      · simp only
        exact (hw2i.comp_add_right z).const_mul _
      · refine (hk.mul_const (∫ x, ‖w x‖ ^ 2)).congr (Filter.Eventually.of_forall fun z => ?_)
        simp only
        have : ∀ x, ‖k z * ‖w (x + z)‖ ^ 2‖ = k z * ‖w (x + z)‖ ^ 2 := fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 z) (by positivity))]
        simp_rw [this]
        rw [integral_const_mul, integral_add_right_eq_self (fun x => ‖w x‖ ^ 2) z]
    exact hΦ.integral_prod_left
  have hfar : ∀ x, x ∉ N → ∫ z : Space, |‖z‖ ^ (-(3 + 2 * α)) *
      scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤
      3 * C ^ 2 * (‖w x‖ ^ 2 * (∫ z, k z) + G x) := by
    intro x hx
    have hz2 : ∀ y, dist y x ≤ 2 → φ y = 0 := by
      intro y hy
      by_contra hne
      exact hx (Metric.mem_cthickening_of_dist_le x y 2 _ (subset_tsupport _ hne) (by rwa [dist_comm]))
    have hφx : φ x = 0 := hz2 x (by simp)
    have hev : pairTerm φ w x =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
      have : φ y = 0 := hz2 y (by linarith [Metric.mem_ball.mp hy])
      simp [pairTerm, this, hφx]
    have hd1 : fderiv ℝ (pairTerm φ w x) x = 0 := by rw [hev.fderiv_eq]; simp
    have hd2 : iteratedFDeriv ℝ 2 (pairTerm φ w x) x = 0 := by
      rw [(hev.iteratedFDeriv ℝ 2).eq_of_nhds]; simp
    have hR : ∀ z, |‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z| ≤
        3 * C ^ 2 * (k z * ‖w x‖ ^ 2 + k z * ‖w (x + z)‖ ^ 2) := by
      intro z
      have hr : scalarSecondOrderRemainder (pairTerm φ w x) x z = pairTerm φ w x (x + z) := by
        simp [scalarSecondOrderRemainder, hd1, hd2, pairTerm_self]
      rw [hr]
      by_cases hz : z ∈ farSet 1
      · rw [show k z = ‖z‖ ^ (-(3 + 2 * α)) from Set.indicator_of_mem hz _, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        calc ‖z‖ ^ (-(3 + 2 * α)) * |pairTerm φ w x (x + z)|
            ≤ ‖z‖ ^ (-(3 + 2 * α)) * (3 * C ^ 2 * (‖w x‖ ^ 2 + ‖w (x + z)‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left (pairTerm_bound hC' w x (x + z)) (Real.rpow_nonneg (norm_nonneg _) _)
          _ = _ := by ring
      · have hz' : ‖z‖ ≤ 1 := by simpa [farSet] using hz
        have : φ (x + z) = 0 := hz2 _ (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
        rw [show k z = 0 from Set.indicator_of_notMem hz _]
        simp [pairTerm, this, hφx]
    refine (integral_mono (pair_integrable hα1 hα2 hw hφ hφc x).abs
      (((hk.mul_const _).add (hkw x)).const_mul _) hR).trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add (hk.mul_const _) (hkw x), integral_mul_const]
    simp only [G]
    ring
  refine ⟨fun x => N.indicator (fun x => c1 x * ∫ z, kernelProfile α z) x +
    3 * C ^ 2 * (‖w x‖ ^ 2 * (∫ z, k z) + G x), ?_, fun x => ?_⟩
  · have i1 : Integrable (fun x => N.indicator (fun x => c1 x * ∫ z, kernelProfile α z) x) :=
      (((hc1.mul continuous_const).continuousOn).integrableOn_compact hNc).integrable_indicator hNm
    have i2 : Integrable (fun x => 3 * C ^ 2 * (‖w x‖ ^ 2 * (∫ z, k z) + G x)) :=
      ((hw2i.mul_const _).add hGi).const_mul _
    exact i1.add i2
  · dsimp only
    have hG0 : 0 ≤ G x := integral_nonneg fun z => mul_nonneg (hk0 z) (by positivity)
    have hk0' : 0 ≤ ∫ z, k z := integral_nonneg hk0
    by_cases hx : x ∈ N
    · rw [Set.indicator_of_mem hx]
      have := hnear x
      have : 0 ≤ 3 * C ^ 2 * (‖w x‖ ^ 2 * (∫ z, k z) + G x) :=
        mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by positivity) hk0') hG0)
      linarith
    · rw [Set.indicator_of_notMem hx, zero_add]
      exact hfar x hx

theorem truncated_identity {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (tailIntegral α φ w δ) ∧ IntegrableOn (pairSquare α φ w) (farPairs δ) (volume.prod volume) ∧
    ∫ x, tailIntegral α φ w δ x = -(1 / 4) * ∫ z in farPairs δ, pairSquare α φ w z ∂(volume.prod volume) := by
  set Fp : Space × Space → ℝ := fun p => ‖p.1 - p.2‖ ^ (-(3 + 2 * α)) * pairTerm φ w p.1 p.2
  set H := (farPairs δ).indicator Fp
  have hH : Integrable H (volume.prod volume) :=
    (far_pair_integrable hα1 hα2 hw hw2 hφ hφc hδ).integrable_indicator (farPairs_measurable δ)
  have hΦ : MeasurePreserving (MeasurableEquiv.shearAddRight Space) (volume.prod volume)
      (volume.prod volume) := measurePreserving_prod_add volume volume
  have hHΦ : (fun q : Space × Space => H (MeasurableEquiv.shearAddRight Space q)) = fun q =>
      (farSet δ).indicator (fun z => ‖z‖ ^ (-(3 + 2 * α)) * pairTerm φ w q.1 (q.1 + z)) q.2 := by
    funext q
    change H (q.1, q.1 + q.2) = _
    simp only [H, Fp, Set.indicator, farPairs, farSet,
      Set.mem_setOf_eq, sub_add_cancel_left, norm_neg]
  have hHΦi : Integrable (fun q : Space × Space => H (MeasurableEquiv.shearAddRight Space q))
      (volume.prod volume) := (hΦ.integrable_comp hH.aestronglyMeasurable).2 hH
  rw [hHΦ] at hHΦi
  set A : Space → ℝ := fun x => ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * pairTerm φ w x (x + z)
  have hAeq : ∀ x, ∫ z, (farSet δ).indicator
      (fun z => ‖z‖ ^ (-(3 + 2 * α)) * pairTerm φ w x (x + z)) z = A x :=
    fun x => integral_indicator (farSet_measurable δ)
  have hA : Integrable A := by
    have := hHΦi.integral_prod_left
    simp only [hAeq] at this
    exact this
  have hAint : ∫ x, A x = ∫ p, H p ∂(volume.prod volume) := by
    rw [← hΦ.integral_comp' H, hHΦ, integral_prod _ hHΦi]
    simp only [hAeq]
  obtain ⟨hQ, hQ0⟩ := quad_vanish hα1 hα2 hw hw2 hφ hφc hδ
  have htail : ∀ x, tailIntegral α φ w δ x = A x -
      ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * quadPart φ w x z := by
    intro x
    have i1 := (pair_integrable hα1 hα2 hw hφ hφc x).integrableOn (s := farSet δ)
    have i2 := lin_far_integrable hα1 hδ φ w x
    have i3 := quad_far_integrable hα1 hδ φ w x
    have hpt : ∀ z, ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z =
        ‖z‖ ^ (-(3 + 2 * α)) * pairTerm φ w x (x + z) - ‖z‖ ^ (-(3 + 2 * α)) * linPart φ w x z
          - ‖z‖ ^ (-(3 + 2 * α)) * quadPart φ w x z := by
      intro z
      simp only [scalarSecondOrderRemainder, pairTerm_self, linPart, quadPart]
      ring
    have i0 : IntegrableOn (fun z => ‖z‖ ^ (-(3 + 2 * α)) * pairTerm φ w x (x + z)) (farSet δ) := by
      refine ((i1.add i2).add i3).congr_fun (fun z _ => ?_) (farSet_measurable δ)
      simp only [Pi.add_apply, hpt]
      ring
    unfold tailIntegral
    simp only [hpt]
    have e1 := integral_sub (i0.sub i2) i3
    have e2 := integral_sub i0 i2
    simp only [Pi.sub_apply] at e1 e2
    rw [e1, e2, lin_vanish hα1 hδ φ w x, sub_zero]
  have htailf : tailIntegral α φ w δ = fun x => A x -
      ∫ z in farSet δ, ‖z‖ ^ (-(3 + 2 * α)) * quadPart φ w x z := funext htail
  have hsw : ∀ p : Space × Space, H p + H p.swap =
      -(1 / 2) * (farPairs δ).indicator (pairSquare α φ w) p := by
    intro p
    simp only [H, Fp, Set.indicator, farPairs, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap,
      norm_sub_rev p.2 p.1, pairSquare]
    split_ifs
    · rw [← mul_add, pairTerm_symm]
      ring
    · ring
  have hSqOn : IntegrableOn (pairSquare α φ w) (farPairs δ) (volume.prod volume) := by
    have h := (hH.add hH.swap).const_mul (-2)
    rw [← integrable_indicator_iff (farPairs_measurable δ)]
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, Function.comp_apply]
    rw [hsw p]
    ring
  refine ⟨?_, hSqOn, ?_⟩
  · rw [htailf]; exact hA.sub hQ
  · rw [htailf, integral_sub hA hQ, hQ0, sub_zero, hAint]
    have h2 : ∫ p, H p ∂(volume.prod volume) + ∫ p, H p.swap ∂(volume.prod volume) =
        -(1 / 2) * ∫ p in farPairs δ, pairSquare α φ w p ∂(volume.prod volume) := by
      have e := integral_add hH hH.swap
      simp only [Pi.add_apply, Function.comp_apply] at e
      rw [← e]
      simp_rw [hsw]
      rw [integral_const_mul, integral_indicator (farPairs_measurable δ)]
    have h3 : ∫ p, H p.swap ∂(volume.prod volume) = ∫ p, H p ∂(volume.prod volume) :=
      integral_prod_swap H
    rw [h3] at h2
    linarith

theorem eventually_far {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / (n + 1) < r := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  refine Filter.eventually_atTop.2 ⟨n, fun m hm => lt_of_le_of_lt ?_ hn⟩
  exact Nat.one_div_le_one_div hm

theorem tail_tendsto {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : Space) :
    Filter.Tendsto (fun n : ℕ => tailIntegral α φ w (1 / (n + 1)) x) Filter.atTop
      (nhds (pairRemainderIntegral α φ w x)) := by
  have hI := pair_integrable hα1 hα2 hw hφ hφc x
  unfold tailIntegral pairRemainderIntegral
  simp_rw [← integral_indicator (farSet_measurable _)]
  refine tendsto_integral_of_dominated_convergence (fun z => ‖‖z‖ ^ (-(3 + 2 * α)) *
      scalarSecondOrderRemainder (pairTerm φ w x) x z‖)
    (fun n => (hI.indicator (farSet_measurable _)).aestronglyMeasurable) hI.norm
    (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
  · rw [Set.indicator]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  · by_cases hz : z = 0
    · subst hz
      have h0 : ‖(0 : Space)‖ ^ (-(3 + 2 * α)) = 0 := by
        rw [norm_zero, Real.zero_rpow (by linarith)]
      have hn : ∀ n : ℕ, (farSet (1 / ((n : ℝ) + 1))).indicator (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
          scalarSecondOrderRemainder (pairTerm φ w x) x z) 0 = 0 := by
        intro n
        rw [Set.indicator_of_notMem]
        simp only [farSet, Set.mem_setOf_eq, norm_zero, not_lt]
        positivity
      simp only [hn, h0, zero_mul]
      exact tendsto_const_nhds
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_far (norm_pos_iff.mpr hz)] with n hn
      rw [Set.indicator_of_mem (by exact hn)]

theorem global_split {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    Integrable (pairRemainderIntegral α φ w) ∧ Integrable (pairSquare α φ w) (volume.prod volume) ∧
    ∫ x, pairRemainderIntegral α φ w x =
      -(1 / 4) * ∫ z, pairSquare α φ w z ∂(volume.prod volume) := by
  obtain ⟨D, hdom, hD⟩ := remainder_dominated hα1 hα2 hw hw2 hφ hφc
  have htr := fun n : ℕ => truncated_identity hα1 hα2 hw hw2 hφ hφc (δ := 1 / (n + 1)) (by positivity)
  have hbound : ∀ n : ℕ, ∀ x, ‖tailIntegral α φ w (1 / (n + 1)) x‖ ≤
      ∫ z : Space, |‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder (pairTerm φ w x) x z| := by
    intro n x
    unfold tailIntegral
    refine (norm_integral_le_integral_norm _).trans ?_
    exact setIntegral_le_integral (pair_integrable hα1 hα2 hw hφ hφc x).norm
      (Filter.Eventually.of_forall fun z => norm_nonneg _)
  have hbound2 : ∀ n : ℕ, ∀ x, ‖tailIntegral α φ w (1 / (n + 1)) x‖ ≤ D x :=
    fun n x => (hbound n x).trans (hD x)
  have hlimL : Filter.Tendsto (fun n : ℕ => ∫ x, tailIntegral α φ w (1 / (n + 1)) x) Filter.atTop
      (nhds (∫ x, pairRemainderIntegral α φ w x)) :=
    tendsto_integral_of_dominated_convergence _ (fun n => (htr n).1.aestronglyMeasurable) hdom
      (fun n => Filter.Eventually.of_forall (hbound2 n))
      (Filter.Eventually.of_forall fun x => tail_tendsto hα1 hα2 hw hφ hφc x)
  have hmeasP : AEStronglyMeasurable (pairRemainderIntegral α φ w) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun n => (htr n).1.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => tail_tendsto hα1 hα2 hw hφ hφc x)
  have hP : Integrable (pairRemainderIntegral α φ w) := by
    refine hdom.mono' hmeasP (Filter.Eventually.of_forall fun x => ?_)
    exact le_of_tendsto (tail_tendsto hα1 hα2 hw hφ hφc x).norm
      (Filter.Eventually.of_forall fun n => hbound2 n x)
  have hsq : ∀ z, 0 ≤ pairSquare α φ w z := fun z => by
    unfold pairSquare
    have := Real.rpow_nonneg (norm_nonneg (z.1 - z.2)) (-(3 + 2 * α))
    positivity
  have mSq : Measurable (pairSquare α φ w) := by
    unfold pairSquare
    have h1 := hφ.continuous.measurable
    have h2 := hw.continuous.measurable
    fun_prop
  have hind : ∀ z, Filter.Tendsto (fun n : ℕ => (farPairs (1 / ((n : ℝ) + 1))).indicator
      (pairSquare α φ w) z) Filter.atTop (nhds (pairSquare α φ w z)) := by
    intro z
    by_cases hz : z.1 = z.2
    · have h0 : pairSquare α φ w z = 0 := by simp [pairSquare, hz]
      have hn : ∀ n : ℕ, (farPairs (1 / ((n : ℝ) + 1))).indicator (pairSquare α φ w) z = 0 :=
        fun n => Set.indicator_apply_eq_zero.2 (fun _ => h0)
      simp only [hn, h0]
      exact tendsto_const_nhds
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_far (norm_pos_iff.mpr (sub_ne_zero.mpr hz))] with n hn
      rw [Set.indicator_of_mem (by exact hn)]
  have hsetB : ∀ n : ℕ, ∫ z in farPairs (1 / ((n : ℝ) + 1)), pairSquare α φ w z ∂(volume.prod volume) ≤
      4 * ∫ x, D x := by
    intro n
    have h3 := (htr n).2.2
    have h4 : -(∫ x, tailIntegral α φ w (1 / (n + 1)) x) ≤
        ∫ x, D x := by
      refine (neg_le_abs _).trans ?_
      refine (abs_integral_le_integral_abs).trans ?_
      exact integral_mono (htr n).1.abs hdom (fun x => by simpa [Real.norm_eq_abs] using hbound2 n x)
    linarith
  have hmono : ∀ z, Monotone (fun n : ℕ => ENNReal.ofReal ((farPairs (1 / ((n : ℝ) + 1))).indicator
      (pairSquare α φ w) z)) := by
    intro z n m hnm
    refine ENNReal.ofReal_le_ofReal (Set.indicator_le_indicator_of_subset ?_ (fun z => hsq z) z)
    intro y hy
    exact lt_of_le_of_lt (Nat.one_div_le_one_div hnm) (show _ < ‖y.1 - y.2‖ from hy)
  have hlin := lintegral_tendsto_of_tendsto_of_monotone (μ := volume.prod volume)
    (f := fun n : ℕ => fun z => ENNReal.ofReal ((farPairs (1 / ((n : ℝ) + 1))).indicator
      (pairSquare α φ w) z)) (F := fun z => ENNReal.ofReal (pairSquare α φ w z))
    (fun n => ((mSq.indicator (farPairs_measurable _)).ennreal_ofReal).aemeasurable)
    (Filter.Eventually.of_forall hmono)
    (Filter.Eventually.of_forall fun z => ENNReal.tendsto_ofReal (hind z))
  have hlinB : ∀ n : ℕ, ∫⁻ z, ENNReal.ofReal ((farPairs (1 / ((n : ℝ) + 1))).indicator
      (pairSquare α φ w) z) ∂(volume.prod volume) ≤ ENNReal.ofReal
      (4 * ∫ x, D x) := by
    intro n
    have hi := ((htr n).2.1).integrable_indicator (farPairs_measurable _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun z => Set.indicator_nonneg (fun z _ => hsq z) z),
      integral_indicator (farPairs_measurable _)]
    exact ENNReal.ofReal_le_ofReal (hsetB n)
  have hSqI : Integrable (pairSquare α φ w) (volume.prod volume) := by
    refine ⟨mSq.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hsq)]
    exact lt_of_le_of_lt (le_of_tendsto' hlin hlinB) ENNReal.ofReal_lt_top
  have hlimR : Filter.Tendsto (fun n : ℕ => ∫ z in farPairs (1 / ((n : ℝ) + 1)), pairSquare α φ w z
      ∂(volume.prod volume)) Filter.atTop (nhds (∫ z, pairSquare α φ w z ∂(volume.prod volume))) := by
    simp_rw [← integral_indicator (farPairs_measurable _)]
    refine tendsto_integral_of_dominated_convergence (pairSquare α φ w)
      (fun n => (hSqI.indicator (farPairs_measurable _)).aestronglyMeasurable) hSqI
      (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall hind)
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun z _ => hsq z) z)]
    exact Set.indicator_le_self' (fun z _ => hsq z) z
  refine ⟨hP, hSqI, tendsto_nhds_unique hlimL ?_⟩
  have : (fun n : ℕ => ∫ x, tailIntegral α φ w (1 / (n + 1)) x) = fun n : ℕ =>
      -(1 / 4) * ∫ z in farPairs (1 / ((n : ℝ) + 1)), pairSquare α φ w z ∂(volume.prod volume) :=
    funext fun n => (htr n).2.2
  rw [this]
  exact hlimR.const_mul _

end Breakdown.FracInternal.Localization

namespace Breakdown

open FracInternal.Localization in
theorem fracLocalization : FracLocalizationStatement := by
  intro α hα1 hα2 w hw hw2 φ hφ hφc
  obtain ⟨hP, hI, hE⟩ := global_split hα1 hα2 hw hw2 hφ hφc
  refine ⟨hI, ?_⟩
  have hφ2 : ContDiff ℝ ∞ (fun y => φ y ^ 2 • w y) := (hφ.pow 2).smul hw
  have hφ2c : HasCompactSupport (fun y => φ y ^ 2 • w y) :=
    HasCompactSupport.smul_right (f := fun y => φ y ^ 2)
      (hφc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hφ1 : ContDiff ℝ ∞ (fun y => φ y • w y) := hφ.smul hw
  have hφ1c : HasCompactSupport (fun y => φ y • w y) :=
    HasCompactSupport.smul_right (f := φ) hφc
  have hL := (symmetryCompact α hα1 hα2 w (fun y => φ y ^ 2 • w y) hw (Or.inl hw2) hφ2 hφ2c).2.1
  have hR := (symmetryCompact α hα1 hα2 (fun y => φ y • w y) (fun y => φ y • w y) hφ1
    (Or.inl (hφ1.continuous.memLp_of_hasCompactSupport (μ := volume) hφ1c)) hφ1 hφ1c).2.1
  have hS : Integrable (fun x => (scalarPowerAt α (fun y => φ y ^ 2) x - 2 * φ x * scalarPowerAt α φ x) *
      ‖w x‖ ^ 2) := by
    have h := ((hL.sub hR).sub (hP.const_mul (fractionalNormalizer α)⁻¹)).const_mul 2
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    have := pointwise_split hα1 hα2 hw hφ hφc x
    simp only [Pi.sub_apply]
    linarith
  have key : ∀ x, inner ℝ (w x) (fractionalPowerAt α (fun y => φ y ^ 2 • w y) x) =
      inner ℝ (φ x • w x) (fractionalPowerAt α (fun y => φ y • w y) x)
      + (1 / 2) * ((scalarPowerAt α (fun y => φ y ^ 2) x - 2 * φ x * scalarPowerAt α φ x) *
          ‖w x‖ ^ 2) + (fractionalNormalizer α)⁻¹ * pairRemainderIntegral α φ w x := by
    intro x
    have := pointwise_split hα1 hα2 hw hφ hφc x
    linarith
  have e1 := integral_add (hR.add (hS.const_mul (1 / 2))) (hP.const_mul (fractionalNormalizer α)⁻¹)
  have e2 := integral_add hR (hS.const_mul (1 / 2))
  simp only [Pi.add_apply] at e1 e2
  simp_rw [key]
  rw [e1, e2, integral_const_mul, integral_const_mul, hE]
  simp only [pairSquare]
  ring

end Breakdown

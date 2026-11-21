import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxDualPartsRest

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

structure IsTraceRegular (X : Space → Space) : Prop where
  two : MemLp X 2 volume
  diff : ∀ᵐ y ∂volume, DifferentiableAt ℝ X y
  grad : IsWeakGradientOf X (fun y => fderiv ℝ X y)
  gradTwo : ∀ i : Fin 3, MemLp (fun y => fderiv ℝ X y (unitVector i)) 2 volume
  trace : ∃ L : Space → Space, CellCert.Reduction.IsWeakNegTraceOf X L ∧ LocallyIntegrable L volume ∧
    MemLp (fun y => ‖y‖ • L y) 2 volume

structure IsRadialFluxRegular (Y : Space → (Space →L[ℝ] Space)) : Prop where
  meas : AEStronglyMeasurable Y volume
  cols : ∀ i : Fin 3, MemLp (fun y => Y y (unitVector i)) 2 volume
  div : ∃ D : Space → Space, CellCert.Reduction.IsWeakMatrixDivergenceOf Y D ∧ LocallyIntegrable D volume ∧
    MemLp (fun y => ‖y‖ • D y) 2 volume

namespace DualPartsInternal

theorem comp_fderiv {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (c : Fin 3) (y v : Space) :
    fderiv ℝ (fun z => Φ z c) y v = fderiv ℝ Φ y v c := by
  have h := ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt).comp y
    ((hΦ.differentiable (by simp)) y).hasFDerivAt
  rw [show (fun z => Φ z c) = (EuclideanSpace.proj c : Space →L[ℝ] ℝ) ∘ Φ from rfl, h.fderiv]
  rfl

theorem comp_test {Φ : Space → Space} (hΦ : IsTestVectorField Φ) (c : Fin 3) :
    IsTestScalar (fun z => Φ z c) := by
  refine ⟨(EuclideanSpace.proj c : Space →L[ℝ] ℝ).contDiff.comp hΦ.1, ?_⟩
  exact hΦ.2.comp_left (g := fun w : Space => w c) (by simp)

theorem vec_weak {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradientOf v G)
    (hv : LocallyIntegrable v volume) (j : Fin 3) (hG : LocallyIntegrable (fun y => G y (unitVector j)) volume)
    {Φ : Space → Space} (hΦ : IsTestVectorField Φ) :
    ∫ y, inner ℝ (v y) (fderiv ℝ Φ y (unitVector j)) = -∫ y, inner ℝ (G y (unitVector j)) (Φ y) := by
  have hcomp : ∀ c : Fin 3, Integrable (fun y => fderiv ℝ Φ y (unitVector j) c * v y c) ∧
      Integrable (fun y => Φ y c * G y (unitVector j) c) ∧
      ∫ y, fderiv ℝ Φ y (unitVector j) c * v y c = -∫ y, Φ y c * G y (unitVector j) c := by
    intro c
    have hT := comp_test hΦ c
    have h := hw _ hT j
    have hi1 : Integrable (fun y => fderiv ℝ (fun z => Φ z c) y (unitVector j) • v y) :=
      hv.integrable_smul_left_of_hasCompactSupport
        ((hT.1.continuous_fderiv (by simp)).clm_apply continuous_const)
        ((hT.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] ℝ => T (unitVector j)) (by simp))
    have hi2 : Integrable (fun y => (fun z => Φ z c) y • G y (unitVector j)) :=
      hG.integrable_smul_left_of_hasCompactSupport hT.1.continuous hT.2
    have e := congrArg (EuclideanSpace.proj c : Space →L[ℝ] ℝ) h
    rw [map_neg, ← (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hi1,
      ← (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hi2] at e
    refine ⟨?_, ?_, by simpa [comp_fderiv hΦ.1 c] using e⟩
    · simpa [comp_fderiv hΦ.1 c] using ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp hi1)
    · simpa using ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp hi2)
  have l1 : ∀ y, inner ℝ (v y) (fderiv ℝ Φ y (unitVector j)) = ∑ c, fderiv ℝ Φ y (unitVector j) c * v y c := by
    intro y; simp [PiLp.inner_apply]
  have l2 : ∀ y, inner ℝ (G y (unitVector j)) (Φ y) = ∑ c, Φ y c * G y (unitVector j) c := by
    intro y; simp [PiLp.inner_apply]
  simp_rw [l1, l2]
  rw [integral_finsetSum _ (fun c _ => (hcomp c).1), integral_finsetSum _ (fun c _ => (hcomp c).2.1),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun c _ => (hcomp c).2.2)

theorem int_loc {L Φ : Space → Space} (hL : LocallyIntegrable L volume) (hΦ : Continuous Φ)
    (hc : HasCompactSupport Φ) : Integrable (fun y => inner ℝ (L y) (Φ y)) := by
  have hprod : Integrable (fun y => ‖Φ y‖ • ‖L y‖) :=
    (hL.mono hL.aestronglyMeasurable.norm (Filter.Eventually.of_forall (fun y => by simp))).integrable_smul_left_of_hasCompactSupport hΦ.norm hc.norm
  refine hprod.mono' (hL.aestronglyMeasurable.inner hΦ.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun y => by
    have := abs_real_inner_le_norm (L y) (Φ y)
    simp only [Real.norm_eq_abs, smul_eq_mul]
    linarith [mul_comm ‖L y‖ ‖Φ y‖])

theorem dir_test {Φ : Space → Space} (hΦ : IsTestVectorField Φ) (i : Fin 3) :
    IsTestVectorField (fun z => fderiv ℝ Φ z (unitVector i)) := by
  refine ⟨(hΦ.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, ?_⟩
  exact (hΦ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] Space => T (unitVector i)) (by simp)

theorem ssp_eq {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (y : Space) :
    sumSecondPartialsAt Φ y = ∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector i)) y (unitVector i) := by
  unfold sumSecondPartialsAt
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) y :=
    ((hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem trace_of_cols {X : Space → Space} {H : Fin 3 → Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradientOf X (fun y => fderiv ℝ X y)) (hX : LocallyIntegrable X volume)
    (hG : ∀ i, LocallyIntegrable (fun y => fderiv ℝ X y (unitVector i)) volume)
    (hH : ∀ i, IsWeakGradientOf (fun y => fderiv ℝ X y (unitVector i)) (H i))
    (hHi : ∀ i, LocallyIntegrable (fun y => H i y (unitVector i)) volume) :
    CellCert.Reduction.IsWeakNegTraceOf X (fun y => -∑ i, H i y (unitVector i)) := by
  intro Φ hΦ
  have hΨ := fun i => dir_test hΦ i
  have s1 : ∀ i, ∫ y, inner ℝ (X y) (fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector i)) y (unitVector i)) =
      ∫ y, inner ℝ (H i y (unitVector i)) (Φ y) := by
    intro i
    rw [vec_weak hw hX i (hG i) (hΨ i), vec_weak (hH i) (hG i) i (hHi i) hΦ, neg_neg]
  have i1 : ∀ i, Integrable (fun y => inner ℝ (X y) (fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector i)) y (unitVector i))) :=
    fun i => int_loc hX (((hΨ i).1.continuous_fderiv (by simp)).clm_apply continuous_const)
      (((hΨ i).2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] Space => T (unitVector i)) (by simp))
  have i2 : ∀ i, Integrable (fun y => inner ℝ (H i y (unitVector i)) (Φ y)) :=
    fun i => int_loc (hHi i) hΦ.1.continuous hΦ.2
  have l1 : ∀ y, inner ℝ (X y) (-sumSecondPartialsAt Φ y) =
      -∑ i, inner ℝ (X y) (fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector i)) y (unitVector i)) := by
    intro y; rw [ssp_eq hΦ.1, inner_neg_right, inner_sum]
  have l2 : ∀ y, inner ℝ (-∑ i, H i y (unitVector i)) (Φ y) = -∑ i, inner ℝ (H i y (unitVector i)) (Φ y) := by
    intro y; rw [inner_neg_left, sum_inner]
  simp_rw [l1, l2]
  rw [integral_neg, integral_neg, integral_finsetSum _ (fun i _ => i1 i), integral_finsetSum _ (fun i _ => i2 i)]
  exact congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => s1 i))

theorem weak_of_boundedSlope {X : Space → Space} {C : NNReal} (hX : LipschitzWith C X) :
    IsWeakGradientOf X (fun y => fderiv ℝ X y) := by
  intro φ hφ j
  obtain ⟨D, hD⟩ := hφ.1.lipschitzWith_of_hasCompactSupport hφ.2 (by simp)
  have hd : ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ X y := hX.ae_differentiableAt
  have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => (hφ.1.differentiable (by simp)) y
  have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ X y (unitVector j)) volume :=
    ((measurable_fderiv ℝ X).apply_continuousLinearMap (unitVector j)).aestronglyMeasurable
  have hbd : ∀ y, ‖fderiv ℝ X y (unitVector j)‖ ≤ C := fun y => by
    calc ‖fderiv ℝ X y (unitVector j)‖ ≤ ‖fderiv ℝ X y‖ * ‖unitVector j‖ := (fderiv ℝ X y).le_opNorm _
      _ ≤ C * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hX
        · simp [unitVector]
      _ = C := mul_one _
  have hi1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • X y) :=
    (((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).smul hX.continuous).integrable_of_hasCompactSupport
      (((hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] ℝ => T (unitVector j)) (by simp)).smul_right)
  have hi2 : Integrable (fun y => φ y • fderiv ℝ X y (unitVector j)) := by
    have hb : Integrable (fun y => (C : ℝ) * ‖φ y‖) :=
      (hφ.1.continuous.norm.integrable_of_hasCompactSupport hφ.2.norm).const_mul _
    refine hb.mono' (hφ.1.continuous.aestronglyMeasurable.smul hmeas) (Filter.Eventually.of_forall (fun y => ?_))
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _)
  ext c
  rw [show (∫ y, fderiv ℝ φ y (unitVector j) • X y) c = (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (∫ y, fderiv ℝ φ y (unitVector j) • X y) from rfl,
    show (-∫ y, φ y • fderiv ℝ X y (unitVector j)) c = (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (-∫ y, φ y • fderiv ℝ X y (unitVector j)) from rfl,
    map_neg, ← (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hi1,
    ← (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hi2]
  have hXc : LipschitzWith C (fun y => X y c) := by
    have h1 := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).lipschitz.comp hX
    have h2 : ‖(EuclideanSpace.proj c : Space →L[ℝ] ℝ)‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
        simpa using PiLp.norm_apply_le v c)
    exact (h1.weaken (by simpa using mul_le_mul_of_nonneg_right h2 (zero_le (a := C))))
  have key := hXc.integral_lineDeriv_mul_eq (μ := (volume : Measure Space)) hD hφ.2 (unitVector j)
  have e1 : ∀ᵐ y ∂(volume : Measure Space), lineDeriv ℝ (fun z => X z c) y (unitVector j) * φ y =
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (φ y • fderiv ℝ X y (unitVector j)) := by
    filter_upwards [hd] with y hy
    have hc : DifferentiableAt ℝ (fun z => X z c) y :=
      ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).differentiableAt).comp y hy
    rw [hc.lineDeriv_eq_fderiv]
    have := ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt.comp y hy.hasFDerivAt).fderiv
    rw [show (fun z => X z c) = (EuclideanSpace.proj c : Space →L[ℝ] ℝ) ∘ X from rfl, this]
    simp [mul_comm]
  have e2 : ∀ y, lineDeriv ℝ φ y (-unitVector j) * X y c =
      -(EuclideanSpace.proj c : Space →L[ℝ] ℝ) (fderiv ℝ φ y (unitVector j) • X y) := by
    intro y
    rw [(hφd y).lineDeriv_eq_fderiv]
    simp
  rw [integral_congr_ae e1, funext e2, integral_neg] at key
  linarith


theorem traceRegular_of_parts {X : Space → Space} {C : NNReal} (hX : LipschitzWith C X) (h2 : MemLp X 2 volume)
    (hg2 : ∀ k : Fin 3, MemLp (fun y => fderiv ℝ X y (unitVector k)) 2 volume)
    (hH : ∃ H : Fin 3 → Space → (Space →L[ℝ] Space),
      (∀ k, IsWeakGradientOf (fun y => fderiv ℝ X y (unitVector k)) (H k)) ∧
      (∀ k, LocallyIntegrable (fun y => H k y (unitVector k)) volume) ∧
      MemLp (fun y => ‖y‖ • ∑ k, H k y (unitVector k)) 2 volume) :
    IsTraceRegular X := by
  obtain ⟨H, hw, hl, hm⟩ := hH
  have hgw := weak_of_boundedSlope hX
  refine ⟨h2, hX.ae_differentiableAt, hgw, hg2, ⟨fun y => -∑ k, H k y (unitVector k), ?_, ?_, ?_⟩⟩
  · exact trace_of_cols hgw (h2.locallyIntegrable (by norm_num))
      (fun k => (hg2 k).locallyIntegrable (by norm_num)) hw hl
  · exact (locallyIntegrable_finsetSum _ (fun k _ => hl k)).neg
  · have e : (fun y : Space => ‖y‖ • -∑ k, H k y (unitVector k)) =
        -(fun y : Space => ‖y‖ • ∑ k, H k y (unitVector k)) := by
      funext y; simp [smul_neg]
    rw [e]
    exact hm.neg

theorem ofComponents_apply (v : Fin 3 → ℝ) (k : Fin 3) : ofComponents v k = v k := by
  fin_cases k <;> simp [ofComponents]

theorem radial_le (y : Space) (k : Fin 3) :
    ‖(innerSL ℝ (ofComponents (radialVec y))) (unitVector k)‖ ≤ 1 := by
  have e : (innerSL ℝ (ofComponents (radialVec y))) (unitVector k) = radialVec y k := by
    simp [innerSL_apply_apply, unitVector, EuclideanSpace.inner_single_right, ofComponents_apply]
  rw [e, radialVec, Real.norm_eq_abs, abs_div, abs_norm]
  rcases (norm_nonneg y).eq_or_lt with h | h
  · simp [← h]
  · rw [div_le_one h]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y k

theorem radial_eq (y : Space) : ofComponents (radialVec y) = ‖y‖⁻¹ • y := by
  ext k
  rw [ofComponents_apply, radialVec, PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem fluxRegular_of_parts {X : Space → Space} {D : Space → Space} (h2 : MemLp X 2 volume)
    (hD : CellCert.Reduction.IsWeakMatrixDivergenceOf
      (fun y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (X y)) D)
    (hDl : LocallyIntegrable D volume) (hDm : MemLp (fun y => ‖y‖ • D y) 2 volume) :
    IsRadialFluxRegular (fun y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (X y)) := by
  have hv : AEStronglyMeasurable (fun y : Space => ofComponents (radialVec y)) volume := by
    have e : (fun y : Space => ofComponents (radialVec y)) = fun y => ‖y‖⁻¹ • y := funext radial_eq
    rw [e]
    exact (measurable_norm.inv.smul measurable_id).aestronglyMeasurable
  let B : Space →L[ℝ] Space →L[ℝ] (Space →L[ℝ] Space) :=
    (ContinuousLinearMap.smulRightL ℝ Space Space).comp (innerSL ℝ)
  have hB : ∀ a b : Space, B a b = (innerSL ℝ a).smulRight b := fun a b => rfl
  have hmeas : AEStronglyMeasurable (fun y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (X y)) volume := by
    have h := B.continuous₂.comp_aestronglyMeasurable (hv.prodMk h2.aestronglyMeasurable)
    simpa only [Function.comp_def, Function.uncurry_apply_pair, hB] using h
  refine ⟨hmeas, fun k => ?_, ⟨D, hD, hDl, hDm⟩⟩
  refine h2.of_le (hmeas.apply_continuousLinearMap (unitVector k)) (Filter.Eventually.of_forall (fun y => ?_))
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (radial_le y k)

theorem poly_bound (p : MvPolynomial (Fin 2) ℂ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t u : ℝ, |t| ≤ 1 → |u| ≤ 1 →
    ‖MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p‖ ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, norm_nonneg _, fun t u _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨B1, h1, hB1⟩ := hp
    obtain ⟨B2, h2, hB2⟩ := hq
    refine ⟨B1 + B2, by positivity, fun t u ht hu => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hB1 t u ht hu) (hB2 t u ht hu))
  | mul_X p n hp =>
    obtain ⟨B, h0, hB⟩ := hp
    refine ⟨B, h0, fun t u ht hu => ?_⟩
    rw [map_mul, norm_mul, MvPolynomial.eval_X]
    have hn : ‖(![(t : ℂ), (u : ℂ)] : Fin 2 → ℂ) n‖ ≤ 1 := by
      fin_cases n <;> simpa [Complex.norm_real, Real.norm_eq_abs]
    calc ‖MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p‖ * ‖(![(t : ℂ), (u : ℂ)] : Fin 2 → ℂ) n‖ ≤ B * 1 :=
          mul_le_mul (hB t u ht hu) hn (norm_nonneg _) h0
      _ = B := mul_one B

theorem poly_endRemainder (p : MvPolynomial (Fin 2) ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t u : ℝ, 0 ≤ t → t ≤ 1 → |u| ≤ 1 →
    ‖MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p - MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] p -
      ((t : ℂ) - 1) * MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 p)‖ ≤ C * (1 - t) ^ 2 := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, le_rfl, fun t u _ _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨B1, h1, hB1⟩ := hp
    obtain ⟨B2, h2, hB2⟩ := hq
    refine ⟨B1 + B2, by positivity, fun t u ht0 ht hu => ?_⟩
    have e : MvPolynomial.eval ![(t : ℂ), (u : ℂ)] (p + q) - MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (p + q) -
        ((t : ℂ) - 1) * MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 (p + q)) =
        (MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p - MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] p -
          ((t : ℂ) - 1) * MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 p)) +
        (MvPolynomial.eval ![(t : ℂ), (u : ℂ)] q - MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] q -
          ((t : ℂ) - 1) * MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 q)) := by
      simp only [map_add]; ring
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hB1 t u ht0 ht hu) (hB2 t u ht0 ht hu))
  | mul_X p n hp =>
    obtain ⟨C, h0, hC⟩ := hp
    obtain ⟨B, hB0, hB⟩ := poly_bound (MvPolynomial.pderiv 0 p)
    have h1u : ∀ u : ℝ, |u| ≤ 1 → ‖MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 p)‖ ≤ B := by
      intro u hu
      have := hB 1 u (by norm_num) hu
      simpa using this
    refine ⟨C + B, by positivity, fun t u ht0 ht hu => ?_⟩
    set a := MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p
    set b := MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] p
    set d := MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 p)
    have hR := hC t u ht0 ht hu
    have hd := h1u u hu
    have hsq : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
    fin_cases n
    · have e : MvPolynomial.eval ![(t : ℂ), (u : ℂ)] (p * MvPolynomial.X 0) -
          MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (p * MvPolynomial.X 0) -
          ((t : ℂ) - 1) * MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 (p * MvPolynomial.X 0)) =
          (t : ℂ) * (a - b - ((t : ℂ) - 1) * d) + ((t : ℂ) - 1) ^ 2 * d := by
        simp only [Derivation.leibniz, MvPolynomial.pderiv_X_self, map_add, map_mul, smul_eq_mul,
          MvPolynomial.eval_X, map_one, a, b, d]
        simp
        ring
      simp only [Fin.zero_eta] at *
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have h2 : ‖(t : ℂ) - 1‖ = 1 - t := by
        rw [show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (by linarith)]
        ring
      rw [h2]
      nlinarith [norm_nonneg (a - b - ((t : ℂ) - 1) * d), mul_le_mul_of_nonneg_left hd hsq]
    · have e : MvPolynomial.eval ![(t : ℂ), (u : ℂ)] (p * MvPolynomial.X 1) -
          MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (p * MvPolynomial.X 1) -
          ((t : ℂ) - 1) * MvPolynomial.eval ![(1 : ℂ), (u : ℂ)] (MvPolynomial.pderiv 0 (p * MvPolynomial.X 1)) =
          (u : ℂ) * (a - b - ((t : ℂ) - 1) * d) := by
        simp only [Derivation.leibniz, map_add, map_mul, smul_eq_mul, MvPolynomial.eval_X, a, b, d]
        simp [MvPolynomial.pderiv_X]
        ring
      simp only [Fin.mk_one] at *
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := mul_le_mul hu hR (norm_nonneg _) zero_le_one
      nlinarith [mul_le_mul_of_nonneg_left hd hsq]

theorem eval_atFirst (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (atFirst c p) = MvPolynomial.eval ![c, v 1] p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [atFirst]
  | add p q hp hq => simp only [atFirst, map_add] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [atFirst, map_mul] at *
    rw [hp]
    fin_cases n <;> simp

theorem interior_lt_one {l : List ℝ} (hs : l.Pairwise (· < ·)) (hl : l.getLast? = some 1) :
    ∀ e ∈ (l.drop 1).dropLast, e < 1 := by
  intro e he
  rw [List.dropLast_drop_eq_drop_dropLast] at he
  have he' := List.mem_of_mem_drop he
  have happ := List.dropLast_append_getLast? (l := l) 1 (by rw [Option.mem_def]; exact hl)
  rw [← happ, List.pairwise_append] at hs
  exact hs.2.2 e he' 1 (by simp)

theorem two_le_length {l : List ℝ} (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) : 2 ≤ l.length := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [a], h0, h1 =>
    simp at h0 h1
    rw [h0] at h1
    norm_num at h1
  | _ :: _ :: _, _, _ => simp

theorem tail_bound_split (S : Spline) (hmesh : IsTensorMesh S.mesh)
    (htail : ∀ k < cellCount S.mesh.xBreaks, atFirst 1 (S.piece (atomLastT S) k) = 0 ∧
      atFirst 1 (tDeriv 1 (S.piece (atomLastT S) k)) = 0) (odd : Bool) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t x : ℝ, 0 ≤ t → t < 1 → |x| ≤ 1 → ‖S.eval odd t x‖ ≤ K * (1 - t) ^ 2 := by
  set It := (S.mesh.tBreaks.drop 1).dropLast with hIt
  set Ix := (S.mesh.xBreaks.drop 1).dropLast with hIx
  have hlt : ∀ e ∈ It, e < 1 := interior_lt_one hmesh.t_sorted hmesh.t_last
  have hlx := two_le_length hmesh.x_first hmesh.x_last
  set fs : Finset ℝ := insert 0 It.toFinset with hfs
  have hne : fs.Nonempty := Finset.insert_nonempty _ _
  set b := fs.max' hne with hb
  have hb1 : b < 1 := by
    rw [hb, Finset.max'_lt_iff]
    intro e he
    rw [hfs, Finset.mem_insert, List.mem_toFinset] at he
    rcases he with rfl | he
    · norm_num
    · exact hlt e he
  have hbe : ∀ e ∈ It, e ≤ b := fun e he => Finset.le_max' _ _ (by simp [hfs, he])
  set R := Finset.range (It.length + 1) ×ˢ Finset.range (Ix.length + 1) with hR
  choose B hB0 hB using fun ik : ℕ × ℕ => poly_bound (S.piece ik.1 ik.2)
  choose C hC0 hC using fun k : ℕ => poly_endRemainder (S.piece (atomLastT S) k)
  set Bt := ∑ ik ∈ R, B ik with hBt
  set Ct := ∑ k ∈ Finset.range (Ix.length + 1), C k with hCt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg (fun ik _ => hB0 ik)
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg (fun k _ => hC0 k)
  have h1b : 0 < 1 - b := by linarith
  refine ⟨Ct + Bt / (1 - b) ^ 2, by positivity, fun t x ht0 ht1 hx => ?_⟩
  have hnorm : ‖S.eval odd t x‖ = ‖S.evalHalf t |x|‖ := by
    unfold Spline.eval
    split_ifs <;> simp
  rw [hnorm]
  have hu0 : |(|x|)| ≤ 1 := by rwa [abs_abs]
  have hti : cellIndex S.mesh.tBreaks t ≤ It.length := List.length_filter_le _ _
  have hxi : cellIndex S.mesh.xBreaks |x| ≤ Ix.length := List.length_filter_le _ _
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hsq : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  by_cases hall : ∀ e ∈ It, e ≤ t
  · have hidx : cellIndex S.mesh.tBreaks t = atomLastT S := by
      have : cellIndex S.mesh.tBreaks t = It.length := by
        unfold cellIndex
        rw [List.filter_eq_self.2 (fun e he => by simpa using hall e he)]
      rw [this, hIt, atomLastT, cellCount]
      simp [List.length_dropLast]
    have hk : cellIndex S.mesh.xBreaks |x| < cellCount S.mesh.xBreaks := by
      have : Ix.length = S.mesh.xBreaks.length - 2 := by
        rw [hIx]; simp [List.length_dropLast]; omega
      unfold cellCount; omega
    obtain ⟨h1, h2⟩ := htail _ hk
    set k := cellIndex S.mesh.xBreaks |x|
    set p := S.piece (atomLastT S) k
    have e1 : MvPolynomial.eval ![(1 : ℂ), ((|x| : ℝ) : ℂ)] p = 0 := by
      have := congrArg (MvPolynomial.eval ![(1 : ℂ), ((|x| : ℝ) : ℂ)]) h1
      rw [eval_atFirst] at this
      simpa using this
    have e2 : MvPolynomial.eval ![(1 : ℂ), ((|x| : ℝ) : ℂ)] (MvPolynomial.pderiv 0 p) = 0 := by
      have := congrArg (MvPolynomial.eval ![(1 : ℂ), ((|x| : ℝ) : ℂ)]) h2
      rw [eval_atFirst] at this
      simpa [tDeriv] using this
    have hT := hC k t |x| ht0 ht1.le hu0
    rw [e1, e2] at hT
    simp only [sub_zero, mul_zero] at hT
    have hCk : C k ≤ Ct := Finset.single_le_sum (fun k _ => hC0 k) (Finset.mem_range.2 (by omega))
    unfold Spline.evalHalf
    rw [hidx]
    calc ‖MvPolynomial.eval ![(t : ℂ), ((|x| : ℝ) : ℂ)] p‖ ≤ C k * (1 - t) ^ 2 := hT
      _ ≤ (Ct + Bt / (1 - b) ^ 2) * (1 - t) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsq
        have : 0 ≤ Bt / (1 - b) ^ 2 := by positivity
        linarith
  · simp only [not_forall, not_le] at hall
    obtain ⟨e, he, het⟩ := hall
    have htb : t < b := lt_of_lt_of_le het (hbe e he)
    have hmem : (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks |x|) ∈ R := by
      rw [hR, Finset.mem_product, Finset.mem_range, Finset.mem_range]; omega
    have hBk := hB (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks |x|) t |x| ht' hu0
    have hle : B (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks |x|) ≤ Bt :=
      Finset.single_le_sum (fun ik _ => hB0 ik) hmem
    have hq : (1 - b) ^ 2 ≤ (1 - t) ^ 2 := by
      apply pow_le_pow_left₀ h1b.le; linarith
    have hdiv : Bt ≤ Bt / (1 - b) ^ 2 * (1 - t) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hq hBt0
    unfold Spline.evalHalf
    calc _ ≤ Bt := hBk.trans hle
      _ ≤ Bt / (1 - b) ^ 2 * (1 - t) ^ 2 := hdiv
      _ ≤ (Ct + Bt / (1 - b) ^ 2) * (1 - t) ^ 2 := by nlinarith

theorem cellIndex_measurable (l : List ℝ) : Measurable (fun u : ℝ => cellIndex l u) := by
  unfold cellIndex
  generalize (l.drop 1).dropLast = l'
  induction l' with
  | nil => simp
  | cons b l ih =>
    have e : (fun u : ℝ => (List.filter (fun c => decide (c ≤ u)) (b :: l)).length) =
        fun u => (if b ≤ u then 1 else 0) + (List.filter (fun c => decide (c ≤ u)) l).length := by
      funext u
      by_cases h : b ≤ u <;> simp [h, add_comm]
    rw [e]
    refine Measurable.add ?_ ih
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem vec_cont : Continuous (fun p : ℝ × ℝ => (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ)) := by
  refine continuous_pi (fun k => ?_)
  fin_cases k
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact Complex.continuous_ofReal.comp continuous_snd

theorem evalHalf_measurable (S : Spline) : Measurable (Function.uncurry S.evalHalf) := by
  let g : ℝ × ℝ → (ℝ × ℝ) × (ℕ × ℕ) := fun p => (p, (cellIndex S.mesh.tBreaks p.1, cellIndex S.mesh.xBreaks p.2))
  let F : (ℝ × ℝ) × (ℕ × ℕ) → ℂ := fun q => MvPolynomial.eval ![(q.1.1 : ℂ), (q.1.2 : ℂ)] (S.piece q.2.1 q.2.2)
  have h1 : Measurable g :=
    measurable_id.prodMk (((cellIndex_measurable _).comp measurable_fst).prodMk ((cellIndex_measurable _).comp measurable_snd))
  have h2 : Measurable F := by
    refine measurable_from_prod_countable_left (fun n => ?_)
    exact ((MvPolynomial.continuous_eval (S.piece n.1 n.2)).comp vec_cont).measurable
  have e : Function.uncurry S.evalHalf = F ∘ g := by
    funext p
    rfl
  rw [e]
  exact h2.comp h1

theorem eval_measurable (S : Spline) (odd : Bool) : Measurable (Function.uncurry (S.eval odd)) := by
  have ha : Measurable (fun p : ℝ × ℝ => (p.1, |p.2|)) :=
    measurable_fst.prodMk (continuous_abs.measurable.comp measurable_snd)
  have hh : Measurable (Function.uncurry S.evalHalf ∘ fun p : ℝ × ℝ => (p.1, |p.2|)) :=
    (evalHalf_measurable S).comp ha
  have hs : MeasurableSet {p : ℝ × ℝ | (odd && decide (p.2 < 0)) = true} := by
    cases odd
    · simp
    · simpa using measurableSet_lt measurable_snd measurable_const
  have hc : Measurable (fun p : ℝ × ℝ => if (odd && decide (p.2 < 0)) = true then (-1 : ℂ) else 1) :=
    Measurable.ite hs measurable_const measurable_const
  have e : Function.uncurry (S.eval odd) =
      (fun p : ℝ × ℝ => if (odd && decide (p.2 < 0)) = true then (-1 : ℂ) else 1) * (Function.uncurry S.evalHalf ∘ fun p : ℝ × ℝ => (p.1, |p.2|)) := by
    funext p
    rfl
  rw [e]
  exact hc.mul hh

theorem chart_facts (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    0 ≤ chartT P y ∧ chartT P y < 1 ∧ |heightRatio y| ≤ 1 ∧ 0 < chartS P y ∧
      chartS P y ≤ max P.L0 1 / (1 + ‖y‖) := by
  have hL := hP.L0_pos
  have hr := norm_nonneg y
  have hpos : 0 < ‖y‖ + P.L0 := by linarith
  have hS : chartS P y = P.L0 / (‖y‖ + P.L0) := by
    unfold chartS chartT; field_simp; ring
  refine ⟨div_nonneg hr hpos.le, (div_lt_one hpos).2 (by linarith), ?_, ?_, ?_⟩
  · unfold heightRatio
    rw [abs_div, abs_norm]
    rcases hr.eq_or_lt with h | h
    · simp [← h]
    · rw [div_le_one h]; simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 2
  · rw [hS]; exact div_pos hL hpos
  · rw [hS, div_le_div_iff₀ hpos (by linarith)]
    rcases le_total P.L0 1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

theorem atom_measurable (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) :
    Measurable (fun y => atomTerm P j a M β S y) := by
  have hE : Measurable (fun y : Space => S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) := by
    have h1 : Measurable (fun y : Space => (chartT P y, heightRatio y)) := by
      unfold chartT heightRatio; fun_prop
    exact (eval_measurable S _).comp h1
  have hA : Measurable (fun y : Space => angleOf y) := by
    unfold angleOf
    have : Measurable (fun y : Space => ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)) := by fun_prop
    have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y : Space => ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
      funext y; exact (Complex.mk_eq_add_mul_I _ _)
    refine Complex.measurable_arg.comp ?_
    rw [e]
    exact this
  have hL : Measurable (fun y : Space => logPhase P y) := by
    unfold logPhase; fun_prop
  have hQ : Measurable (fun y : Space => Real.sqrt (qOf y) ^ a) := by
    unfold qOf heightRatio; fun_prop
  unfold atomTerm
  fun_prop

theorem atomTerm_memLpTwo_of_tail (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ)
    (S : Spline) (hmesh : IsTensorMesh S.mesh)
    (htail : ∀ k < cellCount S.mesh.xBreaks, atFirst 1 (S.piece (atomLastT S) k) = 0 ∧
      atFirst 1 (tDeriv 1 (S.piece (atomLastT S) k)) = 0) (w : ℂ) (i : Fin 3) :
    MemLp (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) 2 volume := by
  obtain ⟨K, hK0, hK⟩ := tail_bound_split S hmesh htail (decide (a = 0))
  set q : ℝ := 2 + 2 * P.eps with hq
  have heps := hP.eps_pos
  set c : ℝ := max P.L0 1 with hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  set g : Space → ℝ := fun y => ‖w‖ * K * c ^ q * (1 + ‖y‖) ^ (-q) with hg
  have hgm : MemLp g 2 volume := by
    have hmeas : AEStronglyMeasurable g volume := by
      refine Measurable.aestronglyMeasurable ?_
      simp only [hg]; fun_prop
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(2 * q))) volume := by
      refine integrable_one_add_norm ?_
      simp only [finrank_euclideanSpace, Fintype.card_fin, hq]
      push_cast
      linarith
    refine (hi.const_mul ((‖w‖ * K * c ^ q) ^ 2)).congr (Filter.Eventually.of_forall (fun y => ?_))
    have h1 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
    have e : ((1 + ‖y‖) ^ (-q)) ^ 2 = (1 + ‖y‖) ^ (-(2 * q)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le]
      congr 1
      push_cast
      ring
    simp only [hg]
    rw [← e]
    ring
  have hfm : AEStronglyMeasurable (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) volume := by
    refine Measurable.aestronglyMeasurable ?_
    have hd : Measurable (fun y : Space => decayFactor P y) := by
      unfold decayFactor chartS chartT; fun_prop
    have ha := atom_measurable P j a M β S
    exact (Complex.measurable_re.comp ((measurable_const.mul (Complex.measurable_ofReal.comp hd)).mul ha)).smul_const _
  refine hgm.of_le hfm (Filter.Eventually.of_forall (fun y => ?_))
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := chart_facts P hP y
  have hsq : chartS P y = 1 - chartT P y := rfl
  have hA : ‖atomTerm P j a M β S y‖ ≤ K * chartS P y ^ 2 := by
    unfold atomTerm
    rw [norm_mul, norm_mul]
    have e1 : ‖Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    have e2 : ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr ?_)
      unfold qOf; nlinarith [sq_nonneg (heightRatio y)]
    have e3 := hK _ _ ht0 ht1 hx
    rw [e1, one_mul, hsq]
    calc ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ * ‖S.eval (decide (a = 0)) (chartT P y) (heightRatio y)‖
        ≤ 1 * (K * (1 - chartT P y) ^ 2) := mul_le_mul e2 e3 (norm_nonneg _) zero_le_one
      _ = K * (1 - chartT P y) ^ 2 := one_mul _
  have hdec : 0 ≤ decayFactor P y := Real.rpow_nonneg hs0.le _
  have hpow : chartS P y ^ (2 * P.eps) * chartS P y ^ 2 ≤ c ^ q * (1 + ‖y‖) ^ (-q) := by
    have h1 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
    rw [← Real.rpow_natCast (chartS P y) 2, ← Real.rpow_add hs0]
    calc chartS P y ^ (2 * P.eps + ((2 : ℕ) : ℝ)) = chartS P y ^ q := by
          rw [hq]; push_cast; ring_nf
      _ ≤ (c / (1 + ‖y‖)) ^ q := Real.rpow_le_rpow hs0.le hsc (by linarith)
      _ = c ^ q * (1 + ‖y‖) ^ (-q) := by
          rw [Real.div_rpow hc0.le h1.le, Real.rpow_neg h1.le, div_eq_mul_inv]
  calc ‖(w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i‖
      ≤ ‖w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y‖ := by
        rw [norm_smul]
        have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
        rw [hu, mul_one]
        exact Complex.abs_re_le_norm _
    _ = ‖w‖ * decayFactor P y * ‖atomTerm P j a M β S y‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdec]
    _ ≤ ‖w‖ * decayFactor P y * (K * chartS P y ^ 2) :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg (norm_nonneg _) hdec)
    _ = ‖w‖ * K * (chartS P y ^ (2 * P.eps) * chartS P y ^ 2) := by unfold decayFactor; ring
    _ ≤ ‖w‖ * K * (c ^ q * (1 + ‖y‖) ^ (-q)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (norm_nonneg _) hK0)
    _ = ‖g y‖ := by
        have h1 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
        rw [hg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring

end DualPartsInternal

open DualPartsInternal

theorem atomTerm_traceRegular (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) (w : ℂ) (i : Fin 3) :
    IsTraceRegular (fun y => (w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i) := by
  obtain ⟨C, hC⟩ := atomTerm_boundedSlope P hP j a M β S ha hS hM w i
  exact traceRegular_of_parts hC (atomTerm_memLpTwo_of_tail P hP j a M β S hS.spline.mesh hS.at_infinity w i)
    (atomTerm_gradMemLpTwo P hP j a M β S ha hS hM w i) (atomTerm_second P hP j a M β S ha hS hM w i)

theorem fieldMode_traceRegular (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    IsTraceRegular (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) := by
  obtain ⟨C, hC⟩ := fieldMode_boundedSlope P hP D hD n hn β
  exact traceRegular_of_parts hC (fieldMode_memLpTwo P hP D hD n hn β)
    (fieldMode_gradMemLpTwo P hP D hD n hn β) (fieldMode_second P hP D hD n hn β)

theorem fluxTerm_radialRegular (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) (w : ℂ) (i : Fin 3) :
    IsRadialFluxRegular (fun y => (innerSL ℝ (ofComponents (radialVec y))).smulRight
      ((w * ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y).re • unitVector i)) := by
  obtain ⟨D, hD, hDl, hDm⟩ := fluxTerm_radialDiv P hP j a M β S hS w i
  exact fluxRegular_of_parts (atomTerm_memLpTwo_of_tail P hP j a M β S hS.continuous.mesh hS.at_infinity w i) hD hDl hDm

end GivenFields

end CellCert

end Breakdown

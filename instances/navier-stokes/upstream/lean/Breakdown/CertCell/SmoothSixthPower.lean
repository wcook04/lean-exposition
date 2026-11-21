import Breakdown.CertCell.SixthPowerStatements

open MeasureTheory

noncomputable section

namespace Breakdown

private lemma opNorm_le_sqrt_matSq (A : Space →L[ℝ] Space) : ‖A‖ ≤ Real.sqrt (matSq A) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hx : x = ∑ i, x i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
    simp [unitVector, EuclideanSpace.basisFun_apply]
  have h1 : ‖A x‖ ≤ ∑ i, ‖x i‖ * ‖A (unitVector i)‖ := by
    conv_lhs => rw [hx, map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, norm_smul]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖x i‖) (fun i => ‖A (unitVector i)‖)
  rw [EuclideanSpace.norm_eq x, mul_comm]
  exact h1.trans (by simpa [matSq] using h2)

private lemma norm_fderiv_quartic_le (v : Space) :
    ‖fderiv ℝ (fun z : Space => (‖z‖ ^ 2) ^ 2) v‖ ≤ 4 * ‖v‖ ^ 3 := by
  have hd := (hasDerivAt_pow 2 (‖v‖ ^ 2)).comp_hasFDerivAt v
    (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  rw [show (fun z : Space => (‖z‖ ^ 2) ^ 2) = (fun x : ℝ => x ^ 2) ∘ (fun z : Space => ‖z‖ ^ 2)
    from rfl, hd.fderiv, norm_smul, ← Nat.cast_smul_eq_nsmul ℝ 2, norm_smul, innerSL_apply_norm]
  norm_num
  ring_nf
  exact le_refl _

private lemma matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem smoothSixthPowerBound_of (h : ThreeHalvesGradientBound (1 / (2 * Real.sqrt 3))) :
    SmoothSixthPowerBound (4 / 3) := by
  intro w hw hws
  set g : Space → ℝ := fun z => (‖z‖ ^ 2) ^ 2 with hg
  set u : Space → ℝ := g ∘ w with hu
  have hgc : ContDiff ℝ 1 g := (contDiff_norm_sq ℝ).pow 2
  have huc : ContDiff ℝ 1 u := hgc.comp hw
  have hus : HasCompactSupport u := hws.comp_left (by simp [hg])
  have hmain := h u huc hus
  have hpow : ∀ y, |u y| ^ ((3 : ℝ) / 2) = ‖w y‖ ^ 6 := by
    intro y
    simp only [hu, hg, Function.comp]
    rw [abs_of_nonneg (by positivity), ← pow_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simp only [hpow] at hmain
  have hwd : ∀ y, DifferentiableAt ℝ w y := fun y => (hw.differentiable one_ne_zero) y
  have hgd : ∀ v, DifferentiableAt ℝ g v := fun v => (hgc.differentiable one_ne_zero) v
  have hder : ∀ y, ‖fderiv ℝ u y‖ ≤ 4 * ‖w y‖ ^ 3 * Real.sqrt (matSq (fderiv ℝ w y)) := by
    intro y
    rw [hu, fderiv_comp y (hgd _) (hwd y)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul (norm_fderiv_quartic_le _) (opNorm_le_sqrt_matSq _) (norm_nonneg _)
      (by positivity)
  have hDw : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hF : Continuous fun y => matSq (fderiv ℝ w y) := by
    unfold matSq
    exact continuous_finsetSum _ fun i _ => ((hDw.clm_apply continuous_const).norm).pow 2
  have hFs : HasCompactSupport fun y => matSq (fderiv ℝ w y) :=
    (hws.fderiv (𝕜 := ℝ)).comp_left (g := matSq) (by simp [matSq])
  have hw3 : Continuous fun y => ‖w y‖ ^ 3 := hw.continuous.norm.pow 3
  have hw3s : HasCompactSupport fun y => ‖w y‖ ^ 3 :=
    hws.comp_left (g := fun z : Space => ‖z‖ ^ 3) (by simp)
  have hw6 : Continuous fun y => ‖w y‖ ^ 6 := hw.continuous.norm.pow 6
  have hw6s : HasCompactSupport fun y => ‖w y‖ ^ 6 :=
    hws.comp_left (g := fun z : Space => ‖z‖ ^ 6) (by simp)
  have hsF : Continuous fun y => Real.sqrt (matSq (fderiv ℝ w y)) := hF.sqrt
  have hsFs : HasCompactSupport fun y => Real.sqrt (matSq (fderiv ℝ w y)) :=
    hFs.comp_left (g := Real.sqrt) (by simp)
  have hDu : Continuous fun y => ‖fderiv ℝ u y‖ := (huc.continuous_fderiv one_ne_zero).norm
  have hDus : HasCompactSupport fun y => ‖fderiv ℝ u y‖ :=
    (hus.fderiv (𝕜 := ℝ)).comp_left (g := fun A => ‖A‖) (by simp)
  have hprod : Continuous fun y => ‖w y‖ ^ 3 * Real.sqrt (matSq (fderiv ℝ w y)) := hw3.mul hsF
  have hprods : HasCompactSupport fun y => ‖w y‖ ^ 3 * Real.sqrt (matSq (fderiv ℝ w y)) :=
    hw3s.mul_right
  have hN : ∫ y, ‖fderiv ℝ u y‖ ≤
      4 * ((∫ y, ‖w y‖ ^ 6) ^ ((1 : ℝ) / 2) * (∫ y, matSq (fderiv ℝ w y)) ^ ((1 : ℝ) / 2)) := by
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure Space))
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun y => (by positivity : (0 : ℝ) ≤ ‖w y‖ ^ 3))
      (Filter.Eventually.of_forall fun y => Real.sqrt_nonneg (matSq (fderiv ℝ w y)))
      (hw3.memLp_of_hasCompactSupport hw3s) (hsF.memLp_of_hasCompactSupport hsFs)
    have e1 : ∀ y, (‖w y‖ ^ 3) ^ (2 : ℝ) = ‖w y‖ ^ 6 := fun y => by
      rw [Real.rpow_two, ← pow_mul]
    have e2 : ∀ y, (Real.sqrt (matSq (fderiv ℝ w y))) ^ (2 : ℝ) = matSq (fderiv ℝ w y) :=
      fun y => by rw [Real.rpow_two, Real.sq_sqrt (matSq_nonneg' _)]
    simp only [e1, e2] at hCS
    calc ∫ y, ‖fderiv ℝ u y‖ ≤ ∫ y, 4 * (‖w y‖ ^ 3 * Real.sqrt (matSq (fderiv ℝ w y))) :=
          integral_mono (hDu.integrable_of_hasCompactSupport hDus)
            ((hprod.integrable_of_hasCompactSupport hprods).const_mul 4)
            fun y => (hder y).trans (le_of_eq (mul_assoc _ _ _))
      _ = 4 * ∫ y, ‖w y‖ ^ 3 * Real.sqrt (matSq (fderiv ℝ w y)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hCS (by norm_num)
  set X := ∫ y, ‖w y‖ ^ 6 with hXdef
  set Y := ∫ y, matSq (fderiv ℝ w y) with hYdef
  have hX0 : 0 ≤ X := integral_nonneg fun y => by positivity
  have hY0 : 0 ≤ Y := integral_nonneg fun y => matSq_nonneg' _
  have hc : 0 < Real.sqrt 3 := by positivity
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : X ^ ((2 : ℝ) / 3) ≤ 2 / Real.sqrt 3 * (X ^ ((1 : ℝ) / 2) * Y ^ ((1 : ℝ) / 2)) := by
    calc X ^ ((2 : ℝ) / 3) ≤ 1 / (2 * Real.sqrt 3) * ∫ y, ‖fderiv ℝ u y‖ := hmain
      _ ≤ 1 / (2 * Real.sqrt 3) * (4 * (X ^ ((1 : ℝ) / 2) * Y ^ ((1 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by field_simp; ring
  rcases hX0.eq_or_lt with hX | hX
  · rw [← hX, Real.zero_rpow (by norm_num)]
    positivity
  · have ha : 0 < X ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hX _
    have e4 : X ^ ((2 : ℝ) / 3) = (X ^ ((1 : ℝ) / 6)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num
    have e3 : X ^ ((1 : ℝ) / 2) = (X ^ ((1 : ℝ) / 6)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num
    have e2 : X ^ ((1 : ℝ) / 3) = (X ^ ((1 : ℝ) / 6)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num
    have hb : 0 ≤ Y ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hY0 _
    have eY : Y = (Y ^ ((1 : ℝ) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
    rw [e4, e3] at key
    set a := X ^ ((1 : ℝ) / 6)
    set b := Y ^ ((1 : ℝ) / 2)
    have hab : a ≤ 2 / Real.sqrt 3 * b := by
      have h3 : 0 < a ^ 3 := by positivity
      have : a ^ 3 * a ≤ a ^ 3 * (2 / Real.sqrt 3 * b) := by
        calc a ^ 3 * a = a ^ 4 := by ring
          _ ≤ _ := key
          _ = _ := by ring
      exact le_of_mul_le_mul_left this h3
    rw [e2, eY]
    calc a ^ 2 ≤ (2 / Real.sqrt 3 * b) ^ 2 := pow_le_pow_left₀ ha.le hab 2
      _ = 4 / 3 * b ^ 2 := by rw [mul_pow, div_pow, hs3]; ring

end Breakdown

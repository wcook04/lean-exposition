import Breakdown.FracCell.StCircleWeak

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis SteadyCert

namespace Internal.AngularFrame

theorem vec_expand (v : Space) : v = ∑ i : Fin 3, v i • unitVector i := by
  ext j
  fin_cases j <;> simp [unitVector, Fin.sum_univ_three]

theorem inner_expand (M : Space →L[ℝ] Space) (v w : Space) :
    inner ℝ (M v) w = ∑ i : Fin 3, ∑ l : Fin 3, v i * w l * inner ℝ (M (unitVector i)) (unitVector l) := by
  conv_lhs => rw [vec_expand v, vec_expand w]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

def gv (Hy : Space →L[ℝ] Space →L[ℝ] Space) (i l : Fin 3) : Space :=
  ∑ j : Fin 3, inner ℝ (Hy (unitVector j) (unitVector i)) (unitVector l) • unitVector j

theorem gv_inner (Hy : Space →L[ℝ] Space →L[ℝ] Space) (i l : Fin 3) (v : Space) :
    inner ℝ (gv Hy i l) v = inner ℝ (Hy v (unitVector i)) (unitVector l) := by
  conv_rhs => rw [vec_expand v]
  simp only [gv, sum_inner, real_inner_smul_left, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [unitVector, EuclideanSpace.inner_single_left]
  ring

theorem third_expand (θ : ℝ) (Hy : Space →L[ℝ] Space →L[ℝ] Space) (a b : Fin 3) :
    frameThird θ Hy a b 1 = ∑ i : Fin 3, ∑ l : Fin 3,
      frameUnit θ b i * frameUnit θ a l * inner ℝ (gv Hy i l) (angularUnit θ) := by
  rw [frameThird, inner_expand]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [gv_inner]
  rfl

theorem mat_expand (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ M a b = ∑ i : Fin 3, ∑ l : Fin 3,
      frameUnit θ b i * frameUnit θ a l * inner ℝ (M (unitVector i)) (unitVector l) := by
  rw [frameMat, inner_expand]
  rfl

theorem frame_comp_deriv (b i : Fin 3) (θ : ℝ) :
    HasDerivAt (fun t => frameUnit t b i) (∑ c : Fin 3, frameTurn c b * frameUnit θ c i) θ := by
  fin_cases b <;> fin_cases i <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, frameTurn]
  all_goals first
    | exact Real.hasDerivAt_cos θ
    | exact Real.hasDerivAt_sin θ
    | exact (Real.hasDerivAt_sin θ).neg
    | exact (Real.hasDerivAt_cos θ).neg
    | exact hasDerivAt_const θ _

theorem frame_comp_smooth (b i : Fin 3) : ContDiff ℝ ∞ (fun t => frameUnit t b i) := by
  fin_cases b <;> fin_cases i <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit]
  all_goals first
    | exact Real.contDiff_cos
    | exact Real.contDiff_sin
    | exact Real.contDiff_sin.neg
    | exact contDiff_const

theorem frame_comp_periodic (b i : Fin 3) : Function.Periodic (fun t => frameUnit t b i) (2 * Real.pi) := by
  intro t
  fin_cases b <;> fin_cases i <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

def wgt (k : ℝ) (a b i l : Fin 3) (θ : ℝ) : ℂ :=
  Complex.exp (-(k * θ : ℝ) * Complex.I) * ((frameUnit θ b i * frameUnit θ a l : ℝ) : ℂ)

theorem wgt_hasDeriv (k : ℝ) (a b i l : Fin 3) (θ : ℝ) :
    HasDerivAt (wgt k a b i l) (Complex.exp (-(k * θ : ℝ) * Complex.I) *
      (-(k : ℂ) * Complex.I * ((frameUnit θ b i * frameUnit θ a l : ℝ) : ℂ) +
        (((∑ c : Fin 3, frameTurn c b * frameUnit θ c i) * frameUnit θ a l +
          frameUnit θ b i * ∑ c : Fin 3, frameTurn c a * frameUnit θ c l : ℝ) : ℂ))) θ := by
  have hP := ((frame_comp_deriv b i θ).mul (frame_comp_deriv a l θ)).ofReal_comp
  have hlin : HasDerivAt (fun t : ℝ => (-(k * t : ℝ) * Complex.I : ℂ)) (-(k : ℂ) * Complex.I) θ := by
    have h1 := ((hasDerivAt_id θ).const_mul k).ofReal_comp.neg.mul_const Complex.I
    exact (h1 : HasDerivAt (fun t : ℝ => (-(k * t : ℝ) * Complex.I : ℂ)) _ θ).congr_deriv (by simp)
  have hE := hlin.cexp
  have h2 := hE.mul hP
  refine (h2 : HasDerivAt (wgt k a b i l) _ θ).congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

theorem wgt_smooth (k : ℝ) (a b i l : Fin 3) : ContDiff ℝ ∞ (wgt k a b i l) := by
  have h1 := frame_comp_smooth b i
  have h2 := frame_comp_smooth a l
  have hE : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (-(k * t : ℝ) * Complex.I)) := by
    have hlin : ContDiff ℝ ∞ (fun t : ℝ => (-(k * t : ℝ) * Complex.I : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).neg.mul contDiff_const
    exact Complex.contDiff_exp.comp hlin
  exact hE.mul (Complex.ofRealCLM.contDiff.comp (h1.mul h2))

theorem wgt_periodic (j : ℤ) (a b i l : Fin 3) : Function.Periodic (wgt (j : ℝ) a b i l) (2 * Real.pi) := by
  intro θ
  simp only [wgt]
  have e1 := frame_comp_periodic b i θ
  have e2 := frame_comp_periodic a l θ
  simp only at e1 e2
  rw [e1, e2]
  congr 1
  have : (-(((j : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ)) * Complex.I =
      -(((j : ℝ) * θ : ℝ) : ℂ) * Complex.I + ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem comb_algebra (k : ℝ) (E : ℂ) (a b : Fin 3) (e : Fin 3 → Fin 3 → ℝ) (F : Fin 3 → Fin 3 → ℝ) :
    ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * (E * ((∑ i : Fin 3, ∑ l : Fin 3, e b' i * e a' l * F i l : ℝ) : ℂ)) =
      ∑ i : Fin 3, ∑ l : Fin 3, -(E * (-(k : ℂ) * Complex.I * ((e b i * e a l : ℝ) : ℂ) +
        (((∑ c : Fin 3, frameTurn c b * e c i) * e a l + e b i * ∑ c : Fin 3, frameTurn c a * e c l : ℝ) : ℂ))) *
        (F i l : ℂ) := by
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three, angularComb, frameTurn] <;> push_cast <;> ring

theorem ii_cmul {f : ℝ → ℝ} {g : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (hg : Continuous g) :
    IntervalIntegrable (fun θ => g θ * (f θ : ℂ)) volume 0 (2 * Real.pi) := by
  have h : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * Real.pi) := ⟨hf.1.ofReal, hf.2.ofReal⟩
  exact h.continuousOn_mul hg.continuousOn

theorem ii_sum2 {F : Fin 3 → Fin 3 → ℝ → ℂ} (h : ∀ i l, IntervalIntegrable (F i l) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ => ∑ i : Fin 3, ∑ l : Fin 3, F i l θ) volume 0 (2 * Real.pi) := by
  simp only [Fin.sum_univ_three]
  have := fun i => ((h i 0).add (h i 1)).add (h i 2)
  exact ((this 0).add (this 1)).add (this 2)

theorem int_sum2 {F : Fin 3 → Fin 3 → ℝ → ℂ} (h : ∀ i l, IntervalIntegrable (F i l) volume 0 (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ i : Fin 3, ∑ l : Fin 3, F i l θ =
      ∑ i : Fin 3, ∑ l : Fin 3, ∫ θ in (0 : ℝ)..(2 * Real.pi), F i l θ := by
  rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
  · exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_finsetSum fun l _ => h i l
  · simp only [Fin.sum_univ_three]
    exact ((h i 0).add (h i 1)).add (h i 2)

theorem point (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b : Fin 3) (r z : ℝ)
    (hf : ∀ i l, IntervalIntegrable (fun θ => inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l))
      volume 0 (2 * Real.pi))
    (hg : ∀ i l, IntervalIntegrable (fun θ => inner ℝ (gv (H (cylPoint r θ z)) i l) (angularUnit θ))
      volume 0 (2 * Real.pi))
    (hid : ∀ i l, ∫ θ in (0 : ℝ)..(2 * Real.pi), wgt (azimuth m n) a b i l θ *
        ((r * inner ℝ (gv (H (cylPoint r θ z)) i l) (angularUnit θ) : ℝ) : ℂ) =
      -∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (wgt (azimuth m n) a b i l) θ *
        ((inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l) : ℝ) : ℂ)) :
    angularGradMode m n H a b (r, z) =
      ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' (r, z) := by
  have hEc : Continuous (fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)) := by fun_prop
  have hec : ∀ c i, Continuous (fun θ => frameUnit θ c i) := fun c i => (frame_comp_smooth c i).continuous
  have hI : ∀ i l, IntervalIntegrable (fun θ => wgt (azimuth m n) a b i l θ *
      ((r * inner ℝ (gv (H (cylPoint r θ z)) i l) (angularUnit θ) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun i l => ii_cmul ((hg i l).const_mul r) (wgt_smooth _ a b i l).continuous
  have hJ : ∀ i l, IntervalIntegrable (fun θ => -deriv (wgt (azimuth m n) a b i l) θ *
      ((inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun i l => ii_cmul (hf i l) ((wgt_smooth _ a b i l).continuous_deriv (by simp)).neg
  have hM : ∀ a' b', IntervalIntegrable (fun θ => ((frameMat θ (G (cylPoint r θ z)) a' b' : ℝ) : ℂ))
      volume 0 (2 * Real.pi) := by
    intro a' b'
    have e : (fun θ => ((frameMat θ (G (cylPoint r θ z)) a' b' : ℝ) : ℂ)) = fun θ =>
        ∑ i : Fin 3, ∑ l : Fin 3, (((frameUnit θ b' i * frameUnit θ a' l : ℝ) : ℂ)) *
          ((inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l) : ℝ) : ℂ) := by
      funext θ
      rw [mat_expand]
      push_cast
      rfl
    rw [e]
    exact ii_sum2 fun i l => ii_cmul (hf i l)
      (Complex.continuous_ofReal.comp ((hec b' i).mul (hec a' l)))
  have hK : ∀ a' b', IntervalIntegrable (fun θ => angularComb (azimuth m n) a b a' b' *
      (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * ((frameMat θ (G (cylPoint r θ z)) a' b' : ℝ) : ℂ)))
      volume 0 (2 * Real.pi) :=
    fun a' b' => ((hM a' b').continuousOn_mul hEc.continuousOn).const_mul _
  have hL : angularGradMode m n H a b (r, z) = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ i : Fin 3, ∑ l : Fin 3, -deriv (wgt (azimuth m n) a b i l) θ *
        ((inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l) : ℝ) : ℂ) := by
    rw [int_sum2 hJ]
    have step : ∀ i l, ∫ θ in (0 : ℝ)..(2 * Real.pi), -deriv (wgt (azimuth m n) a b i l) θ *
        ((inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l) : ℝ) : ℂ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), wgt (azimuth m n) a b i l θ *
          ((r * inner ℝ (gv (H (cylPoint r θ z)) i l) (angularUnit θ) : ℝ) : ℂ) := by
      intro i l
      simp only [neg_mul, intervalIntegral.integral_neg]
      rw [hid i l]
    simp only [step]
    rw [← int_sum2 hI]
    simp only [angularGradMode, modeThird]
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [third_expand, wgt, Fin.sum_univ_three]
    push_cast
    ring
  have hR : ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' (r, z) =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ a' : Fin 3, ∑ b' : Fin 3,
        angularComb (azimuth m n) a b a' b' *
          (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * ((frameMat θ (G (cylPoint r θ z)) a' b' : ℝ) : ℂ)) := by
    rw [int_sum2 hK, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [intervalIntegral.integral_const_mul]
    simp only [gradMode, modeMat]
    ring
  rw [hL, hR]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [(wgt_hasDeriv _ a b _ _ θ).deriv, mat_expand]
  exact (comb_algebra (azimuth m n) (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)) a b
    (fun c i => frameUnit θ c i) (fun i l => inner ℝ (G (cylPoint r θ z) (unitVector i)) (unitVector l))).symm

theorem locInt_sq {s : Space → ℝ} (hs : AEStronglyMeasurable s volume) {F : Space → ℝ} (hF : Integrable F volume)
    (hle : ∀ y, s y ^ 2 ≤ F y) : LocallyIntegrable s volume := by
  have h2 : Integrable (fun y => s y ^ 2) volume :=
    hF.mono' (hs.pow 2) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hle y)
  exact ((memLp_two_iff_integrable_sq hs).2 h2).locallyIntegrable (by norm_num)

theorem locInt_vec {s : Space → Space} (hs : AEStronglyMeasurable s volume) {F : Space → ℝ}
    (hF : Integrable F volume) (hle : ∀ y, ‖s y‖ ^ 2 ≤ F y) : LocallyIntegrable s volume := by
  have h2 : Integrable (fun y => ‖s y‖ ^ 2) volume :=
    hF.mono' (hs.norm.pow 2) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hle y)
  exact ((memLp_two_iff_integrable_sq_norm hs).2 h2).locallyIntegrable (by norm_num)

theorem unit_norm (l : Fin 3) : ‖unitVector l‖ = 1 := by
  simp [unitVector]

theorem inner_sq_le (v : Space) (l : Fin 3) : inner ℝ v (unitVector l) ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := abs_real_inner_le_norm v (unitVector l)
  rw [unit_norm, mul_one] at h
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem meas_G {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume) (i : Fin 3) :
    AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
  (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG

theorem meas_H {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume) (j i : Fin 3) :
    AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
  (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
    ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous.comp_aestronglyMeasurable hH)

theorem G_sq_le (M : Space →L[ℝ] Space) (i : Fin 3) : ‖M (unitVector i)‖ ^ 2 ≤ entrySq M :=
  Finset.single_le_sum (f := fun i => ‖M (unitVector i)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem H_sq_le (M : Space →L[ℝ] Space →L[ℝ] Space) (j i : Fin 3) :
    ‖M (unitVector j) (unitVector i)‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖M (unitVector i) (unitVector j)‖ ^ 2 :=
  (Finset.single_le_sum (f := fun j' => ‖M (unitVector j) (unitVector j')‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)).trans
  (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖M (unitVector i') (unitVector j')‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j))

end Internal.AngularFrame

open Internal.AngularFrame in
theorem angularFrame_of_circle (hC : CircleWeakStatement) : AngularFrameStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u hS n a b
  have hF := hS.field
  have locG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hF.measurable_gradient i) hF.gradient_two fun y => G_sq_le (G y) i
  have locH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hF.measurable_second j i) hF.second_two fun y => H_sq_le (H y) j i
  have locf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hF.measurable_gradient i).inner aestronglyMeasurable_const)
      hF.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have locs : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hF.measurable_second j i).inner aestronglyMeasurable_const)
      hF.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have locg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun K hK => ((locs j i l).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hF.weak_second φ hφ i j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := (locG i).integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • H y (unitVector j) (unitVector i)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [L, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => hC (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) (fun y => gv (H y) i l)
    (locf i l) (locg i l) (hweak i l)
  have hk : azimuth c.order n = ((n * c.order : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth c.order n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  have h0 : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
      rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) by
        ext p; simp, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
    simpa using hp
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  rw [ae_restrict_iff' hrect]
  filter_upwards [hint, hid, h0] with p h1 h2 h3 hp
  have hr : 0 < p.1 := lt_of_le_of_ne (hS.box.r_order.1.trans hp.1.1) (Ne.symm h3)
  obtain ⟨r, z⟩ := p
  exact point c.order n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2)
    (fun i l => h2 i l hr)

end Breakdown.CellCert.CellEnergy

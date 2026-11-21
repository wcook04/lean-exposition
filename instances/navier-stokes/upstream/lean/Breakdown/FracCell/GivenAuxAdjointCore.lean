import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenProfileSmoothModes
import Breakdown.FracCell.GivenAuxPinSmoothLocal
import Breakdown.FracCell.GivenAuxDualParts
import Breakdown.FracCell.PuncturedWeakScalar
import Breakdown.FracCell.GivenAuxPressureOpen
import Breakdown.FracCell.GivenAuxFarDecayLeaves

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace AdjointCoreInternal

theorem ofComponents_sum (s : Finset ℤ) (w : ℤ → Fin 3 → ℝ) :
    ofComponents (fun i => ∑ n ∈ s, w n i) = ∑ n ∈ s, ofComponents (w n) := by
  ext j
  fin_cases j <;> simp [ofComponents]

theorem field_modes (P : ChartParams) (D : FieldData) (β : ℝ) :
    fieldOf P D β = fun y => ∑ n ∈ D.modes, (1 : ℝ) • modeFieldOf P D β n y := by
  funext y
  simp only [one_smul]
  unfold fieldOf modeFieldOf
  rw [← ofComponents_sum]
  congr 1
  funext i
  rw [Finset.mul_sum, Complex.re_sum]

theorem mode_contDiff (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : ContDiff ℝ 1 (modeFieldOf P D β n) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases h0 : n = 0
  · subst h0
    by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_mean P hP hD β hn
    · have hph : modePhase P 0 β = fun _ => 1 := by
        funext z
        simp [modePhase]
      refine modeFieldOf_contDiffAt_of P hP D β 0 (reducedField_mean_contDiff P hP hD β hn) y hy ?_
      rw [hph]
      exact contDiffAt_const
  · by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_wave P hP hD β n hn h0
    exact modeFieldOf_contDiffAt_axis_of P hP hD β n hn h0 y hy

theorem field_contDiff (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ContDiff ℝ 1 (fieldOf P D β) := by
  rw [field_modes]
  exact ContDiff.sum fun n hn => (mode_contDiff P hP D hD β n hn).const_smul (1 : ℝ)

theorem wave_div_zero (P : ChartParams) (hm : P.m ≠ 0) (D : FieldData) (n : ℤ)
    (h0 : n ≠ 0) (β t x : ℝ) : FracInternal.reducedDivergence P D n β t x = 0 := by
  have hf : (fun t' x' => reducedField P D n β t' x' 0) = fun t' x' =>
      weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x' := by
    funext t' x'
    simp [reducedField, h0]
  have hg : ∀ t' x', reducedField P D n β t' x' 1 =
      weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).polarAmp.eval true t' x' := by
    intro t' x'
    simp [reducedField, h0]
  have hk : ((n * P.m : ℤ) : ℂ) ≠ 0 := by
    have : (n * P.m : ℤ) ≠ 0 := mul_ne_zero h0 (by exact_mod_cast hm)
    exact_mod_cast this
  unfold FracInternal.reducedDivergence
  rw [hf]
  simp only [hg]
  simp only [reducedField, h0, if_false, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp
  rw [Complex.I_sq]
  ring

theorem field_divergence (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∀ y, divergenceAt (fieldOf P D β) y = 0 := by
  have hdiff : ∀ n ∈ D.modes, Differentiable ℝ (modeFieldOf P D β n) := fun n hn =>
    (mode_contDiff P hP D hD β n hn).differentiable (by norm_num)
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ n ∈ D.modes, divergenceAt (modeFieldOf P D β n) y = 0 := by
    rw [Filter.eventually_all_finset]
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      filter_upwards [FracInternal.ae_generic P hP.L0_pos (D.amp 0).streamAmp.mesh.tBreaks
        (D.amp 0).streamAmp.mesh.xBreaks] with y hy
      obtain ⟨_, h1, h2, ht, hx⟩ := hy
      have hy0 : y ≠ 0 := fun h => h1 (by simp [h])
      have hx0 : heightRatio y ≠ 0 := div_ne_zero h2 (norm_ne_zero_iff.2 hy0)
      rw [FracInternal.modeFieldOf_divergence_eq hP D β 0 h1
        (fun k => (reducedField_mean_contDiff P hP hD β hn k).differentiable (by norm_num) _),
        FracInternal.reducedDivergence_mean_eq_zero P D β hx0 ht hx]
      simp
    · filter_upwards [FracInternal.ae_coord_ne_zero 1] with y hy
      rw [FracInternal.modeFieldOf_divergence_eq hP D β n hy
        (fun k => (reducedField_wave_contDiff P hP hD β n hn h0 k).differentiable (by norm_num) _),
        wave_div_zero P hP.m_pos.ne' D n h0]
      simp
  refine FracInternal.divergenceAt_eq_zero_of_ae (field_contDiff P hP D hD β) ?_
  filter_upwards [hall] with y hy
  rw [field_modes, FracInternal.divergenceAt_finset_sum D.modes (fun _ => (1 : ℝ))
    (fun n => modeFieldOf P D β n) hdiff y]
  exact Finset.sum_eq_zero fun n hn => by rw [hy n hn, mul_zero]

private theorem far_ofReal {f : Space → ℝ} {a : ℝ} (h : FarDecayInternal.FarDecay f a) :
    FarDecayInternal.FarDecay (fun y => (f y : ℂ)) a := by
  have h' := h.clm Complex.ofRealCLM
  have e : (fun y => Complex.ofRealCLM (f y)) = fun y => (f y : ℂ) := funext fun y => Complex.ofRealCLM_apply _
  rw [e] at h'
  exact h'

private theorem far_re {f : Space → ℂ} {a : ℝ} (h : FarDecayInternal.FarDecay f a) :
    FarDecayInternal.FarDecay (fun y => (f y).re) a := by
  have h' := h.clm Complex.reCLM
  have e : (fun y => Complex.reCLM (f y)) = fun y => (f y).re := funext fun y => Complex.reCLM_apply _
  rw [e] at h'
  exact h'

private theorem single_clm (i : Fin 3) (a : ℝ) :
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single i (1 : ℝ)) :
      ℝ →L[ℝ] Space) a = EuclideanSpace.single i a := by
  ext j
  by_cases h : j = i <;> simp [h]

private theorem mode_farDecay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : FarDecayInternal.FarDecay (modeFieldOf P D β n) 3 := by
  have hR := FarDecayInternal.phased_far P hP D hD β n hn
  have hd := far_ofReal (FarDecayInternal.decay_far P hP)
  have hc : ∀ i : Fin 3, FarDecayInternal.FarDecay (fun y => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re) 3 := by
    intro i
    have h0 := (hd.mul ((hR 0).mul (far_ofReal (FarDecayInternal.radial_far i)))).mono (b := 3) (le_of_eq (by norm_num))
    have h1 := (hd.mul ((hR 1).mul (far_ofReal (FarDecayInternal.polar_far i)))).mono (b := 3) (le_of_eq (by norm_num))
    have h2 := (hd.mul ((hR 2).mul (far_ofReal (FarDecayInternal.azim_far i)))).mono (b := 3) (le_of_eq (by norm_num))
    have hs := far_re ((h0.add h1).add h2)
    have e : (fun y => ((decayFactor P y : ℂ) * (modePhase P n β y *
        (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
          reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
          reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re) =
        fun y => ((decayFactor P y : ℂ) * (modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 0 *
          (radialVec y i : ℂ)) + (decayFactor P y : ℂ) * (modePhase P n β y *
            reducedField P D n β (chartT P y) (heightRatio y) 1 * (polarVecQ y i : ℂ)) +
          (decayFactor P y : ℂ) * (modePhase P n β y *
            reducedField P D n β (chartT P y) (heightRatio y) 2 * (azimVecQ y i : ℂ))).re := by
      funext y
      congr 1
      ring
    rw [e]
    exact hs
  have hL : ∀ i : Fin 3, FarDecayInternal.FarDecay (fun y =>
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single i (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) 3 :=
    fun i => (hc i).clm _
  have hsum := ((hL 0).add (hL 1)).add (hL 2)
  have e : modeFieldOf P D β n = fun y =>
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single 0 (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y 0 +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y 0 +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y 0))).re) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single 1 (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y 1 +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y 1 +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y 1))).re) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single 2 (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y 2 +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y 2 +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y 2))).re) := by
    funext y
    simp only [single_clm]
    rfl
  rw [e]
  exact hsum

theorem mode_far (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖modeFieldOf P D β n y‖ ≤ C * ‖y‖ ^ (-(3 : ℝ)) ∧
        ‖fderiv ℝ (modeFieldOf P D β n) y‖ ≤ C * ‖y‖ ^ (-(4 : ℝ)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) (fderiv ℝ (modeFieldOf P D β n))
            (Metric.ball y 1) := by
  obtain ⟨R, C, h⟩ := (mode_farDecay P hP D hD β n hn).bounds
  refine ⟨R, C, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h y hy
  have e4 : -((3 : ℝ) + 1) = -(4 : ℝ) := by norm_num
  have e5 : -((3 : ℝ) + 2) = -(5 : ℝ) := by norm_num
  rw [e4] at h2
  rw [e5] at h3
  exact ⟨h1, h2, h3⟩

theorem slopeOn_sum_le {E : Type*} [NormedAddCommGroup E] {s : Set Space} (u : Finset ℤ)
    (g : ℤ → Space → E) (K : ℤ → NNReal) (hg : ∀ n ∈ u, LipschitzOnWith (K n) (g n) s) :
    LipschitzOnWith (∑ n ∈ u, K n) (fun y => ∑ n ∈ u, g n y) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : E)).lipschitzOnWith (s := s)
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a u)).add (ih fun n hn => hg n (Finset.mem_insert_of_mem hn))

theorem norm_sum_le_weight (u : Finset ℤ) {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) (C : ℤ → ℝ) (w : ℝ)
    (hw : 0 ≤ w) (h : ∀ n ∈ u, ‖f n‖ ≤ C n * w) : ‖∑ n ∈ u, f n‖ ≤ (∑ n ∈ u, |C n|) * w := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun n hn => (h n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)

theorem field_far (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∃ R C : ℝ, 1 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ →
      ‖fieldOf P D β y‖ ≤ C * ‖y‖ ^ (-(3 : ℝ)) ∧
        ‖fderiv ℝ (fieldOf P D β) y‖ ≤ C * ‖y‖ ^ (-(4 : ℝ)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) (fderiv ℝ (fieldOf P D β))
            (Metric.ball y 1) := by
  classical
  have hex : ∀ n : ℤ, ∃ R C : ℝ, n ∈ D.modes → ∀ y : Space, R ≤ ‖y‖ →
      ‖modeFieldOf P D β n y‖ ≤ C * ‖y‖ ^ (-(3 : ℝ)) ∧
        ‖fderiv ℝ (modeFieldOf P D β n) y‖ ≤ C * ‖y‖ ^ (-(4 : ℝ)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) (fderiv ℝ (modeFieldOf P D β n))
            (Metric.ball y 1) := by
    intro n
    by_cases hn : n ∈ D.modes
    · obtain ⟨R, C, h⟩ := mode_far P hP D hD β n hn
      exact ⟨R, C, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose Rn Cn hRC using hex
  have hdiff : ∀ n ∈ D.modes, Differentiable ℝ (modeFieldOf P D β n) := fun n hn =>
    (mode_contDiff P hP D hD β n hn).differentiable (by norm_num)
  have heq : fderiv ℝ (fieldOf P D β) =
      fun z => ∑ n ∈ D.modes, (1 : ℝ) • fderiv ℝ (modeFieldOf P D β n) z := by
    rw [field_modes]
    exact FracInternal.fderiv_finset_sum_smul D.modes (fun _ => (1 : ℝ)) (fun n => modeFieldOf P D β n) hdiff
  refine ⟨1 + ∑ n ∈ D.modes, |Rn n|, ∑ n ∈ D.modes, |Cn n|, ?_, fun y hy => ?_⟩
  · have := Finset.sum_nonneg (fun n (_ : n ∈ D.modes) => abs_nonneg (Rn n))
    linarith
  have hR : ∀ n ∈ D.modes, Rn n ≤ ‖y‖ := fun n hn => by
    have h1 : Rn n ≤ |Rn n| := le_abs_self _
    have h2 : |Rn n| ≤ ∑ m ∈ D.modes, |Rn m| :=
      Finset.single_le_sum (f := fun m => |Rn m|) (fun m _ => abs_nonneg _) hn
    linarith
  have hw : ∀ a : ℝ, 0 ≤ ‖y‖ ^ a := fun a => Real.rpow_nonneg (norm_nonneg y) a
  refine ⟨?_, ?_, ?_⟩
  · rw [field_modes]
    simp only [one_smul]
    exact norm_sum_le_weight D.modes _ Cn _ (hw _) fun n hn => (hRC n hn y (hR n hn)).1
  · rw [heq]
    simp only [one_smul]
    exact norm_sum_le_weight D.modes _ Cn _ (hw _) fun n hn => (hRC n hn y (hR n hn)).2.1
  · rw [heq]
    simp only [one_smul]
    refine (slopeOn_sum_le D.modes (fun n => fderiv ℝ (modeFieldOf P D β n))
      (fun n => Real.toNNReal (Cn n * ‖y‖ ^ (-(5 : ℝ)))) fun n hn => (hRC n hn y (hR n hn)).2.2).weaken ?_
    rw [← Real.toNNReal_coe (r := ∑ n ∈ D.modes, Real.toNNReal (Cn n * ‖y‖ ^ (-(5 : ℝ))))]
    refine Real.toNNReal_le_toNNReal ?_
    rw [NNReal.coe_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [Real.coe_toNNReal']
    exact max_le (mul_le_mul_of_nonneg_right (le_abs_self _) (hw _)) (mul_nonneg (abs_nonneg _) (hw _))

theorem far_weight {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r) : r ^ (-a) ≤ 2 ^ a * (1 + r) ^ (-a) := by
  have hr0 : 0 < r := by linarith
  have h1 : 0 < 1 + r := by linarith
  rw [Real.rpow_neg hr0.le, Real.rpow_neg h1.le, ← Real.inv_rpow hr0.le, ← Real.inv_rpow h1.le,
    ← Real.mul_rpow (by norm_num) (inv_nonneg.2 h1.le)]
  refine Real.rpow_le_rpow (inv_nonneg.2 hr0.le) ?_ ha
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hr0 h1]
  linarith

theorem near_weight {a r R : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hR : r ≤ R) : 1 ≤ (1 + R) ^ a * (1 + r) ^ (-a) := by
  have h1 : 0 < 1 + r := by linarith
  rw [Real.rpow_neg h1.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos h1 a)]
  exact Real.rpow_le_rpow h1.le (by linarith) ha

theorem weight_glue {g : Space → ℝ} {a R M C : ℝ} (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hnear : ∀ y : Space, ‖y‖ ≤ R → g y ≤ M) (hfar : ∀ y : Space, R ≤ ‖y‖ → g y ≤ C * ‖y‖ ^ (-a)) :
    ∃ K : ℝ, ∀ y, g y ≤ K * (1 + ‖y‖) ^ (-a) := by
  refine ⟨|M| * (1 + R) ^ a + |C| * 2 ^ a, fun y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-a) := Real.rpow_nonneg (by positivity) _
  have hMa : 0 ≤ |M| * (1 + R) ^ a := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hCa : 0 ≤ |C| * 2 ^ a := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  rw [add_mul]
  rcases le_total ‖y‖ R with h | h
  · have h1 := near_weight ha (norm_nonneg y) h
    calc g y ≤ |M| := (hnear y h).trans (le_abs_self M)
      _ = |M| * 1 := (mul_one _).symm
      _ ≤ |M| * ((1 + R) ^ a * (1 + ‖y‖) ^ (-a)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |M| * (1 + R) ^ a * (1 + ‖y‖) ^ (-a) := by ring
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hCa hw)
  · have h1 := far_weight ha (hR.trans h)
    have hy : 0 ≤ ‖y‖ ^ (-a) := Real.rpow_nonneg (norm_nonneg y) _
    calc g y ≤ C * ‖y‖ ^ (-a) := hfar y h
      _ ≤ |C| * ‖y‖ ^ (-a) := mul_le_mul_of_nonneg_right (le_abs_self C) hy
      _ ≤ |C| * (2 ^ a * (1 + ‖y‖) ^ (-a)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |C| * 2 ^ a * (1 + ‖y‖) ^ (-a) := by ring
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hMa hw)

theorem ball_bound {g : Space → ℝ} (hg : Continuous g) (R : ℝ) :
    ∃ M : ℝ, ∀ y : Space, ‖y‖ ≤ R → g y ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun y hy => ?_⟩
  have := hM y (by rw [Metric.mem_closedBall, dist_zero_right]; exact hy)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

theorem field_decay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∃ C : ℝ, ∀ y, ‖fieldOf P D β y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  obtain ⟨R, C, hR, hfar⟩ := field_far P hP D hD β
  obtain ⟨M, hM⟩ := ball_bound (field_contDiff P hP D hD β).continuous.norm R
  exact weight_glue (by norm_num) hR hM fun y hy => (hfar y hy).1

theorem field_gradDecay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∃ C : ℝ, ∀ y, ‖fderiv ℝ (fieldOf P D β) y‖ ≤ C * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  obtain ⟨R, C, hR, hfar⟩ := field_far P hP D hD β
  obtain ⟨M, hM⟩ := ball_bound ((field_contDiff P hP D hD β).continuous_fderiv (by norm_num)).norm R
  exact weight_glue (by norm_num) hR hM fun y hy => (hfar y hy).2.1

theorem field_ballSlope (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (R : ℝ) : ∃ C : NNReal, LipschitzOnWith C (fderiv ℝ (fieldOf P D β)) (Metric.closedBall 0 R) := by
  have hdiff : ∀ n ∈ D.modes, Differentiable ℝ (modeFieldOf P D β n) := fun n hn =>
    (mode_contDiff P hP D hD β n hn).differentiable (by norm_num)
  have hmode : ∀ n ∈ D.modes, ∀ R : ℝ, ∃ C : NNReal,
      LipschitzOnWith C (fderiv ℝ (modeFieldOf P D β n)) (Metric.closedBall 0 R) := by
    intro n hn R
    by_cases h0 : n = 0
    · subst h0
      exact modeFieldOf_fderiv_slopeOn_mean P hP hD β hn R
    · exact modeFieldOf_fderiv_slopeOn_wave P hP hD β n hn h0 R
  have heq : fderiv ℝ (fieldOf P D β) =
      fun z => ∑ n ∈ D.modes, (1 : ℝ) • fderiv ℝ (modeFieldOf P D β n) z := by
    rw [field_modes]
    exact FracInternal.fderiv_finset_sum_smul D.modes (fun _ => (1 : ℝ)) (fun n => modeFieldOf P D β n) hdiff
  rw [heq]
  exact FracInternal.slopeOn_finset_sum D.modes (fun _ => (1 : ℝ))
    (fun n => fderiv ℝ (modeFieldOf P D β n)) hmode R

theorem slope_glue {E : Type*} [NormedAddCommGroup E] {g : Space → E} {R M C : ℝ} {Cb : NNReal}
    (hb : LipschitzOnWith Cb g (Metric.closedBall 0 R)) (hM : ∀ y, ‖g y‖ ≤ M)
    (hfar : ∀ y : Space, R ≤ ‖y‖ → LipschitzOnWith (Real.toNNReal C) g (Metric.ball y 1)) :
    ∃ K : NNReal, LipschitzWith K g := by
  set K : NNReal := Cb + Real.toNNReal C + Real.toNNReal (2 * M) with hKdef
  have hK : (K : ℝ) = Cb + Real.toNNReal C + Real.toNNReal (2 * M) := by
    rw [hKdef, NNReal.coe_add, NNReal.coe_add]
  have c1 := NNReal.coe_nonneg Cb
  have c2 := NNReal.coe_nonneg (Real.toNNReal C)
  have c3 := NNReal.coe_nonneg (Real.toNNReal (2 * M))
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
  have h0 : 0 ≤ dist x z := dist_nonneg
  by_cases hd : 1 ≤ dist x z
  · calc dist (g x) (g z) ≤ ‖g x‖ + ‖g z‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hM x, hM z]
      _ ≤ (Real.toNNReal (2 * M) : ℝ) := Real.le_coe_toNNReal _
      _ ≤ K * 1 := by rw [hK]; linarith
      _ ≤ K * dist x z := mul_le_mul_of_nonneg_left hd K.2
  · rw [not_le] at hd
    have hCK : (Real.toNNReal C : ℝ) ≤ K := by rw [hK]; linarith
    by_cases hx : R ≤ ‖x‖
    · have hxx : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
      have hzx : z ∈ Metric.ball x 1 := by rw [Metric.mem_ball, dist_comm]; exact hd
      calc dist (g x) (g z) ≤ Real.toNNReal C * dist x z := (hfar x hx).dist_le_mul x hxx z hzx
        _ ≤ K * dist x z := mul_le_mul_of_nonneg_right hCK h0
    · by_cases hz : R ≤ ‖z‖
      · have hzz : z ∈ Metric.ball z 1 := Metric.mem_ball_self one_pos
        have hxz : x ∈ Metric.ball z 1 := by rw [Metric.mem_ball]; exact hd
        calc dist (g x) (g z) ≤ Real.toNNReal C * dist x z := (hfar z hz).dist_le_mul x hxz z hzz
          _ ≤ K * dist x z := mul_le_mul_of_nonneg_right hCK h0
      · rw [not_le] at hx hz
        have hxb : x ∈ Metric.closedBall (0 : Space) R := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hx.le
        have hzb : z ∈ Metric.closedBall (0 : Space) R := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hz.le
        calc dist (g x) (g z) ≤ Cb * dist x z := hb.dist_le_mul x hxb z hzb
          _ ≤ K * dist x z := mul_le_mul_of_nonneg_right (by rw [hK]; linarith) h0

theorem le_abs_of_weight {C w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : C * w ≤ |C| :=
  (mul_le_mul_of_nonneg_right (le_abs_self C) hw0).trans (mul_le_of_le_one_right (abs_nonneg C) hw1)

theorem field_gradSlope (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∃ K : NNReal, LipschitzWith K (fderiv ℝ (fieldOf P D β)) := by
  obtain ⟨R, C, hR, hfar⟩ := field_far P hP D hD β
  obtain ⟨C4, h4⟩ := field_gradDecay P hP D hD β
  obtain ⟨Cb, hb⟩ := field_ballSlope P hP D hD β R
  refine slope_glue (M := |C4|) (C := |C|) hb (fun y => (h4 y).trans (le_abs_of_weight
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_le_one_of_one_le_of_nonpos (by
      have := norm_nonneg y; linarith) (by norm_num)))) (fun y hy => ?_)
  refine (hfar y hy).2.2.weaken (Real.toNNReal_le_toNNReal ?_)
  exact le_abs_of_weight (Real.rpow_nonneg (norm_nonneg y) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (hR.trans hy) (by norm_num))

theorem field_secondDecay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∃ C : ℝ, ∀ᵐ y ∂volume, ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
  obtain ⟨R, C, hR, hfar⟩ := field_far P hP D hD β
  obtain ⟨K, hK⟩ := field_gradSlope P hP D hD β
  have hfar5 : ∀ y : Space, R ≤ ‖y‖ →
      ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ |C| * ‖y‖ ^ (-(5 : ℝ)) := by
    intro y hy
    have hw : 0 ≤ ‖y‖ ^ (-(5 : ℝ)) := Real.rpow_nonneg (norm_nonneg y) _
    refine (norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) (hfar y hy).2.2).trans ?_
    rw [Real.coe_toNNReal']
    exact max_le (mul_le_mul_of_nonneg_right (le_abs_self C) hw) (mul_nonneg (abs_nonneg C) hw)
  obtain ⟨K2, hK2⟩ := weight_glue (g := fun y => ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖) (a := 5)
    (M := K) (by norm_num) hR (fun y _ => norm_fderiv_le_of_lipschitz ℝ hK) hfar5
  exact ⟨K2, Filter.Eventually.of_forall hK2⟩

theorem turn0 (m : ℕ) (y : Space) : turnStep m y 0 = Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1 := by
  simp [turnStep]

theorem turn1 (m : ℕ) (y : Space) : turnStep m y 1 = Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1 := by
  simp [turnStep]

theorem turn2 (m : ℕ) (y : Space) : turnStep m y 2 = y 2 := by
  simp [turnStep]

theorem norm_turn (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, turn0, turn1, turn2]
  have h := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * h

theorem angle_turn (m : ℕ) (hm : 0 < m) (n : ℤ) (y : Space) :
    ∃ K : ℤ, (((n * m : ℤ) : ℝ)) * angleOf (turnStep m y) = ((n * m : ℤ) : ℝ) * angleOf y + 2 * Real.pi * K := by
  set w : ℂ := (Real.cos (2 * Real.pi / m) : ℂ) + (Real.sin (2 * Real.pi / m) : ℂ) * Complex.I with hw
  have hrot : (⟨turnStep m y 0, turnStep m y 1⟩ : ℂ) = w * ⟨y 0, y 1⟩ := by
    apply Complex.ext <;> simp only [hw, turn0, turn1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  unfold angleOf
  rw [hrot]
  by_cases hz : (⟨y 0, y 1⟩ : ℂ) = 0
  · exact ⟨0, by rw [hz]; simp⟩
  have hw0 : w ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [hw, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] at h1 h2
    have := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
    rw [h1, h2] at this
    norm_num at this
  have ha := Complex.arg_mul_coe_angle hw0 hz
  have hwarg : (Complex.arg w : Real.Angle) = ((2 * Real.pi / m : ℝ) : Real.Angle) := by
    have := Complex.arg_cos_add_sin_mul_I_coe_angle ((2 * Real.pi / m : ℝ) : Real.Angle)
    simpa [Real.Angle.cos_coe, Real.Angle.sin_coe, hw] using this
  rw [hwarg, ← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at ha
  obtain ⟨j, hj⟩ := ha
  refine ⟨n + n * m * j, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : Complex.arg (w * ⟨y 0, y 1⟩) = 2 * Real.pi / m + Complex.arg ⟨y 0, y 1⟩ + 2 * Real.pi * j := by
    linarith
  rw [e]
  push_cast
  field_simp
  ring

theorem phase_turn (P : ChartParams) (hm : 0 < P.m) (n : ℤ) (β : ℝ) (y : Space) :
    modePhase P n β (turnStep P.m y) = modePhase P n β y := by
  obtain ⟨K, hK⟩ := angle_turn P.m hm n y
  unfold modePhase logPhase
  rw [norm_turn, hK]
  have e : Complex.I * (((((n * P.m : ℤ) : ℝ) * angleOf y + 2 * Real.pi * K) +
      n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ) =
      Complex.I * (((((n * P.m : ℤ) : ℝ) * angleOf y) + n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ) +
        (K : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem ofComponents_apply (w : Fin 3 → ℝ) (i : Fin 3) : ofComponents w i = w i := by
  fin_cases i <;> simp [ofComponents]

theorem re_lin (d : ℂ) (s : Finset ℤ) (ph R0 R1 R2 : ℤ → ℂ) (r p a : ℝ) :
    (d * ∑ n ∈ s, ph n * (R0 n * r + R1 n * p + R2 n * a)).re =
      (d * ∑ n ∈ s, ph n * R0 n).re * r + (d * ∑ n ∈ s, ph n * R1 n).re * p +
        (d * ∑ n ∈ s, ph n * R2 n).re * a := by
  have h : ∑ n ∈ s, ph n * (R0 n * r + R1 n * p + R2 n * a) =
      (∑ n ∈ s, ph n * R0 n) * r + (∑ n ∈ s, ph n * R1 n) * p + (∑ n ∈ s, ph n * R2 n) * a := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h]
  simp only [mul_add, ← mul_assoc, Complex.add_re, Complex.re_mul_ofReal]

def coefOf (P : ChartParams) (D : FieldData) (β : ℝ) (k : Fin 3) (y : Space) : ℝ :=
  (((decayFactor P y : ℝ) : ℂ) * ∑ n ∈ D.modes, modePhase P n β y *
    reducedField P D n β (chartT P y) (heightRatio y) k).re

theorem field_comp (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space) (i : Fin 3) :
    fieldOf P D β y i = coefOf P D β 0 y * radialVec y i + coefOf P D β 1 y * polarVecQ y i +
      coefOf P D β 2 y * azimVecQ y i := by
  unfold fieldOf
  rw [ofComponents_apply, re_lin]
  rfl

theorem coef_turn (P : ChartParams) (hm : 0 < P.m) (D : FieldData) (β : ℝ) (k : Fin 3) (y : Space) :
    coefOf P D β k (turnStep P.m y) = coefOf P D β k y := by
  have hT : chartT P (turnStep P.m y) = chartT P y := by simp [chartT, norm_turn]
  have hH : heightRatio (turnStep P.m y) = heightRatio y := by simp [heightRatio, norm_turn, turn2]
  have hD : decayFactor P (turnStep P.m y) = decayFactor P y := by simp [decayFactor, chartS, hT]
  simp only [coefOf, hT, hH, hD, phase_turn P hm]

theorem field_turn (P : ChartParams) (hm : 0 < P.m) (D : FieldData) (β : ℝ) (y : Space) :
    fieldOf P D β (turnStep P.m y) = turnStep P.m (fieldOf P D β y) := by
  have hH : heightRatio (turnStep P.m y) = heightRatio y := by simp [heightRatio, norm_turn, turn2]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [field_comp, turn0, field_comp, field_comp, coef_turn P hm, coef_turn P hm, coef_turn P hm]
    simp only [radialVec, polarVecQ, azimVecQ, qOf, hH, norm_turn, turn0, turn1, turn2]
    simp
    ring
  · simp only [Fin.mk_one]
    rw [field_comp, turn1, field_comp, field_comp, coef_turn P hm, coef_turn P hm, coef_turn P hm]
    simp only [radialVec, polarVecQ, azimVecQ, qOf, hH, norm_turn, turn0, turn1, turn2]
    simp
    ring
  · show fieldOf P D β (turnStep P.m y) 2 = turnStep P.m (fieldOf P D β y) 2
    rw [field_comp, turn2, field_comp, coef_turn P hm, coef_turn P hm, coef_turn P hm]
    simp only [radialVec, polarVecQ, azimVecQ, qOf, hH, norm_turn, turn0, turn1, turn2]
    simp

theorem cellIndex_lt (l : List ℝ) (hf : l.head? = some 0) (hl : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  unfold cellIndex cellCount
  match l, hf, hl with
  | [a], hf, hl => simp at hf hl; linarith
  | a :: b :: rest, _, _ =>
    have := List.length_filter_le (fun c => decide (c ≤ u)) ((List.drop 1 (a :: b :: rest)).dropLast)
    simp only [List.drop_one, List.tail_cons, List.length_dropLast, List.length_cons] at this ⊢
    omega

theorem cellIndex_zero (l : List ℝ) (hs : l.Pairwise (· < ·)) (hf : l.head? = some 0) : cellIndex l 0 = 0 := by
  unfold cellIndex
  match l, hs, hf with
  | a :: rest, hs, hf =>
    simp only [List.head?_cons, Option.some.injEq] at hf
    subst hf
    rw [List.pairwise_cons] at hs
    simp only [List.drop_one, List.tail_cons, List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq, not_le]
    intro c hc
    exact hs.1 c (List.dropLast_subset _ hc)

theorem evalHalf_zero (S : Spline) (a b : ℕ) (hS : IsSplineClass a b true S) (t : ℝ) : S.evalHalf t 0 = 0 := by
  unfold Spline.evalHalf
  rw [cellIndex_zero _ hS.mesh.x_sorted hS.mesh.x_first]
  have hi := cellIndex_lt _ hS.mesh.t_first hS.mesh.t_last t
  have hp := hS.parity _ hi 0 (Nat.zero_le _) (by simp)
  simp only [xDeriv, Function.iterate_zero, id] at hp
  have e : MvPolynomial.eval ![(t : ℂ), ((0 : ℝ) : ℂ)] (atSecond 0 (S.piece (cellIndex S.mesh.tBreaks t) 0)) =
      MvPolynomial.eval ![(t : ℂ), ((0 : ℝ) : ℂ)] (S.piece (cellIndex S.mesh.tBreaks t) 0) := by
    unfold atSecond
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) ![(t : ℂ), ((0 : ℝ) : ℂ)] _ =
      MvPolynomial.eval₂Hom (RingHom.id ℂ) ![(t : ℂ), ((0 : ℝ) : ℂ)] _
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext k
    fin_cases k <;> simp
  rw [← e, hp]
  simp

theorem evalOdd_neg (S : Spline) (h0 : ∀ t, S.evalHalf t 0 = 0) (t x : ℝ) : S.eval true t (-x) = -S.eval true t x := by
  unfold Spline.eval
  rcases lt_trichotomy x 0 with h | h | h
  · have h' : ¬ (-x < 0) := by linarith
    simp [h, h', abs_neg]
  · subst h
    simp [h0]
  · have h' : -x < 0 := by linarith
    have h'' : ¬ (x < 0) := by linarith
    simp [h', h'', abs_neg]

theorem evalEven_neg (S : Spline) (t x : ℝ) : S.eval false t (-x) = S.eval false t x := by
  simp [Spline.eval, abs_neg]

theorem hd_odd (g : ℝ → ℝ → ℂ) (hg : ∀ t x, g t (-x) = -g t x) (t x : ℝ) :
    heightDeriv g t (-x) = heightDeriv g t x := by
  unfold heightDeriv
  have e : (fun x' => g t x') = -(fun x' => g t (-x')) := funext fun x' => by simp [hg]
  conv_lhs => rw [e]
  rw [deriv.neg, deriv_comp_neg (f := g t), neg_neg, neg_neg]

theorem hd_even (g : ℝ → ℝ → ℂ) (hg : ∀ t x, g t (-x) = g t x) (t x : ℝ) :
    heightDeriv g t (-x) = -heightDeriv g t x := by
  unfold heightDeriv
  have e : (fun x' => g t x') = fun x' => g t (-x') := funext fun x' => by rw [hg]
  conv_lhs => rw [e]
  rw [deriv_comp_neg (f := g t), neg_neg]

theorem ts_odd (P : ChartParams) (n : ℤ) (β : ℝ) (g : ℝ → ℝ → ℂ) (hg : ∀ t x, g t (-x) = -g t x) (t x : ℝ) :
    twistedScale P n β g t (-x) = -twistedScale P n β g t x := by
  unfold twistedScale radialScale
  have e : (fun t' => g t' (-x)) = -(fun t' => g t' x) := funext fun t' => by simp [hg]
  rw [e, deriv.neg, hg]
  ring

theorem ts_even (P : ChartParams) (n : ℤ) (β : ℝ) (g : ℝ → ℝ → ℂ) (hg : ∀ t x, g t (-x) = g t x) (t x : ℝ) :
    twistedScale P n β g t (-x) = twistedScale P n β g t x := by
  unfold twistedScale radialScale
  have e : (fun t' => g t' (-x)) = fun t' => g t' x := funext fun t' => hg t' x
  rw [e, hg]

theorem reduced_neg (P : ChartParams) (D : FieldData) (hD : IsFieldData P 3 D) (n : ℤ) (hn : n ∈ D.modes)
    (β t x : ℝ) :
    reducedField P D n β t (-x) 0 = reducedField P D n β t x 0 ∧
      reducedField P D n β t (-x) 1 = -reducedField P D n β t x 1 ∧
      reducedField P D n β t (-x) 2 = reducedField P D n β t x 2 := by
  by_cases h0 : n = 0
  · subst h0
    have hΨ := evalOdd_neg _ (evalHalf_zero _ 2 2 (hD.meanStream hn).1)
    have hG := evalEven_neg (D.amp 0).swirlAmp
    have o1 : ∀ t' x', (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t' (-x') =
        -(fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t' x' := by
      intro t' x'
      simp only [hΨ, neg_sq, mul_neg]
    have o2 : ∀ t' x', (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') t' (-x') =
        -(fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') t' x' := by
      intro t' x'
      simp only [hΨ, mul_neg]
    refine ⟨?_, ?_, ?_⟩
    · simp only [reducedField, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hd_odd _ o1]
    · simp only [reducedField, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [ts_odd P 0 β _ o2, hΨ]
      ring
    · simp only [reducedField, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hG]
  · have hB := evalOdd_neg _ (evalHalf_zero _ 1 2 (hD.wavePolar n hn h0))
    have hA := evalEven_neg (D.amp n).radialAmp
    have e1 : ∀ t' x', (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x') t' (-x') =
        (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x') t' x' := by
      intro t' x'
      simp only [hA, neg_sq]
    have o1 : ∀ t' x', (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t' (-x') =
        -(fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t' x' := by
      intro t' x'
      simp only [hB, neg_sq, mul_neg]
    refine ⟨?_, ?_, ?_⟩
    · simp only [reducedField, h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact e1 t x
    · simp only [reducedField, h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      simp only [hB, neg_sq, mul_neg]
    · simp only [reducedField, h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [ts_even P n β _ e1, hd_odd _ o1]
      simp only [hA, neg_sq]

theorem mir0 (y : Space) : mirror y 0 = y 0 := by simp [mirror]

theorem mir1 (y : Space) : mirror y 1 = y 1 := by simp [mirror]

theorem mir2 (y : Space) : mirror y 2 = -y 2 := by simp [mirror]

theorem norm_mirror (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, mir0, mir1, mir2, neg_sq]

theorem coef_mirror (P : ChartParams) (D : FieldData) (hD : IsFieldData P 3 D) (β : ℝ) (y : Space) :
    coefOf P D β 0 (mirror y) = coefOf P D β 0 y ∧ coefOf P D β 1 (mirror y) = -coefOf P D β 1 y ∧
      coefOf P D β 2 (mirror y) = coefOf P D β 2 y := by
  have hT : chartT P (mirror y) = chartT P y := by simp [chartT, norm_mirror]
  have hH : heightRatio (mirror y) = -heightRatio y := by simp [heightRatio, norm_mirror, mir2, neg_div]
  have hDf : decayFactor P (mirror y) = decayFactor P y := by simp [decayFactor, chartS, hT]
  have hPh : ∀ n, modePhase P n β (mirror y) = modePhase P n β y := by
    intro n
    simp [modePhase, angleOf, logPhase, mir0, mir1, norm_mirror]
  have s0 : ∑ n ∈ D.modes, modePhase P n β (mirror y) * reducedField P D n β (chartT P y) (-heightRatio y) 0 =
      ∑ n ∈ D.modes, modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 0 :=
    Finset.sum_congr rfl fun n hn => by rw [hPh, (reduced_neg P D hD n hn β _ _).1]
  have s1 : ∑ n ∈ D.modes, modePhase P n β (mirror y) * reducedField P D n β (chartT P y) (-heightRatio y) 1 =
      -∑ n ∈ D.modes, modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n hn => by rw [hPh, (reduced_neg P D hD n hn β _ _).2.1, mul_neg]
  have s2 : ∑ n ∈ D.modes, modePhase P n β (mirror y) * reducedField P D n β (chartT P y) (-heightRatio y) 2 =
      ∑ n ∈ D.modes, modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 2 :=
    Finset.sum_congr rfl fun n hn => by rw [hPh, (reduced_neg P D hD n hn β _ _).2.2]
  refine ⟨?_, ?_, ?_⟩
  · unfold coefOf
    rw [hT, hH, hDf, s0]
  · unfold coefOf
    rw [hT, hH, hDf, s1, mul_neg, Complex.neg_re]
  · unfold coefOf
    rw [hT, hH, hDf, s2]

theorem field_mirror' (P : ChartParams) (D : FieldData) (hD : IsFieldData P 3 D) (β : ℝ) (y : Space) :
    fieldOf P D β (mirror y) = mirror (fieldOf P D β y) := by
  have hH : heightRatio (mirror y) = -heightRatio y := by simp [heightRatio, norm_mirror, mir2, neg_div]
  obtain ⟨c0, c1, c2⟩ := coef_mirror P D hD β y
  ext i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [field_comp, mir0, field_comp, c0, c1, c2]
    simp only [radialVec, polarVecQ, azimVecQ, qOf, hH, norm_mirror, mir0, mir1, mir2]
    simp
    ring
  · simp only [Fin.mk_one]
    rw [field_comp, mir1, field_comp, c0, c1, c2]
    simp only [radialVec, polarVecQ, azimVecQ, qOf, hH, norm_mirror, mir0, mir1, mir2]
    simp
    ring
  · show fieldOf P D β (mirror y) 2 = mirror (fieldOf P D β y) 2
    rw [field_comp, mir2, field_comp, c0, c1, c2]
    simp only [radialVec, polarVecQ, azimVecQ, qOf, hH, norm_mirror, mir0, mir1, mir2]
    simp
    ring

theorem field_mirror (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∀ y, fieldOf P D β (mirror y) = mirror (fieldOf P D β y) :=
  fun y => field_mirror' P D hD β y

theorem field_class (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) : ∀ y, fieldOf P D β (turnStep P.m y) = turnStep P.m (fieldOf P D β y) ∧
      fieldOf P D β (mirror y) = mirror (fieldOf P D β y) :=
  fun y => ⟨field_turn P hP.m_pos D β y, field_mirror P hP D hD β y⟩

theorem atomTerm_tail (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    {odd : Bool} (hS : IsAtomSpline odd S j) :
    ∃ K : ℝ, ∀ y, ‖atomTerm P j a M β S y‖ ≤ K * chartS P y ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := DualPartsInternal.tail_bound_split S hS.spline.mesh hS.at_infinity (decide (a = 0))
  refine ⟨K, fun y => ?_⟩
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have hsq : chartS P y = 1 - chartT P y := rfl
  unfold atomTerm
  rw [norm_mul, norm_mul]
  have e1 : ‖Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have e2 : ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr ?_)
    unfold qOf
    nlinarith [sq_nonneg (heightRatio y)]
  have e3 := hK _ _ ht0 ht1 hx
  rw [e1, one_mul, hsq]
  calc ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ * ‖S.eval (decide (a = 0)) (chartT P y) (heightRatio y)‖
      ≤ 1 * (K * (1 - chartT P y) ^ 2) := mul_le_mul e2 e3 (norm_nonneg _) zero_le_one
    _ = K * (1 - chartT P y) ^ 2 := one_mul _

theorem sum_tail {ι : Type*} (s : Finset ι) (f : ι → Space → ℂ) (w : Space → ℝ)
    (h : ∀ i ∈ s, ∃ K : ℝ, ∀ y, ‖f i y‖ ≤ K * w y) :
    ∃ K : ℝ, ∀ y, ‖∑ i ∈ s, f i y‖ ≤ K * w y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨K1, h1⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨K2, h2⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨K2 + K1, fun y => ?_⟩
    rw [Finset.sum_insert ha, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h2 y) (h1 y))

theorem decay_le_one (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    0 ≤ decayFactor P y ∧ decayFactor P y ≤ 1 := by
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have hs1 : chartS P y ≤ 1 := by
    have : chartS P y = 1 - chartT P y := rfl
    linarith
  exact ⟨Real.rpow_nonneg hs0.le _, Real.rpow_le_one hs0.le hs1 (by linarith [hP.eps_pos])⟩

theorem sq_weight (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    chartS P y ^ 2 ≤ max P.L0 1 ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have h1 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  rw [Real.rpow_neg h1.le, Real.rpow_two, ← div_eq_mul_inv, ← div_pow]
  exact pow_le_pow_left₀ hs0.le hsc 2

theorem norm_ofComponents_le (a b c : ℝ) : ‖ofComponents ![a, b, c]‖ ≤ |a| + |b| + |c| := by
  unfold ofComponents
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
    simp

theorem measurable_ofComponents3 {f g h : Space → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun y => ofComponents ![f y, g y, h y]) := by
  have e : (fun y => ofComponents ![f y, g y, h y]) =
      fun y => WithLp.toLp 2 (![f y, g y, h y] : Fin 3 → ℝ) := by
    funext y
    ext i
    fin_cases i <;> simp [ofComponents]
  rw [e]
  refine (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp ?_
  exact measurable_pi_iff.2 fun i => by fin_cases i <;> simpa

theorem atom_bound (P : ChartParams) (hP : IsChartParams P) (X : AtomData) (hX : IsAtomData P X) (β : ℝ) :
    AEStronglyMeasurable (atomOf P X β) volume ∧ ∃ C : ℝ, ∀ y, ‖atomOf P X β y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  have hd : Measurable (fun y : Space => decayFactor P y) := by
    unfold decayFactor chartS chartT
    fun_prop
  have hPm : Measurable (fun y => atomPlane P X β y) := by
    unfold atomPlane
    refine (Complex.measurable_ofReal.comp hd).mul (Measurable.add ?_ ?_)
    · exact Finset.measurable_sum _ fun j _ => DualPartsInternal.atom_measurable P j 1 _ β _
    · exact Finset.measurable_sum _ fun j _ =>
        Complex.continuous_conj.measurable.comp (DualPartsInternal.atom_measurable P j 1 _ β _)
  have hHm : Measurable (fun y => atomHeight P X β y) := by
    unfold atomHeight
    refine (Complex.measurable_ofReal.comp hd).mul ?_
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul (DualPartsInternal.atom_measurable P j 0 _ β _)
  refine ⟨(measurable_ofComponents3 (Complex.measurable_re.comp hPm) (Complex.measurable_im.comp hPm)
    (Complex.measurable_re.comp hHm)).aestronglyMeasurable, ?_⟩
  obtain ⟨K1, h1⟩ := sum_tail X.harmonics (fun j y => atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y)
    (fun y => chartS P y ^ 2) fun j hj => atomTerm_tail P hP j 1 _ β _ (hX.plus_shape j hj)
  obtain ⟨K2, h2⟩ := sum_tail (X.harmonics.filter (fun j => 1 ≤ j))
    (fun j y => (starRingEnd ℂ) (atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y))
    (fun y => chartS P y ^ 2) fun j hj => by
      rw [Finset.mem_filter] at hj
      obtain ⟨K, hK⟩ := atomTerm_tail P hP j 1 ((j : ℤ) * P.m - 1) β _ (hX.minus_shape j hj.1 hj.2)
      exact ⟨K, fun y => by rw [Complex.norm_conj]; exact hK y⟩
  obtain ⟨K3, h3⟩ := sum_tail X.harmonics
    (fun j y => ((if j = 0 then 1 else 2 : ℝ) : ℂ) * atomTerm P j 0 ((j : ℤ) * P.m) β (X.heightAmp j) y)
    (fun y => chartS P y ^ 2) fun j hj => by
      obtain ⟨K, hK⟩ := atomTerm_tail P hP j 0 ((j : ℤ) * P.m) β _ (hX.height_shape j hj)
      refine ⟨2 * |K|, fun y => ?_⟩
      have hs := sq_nonneg (chartS P y)
      have hc : ‖((if j = 0 then 1 else 2 : ℝ) : ℂ)‖ ≤ 2 := by
        split_ifs <;> norm_num
      rw [norm_mul]
      calc _ ≤ 2 * (|K| * chartS P y ^ 2) :=
            mul_le_mul hc ((hK y).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hs))
              (norm_nonneg _) (by norm_num)
        _ = 2 * |K| * chartS P y ^ 2 := by ring
  set c := max P.L0 1
  refine ⟨(2 * (|K1| + |K2|) + |K3|) * c ^ 2, fun y => ?_⟩
  obtain ⟨hd0, hd1⟩ := decay_le_one P hP y
  have hs := sq_nonneg (chartS P y)
  have hw := sq_weight P hP y
  have hplane : ‖atomPlane P X β y‖ ≤ (|K1| + |K2|) * chartS P y ^ 2 := by
    unfold atomPlane
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
    refine (mul_le_of_le_one_left (norm_nonneg _) hd1).trans ?_
    refine (norm_add_le _ _).trans ?_
    have a1 := (h1 y).trans (mul_le_mul_of_nonneg_right (le_abs_self K1) hs)
    have a2 := (h2 y).trans (mul_le_mul_of_nonneg_right (le_abs_self K2) hs)
    linarith
  have hheight : ‖atomHeight P X β y‖ ≤ |K3| * chartS P y ^ 2 := by
    unfold atomHeight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hd1).trans
      ((h3 y).trans (mul_le_mul_of_nonneg_right (le_abs_self K3) hs))
  have hK : 0 ≤ 2 * (|K1| + |K2|) + |K3| := by positivity
  unfold atomOf
  refine (norm_ofComponents_le _ _ _).trans ?_
  have r1 := Complex.abs_re_le_norm (atomPlane P X β y)
  have r2 := Complex.abs_im_le_norm (atomPlane P X β y)
  have r3 := Complex.abs_re_le_norm (atomHeight P X β y)
  calc |(atomPlane P X β y).re| + |(atomPlane P X β y).im| + |(atomHeight P X β y).re|
      ≤ (2 * (|K1| + |K2|) + |K3|) * chartS P y ^ 2 := by nlinarith
    _ ≤ (2 * (|K1| + |K2|) + |K3|) * (c ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left hw hK
    _ = _ := by ring

theorem cellIndex_le_length (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  refine (List.length_filter_le _ _).trans ?_
  simp only [List.length_dropLast, List.length_drop]
  omega

theorem spline_bound (S : Spline) (odd : Bool) :
    ∃ B : ℝ, ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖S.eval odd t x‖ ≤ B := by
  choose B hB0 hB using fun ik : ℕ × ℕ => DualPartsInternal.poly_bound (S.piece ik.1 ik.2)
  set R := Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1) with hR
  refine ⟨∑ ik ∈ R, B ik, fun t x ht hx => ?_⟩
  have hnorm : ‖S.eval odd t x‖ = ‖S.evalHalf t |x|‖ := by
    unfold Spline.eval
    split_ifs <;> simp
  rw [hnorm]
  have hmem : (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks |x|) ∈ R := by
    rw [hR, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (cellIndex_le_length _ _), Nat.lt_succ_of_le (cellIndex_le_length _ _)⟩
  unfold Spline.evalHalf
  exact (hB (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks |x|) t |x| ht (by rwa [abs_abs])).trans
    (Finset.single_le_sum (fun ik _ => hB0 ik) hmem)

theorem norm_modePhase (P : ChartParams) (n : ℤ) (β : ℝ) (y : Space) : ‖modePhase P n β y‖ = 1 := by
  unfold modePhase
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem modePhase_measurable (P : ChartParams) (n : ℤ) (β : ℝ) : Measurable (fun y => modePhase P n β y) := by
  have hA : Measurable (fun y : Space => angleOf y) := by
    unfold angleOf
    have h : Measurable (fun y : Space => ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)) := by fun_prop
    have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y : Space => ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
      funext y
      exact Complex.mk_eq_add_mul_I _ _
    refine Complex.measurable_arg.comp ?_
    rw [e]
    exact h
  have hL : Measurable (fun y : Space => logPhase P y) := by
    unfold logPhase
    fun_prop
  unfold modePhase
  fun_prop

theorem evalChart_measurable (P : ChartParams) (S : Spline) (odd : Bool) :
    Measurable (fun y : Space => S.eval odd (chartT P y) (heightRatio y)) := by
  have h1 : Measurable (fun y : Space => (chartT P y, heightRatio y)) := by
    unfold chartT heightRatio
    fun_prop
  exact (DualPartsInternal.eval_measurable S odd).comp h1

theorem shape_measurable (P : ChartParams) (low high axis : ℕ) (S : Spline) :
    Measurable (fun y => pressureShape P low high axis S y) := by
  have hE := evalChart_measurable P S false
  have hc : Measurable (fun y : Space => chartT P y ^ low * chartS P y ^ high * qOf y ^ axis) := by
    unfold chartS chartT qOf heightRatio
    fun_prop
  unfold pressureShape
  exact (Complex.measurable_ofReal.comp hc).mul hE

theorem shape_bound (P : ChartParams) (hP : IsChartParams P) (low high axis : ℕ) (hh : 2 ≤ high) (S : Spline) :
    ∃ B : ℝ, ∀ y, ‖pressureShape P low high axis S y‖ ≤ B * chartS P y ^ 2 := by
  obtain ⟨B, hB⟩ := spline_bound S false
  refine ⟨|B|, fun y => ?_⟩
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have hs1 : chartS P y ≤ 1 := by
    have : chartS P y = 1 - chartT P y := rfl
    linarith
  have hq0 : 0 ≤ qOf y := by
    unfold qOf
    nlinarith [abs_le.mp hx, sq_abs (heightRatio y)]
  have hq1 : qOf y ≤ 1 := by
    unfold qOf
    nlinarith [sq_nonneg (heightRatio y)]
  have he := hB (chartT P y) (heightRatio y) (by rw [abs_of_nonneg ht0]; linarith) hx
  unfold pressureShape
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : chartT P y ^ low ≤ 1 := pow_le_one₀ ht0 ht1.le
  have h2 : chartS P y ^ high ≤ chartS P y ^ 2 := pow_le_pow_of_le_one hs0.le hs1 hh
  have h3 : qOf y ^ axis ≤ 1 := pow_le_one₀ hq0 hq1
  have hc : chartT P y ^ low * chartS P y ^ high * qOf y ^ axis ≤ chartS P y ^ 2 := by
    calc chartT P y ^ low * chartS P y ^ high * qOf y ^ axis ≤ 1 * chartS P y ^ 2 * 1 := by
          gcongr
      _ = chartS P y ^ 2 := by ring
  calc chartT P y ^ low * chartS P y ^ high * qOf y ^ axis * ‖S.eval false (chartT P y) (heightRatio y)‖
      ≤ chartS P y ^ 2 * |B| := mul_le_mul hc (he.trans (le_abs_self B)) (norm_nonneg _) (sq_nonneg _)
    _ = |B| * chartS P y ^ 2 := by ring

theorem chartMap_contDiffAt (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (fun z : Space => chartT P z) y ∧ ContDiffAt ℝ 1 (fun z : Space => heightRatio z) y := by
  have hn : ContDiffAt ℝ 1 (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy
  have hpos : ‖y‖ + P.L0 ≠ 0 := by
    have := hP.L0_pos
    positivity
  refine ⟨?_, ?_⟩
  · unfold chartT
    exact hn.div (hn.add contDiffAt_const) hpos
  · unfold heightRatio
    have hc : ContDiffAt ℝ 1 (fun z : Space => z 2) y :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffAt
    exact hc.div hn (norm_ne_zero_iff.2 hy)

theorem phase_contDiffAt (P : ChartParams) (n : ℤ) (β : ℝ) {y : Space} (hy1 : y 1 ≠ 0) :
    ContDiffAt ℝ 1 (fun z => modePhase P n β z) y := by
  have hslit : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using hy1
  have hc : ∀ i : Fin 3, ContDiffAt ℝ 1 (fun z : Space => z i) y := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have hcpx : ContDiffAt ℝ 1 (fun z : Space => ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) y :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hc 0)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp y (hc 1)).mul contDiffAt_const)
  have hA : ContDiffAt ℝ 1 (fun z : Space => angleOf z) y := by
    have h1 : ContDiffAt ℝ 1
        (fun z : Space => Complex.imCLM (Complex.log ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I))) y :=
      Complex.imCLM.contDiff.contDiffAt.comp y
        (ContDiffAt.comp (f := fun z : Space => ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) y
          ((Complex.contDiffAt_log hslit).restrict_scalars ℝ) hcpx)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [angleOf, Complex.imCLM_apply, Complex.log_im]
    rw [Complex.mk_eq_add_mul_I]
  have hlogpos : 1 + ‖y‖ ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  have hL : ContDiffAt ℝ 1 (fun z : Space => logPhase P z) y := by
    unfold logPhase
    exact contDiffAt_const.mul ((contDiffAt_const.add ((contDiff_norm_sq ℝ).contDiffAt.div_const _)).log hlogpos)
  unfold modePhase
  refine Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y ?_))
  exact (contDiffAt_const.mul hA).add (contDiffAt_const.mul hL)

theorem evalChart_differentiableAt (P : ChartParams) (hP : IsChartParams P) (S : Spline) {y : Space}
    (hy2 : y 2 ≠ 0) (ht : chartT P y ∉ S.mesh.tBreaks) (hx : |heightRatio y| ∉ S.mesh.xBreaks) :
    DifferentiableAt ℝ (fun z : Space => S.eval false (chartT P z) (heightRatio z)) y := by
  have hy : y ≠ 0 := fun h => hy2 (by simp [h])
  have hx0 : heightRatio y ≠ 0 := div_ne_zero hy2 (norm_ne_zero_iff.2 hy)
  obtain ⟨Q, hQ, hev⟩ := FracInternal.spline_eventually_poly S false _ _ ht hx hx0
  obtain ⟨h1, h2⟩ := chartMap_contDiffAt P hP hy
  have hm : ContDiffAt ℝ 1 (fun z : Space => ((chartT P z, heightRatio z) : ℝ × ℝ)) y := h1.prodMk h2
  have hQd : DifferentiableAt ℝ (fun z : Space => Q (chartT P z, heightRatio z)) y :=
    ((hQ.differentiable (by simp)) _).comp y (hm.differentiableAt (by norm_num))
  refine hQd.congr_of_eventuallyEq ?_
  filter_upwards [hm.continuousAt.tendsto.eventually hev] with z hz
  exact hz

theorem pressure_diff (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (β : ℝ) :
    ∀ᵐ y ∂volume, DifferentiableAt ℝ (pressureOf P D β) y := by
  have hgen : ∀ᵐ y ∂(volume : Measure Space), ∀ n ∈ D.modes,
      (chartT P y ∉ (D.firstAmp n).mesh.tBreaks ∧ |heightRatio y| ∉ (D.firstAmp n).mesh.xBreaks) ∧
      (chartT P y ∉ (D.secondAmp n).mesh.tBreaks ∧ |heightRatio y| ∉ (D.secondAmp n).mesh.xBreaks) := by
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [FracInternal.ae_generic P hP.L0_pos (D.firstAmp n).mesh.tBreaks (D.firstAmp n).mesh.xBreaks,
      FracInternal.ae_generic P hP.L0_pos (D.secondAmp n).mesh.tBreaks (D.secondAmp n).mesh.xBreaks] with y h1 h2
    exact ⟨⟨h1.2.2.2.1, h1.2.2.2.2⟩, ⟨h2.2.2.2.1, h2.2.2.2.2⟩⟩
  filter_upwards [hgen, FracInternal.ae_coord_ne_zero 1, FracInternal.ae_coord_ne_zero 2] with y hy hy1 hy2
  have hy0 : y ≠ 0 := fun h => hy2 (by simp [h])
  obtain ⟨hT, hH⟩ := chartMap_contDiffAt P hP hy0
  have hS : 0 < chartS P y := (DualPartsInternal.chart_facts P hP y).2.2.2.1
  have hSd : ContDiffAt ℝ 1 (fun z => chartS P z) y := by
    unfold chartS
    exact contDiffAt_const.sub hT
  have hD1 : ContDiffAt ℝ 1 (fun z => decayFactor P z) y := by
    unfold decayFactor
    exact hSd.rpow_const_of_ne hS.ne'
  have hdec : DifferentiableAt ℝ (fun z => ((decayFactor P z : ℝ) : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp y hD1).differentiableAt (by norm_num)
  have hdec2 : DifferentiableAt ℝ (fun z => ((decayFactor P z ^ 2 : ℝ) : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hD1.pow 2)).differentiableAt (by norm_num)
  have hph : ∀ n, DifferentiableAt ℝ (fun z => modePhase P n β z) y := fun n =>
    (phase_contDiffAt P n β hy1).differentiableAt (by norm_num)
  have hq : ContDiffAt ℝ 1 (fun z => qOf z) y := by
    unfold qOf
    exact contDiffAt_const.sub (hH.pow 2)
  have hshape : ∀ (low high axis : ℕ) (S : Spline), chartT P y ∉ S.mesh.tBreaks →
      |heightRatio y| ∉ S.mesh.xBreaks → DifferentiableAt ℝ (fun z => pressureShape P low high axis S z) y := by
    intro low high axis S ht hx
    have hc : ContDiffAt ℝ 1 (fun z : Space => chartT P z ^ low * chartS P z ^ high * qOf z ^ axis) y :=
      ((hT.pow low).mul (hSd.pow high)).mul (hq.pow axis)
    unfold pressureShape
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp y hc).differentiableAt (by norm_num)).mul
      (evalChart_differentiableAt P hP S hy2 ht hx)
  unfold pressureOf
  refine Complex.reCLM.differentiableAt.comp y (DifferentiableAt.fun_sum fun n hn => ?_)
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hy n hn
  exact ((hdec.mul (hph n)).mul (hshape _ _ _ _ h1 h2)).add ((hdec2.mul (hph n)).mul (hshape _ _ _ _ h3 h4))

theorem pressure_slope (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) :
    ∃ K : ℝ, ∀ᵐ y ∂volume, ‖fderiv ℝ (pressureOf P D β) y‖ ≤ K * chartS P y ^ 2 / ‖y‖ := by
  classical
  set T : ℤ → Space → ℂ := fun n z => ((decayFactor P z : ℝ) : ℂ) * modePhase P n β z *
      pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) z +
    ((decayFactor P z ^ 2 : ℝ) : ℂ) * modePhase P n β z *
      pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) z with hT
  have hex : ∀ n : ℤ, ∃ K : ℝ, n ∈ D.modes → ∀ᵐ y ∂volume,
      DifferentiableAt ℝ (T n) y ∧ ‖fderiv ℝ (T n) y‖ ≤ K * chartS P y ^ 2 / ‖y‖ := by
    intro n
    by_cases hn : n ∈ D.modes
    · have hax : n ≠ 0 → 1 ≤ D.axisOrder n := hD.low_axis_ge n hn
      obtain ⟨K1, h1⟩ := PressureOpen.term_slope P hP n β 1 (D.firstLow n) D.firstHigh (D.axisOrder n)
        (D.firstAmp n) (hD.amp_class n hn).1 hD.high_ge.1 hax
      obtain ⟨K2, h2⟩ := PressureOpen.term_slope P hP n β 2 (D.secondLow n) D.secondHigh (D.axisOrder n)
        (D.secondAmp n) (hD.amp_class n hn).2 hD.high_ge.2 hax
      simp only [pow_one] at h1
      refine ⟨K1 + K2, fun _ => ?_⟩
      filter_upwards [h1, h2] with y hy1 hy2
      have hA := hy1.1.hasFDerivAt
      have hB := hy2.1.hasFDerivAt
      have hS0 := hA.add hB
      have hS : HasFDerivAt (T n) _ y := hS0
      refine ⟨hS.differentiableAt, ?_⟩
      rw [hS.fderiv]
      refine (norm_add_le _ _).trans ?_
      have := add_le_add hy1.2 hy2.2
      rw [add_mul, add_div]
      exact this
    · exact ⟨0, fun h => absurd h hn⟩
  choose K hK using hex
  refine ⟨∑ n ∈ D.modes, |K n|, ?_⟩
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ n ∈ D.modes,
      DifferentiableAt ℝ (T n) y ∧ ‖fderiv ℝ (T n) y‖ ≤ K n * chartS P y ^ 2 / ‖y‖ := by
    rw [Filter.eventually_all_finset]
    exact fun n hn => hK n hn
  filter_upwards [hall] with y hy
  have hsum : HasFDerivAt (fun z => ∑ n ∈ D.modes, T n z) (∑ n ∈ D.modes, fderiv ℝ (T n) y) y :=
    HasFDerivAt.fun_sum fun n hn => (hy n hn).1.hasFDerivAt
  have hre : HasFDerivAt (pressureOf P D β) (Complex.reCLM.comp (∑ n ∈ D.modes, fderiv ℝ (T n) y)) y :=
    Complex.reCLM.hasFDerivAt.comp y hsum
  rw [hre.fderiv]
  have hw : 0 ≤ chartS P y ^ 2 / ‖y‖ := div_nonneg (sq_nonneg _) (norm_nonneg _)
  have hb := norm_sum_le_weight D.modes (fun n => fderiv ℝ (T n) y) K (chartS P y ^ 2 / ‖y‖) hw
    fun n hn => by rw [← mul_div_assoc]; exact (hy n hn).2
  calc ‖Complex.reCLM.comp (∑ n ∈ D.modes, fderiv ℝ (T n) y)‖
      ≤ ‖Complex.reCLM‖ * ‖∑ n ∈ D.modes, fderiv ℝ (T n) y‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((∑ n ∈ D.modes, |K n|) * (chartS P y ^ 2 / ‖y‖)) := by
        rw [Complex.reCLM_norm]
        exact mul_le_mul_of_nonneg_left hb zero_le_one
    _ = (∑ n ∈ D.modes, |K n|) * chartS P y ^ 2 / ‖y‖ := by ring

theorem pressure_measurable (P : ChartParams) (D : PressureData) (β : ℝ) : Measurable (pressureOf P D β) := by
  have hd : Measurable (fun y : Space => decayFactor P y) := by
    unfold decayFactor chartS chartT
    fun_prop
  unfold pressureOf
  refine Complex.measurable_re.comp (Finset.measurable_sum _ fun n _ => ?_)
  exact (((Complex.measurable_ofReal.comp hd).mul (modePhase_measurable P n β)).mul (shape_measurable P _ _ _ _)).add
    (((Complex.measurable_ofReal.comp (hd.pow_const 2)).mul (modePhase_measurable P n β)).mul
      (shape_measurable P _ _ _ _))

theorem pressure_bounded (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) : ∃ M : ℝ, ∀ y, |pressureOf P D β y| ≤ M := by
  obtain ⟨K, hK⟩ := sum_tail D.modes (fun n y => ((decayFactor P y : ℝ) : ℂ) * modePhase P n β y *
      pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y +
      ((decayFactor P y ^ 2 : ℝ) : ℂ) * modePhase P n β y *
        pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)
    (fun y => chartS P y ^ 2) fun n _ => by
      obtain ⟨B1, h1⟩ := shape_bound P hP (D.firstLow n) D.firstHigh (D.axisOrder n) hD.high_ge.1 (D.firstAmp n)
      obtain ⟨B2, h2⟩ := shape_bound P hP (D.secondLow n) D.secondHigh (D.axisOrder n) hD.high_ge.2 (D.secondAmp n)
      refine ⟨|B1| + |B2|, fun y => ?_⟩
      obtain ⟨hd0, hd1⟩ := decay_le_one P hP y
      have hs := sq_nonneg (chartS P y)
      have hd2 : decayFactor P y ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_modePhase, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd0, abs_of_nonneg (by positivity)]
      have a1 := (h1 y).trans (mul_le_mul_of_nonneg_right (le_abs_self B1) hs)
      have a2 := (h2 y).trans (mul_le_mul_of_nonneg_right (le_abs_self B2) hs)
      have n1 := norm_nonneg (pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y)
      have n2 := norm_nonneg (pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)
      nlinarith
  refine ⟨|K|, fun y => ?_⟩
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have hs1 : chartS P y ≤ 1 := by
    have : chartS P y = 1 - chartT P y := rfl
    linarith
  have hs2 : chartS P y ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  unfold pressureOf
  refine (Complex.abs_re_le_norm _).trans ((hK y).trans ?_)
  calc K * chartS P y ^ 2 ≤ |K| * chartS P y ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
    _ ≤ |K| * 1 := mul_le_mul_of_nonneg_left hs2 (abs_nonneg K)
    _ = |K| := mul_one _

theorem pressure_weak (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) :
    Reduction.IsWeakScalarGradientOf (pressureOf P D β) (fun y => gradientAt (pressureOf P D β) y) := by
  obtain ⟨K, hK⟩ := pressure_slope P hP D hD β
  obtain ⟨M, hM⟩ := pressure_bounded P hP D hD β
  refine PuncturedWeakInternal.weak_of_punctured (M := M) (C := |K|) (pressure_measurable P D β).aestronglyMeasurable hM
    (fun ε hε R => PressureOpen.pressure_annulusSlope P hP D hD β ε hε R) ?_
  filter_upwards [hK] with y hy
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have hs1 : chartS P y ≤ 1 := by
    have : chartS P y = 1 - chartT P y := rfl
    linarith
  have hs2 : chartS P y ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  refine hy.trans ?_
  rw [mul_div_assoc, div_eq_mul_inv]
  have hi : 0 ≤ ‖y‖⁻¹ := inv_nonneg.2 (norm_nonneg y)
  calc K * (chartS P y ^ 2 * ‖y‖⁻¹) ≤ |K| * (chartS P y ^ 2 * ‖y‖⁻¹) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (mul_nonneg (sq_nonneg _) hi)
    _ ≤ |K| * (1 * ‖y‖⁻¹) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs2 hi) (abs_nonneg K)
    _ = |K| * ‖y‖⁻¹ := by ring

theorem slope_weight {s r c : ℝ} (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 1 ≤ c) (hsc : s ≤ c / (1 + r)) :
    s ^ 2 / r ≤ c ^ 2 * min (r⁻¹) (r ^ (-(3 : ℝ))) := by
  have e3 : r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    norm_cast
  rw [e3, mul_min_of_nonneg _ _ (sq_nonneg c)]
  have hsr : s ≤ c / r := hsc.trans (by gcongr; linarith)
  refine le_min ?_ ?_
  · rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (inv_nonneg.2 hr.le)
  · have h2 : s ^ 2 ≤ c ^ 2 / r ^ 2 := by
      rw [← div_pow]
      exact pow_le_pow_left₀ hs0 hsr 2
    calc s ^ 2 / r ≤ c ^ 2 / r ^ 2 / r := by gcongr
      _ = c ^ 2 * (r ^ 3)⁻¹ := by
        field_simp

theorem norm_gradientAt_le (p : Space → ℝ) (y : Space) : ‖gradientAt p y‖ ≤ 3 * ‖fderiv ℝ p y‖ := by
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖fderiv ℝ p y (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ p y‖ := by
    intro i
    have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
    rw [norm_smul, hu, mul_one]
    simpa [hu] using (fderiv ℝ p y).le_opNorm (unitVector i)
  calc ∑ i : Fin 3, ‖fderiv ℝ p y (unitVector i) • unitVector i‖ ≤ ∑ _i : Fin 3, ‖fderiv ℝ p y‖ :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖fderiv ℝ p y‖ := by simp

theorem pressure_gradBound (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) :
    ∃ C : ℝ, ∀ᵐ y ∂volume, ‖gradientAt (pressureOf P D β) y‖ ≤ C * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := by
  obtain ⟨K, hK⟩ := pressure_slope P hP D hD β
  refine ⟨3 * |K| * max P.L0 1 ^ 2, ?_⟩
  filter_upwards [hK, FracInternal.ae_coord_ne_zero 2] with y hy hy2
  have hy0 : y ≠ 0 := fun h => hy2 (by simp [h])
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  obtain ⟨ht0, ht1, hx, hs0, hsc⟩ := DualPartsInternal.chart_facts P hP y
  have hs1 : chartS P y ≤ 1 := by
    have : chartS P y = 1 - chartT P y := rfl
    linarith
  have hw := slope_weight hr hs0.le hs1 (le_max_right P.L0 1) hsc
  have hK' : K * chartS P y ^ 2 / ‖y‖ ≤ |K| * (chartS P y ^ 2 / ‖y‖) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
  calc ‖gradientAt (pressureOf P D β) y‖ ≤ 3 * ‖fderiv ℝ (pressureOf P D β) y‖ := norm_gradientAt_le _ y
    _ ≤ 3 * (|K| * (chartS P y ^ 2 / ‖y‖)) := by linarith
    _ ≤ 3 * (|K| * (max P.L0 1 ^ 2 * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))))) := by gcongr
    _ = 3 * |K| * max P.L0 1 ^ 2 * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := by ring

theorem pressure_core (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) :
    AEStronglyMeasurable (pressureOf P D β) volume ∧
      (∃ C : ℝ, ∀ y, |pressureOf P D β y| ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) ∧
      (∀ᵐ y ∂volume, DifferentiableAt ℝ (pressureOf P D β) y) ∧
      Reduction.IsWeakScalarGradientOf (pressureOf P D β) (fun y => gradientAt (pressureOf P D β) y) ∧
      ∃ C : ℝ, ∀ᵐ y ∂volume, ‖gradientAt (pressureOf P D β) y‖ ≤ C * min (‖y‖⁻¹) (‖y‖ ^ (-(3 : ℝ))) := by
  have hd : Measurable (fun y : Space => decayFactor P y) := by
    unfold decayFactor chartS chartT
    fun_prop
  have hm : Measurable (pressureOf P D β) := by
    unfold pressureOf
    refine Complex.measurable_re.comp (Finset.measurable_sum _ fun n _ => ?_)
    exact (((Complex.measurable_ofReal.comp hd).mul (modePhase_measurable P n β)).mul (shape_measurable P _ _ _ _)).add
      (((Complex.measurable_ofReal.comp (hd.pow_const 2)).mul (modePhase_measurable P n β)).mul
        (shape_measurable P _ _ _ _))
  obtain ⟨K, hK⟩ := sum_tail D.modes (fun n y => ((decayFactor P y : ℝ) : ℂ) * modePhase P n β y *
      pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y +
      ((decayFactor P y ^ 2 : ℝ) : ℂ) * modePhase P n β y *
        pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)
    (fun y => chartS P y ^ 2) fun n _ => by
      obtain ⟨B1, h1⟩ := shape_bound P hP (D.firstLow n) D.firstHigh (D.axisOrder n) hD.high_ge.1 (D.firstAmp n)
      obtain ⟨B2, h2⟩ := shape_bound P hP (D.secondLow n) D.secondHigh (D.axisOrder n) hD.high_ge.2 (D.secondAmp n)
      refine ⟨|B1| + |B2|, fun y => ?_⟩
      obtain ⟨hd0, hd1⟩ := decay_le_one P hP y
      have hs := sq_nonneg (chartS P y)
      have hd2 : decayFactor P y ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_modePhase, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd0, abs_of_nonneg (by positivity)]
      have a1 := (h1 y).trans (mul_le_mul_of_nonneg_right (le_abs_self B1) hs)
      have a2 := (h2 y).trans (mul_le_mul_of_nonneg_right (le_abs_self B2) hs)
      have n1 := norm_nonneg (pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y)
      have n2 := norm_nonneg (pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)
      nlinarith
  refine ⟨hm.aestronglyMeasurable, ⟨|K| * max P.L0 1 ^ 2, fun y => ?_⟩, pressure_diff P hP D β,
    pressure_weak P hP D hD β, pressure_gradBound P hP D hD β⟩
  have hw := sq_weight P hP y
  have hs := sq_nonneg (chartS P y)
  unfold pressureOf
  refine (Complex.abs_re_le_norm _).trans ((hK y).trans ?_)
  calc K * chartS P y ^ 2 ≤ |K| * chartS P y ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self K) hs
    _ ≤ |K| * (max P.L0 1 ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left hw (abs_nonneg K)
    _ = _ := by ring

end AdjointCoreInternal

end GivenFields

end CellCert

end Breakdown

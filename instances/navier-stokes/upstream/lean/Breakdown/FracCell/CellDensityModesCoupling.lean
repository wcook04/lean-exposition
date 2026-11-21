import Breakdown.FracCell.CellDensityModesBound

open MeasureTheory Real

noncomputable section

namespace Breakdown.FracInternal.CellDensityModesCoupling

open SteadyCert CellCert CellCert.CellAnalysis FracInternal.CellDensityModesMirror Assembly

theorem jForm_eq (S Gm G : Space →L[ℝ] Space) (v : Space) :
    jForm S Gm G v = ∑ a : Fin 3, ∑ b : Fin 3, (-entry S a b) * (curlOf G a * curlOf G b)
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3, (-(permSign i l j) * entry Gm j b) * (v b * entry G i l)
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ q : Fin 3, ((1 / 2) * permSign i j q * entry Gm l j) * (v q * entry G i l) := by
  simp only [jForm, inner_eq, apply_sum S, apply_sum Gm, Fin.sum_univ_three]
  ring

theorem entry_le (M : Space →L[ℝ] Space) (a b : Fin 3) : |entry M a b| ≤ ‖M‖ := by
  have h1 : |entry M a b| ≤ ‖M (unitVector b)‖ := by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le (M (unitVector b)) a
  have h2 : ‖M (unitVector b)‖ ≤ ‖M‖ * ‖unitVector b‖ := M.le_opNorm _
  have h3 : ‖unitVector b‖ = 1 := by simp [unitVector]
  rw [h3, mul_one] at h2
  exact h1.trans h2

theorem symPart_le (M : Space →L[ℝ] Space) : ‖symPart M‖ ≤ ‖M‖ := by
  unfold symPart
  rw [norm_smul]
  have : ‖M + ContinuousLinearMap.adjoint M‖ ≤ ‖M‖ + ‖M‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  have h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [h2]; linarith

theorem entry_curlGradMatrix (H : Space →L[ℝ] Space →L[ℝ] Space) (a b : Fin 3) :
    |entry (curlGradMatrix H) a b| ≤ 9 * ‖H‖ := by
  have e : entry (curlGradMatrix H) a b = ∑ b' : Fin 3, ∑ q : Fin 3, permSign a b' q * H (unitVector b) (unitVector b') q := by
    simp only [curlGradMatrix, entry]
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three, unitVector, inner]
  have hH : ∀ u w : Fin 3, ∀ q : Fin 3, |H (unitVector u) (unitVector w) q| ≤ ‖H‖ := by
    intro u w q
    have h3 : ∀ t : Fin 3, ‖unitVector t‖ = 1 := fun t => by simp [unitVector]
    calc |H (unitVector u) (unitVector w) q| ≤ ‖H (unitVector u) (unitVector w)‖ := by
          rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ q
      _ ≤ ‖H (unitVector u)‖ * ‖unitVector w‖ := (H (unitVector u)).le_opNorm _
      _ ≤ ‖H‖ * ‖unitVector u‖ * ‖unitVector w‖ := by gcongr; exact H.le_opNorm _
      _ = ‖H‖ := by rw [h3, h3]; ring
  have hp : ∀ i j l : Fin 3, |permSign i j l| ≤ 1 := by
    intro i j l; unfold permSign; split_ifs <;> norm_num
  rw [e]
  calc |∑ b' : Fin 3, ∑ q : Fin 3, permSign a b' q * H (unitVector b) (unitVector b') q|
      ≤ ∑ b' : Fin 3, ∑ q : Fin 3, |permSign a b' q * H (unitVector b) (unitVector b') q| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ b' : Fin 3, ∑ q : Fin 3, ‖H‖ := by
        refine Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun q _ => ?_
        rw [abs_mul]
        calc |permSign a b' q| * |H (unitVector b) (unitVector b') q| ≤ 1 * ‖H‖ :=
              mul_le_mul (hp _ _ _) (hH _ _ _) (abs_nonneg _) zero_le_one
          _ = ‖H‖ := one_mul _
    _ = 9 * ‖H‖ := by simp [Finset.sum_const]; ring


theorem model_bounds {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) :
    ∃ C : ℝ, ∀ y a b, |entry (c.modelStrain y) a b| ≤ C ∧ |entry (c.modelCurlGrad y) a b| ≤ C := by
  obtain ⟨C₁, h₁⟩ := hc.model_bounded
  obtain ⟨C₂, h₂⟩ := hc.centre_bounds
  refine ⟨|C₁| + 9 * |C₂|, fun y a b => ?_⟩
  have hC₁ := le_abs_self C₁
  have hC₂ := abs_nonneg C₂
  have hA := abs_nonneg C₁
  by_cases hy : y ∈ c.cellRegion
  · obtain ⟨-, -, hS, hG⟩ := h₁ y hy
    constructor
    · linarith [entry_le (c.modelStrain y) a b]
    · have := entry_le (c.modelCurlGrad y) a b
      have h9 : 0 ≤ 9 * ‖c.centreSecond y‖ := by positivity
      linarith
  · obtain ⟨hS', hG'⟩ := hc.model_outside y hy
    obtain ⟨-, hg, hh⟩ := h₂ y
    have t1 : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    have t2 : (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    have t1' : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith [norm_nonneg y]) _
    have t2' : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by linarith [norm_nonneg y]) _
    have g1 : C₂ * (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ |C₂| := by
      calc C₂ * (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ |C₂| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by gcongr; exact le_abs_self _
        _ ≤ |C₂| * 1 := by gcongr
        _ = |C₂| := mul_one _
    have g2 : C₂ * (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ |C₂| := by
      calc C₂ * (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ |C₂| * (1 + ‖y‖) ^ (-(3 : ℝ)) := by gcongr; exact le_abs_self _
        _ ≤ |C₂| * 1 := by gcongr
        _ = |C₂| := mul_one _
    constructor
    · rw [hS']
      have h5 : |entry (c.centreStrain y) a b| ≤ ‖c.centreGrad y‖ :=
        (entry_le (symPart (c.centreGrad y)) a b).trans (symPart_le _)
      have h6 : 0 ≤ 9 * |C₂| := by positivity
      linarith
    · rw [hG']
      have := entry_curlGradMatrix (c.centreSecond y) a b
      have e : c.centreCurlGrad y = curlGradMatrix (c.centreSecond y) := rfl
      rw [e]
      linarith

theorem norm_le_cyl (y : Space) : ‖y‖ ≤ cylRadius y + |cylHeight y| := by
  have h1 := vec_sq y
  simp only [Fin.sum_univ_three] at h1
  have hR : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hR0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have hh : |cylHeight y| ^ 2 = y 2 ^ 2 := by simp [cylHeight, sq_abs]
  nlinarith [norm_nonneg y, abs_nonneg (cylHeight y)]

theorem solid_finite {K : CellBox} : volume K.solid < ⊤ := by
  refine lt_of_le_of_lt (measure_mono fun y hy => ?_) (measure_closedBall_lt_top (x := (0 : Space)) (r := K.r₂ + K.z₂))
  simp only [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨-, h2, -, h4⟩ := hy
  linarith [norm_le_cyl y]


theorem perm_le (i j l : Fin 3) : |permSign i j l| ≤ 1 := by
  unfold permSign; split_ifs <;> norm_num

theorem coef_le {C t e : ℝ} (ht : |t| ≤ 1) (he : |e| ≤ C) : ‖t * e‖ ≤ C := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |t| * |e| ≤ 1 * C := mul_le_mul ht he (abs_nonneg _) zero_le_one
    _ = C := one_mul _

end Breakdown.FracInternal.CellDensityModesCoupling

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly FracInternal.CellDensityModesMirror FracInternal.CellDensityModesWeak
  FracInternal.CellDensityModesCoupling

theorem jFormIntegrable : JFormIntegrableStatement := by
  intro α _ _ k N c hc K _ x hx
  have hs := hx.1
  have : IsFiniteMeasure (volume.restrict K.solid) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact solid_finite⟩
  obtain ⟨C, hC⟩ := model_bounds hc
  have emeas : ∀ {M : Space → (Space →L[ℝ] Space)}, AEStronglyMeasurable M volume → ∀ a b,
      AEStronglyMeasurable (fun y => entry (M y) a b) (volume.restrict K.solid) := fun hM a b =>
    ((EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      (hM.apply_continuousLinearMap (unitVector b))).restrict
  have hG2 : ∀ a b, MemLp (fun y => entry (x.2.1 y) a b) 2 (volume.restrict K.solid) := fun a b =>
    ((memLp_col hs.measurable_gradient hs.gradient_two b).restrict K.solid).of_le
      (emeas hs.measurable_gradient a b) (Filter.Eventually.of_forall fun y => PiLp.norm_apply_le _ _)
  have hv2 : ∀ b, MemLp (fun y => x.1 y b) 2 (volume.restrict K.solid) := fun b =>
    ((hs.velocity_six.restrict K.solid).mono_exponent (by norm_num)).of_le
      (((EuclideanSpace.proj b : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hs.measurable_velocity).restrict)
      (Filter.Eventually.of_forall fun y => PiLp.norm_apply_le _ _)
  have hcurl : ∀ a, MemLp (fun y => curlOf (x.2.1 y) a) 2 (volume.restrict K.solid) := by
    intro a
    have e : (fun y => curlOf (x.2.1 y) a) = fun y => ∑ j : Fin 3, ∑ l : Fin 3, permSign a j l * entry (x.2.1 y) l j :=
      funext fun y => curl_apply _ _
    rw [e]
    exact memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun l _ => (hG2 l j).const_mul _
  have hSm := hc.model_measurable.2.2.1
  have hGm := hc.model_measurable.2.2.2
  unfold IntegrableOn
  rw [show (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y)) = _ from
    funext fun y => jForm_eq _ _ _ _]
  refine ((integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_).add
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun b _ => ?_)).add
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun q _ => ?_)
  · refine Integrable.bdd_mul (c := C) ((hcurl a).integrable_mul (hcurl b)) (emeas hSm a b).neg
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_neg, Real.norm_eq_abs]; exact (hC y a b).1
  · refine Integrable.bdd_mul (c := C) ((hv2 b).integrable_mul (hG2 i l)) ((emeas hGm j b).const_mul _)
      (Filter.Eventually.of_forall fun y => coef_le (by rw [abs_neg]; exact perm_le _ _ _) (hC y j b).2)
  · refine Integrable.bdd_mul (c := C) ((hv2 q).integrable_mul (hG2 i l)) ((emeas hGm l j).const_mul _)
      (Filter.Eventually.of_forall fun y => coef_le ?_ (hC y l j).2)
    rw [abs_mul]
    have := perm_le i j q
    have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h2]; linarith

end Breakdown.CellCert.CellAnalysis

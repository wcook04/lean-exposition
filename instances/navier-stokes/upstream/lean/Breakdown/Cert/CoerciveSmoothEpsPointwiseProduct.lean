import Breakdown.Cert.CoerciveSmoothPieceEpsRestDefs
import Breakdown.Cert.CoerciveSmoothMuWave

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothEpsPointwise

open Internal.SmoothPieceEpsCore Internal.MuSmooth Internal.PieceAbsorb

theorem modeVel_neg (α : ℤ × ℤ) (X : ℝ → Space → Space) (σ : ℝ) (y : Space) (j : Fin 3) :
    modeVel (-α) X σ y j = (starRingEnd ℂ) (modeVel α X σ y j) :=
  modeAverage_neg _ _ _

theorem grad_bound_of_decay {W : ℝ → Space → Space}
    (hD : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    ∃ B, ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ B := by
  obtain ⟨D, hD⟩ := hD
  refine ⟨|D|, fun s x => ?_⟩
  have h := hD s x 1 (by norm_num)
  rw [norm_iteratedFDeriv_one] at h
  refine h.trans ?_
  have hp : 1 ≤ (1 + ‖x‖) ^ (1 + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
  calc D / (1 + ‖x‖) ^ (1 + 1) ≤ |D| / (1 + ‖x‖) ^ (1 + 1) :=
        div_le_div_of_nonneg_right (le_abs_self D) (by positivity)
    _ ≤ |D| := div_le_self (abs_nonneg D) hp

theorem velW_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (j : Fin 3) :
    ((axialRot (-φ) (W (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
      = ((meanField W y j : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel α W σ y j := by
  rw [rot_field_expansion hW.continuous hWp s hh σ τ φ y j, Complex.ofReal_add]
  congr 1
  · unfold meanField
    rw [space_sum_apply (fun k => (modeVel (0, 0) W 0 y k).re) j, modeVel_mean_shift hWp σ y j]
  · exact re_sum_sym s hs _ fun α => by rw [phase_neg, modeVel_neg, map_mul]

theorem gradW_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (i j : Fin 3) :
    ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
      = ((fderiv ℝ (meanField W) y (unitVector j) i : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeGrad α (gradField W) σ y (i, j) := by
  rw [grad_expansion hW hB hWp s hh σ τ φ y i j, Complex.ofReal_add]
  congr 1
  · rw [meanField_fderiv_apply hW hB hWp σ y i j]
  · exact re_sum_sym s hs _ fun α => by rw [phase_neg, modeGrad_neg, map_mul]

theorem vortW_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (j : Fin 3) :
    ((axialRot (-φ) (vortField W (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
      = ((curlVec (fderiv ℝ (meanField W) y) j : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * curlOfGrad (modeGrad α (gradField W) σ y) j := by
  unfold vortField
  rw [← Internal.CurlEnergy.curlVec_axialRot φ _ j, StretchInternal.curlVec_apply]
  push_cast
  simp_rw [gradW_expansion hW hB hWp s hs hh σ τ φ y]
  unfold curlOfGrad
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  simp only [Fin.sum_univ_three, Finset.sum_add_distrib]
  simp only [mul_left_comm]
  push_cast
  rfl

theorem mode_product_vec (s : Finset (ℤ × ℤ)) (K : ℝ → Space → (Space →L[ℝ] Space))
    (hK : Continuous fun z : ℝ × Space => K z.1 z.2) (u : ℝ → Space → Space) (σ : ℝ) (y : Space)
    (d : Fin 3 → ℝ) (c : ℤ × ℤ → Fin 3 → ℂ)
    (hU : ∀ τ φ : ℝ, ∀ j : Fin 3, ((axialRot (-φ) (u (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
        = (d j : ℂ) + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * c α j)
    (ι : ℤ × ℤ) (i : Fin 3) :
    modeVel ι (fun σ y => K σ y (u σ y)) σ y i
      = ∑ j : Fin 3, (modeGrad ι K σ y (i, j) * (d j : ℂ)
        + ∑ α ∈ s, modeGrad (ι - α) K σ y (i, j) * c α j) := by
  set E : ℤ × ℤ → ℝ → ℝ → ℂ := fun κ τ φ =>
    Complex.exp (-(((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)) with hEdef
  set Kc : Fin 3 → ℝ → ℝ → ℂ := fun j τ φ =>
    ((axialRot (-φ) (K (σ + τ) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ) with hKdef
  have hKc : ∀ j, Continuous fun p : ℝ × ℝ => Kc j p.1 p.2 := by
    intro j
    have h0 : Continuous fun p : ℝ × ℝ => K (σ + p.1) (axialRot p.2 y) :=
      hK.comp ((continuous_const.add continuous_fst).prodMk
        (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd continuous_const))
    have h1 : Continuous fun p : ℝ × ℝ => K (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j)) :=
      h0.clm_apply (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd continuous_const)
    have h2 := ModeDerivative.Internal.continuous_axialRot_comp continuous_snd.neg h1
    exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ i).comp h2)
  have hEc : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 := fun κ => cont_exp_pair κ
  have hmg : ∀ κ j, modeGrad κ K σ y (i, j) = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => E κ τ φ * Kc j τ φ) :=
    fun κ j => rfl
  have hpt : ∀ τ φ, E ι τ φ * ((axialRot (-φ) (K (σ + τ) (axialRot φ y) (u (σ + τ) (axialRot φ y))) i : ℝ) : ℂ)
      = ∑ j : Fin 3, ((d j : ℂ) * (E ι τ φ * Kc j τ φ)
        + ∑ α ∈ s, c α j * (E (ι - α) τ φ * Kc j τ φ)) := by
    intro τ φ
    rw [rot_apply_clm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hU τ φ j]
    have hx : ∀ α, E (ι - α) τ φ
        = E ι τ φ * Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) :=
      fun α => (exp_pair_mul ι α τ φ).symm
    simp_rw [hx]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · simp only [hKdef]
      ring
    · refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hKdef]
      ring
  have hlhs : modeVel ι (fun σ y => K σ y (u σ y)) σ y i
      = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => ∑ j : Fin 3, ((d j : ℂ) * (E ι τ φ * Kc j τ φ)
        + ∑ α ∈ s, c α j * (E (ι - α) τ φ * Kc j τ φ))) := by
    rw [← funext fun τ => funext fun φ => hpt τ φ]
    rfl
  have hc1 : ∀ κ j, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 * Kc j p.1 p.2 := fun κ j => (hEc κ).mul (hKc j)
  rw [hlhs, boxInt_sum _ _ (fun j => ((continuous_const.mul (hc1 ι j)).add
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j))))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [boxInt_add _ _ (continuous_const.mul (hc1 ι j))
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j)),
    boxInt_sum _ _ (fun α => continuous_const.mul (hc1 (ι - α) j)), boxInt_const_mul]
  simp_rw [boxInt_const_mul, hmg]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun α _ => by ring

theorem cnorm3_ofReal (d : Space) : cnorm3 (fun j => ((d j : ℝ) : ℂ)) = ‖d‖ := by
  unfold cnorm3 cnormSq
  rw [← Real.sqrt_sq (norm_nonneg d), space_norm_sq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem cnorm3_product_le (s : Finset (ℤ × ℤ)) (g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ) (d : Space)
    (c : ℤ × ℤ → Fin 3 → ℂ) (ι : ℤ × ℤ) :
    cnorm3 (fun i => ∑ j : Fin 3, (g ι (i, j) * ((d j : ℝ) : ℂ) + ∑ α ∈ s, g (ι - α) (i, j) * c α j))
      ≤ Real.sqrt (cnormSq (g ι)) * ‖d‖ + ∑ α ∈ s, cnorm3 (c α) * Real.sqrt (cnormSq (g (ι - α))) := by
  have hsplit : (fun i => ∑ j : Fin 3, (g ι (i, j) * ((d j : ℝ) : ℂ) + ∑ α ∈ s, g (ι - α) (i, j) * c α j))
      = (fun i => ∑ j : Fin 3, g ι (i, j) * ((d j : ℝ) : ℂ))
        + ∑ α ∈ s, (fun i => ∑ j : Fin 3, g (ι - α) (i, j) * c α j) := by
    funext i
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_comm (s := s)]
  rw [hsplit]
  refine (cnorm3_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (cnorm3_mat_le (g ι) _).trans (le_of_eq ?_)
    rw [cnorm3_ofReal]
  · refine (cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [mul_comm]
    exact cnorm3_mat_le (g (ι - α)) _

theorem modeGrad_vort_eq {v : ℝ → Space → Space} (hv : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2))
    (κ : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeGrad κ (fun s x => fderiv ℝ (vortField v s) x) σ y = curlGradOfSecondDeriv (modeSecondDeriv κ (secondDerivField v) σ y) := by
  funext il
  obtain ⟨i, l⟩ := il
  have hpt : ∀ τ φ : ℝ, axialRot (-φ) (fderiv ℝ (vortField v (σ + τ)) (axialRot φ y) (axialRot φ (unitVector l))) i
      = ∑ jm : Fin 3 × Fin 3, alternatingSymbol i jm.1 jm.2
        * axialRot (-φ) (secondDerivField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector l))
          (axialRot φ (unitVector jm.1))) jm.2 := by
    intro τ φ
    have e := vortGrad_eq hv (σ + τ) (axialRot φ y)
    have e' : fderiv ℝ (vortField v (σ + τ)) (axialRot φ y)
        = Internal.SmoothPieceEps.curlLinear.comp (fderiv ℝ (fderiv ℝ (v (σ + τ))) (axialRot φ y)) := e
    rw [e', ContinuousLinearMap.comp_apply, Internal.SmoothPieceEps.curlLinear_apply,
      ← Internal.CurlEnergy.curlVec_axialRot, Fintype.sum_prod_type]
    rfl
  have hc : Continuous (fun z : ℝ × Space => secondDerivField v z.1 z.2) := secondDeriv_continuous hv
  have hint : ∀ jm : Fin 3 × Fin 3, Integrable (fun p : ℝ × ℝ =>
      axialRot (-p.2) (secondDerivField v (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector l))
        (axialRot p.2 (unitVector jm.1))) jm.2) Internal.ModeRotation.boxMeasure := by
    intro jm
    apply StretchInternal.integrable_box_of_continuous
    have h0 : Continuous fun p : ℝ × ℝ => secondDerivField v (σ + p.1) (axialRot p.2 y) :=
      hc.comp ((continuous_const.add continuous_fst).prodMk
        (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd continuous_const))
    have h1 := (h0.clm_apply (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ : ℝ × ℝ => unitVector l)
      continuous_snd continuous_const)).clm_apply
      (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ : ℝ × ℝ => unitVector jm.1) continuous_snd
        continuous_const)
    exact (PiLp.continuous_apply 2 _ jm.2).comp (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd.neg h1)
  unfold modeGrad curlGradOfSecondDeriv modeSecondDeriv
  simp only [Internal.ModeRotation.modeAverage_eq]
  simp only [hpt]
  rw [Internal.ModeRotation.modeAverage_sum κ (fun jm : Fin 3 × Fin 3 => alternatingSymbol i jm.1 jm.2) _ hint,
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end Internal.SmoothEpsPointwise

end Coercive

end Breakdown

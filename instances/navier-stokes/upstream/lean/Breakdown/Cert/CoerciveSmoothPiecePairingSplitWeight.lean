import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothWeightSplit

open ModeL2Internal (IsSquareField)

def scaledField (v : ℝ → Space → Space) : ℝ → Space → Space := fun σ y => (1 + ‖y‖)⁻¹ • v σ y

theorem axialRot_smul_coord (φ a : ℝ) (x : Space) (i : Fin 3) :
    axialRot φ (a • x) i = a * axialRot φ x i := by
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem modeVel_scaled (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (i : Fin 3) :
    modeVel ι (scaledField v) σ y i = ((1 + ‖y‖)⁻¹ : ℝ) * modeVel ι v σ y i := by
  have e : ∀ τ φ : ℝ, axialRot (-φ) (scaledField v (σ + τ) (axialRot φ y)) i
      = (1 + ‖y‖)⁻¹ * axialRot (-φ) (v (σ + τ) (axialRot φ y)) i := by
    intro τ φ
    unfold scaledField
    rw [axialRot_smul_coord, PairingSplitInternal.norm_axialRot]
  unfold modeVel modeAverage
  simp only [e]
  push_cast
  have e2 : ∀ τ φ : ℝ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * (((1 + ‖y‖ : ℝ) : ℂ)⁻¹ * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) i : ℝ) : ℂ))
      = ((1 + ‖y‖ : ℝ) : ℂ)⁻¹ * (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) i : ℝ) : ℂ)) := fun τ φ => by ring
  push_cast at e2
  simp only [e2, intervalIntegral.integral_const_mul]
  ring

theorem modeVel_eq_scaled (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (i : Fin 3) :
    modeVel ι v σ y i = ((1 + ‖y‖ : ℝ) : ℂ) * modeVel ι (scaledField v) σ y i := by
  have h : ((1 + ‖y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [modeVel_scaled, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ h, one_mul]

theorem periodLIntegral_lt_top_of_le {f g : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hfg : ∀ σ y, f σ y ≤ c * g σ y) (hg : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ := by
  unfold periodLIntegral at hg ⊢
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (g σ y) := by
        refine lintegral_mono fun σ => lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (hfg σ y)
    _ = ENNReal.ofReal c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg

theorem scaledField_square {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    IsSquareField (scaledField v) := by
  have hc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  refine ⟨?_, ?_, ?_⟩
  · have hi : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖)⁻¹) :=
      Continuous.inv₀ (by fun_prop) (fun z => by show (1 : ℝ) + ‖z.2‖ ≠ 0; positivity)
    exact (hi.smul hc).aestronglyMeasurable
  · intro σ y
    unfold scaledField
    rw [hv.periodic σ y]
  · refine periodLIntegral_lt_top_of_le zero_le_one (fun σ y => ?_) hv.weighted_finite
    unfold scaledField
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (1 + ‖y‖)⁻¹),
      inv_pow, one_mul, div_eq_inv_mul]

theorem matSq_le_three_sq (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖G‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := G.le_opNorm (unitVector i)
        rw [Internal.PerturbationFacts.norm_unitVector_eq, mul_one] at h
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 3 * ‖G‖ ^ 2 := by simp

theorem perturbation_fderiv_sq {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    periodLIntegral (fun σ y => matSq (fderiv ℝ (v σ) y)) < ⊤ := by
  refine periodLIntegral_lt_top_of_le (by norm_num : (0 : ℝ) ≤ 3) (fun σ y => ?_)
    (hv.derivatives_finite 1 le_rfl)
  rw [norm_iteratedFDeriv_one]
  exact matSq_le_three_sq _

theorem abs_alternatingSymbol_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem norm_curlVec_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ≤ 27 * ‖G‖ := by
  unfold curlVec
  have hc : ∀ i : Fin 3, |∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l| ≤ 9 * ‖G‖ := by
    intro i
    calc |∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l|
        ≤ ∑ j : Fin 3, ∑ l : Fin 3, |alternatingSymbol i j l * G (unitVector j) l| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, ‖G‖ := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          have h1 := abs_alternatingSymbol_le i j l
          have h2 : |G (unitVector j) l| ≤ ‖G‖ := by
            have a := PiLp.norm_apply_le (G (unitVector j)) l
            have b := G.le_opNorm (unitVector j)
            rw [Internal.PerturbationFacts.norm_unitVector_eq, mul_one] at b
            rw [← Real.norm_eq_abs]
            exact a.trans b
          calc |alternatingSymbol i j l| * |G (unitVector j) l| ≤ 1 * ‖G‖ :=
                mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
            _ = ‖G‖ := one_mul _
      _ = 9 * ‖G‖ := by simp; ring
  calc ‖∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l) • unitVector i‖
      ≤ ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l) • unitVector i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 9 * ‖G‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Internal.PerturbationFacts.norm_unitVector_eq, mul_one, Real.norm_eq_abs]
        exact hc i
    _ = 27 * ‖G‖ := by simp; ring

theorem sq_norm_curlVec_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ^ 2 ≤ 2187 * matSq G := by
  have h1 := norm_curlVec_le G
  have h2 := Internal.PerturbationFacts.sq_norm_le_three_matNorm G
  have h3 : ‖curlVec G‖ ^ 2 ≤ (27 * ‖G‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith

theorem curl_square_of_fderiv {X : ℝ → Space → Space} (hX : ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2))
    (hXp : IsTimePeriodic X) (hX2 : periodLIntegral (fun σ y => matSq (fderiv ℝ (X σ) y)) < ⊤) :
    IsSquareField (fun σ y => curlVec (fderiv ℝ (X σ) y)) := by
  refine ⟨(PairingSplitInternal.continuous_curl hX).aestronglyMeasurable, fun σ y => ?_, ?_⟩
  · show curlVec (fderiv ℝ (X (σ + 1)) y) = curlVec (fderiv ℝ (X σ) y)
    rw [show X (σ + 1) = X σ from funext (hXp σ)]
  · exact periodLIntegral_lt_top_of_le (by norm_num : (0 : ℝ) ≤ 2187) (fun σ y => sq_norm_curlVec_le _) hX2

theorem one_add_norm_mul_le {f : Space → ℝ} {B : ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hB : ∀ y, f y ≤ B ∧ ‖y‖ ^ 2 * f y ≤ B) (y : Space) : (1 + ‖y‖) * f y ≤ 2 * B := by
  obtain ⟨h1, h2⟩ := hB y
  have h0 := hf0 y
  by_cases hy : ‖y‖ ≤ 1
  · nlinarith [norm_nonneg y]
  · have hy' : 1 < ‖y‖ := lt_of_not_ge hy
    nlinarith [norm_nonneg y]

end Internal.SmoothWeightSplit

end Coercive

end Breakdown

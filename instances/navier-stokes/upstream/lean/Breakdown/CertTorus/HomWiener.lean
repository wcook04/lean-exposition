import Breakdown.CertTorus.RegularStatements
import Breakdown.Uniqueness.RegUniqueAux2
import Breakdown.Frac.OpIntegrable

open MeasureTheory Set Real Filter Metric
open scoped ENNReal

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.HomWienerBound

def sobolevSum (k : ℕ) (ξ : Space) : ℝ := ‖ξ‖ ^ (2 * 0) + ‖ξ‖ ^ (2 * (k + 1))

def wienerRatio (k : ℕ) (ξ : Space) : ℝ :=
  (1 + ‖ξ‖) ^ k / (2 * π * ‖ξ‖ * √(sobolevSum k ξ))

theorem one_le_sobolevSum (k : ℕ) (ξ : Space) : 1 ≤ sobolevSum k ξ := by
  unfold sobolevSum
  rw [Nat.mul_zero, pow_zero]
  linarith [pow_nonneg (norm_nonneg ξ) (2 * (k + 1))]

theorem sobolevSum_neg (k : ℕ) (ξ : Space) : sobolevSum k (-ξ) = sobolevSum k ξ := by
  simp only [sobolevSum, norm_neg]

theorem measurable_sobolevSum (k : ℕ) : Measurable (sobolevSum k) := by
  unfold sobolevSum
  fun_prop

theorem measurable_wienerRatio (k : ℕ) : Measurable (wienerRatio k) := by
  unfold wienerRatio
  have := measurable_sobolevSum k
  fun_prop

theorem wienerRatio_nonneg (k : ℕ) (ξ : Space) : 0 ≤ wienerRatio k ξ := by
  unfold wienerRatio
  have := one_le_sobolevSum k ξ
  positivity

theorem norm_conjVec_eq (z : CSpace) : ‖conjVec z‖ = ‖z‖ := by
  simp [EuclideanSpace.norm_eq, conjVec]

theorem norm_velSymbol_le (x : X) (ξ : Space) :
    ‖velSymbol x ξ‖ ≤ (2 * π * ‖ξ‖)⁻¹ * (‖symX x ξ‖ + ‖symX x (-ξ)‖) := by
  unfold velSymbol
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖divFreeC ξ ((1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ))))‖
      ≤ 2 * ‖(1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ)))‖ := norm_divFreeC_le _ _
    _ ≤ ‖symX x ξ‖ + ‖symX x (-ξ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have h := norm_add_le (symX x ξ) (conjVec (symX x (-ξ)))
        rw [norm_conjVec_eq] at h
        linarith

theorem weight_mul_norm_velSymbol_le (k : ℕ) (x : X) (ξ : Space) :
    (1 + ‖ξ‖) ^ k * ‖velSymbol x ξ‖ ≤
      √(sobolevSum k ξ) * ‖symX x ξ‖ * wienerRatio k ξ +
        √(sobolevSum k ξ) * ‖symX x (-ξ)‖ * wienerRatio k ξ := by
  have hs : 0 < √(sobolevSum k ξ) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (one_le_sobolevSum k ξ))
  have he : √(sobolevSum k ξ) * wienerRatio k ξ = (1 + ‖ξ‖) ^ k * (2 * π * ‖ξ‖)⁻¹ := by
    unfold wienerRatio
    rw [div_eq_mul_inv, mul_inv]
    calc √(sobolevSum k ξ) * ((1 + ‖ξ‖) ^ k * ((2 * π * ‖ξ‖)⁻¹ * (√(sobolevSum k ξ))⁻¹))
        = (1 + ‖ξ‖) ^ k * (2 * π * ‖ξ‖)⁻¹ * (√(sobolevSum k ξ) * (√(sobolevSum k ξ))⁻¹) := by
          ring
      _ = (1 + ‖ξ‖) ^ k * (2 * π * ‖ξ‖)⁻¹ := by rw [mul_inv_cancel₀ hs.ne', mul_one]
  calc (1 + ‖ξ‖) ^ k * ‖velSymbol x ξ‖
      ≤ (1 + ‖ξ‖) ^ k * ((2 * π * ‖ξ‖)⁻¹ * (‖symX x ξ‖ + ‖symX x (-ξ)‖)) :=
        mul_le_mul_of_nonneg_left (norm_velSymbol_le x ξ) (by positivity)
    _ = (‖symX x ξ‖ + ‖symX x (-ξ)‖) * (√(sobolevSum k ξ) * wienerRatio k ξ) := by
        rw [he]; ring
    _ = _ := by ring

theorem wienerRatio_sq_le_of_lt_one (k : ℕ) {ξ : Space} (hξ : ‖ξ‖ < 1) :
    wienerRatio k ξ ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 * ‖ξ‖ ^ (-2 : ℝ) := by
  rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | hpos
  · have hz : wienerRatio k ξ = 0 := by
      unfold wienerRatio
      rw [← h0]
      simp
    rw [hz, zero_pow two_ne_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hs : 1 ≤ √(sobolevSum k ξ) := Real.one_le_sqrt.2 (one_le_sobolevSum k ξ)
    have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    have hd : ‖ξ‖ ≤ 2 * π * ‖ξ‖ * √(sobolevSum k ξ) := by
      calc ‖ξ‖ = 1 * ‖ξ‖ * 1 := by ring
        _ ≤ 2 * π * ‖ξ‖ * √(sobolevSum k ξ) := by gcongr
    have hw : (1 + ‖ξ‖) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have hle : wienerRatio k ξ ≤ (2 : ℝ) ^ k / ‖ξ‖ := by
      unfold wienerRatio
      exact div_le_div₀ (by positivity) hw hpos hd
    calc wienerRatio k ξ ^ 2 ≤ ((2 : ℝ) ^ k / ‖ξ‖) ^ 2 :=
          pow_le_pow_left₀ (wienerRatio_nonneg k ξ) hle 2
      _ = ((2 : ℝ) ^ k) ^ 2 * ‖ξ‖ ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two, div_pow, div_eq_mul_inv]

theorem wienerRatio_sq_le_of_one_le (k : ℕ) {ξ : Space} (hξ : 1 ≤ ‖ξ‖) :
    wienerRatio k ξ ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 * ‖ξ‖ ^ (-4 : ℝ) := by
  have hpos : 0 < ‖ξ‖ := lt_of_lt_of_le one_pos hξ
  have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hs : ‖ξ‖ ^ (k + 1) ≤ √(sobolevSum k ξ) := by
    calc ‖ξ‖ ^ (k + 1) = √((‖ξ‖ ^ (k + 1)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(sobolevSum k ξ) := by
          refine Real.sqrt_le_sqrt ?_
          unfold sobolevSum
          rw [← pow_mul, mul_comm (k + 1) 2]
          linarith [pow_nonneg (norm_nonneg ξ) (2 * 0)]
  have hd : ‖ξ‖ * ‖ξ‖ ^ (k + 1) ≤ 2 * π * ‖ξ‖ * √(sobolevSum k ξ) := by
    calc ‖ξ‖ * ‖ξ‖ ^ (k + 1) = 1 * ‖ξ‖ * ‖ξ‖ ^ (k + 1) := by ring
      _ ≤ 2 * π * ‖ξ‖ * √(sobolevSum k ξ) := by gcongr
  have hw : (1 + ‖ξ‖) ^ k ≤ (2 * ‖ξ‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
  have hle : wienerRatio k ξ ≤ (2 : ℝ) ^ k / ‖ξ‖ ^ 2 := by
    unfold wienerRatio
    calc (1 + ‖ξ‖) ^ k / (2 * π * ‖ξ‖ * √(sobolevSum k ξ))
        ≤ (2 * ‖ξ‖) ^ k / (‖ξ‖ * ‖ξ‖ ^ (k + 1)) := div_le_div₀ (by positivity) hw (by positivity) hd
      _ = (2 : ℝ) ^ k / ‖ξ‖ ^ 2 := by
          rw [mul_pow, pow_succ]
          field_simp
  have h4 : ‖ξ‖ ^ (4 : ℝ) = ‖ξ‖ ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast ‖ξ‖ 4
  calc wienerRatio k ξ ^ 2 ≤ ((2 : ℝ) ^ k / ‖ξ‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (wienerRatio_nonneg k ξ) hle 2
    _ = ((2 : ℝ) ^ k) ^ 2 * ‖ξ‖ ^ (-4 : ℝ) := by
        rw [Real.rpow_neg (norm_nonneg _), h4, div_pow, div_eq_mul_inv]
        ring

theorem lintegral_wienerRatio_sq_lt_top (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (wienerRatio k ξ) ^ (2 : ℝ) < ⊤ := by
  have hsq : ∀ ξ, ENNReal.ofReal (wienerRatio k ξ) ^ (2 : ℝ) =
      ENNReal.ofReal (wienerRatio k ξ ^ 2) := fun ξ => by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (wienerRatio_nonneg k ξ)]
  simp_rw [hsq]
  rw [← lintegral_add_compl _ (measurableSet_ball (x := (0 : Space)) (ε := 1))]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_ball fun ξ hξ => ?_)
      (Integrable.lintegral_lt_top (Integrable.const_mul
        (FracInternal.integrableOn_ball_norm_rpow (s := -2) (by norm_num)) (((2 : ℝ) ^ k) ^ 2)))
    refine ENNReal.ofReal_le_ofReal (wienerRatio_sq_le_of_lt_one k ?_)
    simpa using hξ
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_ball.compl fun ξ hξ => ?_)
      (Integrable.lintegral_lt_top (Integrable.const_mul
        (FracInternal.integrableOn_compl_ball_norm_rpow (s := -4) (by norm_num))
          (((2 : ℝ) ^ k) ^ 2)))
    refine ENNReal.ofReal_le_ofReal (wienerRatio_sq_le_of_one_le k ?_)
    simpa using hξ

theorem lintegral_weight_velSymbol_le (k : ℕ) (x : X) :
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol x ξ‖ₑ ≤
      2 * (∫⁻ ξ, ENNReal.ofReal (wienerRatio k ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (homSob 0 x + homSob (k + 1) x) ^ (1 / 2 : ℝ) := by
  have hm : Measurable (symX x) := (Lp.stronglyMeasurable _).measurable
  have hρm := measurable_sobolevSum k
  have hgm := measurable_wienerRatio k
  set F : Space → ℝ≥0∞ := fun ξ => ENNReal.ofReal (√(sobolevSum k ξ)) * ‖symX x ξ‖ₑ with hF
  set G : Space → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wienerRatio k ξ) with hG
  set J := ∫⁻ ξ, ENNReal.ofReal (wienerRatio k ξ) ^ (2 : ℝ) with hJ
  set S := homSob 0 x + homSob (k + 1) x with hS
  have hFm : Measurable F := by rw [hF]; fun_prop
  have hFnm : Measurable fun ξ => F (-ξ) := hFm.comp measurable_neg
  have hGm : Measurable G := by rw [hG]; fun_prop
  have htriple : ∀ (a : ℝ) (ha : 0 ≤ a) (z : CSpace) (b : ℝ),
      ENNReal.ofReal (a * ‖z‖ * b) = ENNReal.ofReal a * ‖z‖ₑ * ENNReal.ofReal b := by
    intro a ha z b
    rw [ENNReal.ofReal_mul (mul_nonneg ha (norm_nonneg _)), ENNReal.ofReal_mul ha,
      ofReal_norm]
  have hpt : ∀ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol x ξ‖ₑ ≤
      F ξ * G ξ + F (-ξ) * G ξ := by
    intro ξ
    calc ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol x ξ‖ₑ
        = ENNReal.ofReal ((1 + ‖ξ‖) ^ k * ‖velSymbol x ξ‖) := by
          rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
      _ ≤ ENNReal.ofReal (√(sobolevSum k ξ) * ‖symX x ξ‖ * wienerRatio k ξ +
            √(sobolevSum k ξ) * ‖symX x (-ξ)‖ * wienerRatio k ξ) :=
          ENNReal.ofReal_le_ofReal (weight_mul_norm_velSymbol_le k x ξ)
      _ = F ξ * G ξ + F (-ξ) * G ξ := by
          have h1 : 0 ≤ √(sobolevSum k ξ) * ‖symX x ξ‖ * wienerRatio k ξ := by
            have := wienerRatio_nonneg k ξ
            positivity
          have h2 : 0 ≤ √(sobolevSum k ξ) * ‖symX x (-ξ)‖ * wienerRatio k ξ := by
            have := wienerRatio_nonneg k ξ
            positivity
          rw [ENNReal.ofReal_add h1 h2, htriple _ (Real.sqrt_nonneg _),
            htriple _ (Real.sqrt_nonneg _)]
          simp only [hF, hG, sobolevSum_neg]
  have hFsq : ∫⁻ ξ, F ξ ^ (2 : ℝ) = S := by
    have hpt2 : ∀ ξ, F ξ ^ (2 : ℝ) = ENNReal.ofReal (‖ξ‖ ^ (2 * 0)) * ‖symX x ξ‖ₑ ^ 2 +
        ENNReal.ofReal (‖ξ‖ ^ (2 * (k + 1))) * ‖symX x ξ‖ₑ ^ 2 := by
      intro ξ
      simp only [hF]
      rw [ENNReal.rpow_two, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
        Real.sq_sqrt (le_trans zero_le_one (one_le_sobolevSum k ξ)), ← add_mul,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      rfl
    rw [lintegral_congr hpt2, lintegral_add_left (by fun_prop)]
    rfl
  have hFnsq : ∫⁻ ξ, F (-ξ) ^ (2 : ℝ) = S := by
    rw [← hFsq]
    exact (Measure.measurePreserving_neg (volume : Measure Space)).lintegral_comp
      (f := fun ξ => F ξ ^ (2 : ℝ)) (by fun_prop)
  have hCS1 : ∫⁻ ξ, F ξ * G ξ ≤ S ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) := by
    rw [← hFsq]
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hFm.aemeasurable
      hGm.aemeasurable
  have hCS2 : ∫⁻ ξ, F (-ξ) * G ξ ≤ S ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) := by
    rw [← hFnsq]
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hFnm.aemeasurable
      hGm.aemeasurable
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol x ξ‖ₑ
      ≤ ∫⁻ ξ, (F ξ * G ξ + F (-ξ) * G ξ) := lintegral_mono hpt
    _ = (∫⁻ ξ, F ξ * G ξ) + ∫⁻ ξ, F (-ξ) * G ξ :=
        lintegral_add_left (hFm.mul hGm) (fun ξ => F (-ξ) * G ξ)
    _ ≤ S ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) + S ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) :=
        add_le_add hCS1 hCS2
    _ = 2 * J ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by ring

end Internal.HomWienerBound

open Internal.HomWienerBound in
theorem homWiener_holds : HomWiener := by
  intro k
  set J := ∫⁻ ξ, ENNReal.ofReal (wienerRatio k ξ) ^ (2 : ℝ) with hJ
  have hJt : J ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (lintegral_wienerRatio_sq_lt_top k).ne
  refine ⟨2 * (J ^ (1 / 2 : ℝ)).toReal, fun x => ?_⟩
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hJt, ENNReal.ofReal_ofNat]
  exact lintegral_weight_velSymbol_le k x

end Breakdown.FarField

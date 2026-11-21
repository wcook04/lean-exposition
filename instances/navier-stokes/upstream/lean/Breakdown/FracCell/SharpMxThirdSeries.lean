import Breakdown.FracCell.SharpModeExpansionRegular
import Breakdown.FracCell.SharpDensityModeSeries

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpMxThirdSeries.Internal

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal
open Breakdown.CellCert.CellAnalysis.SharpDensityModeSeries.Internal
open Breakdown.CellCert.CellAnalysis.SharpModeExpansionRegular.Internal

theorem radius_le (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) :
    p.1 ≤ (1 + K.r₂) * K.lineWeight p.1 := by
  have h1 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have h2 : p.1 ≤ K.r₂ := hp.1.2
  by_cases h : K.r₁ = 0
  · simp only [CellBox.lineWeight, h, if_true]
    nlinarith
  · simp only [CellBox.lineWeight, h, if_false]
    linarith

theorem second_enorm (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ENNReal.ofReal (secondModeSq m n H p) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ‖modeThird m n H a b c p‖ₑ ^ 2 := by
  unfold secondModeSq
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  simp only [sq_enorm]

theorem third_holds (K : CellBox) (hK : IsCellBox K) {m : ℕ} (hm : 1 ≤ m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) :
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * secondModeSq m n H p) := by
  have hr2 : 0 ≤ 1 + K.r₂ := by linarith [hK.r_order.1, hK.r_order.2]
  have hH2 : MemLp H 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hs.measurable_second).2 ((hs.second_two.const_mul 9).mono'
      ((hs.measurable_second.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ModeSquareIntegrable.Internal.bil_norm_sq_le (H y)
  have fH : ∫⁻ y, ‖H y‖ₑ ^ 2 < ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hs.measurable_second).1 hH2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi
  have hg : AEMeasurable (fun y => ‖H y‖ₑ ^ 2) volume := hs.measurable_second.enorm.pow_const 2
  have hD : ENNReal.ofReal (1 + K.r₂) * (27 * ENNReal.ofReal (1 / (2 * π))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  refine summable_of_bound K (fun n p => p.1 * secondModeSq m n H p) (fun n => second_int hK hs n)
    (fun n p hp => mul_nonneg (hK.r_order.1.trans hp.1.1) (second_nonneg m n H p))
    (fun p => ENNReal.ofReal (K.lineWeight p.1) *
      (ENNReal.ofReal (1 + K.r₂) * (27 * ENNReal.ofReal (1 / (2 * π))) *
        ∫⁻ θ in Ioo (-π) π, (fun y => ‖H y‖ₑ ^ 2) (cylPoint p.1 θ p.2)))
    (fin_bound K hK _ hg fH _ hD) fun S => ?_
  refine ae_restrict_of_forall_mem (rect_meas K) fun p hp => ?_
  obtain ⟨C, hC0, hw⟩ := weight_le K hK
  have hw0 : 0 ≤ K.lineWeight p.1 := (hw p hp).1
  set E := ∫⁻ θ in Ioo (-π) π, ‖H (cylPoint p.1 θ p.2)‖ₑ ^ 2 with hE
  calc ∑ n ∈ S, ENNReal.ofReal (p.1 * secondModeSq m n H p)
      ≤ ∑ n ∈ S, ENNReal.ofReal ((1 + K.r₂) * K.lineWeight p.1) * ENNReal.ofReal (secondModeSq m n H p) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (radius_le K hK hp) (second_nonneg m n H p))
    _ = ENNReal.ofReal (K.lineWeight p.1) * (ENNReal.ofReal (1 + K.r₂) *
          ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ n ∈ S, ‖modeThird m n H a b c p‖ₑ ^ 2) := by
        simp only [second_enorm]
        rw [← Finset.mul_sum, ENNReal.ofReal_mul hr2, mul_comm (ENNReal.ofReal (1 + K.r₂)), mul_assoc]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ ≤ ENNReal.ofReal (K.lineWeight p.1) * (ENNReal.ofReal (1 + K.r₂) *
          ∑ _a : Fin 3, ∑ _b : Fin 3, ∑ _c : Fin 3, ENNReal.ofReal (1 / (2 * π)) * E) := by
        gcongr with a _ b _ c _
        exact mt_sum hm S H a b c p
    _ = ENNReal.ofReal (K.lineWeight p.1) *
          (ENNReal.ofReal (1 + K.r₂) * (27 * ENNReal.ofReal (1 / (2 * π))) * E) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Breakdown.CellCert.CellAnalysis.SharpMxThirdSeries.Internal

namespace Breakdown.CellCert.CellAnalysis

theorem thirdSeries_holds : ThirdSeriesStatement := by
  intro K hK m hm v G H hs
  exact SharpMxThirdSeries.Internal.third_holds K hK hm hs

end Breakdown.CellCert.CellAnalysis

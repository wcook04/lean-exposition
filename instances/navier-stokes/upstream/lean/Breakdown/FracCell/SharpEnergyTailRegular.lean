import Breakdown.FracCell.SharpYSharpEnergyTail
import Breakdown.FracCell.SharpYDensityRegular
import Breakdown.FracCell.SharpYChargeRegular

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpEnergyTailRegular.Internal

open SteadyCert Assembly SharpParts

theorem third_coef (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) :
    modeThird m n H a b c p =
      SharpYChargeRegular.Internal.sliceCoef m n (fun θ T => frameThird θ T a b c) H p := by
  rw [ModeSquareIntegrable.Internal.modeThird_eq]
  rfl

theorem third_sum (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m)
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH1 : AEStronglyMeasurable H volume)
    (hH2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (a b c : Fin 3) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m n H a b c p‖ ^ 2) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * ‖modeThird m n H a b c p‖ ^ 2) := by
  have h2 : MemLp H 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hH1).2 ((hH2.const_mul 9).mono'
      ((hH1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ModeSquareIntegrable.Internal.bil_norm_sq_le (H y)
  have hfin : ∫⁻ y, ‖H y‖ₑ ^ 2 ≠ ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hH1).1 h2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi.ne
  have HH := SharpYChargeRegular.Internal.mode_sum K hK m hm hH1 (fun θ T => frameThird θ T a b c)
    (ModeSquareIntegrable.Internal.frameThird_cont a b c) (fun y => ‖H y‖ₑ ^ 2)
    (hH1.enorm.pow_const 2) hfin (fun p _ θ => by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (ModeSquareIntegrable.Internal.frameThird_bound θ _ a b c))
  simp only [third_coef]
  exact HH

theorem second_sum (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m)
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH1 : AEStronglyMeasurable H volume)
    (hH2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * secondModeSq m n H p) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * secondModeSq m n H p) := by
  have hT := fun a b c => third_sum K hK m hm hH1 hH2 a b c
  have e : ∀ n : ℤ, (fun p : ℝ × ℝ => p.1 * secondModeSq m n H p) =
      fun p => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, p.1 * ‖modeThird m n H a b c p‖ ^ 2 := by
    intro n; funext p; simp only [secondModeSq, Finset.mul_sum]
  have hi : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ =>
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, p.1 * ‖modeThird m n H a b c p‖ ^ 2) K.rect :=
    fun n => integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun c _ => (hT a b c).1 n
  refine ⟨fun n => by rw [e n]; exact hi n, ?_⟩
  have e2 : (fun n : ℤ => ∫ p in K.rect, p.1 * secondModeSq m n H p) =
      fun n => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∫ p in K.rect, p.1 * ‖modeThird m n H a b c p‖ ^ 2 := by
    funext n
    rw [e n, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun c _ => (hT a b c).1 n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun c _ => (hT a b c).1 n]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun c _ => (hT a b c).1 n]
  rw [e2]
  exact summable_sum fun a _ => summable_sum fun b _ => summable_sum fun c _ => (hT a b c).2

theorem curlGrad_le (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    curlGradModeSq m n H p ≤ 27 * secondModeSq m n H p := by
  have e1 : curlGradModeSq m n H p = ∑ c : Fin 3, curlSq (fun a b => modeThird m n H a b c p) := by
    unfold curlGradModeSq curlSq
    exact Finset.sum_comm
  have e2 : secondModeSq m n H p = ∑ c : Fin 3, sumSq (fun a b => modeThird m n H a b c p) := by
    simp only [secondModeSq, sumSq, Fin.sum_univ_three]
    ring
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => SharpYDensityRegular.Internal.curlSq_le _

theorem modeEnergy_summable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (x : FieldTuple k)
    (hK : IsCellBox K) (hm : 0 < c.order) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) :
    Summable (SharpEnergyTailParts.modeEnergyAt c K x) := by
  obtain ⟨hi, hsum⟩ := second_sum K hK c.order hm hs.measurable_second hs.second_two
  set C : ℝ := |c.innerWeight - c.coercivity| + 27 * |c.splitVisc - c.innerWeight| with hC
  refine Summable.of_norm_bounded (hsum.mul_left C) fun n => ?_
  unfold SharpEnergyTailParts.modeEnergyAt
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hi n).const_mul C)
    ((ae_restrict_iff' (LowEntry.Internal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_))
  have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have s0 : 0 ≤ secondModeSq c.order n x.2.2.1 p := by unfold secondModeSq; positivity
  have c0 : 0 ≤ curlGradModeSq c.order n x.2.2.1 p := by unfold curlGradModeSq; positivity
  have c1 := curlGrad_le c.order n x.2.2.1 p
  have hb : |(c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
      + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p| ≤
      C * secondModeSq c.order n x.2.2.1 p := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg s0, abs_of_nonneg c0, hC]
    nlinarith [abs_nonneg (c.splitVisc - c.innerWeight), abs_nonneg (c.innerWeight - c.coercivity)]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  calc p.1 * |(c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
        + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p|
      ≤ p.1 * (C * secondModeSq c.order n x.2.2.1 p) := mul_le_mul_of_nonneg_left hb h0
    _ = C * (p.1 * secondModeSq c.order n x.2.2.1 p) := by ring

end Breakdown.CellCert.CellAnalysis.SharpEnergyTailRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

theorem energyTailRegular_of_series (hM : ModeSeriesStatement) : EnergyTailRegularStatement := by
  intro α _ _ k N c hc K S B Cl slots R hD _ x hx
  have hK := hD.box
  have hS := hD.scalars
  have hs : SteadyCert.IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  exact ⟨SharpEnergyTailRegular.Internal.modeEnergy_summable c K x hK hm hs,
    (SharpYDensityRegular.Internal.absorb_facts c K S x α hK hS hs hm hM absorbGrowth).2⟩

end Breakdown.CellCert.CellAnalysis

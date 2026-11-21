import Breakdown.FracCert.StHeldParts
import Breakdown.Weak.SliceEmbedding
import Breakdown.Weak.PairingVelocity
import Breakdown.Weak.VelocityWeakGradient
import Breakdown.Weak.ZeroGradient
import Breakdown.Weak.GradientFreqTr

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace EmbedWeak.Internal

theorem apply_eq_sum (L : Space →L[ℝ] Space) (w : Space) :
    L w = ∑ i : Fin 3, w i • L (unitVector i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp [unitVector, EuclideanSpace.basisFun_apply]

theorem norm_le_sum (L : Space →L[ℝ] Space) : ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun w => ?_
  rw [apply_eq_sum L w]
  calc ‖∑ i : Fin 3, w i • L (unitVector i)‖ ≤ ∑ i : Fin 3, ‖w i • L (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖w i‖ * ‖L (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖w‖ * ‖L (unitVector i)‖ := by
        gcongr with i
        exact PiLp.norm_apply_le w i
    _ = (∑ i : Fin 3, ‖L (unitVector i)‖) * ‖w‖ := by rw [← Finset.mul_sum, mul_comm]

theorem norm_sq_le (L : Space →L[ℝ] Space) : ‖L‖ ^ 2 ≤ 3 * entrySq L := by
  have h1 := norm_le_sum L
  have h0 := norm_nonneg L
  unfold entrySq
  simp only [Fin.sum_univ_three] at h1 ⊢
  have a0 := norm_nonneg (L (unitVector 0))
  have a1 := norm_nonneg (L (unitVector 1))
  have a2 := norm_nonneg (L (unitVector 2))
  nlinarith [sq_nonneg (‖L (unitVector 0)‖ - ‖L (unitVector 1)‖),
    sq_nonneg (‖L (unitVector 0)‖ - ‖L (unitVector 2)‖),
    sq_nonneg (‖L (unitVector 1)‖ - ‖L (unitVector 2)‖)]

theorem integrable_norm_sq {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hG : Integrable (fun y => entrySq (G y))) : Integrable (fun y => ‖G y‖ ^ 2) := by
  refine (hG.const_mul 3).mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_sq_le (G y)

theorem le_ofReal_add {a b : ℝ≥0∞} (ha : a ≠ ⊤) : a ≤ ENNReal.ofReal (a.toReal + b.toReal) := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right ENNReal.toReal_nonneg)

theorem le_ofReal_add' {a b : ℝ≥0∞} (hb : b ≠ ⊤) : b ≤ ENNReal.ofReal (a.toReal + b.toReal) := by
  calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left ENNReal.toReal_nonneg)

end EmbedWeak.Internal

open EmbedWeak.Internal in
theorem embedWeak : EmbedWeakStatement := by
  intro v G _ hv hGm hG hw hdiv
  have hG2 := integrable_norm_sq hGm hG
  have hGL : MemLp G 2 volume := (memLp_two_iff_integrable_sq_norm hGm).2 hG2
  have hv6 : MemLp v ((6 : ℕ) : ℝ≥0∞) volume := by simpa using hv
  have hvi : Integrable (fun y => ‖v y‖ ^ 6) := hv6.integrable_norm_pow (by norm_num)
  have hA : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 6) ≠ ⊤ := hvi.lintegral_lt_top.ne
  have hB : ∫⁻ y, ENNReal.ofReal (‖G y‖ ^ 2) ≠ ⊤ := hG2.lintegral_lt_top.ne
  set C : ℝ := (∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 6)).toReal + (∫⁻ y, ENNReal.ofReal (‖G y‖ ^ 2)).toReal
  have hs : WeakProfile.IsSlice v G C :=
    { grad := ⟨hv.locallyIntegrable (by norm_num), hGL.locallyIntegrable (by norm_num),
        fun φ hφ i => by rw [hw φ hφ i, neg_neg]⟩
      div := by
        filter_upwards [hdiv] with y hy
        simpa [unitVector, EuclideanSpace.inner_single_right] using hy
      six := le_ofReal_add hA
      two := le_ofReal_add' hB }
  obtain ⟨x, h1, h2, -⟩ := WeakProfile.sliceEmbedding_holds WeakProfile.pairingVelocity_holds
    WeakProfile.velocityWeakGradient_holds WeakProfile.zeroGradientSix_holds
    WeakProfile.gradientFreqTr_holds v G C hs
  exact ⟨x, h1, fun j => h2 j⟩

end SteadyCert

end Breakdown

import Breakdown.CertCell.BridgeStatements

open scoped ComplexConjugate

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

theorem modeAverage_neg_eq_conj {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage (-ι) f b = conj (modeAverage ι f b) := by
  unfold modeAverage
  rw [map_mul, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · simp only [map_div₀, map_one, map_mul, Complex.conj_ofReal, map_ofNat]
  · refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [← intervalIntegral.intervalIntegral_conj]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
    congr 2
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    push_cast
    ring

theorem modeConjugate : ModeConjugateHolds := by
  intro v G H ξ σ y
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact modeAverage_neg_eq_conj ξ _ i
  · funext ij
    exact modeAverage_neg_eq_conj ξ _ ij
  · funext ijl
    exact modeAverage_neg_eq_conj ξ _ ijl

end Bridge

end CertCell

end Breakdown

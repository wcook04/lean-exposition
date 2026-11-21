import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.RExports

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

theorem profileMoments_of (h1 : MildOfWeakProfileStatement) (h2 : MildSmoothingStatement)
    (h3 : SimOpComposeStatement) (h4 : SimOpMomentsStatement) : ProfileMomentsStatement := by
  intro α hα hα' a U hU
  obtain ⟨⟨F, hG, hK, -⟩, -⟩ := Freq.fracFramework_holds α hα
  have hF : IsConcreteFrame α F := ⟨hG, hK⟩
  have hmild := h1 α hα hα' a U hU F hF (3 / 4) (by norm_num) (by norm_num)
  have hhalf := h2 α hα hα' F hF _ (3 / 4) (by norm_num) hmild (1 / 2) ⟨by norm_num, by norm_num⟩
  have hmom := h4 α a 2 hα (by norm_num) _ hhalf
  obtain ⟨hone, hcomp⟩ := h3 α a hα
  have heq : simOp α a 2 (simOp α a (1 - 1 / 2) U) = U := by
    rw [hcomp 2 (1 - 1 / 2) (by norm_num) (by norm_num)]
    have : (2 : ℝ) * (1 - 1 / 2) = 1 := by norm_num
    rw [this, hone]
  rw [heq] at hmom
  exact hmom

end Breakdown.FracCert

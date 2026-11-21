import Breakdown.FracCert.StDecay

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

private theorem profileDecay_of_parts (hB : ProfileDecayBaseStatement)
    (hS : ProfileDecayStepStatement) {α a : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) {U : X}
    (hU : IsWeakRotatingProfile α a U) (hm : HasAllMoments U) : ProfileDecay α U := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | _
    · obtain ⟨C, hC⟩ := hB α h1 h2 a U hU hm
      refine ⟨C, fun y => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      simpa using hC y
    · exact hS α h1 h2 a U hU hm j ih

theorem weakToProfile_of (hM : ProfileMomentsStatement) (hR : WeakProfileRegularStatement)
    (hB : ProfileDecayBaseStatement) (hS : ProfileDecayStepStatement)
    (hPw : PowerDecayStatement) (hPr : PressureDecayStatement) (hN : ProfileNonzeroStatement) :
    WeakToProfileStatement := by
  intro α h1 h2 hW
  obtain ⟨a, U, hU⟩ := hW
  have hm := hM α h1 h2 a U hU
  obtain ⟨hV, hdiv, P, hP, hres⟩ := hR α h1 h2 a U hU hm
  have hD := profileDecay_of_parts hB hS h1 h2 hU hm
  obtain ⟨hPws, hPwd⟩ := hPw α h1 h2 a U hU hm hD
  have hPrd := hPr α h1 h2 a U hU hm hD P hP hres
  obtain ⟨y₀, hy₀⟩ := hN U hU.1 hm
  refine ⟨profileField U, P, a, 1, one_pos, hV, hP, hPws, hres, hdiv, ⟨y₀, hy₀⟩, fun j => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD j
  obtain ⟨C₂, hC₂⟩ := hPrd j
  obtain ⟨C₃, hC₃⟩ := hPwd j
  refine ⟨max C₁ (max C₂ C₃), fun y => ⟨?_, ?_, ?_⟩⟩
  · exact (hC₁ y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _))
  · exact (hC₂ y).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (by positivity) _))
  · exact (hC₃ y).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (by positivity) _))

end Breakdown.FracCert

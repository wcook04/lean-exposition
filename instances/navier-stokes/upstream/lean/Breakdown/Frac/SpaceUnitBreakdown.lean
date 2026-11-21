import Breakdown.Frac.StSpaceReg
import Breakdown.Frac.StSpaceBlowup
import Breakdown.Frac.StProfile

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracSpaceUnitBreakdown

theorem isMildOnIcc_of_isMildOn {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {κ : ℝ} (F : ScaledMildFramework X κ) {u : ℝ → X} {a b T : ℝ}
    (h : F.IsMildOn u a b) (hTb : T < b) : F.IsMildOnIcc u a T := by
  have hsub : Icc a T ⊆ Ico a b := Icc_subset_Ico_right hTb
  exact ⟨h.1.mono hsub, fun t ht => h.2 t (hsub ht)⟩

end FracSpaceUnitBreakdown

theorem fracSpaceUnitBreakdown_of (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (h1 : FracMildBlowup)
    (h2 : FracProfileOrbit) (h3 : FracMildRegularStatement α) (h4 : FracRestrictStatement)
    (h5 : FracUniquenessStatement) (h6 : FracOrbitRateFalseStatement α) :
    FracSpaceUnitBreakdownStatement α := by
  intro hW
  obtain ⟨a, U, P, hU, F, hG, hK, hD, hdat⟩ := h1 α hα hα2 hW
  obtain ⟨φ, u, hφ, hu0, -, hu, C, κ, hκ, hrate⟩ := hdat 1 one_pos
  have horb := h2 α hα hα2 a U P hU F hG hK hD 1 one_pos
  refine ⟨φ, hφ.1, hφ.2.1, hφ.2.2, ?_⟩
  rintro ⟨v, q, hv, C', hC'⟩
  have hcont : ContinuousOn (fun z : ℝ × Space => v z.1 z.2) (Icc 0 1 ×ˢ univ) :=
    hv.smooth_velocity.continuousOn.mono (Set.prod_mono Icc_subset_Ici_self Subset.rfl)
  refine h6 F hD _ _ 1 horb u C κ hκ hrate v hcont ?_
  intro t ht
  have hT0 : (0 : ℝ) < (t + 1) / 2 := by linarith [ht.1]
  have hT1 : (t + 1) / 2 < 1 := by linarith [ht.2]
  have htT : t ∈ Icc 0 ((t + 1) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hmild := FracSpaceUnitBreakdown.isMildOnIcc_of_isMildOn F hu hT1
  obtain ⟨W, Q, hWs, hW0, hWE, hWB, hWv⟩ := h3 F hG hK φ hφ u ((t + 1) / 2) hT0 hmild hu0
  have hvs := h4 α φ v q hv hφ.2.2 ((t + 1) / 2)
  have h0 : W 0 = v 0 := by
    rw [hW0]
    funext x
    exact (hv.initial x).symm
  have hvE : EnergyBoundedOn ((t + 1) / 2) v := ⟨C', fun s hs => hC' s hs.1⟩
  have heq := h5 α hα hα2 ((t + 1) / 2) W v Q q hWs hvs hWE hvE hWB h0
  rw [← heq t htT]
  exact hWv t htT

end Breakdown

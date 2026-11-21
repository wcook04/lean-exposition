import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CertReduction

def SmoothSupNormBoundHolds : Prop :=
  ∀ u : Space → Space, ContDiff ℝ ∞ u → MemLp u 6 volume →
    Integrable (fun y => matSq (fderiv ℝ u y)) →
    Integrable (fun y => ‖sumSecondPartialsAt u y‖ ^ 2) →
    ∀ x, ‖u x‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ y, matSq (fderiv ℝ u y)) *
      Real.sqrt (∫ y, ‖sumSecondPartialsAt u y‖ ^ 2)

def WeakFieldMollifyHolds : Prop :=
  ∀ (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsWeakGradient w G →
    (∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j))) →
    (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) < ⊤ →
    (∫⁻ y, ENNReal.ofReal (matSq (G y))) < ⊤ →
    (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) < ⊤ →
    ∃ u : ℕ → Space → Space,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, MemLp (u n) 6 volume) ∧
      (∀ n, Integrable (fun y => matSq (fderiv ℝ (u n) y))) ∧
      (∀ n, Integrable (fun y => ‖sumSecondPartialsAt (u n) y‖ ^ 2)) ∧
      (∀ n, (∫ y, matSq (fderiv ℝ (u n) y)) ≤ ∫ y, matSq (G y)) ∧
      (∀ n, (∫ y, ‖sumSecondPartialsAt (u n) y‖ ^ 2) ≤ ∫ y, ‖secondDerivTrace (H y)‖ ^ 2) ∧
      ∀ᵐ y, Tendsto (fun n => u n y) atTop (𝓝 (w y))

theorem sliceSupNorm_of (hs : SmoothSupNormBoundHolds) (hm : WeakFieldMollifyHolds) :
    SliceSupNormHolds := by
  intro w G H hG hH hw hGs hHs
  obtain ⟨u, hsm, h6, hGi, hLi, hGb, hLb, hlim⟩ := hm w G H hG hH hw hGs hHs
  filter_upwards [hlim] with y hy
  have hc : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hb : ∀ n, ‖u n y‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ z, matSq (G z)) *
      Real.sqrt (∫ z, ‖secondDerivTrace (H z)‖ ^ 2) := by
    intro n
    refine (hs (u n) (hsm n) (h6 n) (hGi n) (hLi n) y).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hGb n)) hc)
      (Real.sqrt_le_sqrt (hLb n)) (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))
  have ht : Tendsto (fun n => ‖u n y‖ ^ 2) atTop (𝓝 (‖w y‖ ^ 2)) := hy.norm.pow 2
  exact le_of_tendsto' ht hb

end CertReduction

end Breakdown

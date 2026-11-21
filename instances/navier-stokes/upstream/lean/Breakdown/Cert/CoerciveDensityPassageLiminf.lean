import Breakdown.Cert.CoercivePieceDensityPassageLimit

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassage

theorem tsum_add_le_liminf {x : ℕ → ℤ × ℤ → ℝ≥0∞} {x₀ : ℤ × ℤ → ℝ≥0∞} {K : ℕ → ℝ≥0∞} {K₀ : ℝ≥0∞}
    (h : ∀ ι, Tendsto (fun n => x n ι) atTop (𝓝 (x₀ ι))) (hK : Tendsto K atTop (𝓝 K₀)) :
    (∑' ι, x₀ ι) + K₀ ≤ liminf (fun n => (∑' ι, x n ι) + K n) atTop := by
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_add]
  refine iSup_le fun s => ?_
  have ht : Tendsto (fun n => (∑ ι ∈ s, x n ι) + K n) atTop (𝓝 ((∑ ι ∈ s, x₀ ι) + K₀)) :=
    (tendsto_finsetSum s fun ι _ => h ι).add hK
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => add_le_add (ENNReal.sum_le_tsum s) le_rfl)

theorem splitLeft_eq (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ) (J : ℝ → Space → ℝ) (σ : ℝ) (y : Space) :
    splitLeft Pos Rest (fun _ _ => 0) J σ y =
      (∑' ι, (ENNReal.ofReal (Pos σ y ι) + ENNReal.ofReal (Rest σ y ι))) + ENNReal.ofReal (J σ y) := by
  simp only [splitLeft, ENNReal.ofReal_zero, add_zero]
  rw [ENNReal.tsum_add]

theorem splitLeft_le_liminf {Pos Rest : ℕ → ℝ → Space → ℤ × ℤ → ℝ} {J : ℕ → ℝ → Space → ℝ}
    {Pos₀ Rest₀ : ℝ → Space → ℤ × ℤ → ℝ} {J₀ : ℝ → Space → ℝ} {σ : ℝ} {y : Space}
    (hp : ∀ ι, Tendsto (fun n => Pos n σ y ι) atTop (𝓝 (Pos₀ σ y ι)))
    (hr : ∀ ι, Tendsto (fun n => Rest n σ y ι) atTop (𝓝 (Rest₀ σ y ι)))
    (hj : Tendsto (fun n => J n σ y) atTop (𝓝 (J₀ σ y))) :
    splitLeft Pos₀ Rest₀ (fun _ _ => 0) J₀ σ y ≤
      liminf (fun n => splitLeft (Pos n) (Rest n) (fun _ _ => 0) (J n) σ y) atTop := by
  simp only [splitLeft_eq]
  exact tsum_add_le_liminf
    (fun ι => ((ENNReal.continuous_ofReal.tendsto _).comp (hp ι)).add ((ENNReal.continuous_ofReal.tendsto _).comp (hr ι)))
    ((ENNReal.continuous_ofReal.tendsto _).comp hj)

end Internal.DensityPassage

end Coercive

end Breakdown

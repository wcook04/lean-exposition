import Breakdown.FracCell.GivenAuxActuatorOpen

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem ofComponents_sum (s : Finset ℤ) (w : ℤ → Fin 3 → ℝ) :
    ofComponents (fun i => ∑ n ∈ s, w n i) = ∑ n ∈ s, ofComponents (w n) := by
  ext j
  fin_cases j <;> simp [ofComponents]

theorem fieldOf_eq_sum_modes (P : ChartParams) (D : FieldData) (β : ℝ) :
    fieldOf P D β = fun y => ∑ n ∈ D.modes, modeFieldOf P D β n y := by
  funext y
  unfold fieldOf modeFieldOf
  rw [← ofComponents_sum]
  congr 1
  funext i
  rw [Finset.mul_sum, Complex.re_sum]

theorem fieldOf_contDiff_of_compact (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} {D : FieldData}
    (hc : IsCompactFieldData P e tb D) (hpos : 0 < tb) (β : ℝ) : ContDiff ℝ 1 (fieldOf P D β) := by
  rw [fieldOf_eq_sum_modes]
  apply ContDiff.sum
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    exact modeFieldOf_contDiff_mean P hP hc hpos β hn
  · exact modeFieldOf_contDiff_wave P hP hc hpos β n hn h0

end GivenFields

end CellCert

end Breakdown

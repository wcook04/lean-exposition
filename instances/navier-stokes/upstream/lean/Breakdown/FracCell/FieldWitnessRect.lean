import Breakdown.FracCell.FieldWitnessSt

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def RectOffStatement : Prop :=
  ∀ (q : ℕ) (r0 r1 z0 z1 lam vr vz a : ℝ), 0 < lam → r0 < r1 → z0 < z1 → 0 ≤ a →
    IntervalCertificate q (lam * (r1 - r0) ^ 2 / 4) vr → IntervalCertificate q (lam * (z1 - z0) ^ 2 / 4) vz →
    ∀ P : ℝ[X][X], P.natDegree ≤ q → (∀ j, (P.coeff j).natDegree ≤ q) →
      ∃ Q : ℝ → ℝ → ℝ, ContDiff ℝ 1 (Function.uncurry Q) ∧
        (∀ z, Q r0 z = 0) ∧ (∀ z, Q r1 z = 0) ∧ (∀ r, Q r z0 = 0) ∧ (∀ r, Q r z1 = 0) ∧
        (∫ r in r0..r1, ∫ z in z0..z1, ((twoVarEval P r z - Q r z) ^ 2
            + lam⁻¹ * (deriv (fun s => Q s z) r ^ 2 + deriv (fun t => Q r t) z ^ 2 + a * Q r z ^ 2)))
          ≤ (vr + vz + ratioFn lam a) * ∫ r in r0..r1, ∫ z in z0..z1, twoVarEval P r z ^ 2

def RectAxisStatement : Prop :=
  ∀ (q i : ℕ) (R z0 z1 lam ν va vz : ℝ) (χ : ℝ → ℝ), 0 < lam → 0 < R → z0 < z1 → i ≤ 1 →
    ν ≤ lam * R ^ 2 → AxisCertificate q ν va χ → IntervalCertificate q (lam * (z1 - z0) ^ 2 / 4) vz →
    ∀ P : ℝ[X][X], P.natDegree ≤ q → (∀ j, (P.coeff j).natDegree ≤ q) → (i = 1 → X ∣ P) →
      ∃ u : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (u j)) ∧ (∀ j, u j z0 = 0 ∧ u j z1 = 0) ∧ (i = 1 → u 0 = 0) ∧
        (∫ r in (0 : ℝ)..R, ∫ z in z0..z1,
            ((twoVarEval P r z - χ (r / R) * ∑ j ∈ Finset.range (q + 1), r ^ j * u j z) ^ 2
              + lam⁻¹ * (deriv (fun s => χ (s / R) * ∑ j ∈ Finset.range (q + 1), s ^ j * u j z) r ^ 2
                + (χ (r / R) * ∑ j ∈ Finset.range (q + 1), r ^ j * deriv (u j) z) ^ 2
                + (i : ℝ) ^ 2 * (χ (r / R) * ∑ j ∈ Finset.range (q + 1), r ^ j * u j z) ^ 2 / r ^ 2)) * r)
          ≤ (va + vz) * ∫ r in (0 : ℝ)..R, ∫ z in z0..z1, twoVarEval P r z ^ 2 * r

end Spectral

end CellCert

end Breakdown

import Breakdown.CellReduction.AdjointAssemblyBasics
import Breakdown.CellReduction.AdjointStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

theorem transposeApply_add (K₁ K₂ : Space →L[ℝ] Space) (z : Space) :
    transposeApply (K₁ + K₂) z = transposeApply K₁ z + transposeApply K₂ z := by
  simp only [transposeApply, ContinuousLinearMap.add_apply, inner_add_left, add_smul, Finset.sum_add_distrib]

theorem transposeApply_smul (c : ℝ) (K : Space →L[ℝ] Space) (z : Space) :
    transposeApply (c • K) z = c • transposeApply K z := by
  simp only [transposeApply, ContinuousLinearMap.smul_apply, real_inner_smul_left, Finset.smul_sum, smul_smul]

theorem transposeApply_zero (z : Space) : transposeApply 0 z = 0 := by
  simp [transposeApply]

theorem transposeApply_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (K : ι → Space →L[ℝ] Space) (z : Space) :
    transposeApply (∑ i ∈ s, c i • K i) z = ∑ i ∈ s, c i • transposeApply (K i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [transposeApply_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, transposeApply_add, transposeApply_smul, ih]

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem norm_transposeApply_le (K : Space →L[ℝ] Space) (z : Space) :
    ‖transposeApply K z‖ ≤ 3 * (‖K‖ * ‖z‖) := by
  unfold transposeApply
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖inner ℝ (K (unitVector i)) z • unitVector i‖ ≤ ‖K‖ * ‖z‖ := by
    intro i
    rw [norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := K.le_opNorm (unitVector i)
    rw [norm_unitVector, mul_one] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg z)
  calc ∑ i : Fin 3, ‖inner ℝ (K (unitVector i)) z • unitVector i‖ ≤ ∑ _i : Fin 3, ‖K‖ * ‖z‖ :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * (‖K‖ * ‖z‖) := by simp

theorem transport_split {k : ℕ} (P Pc : ℝ) (rate q : Fin k → ℝ) (E : Finset (Fin k))
    (W c e ζ : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space)
    (hP : 1 / P = 1 / Pc + ∑ i, q i * rate i)
    (hW : ∀ σ y, W σ y = c σ y + (∑ i ∈ E, q i • b i σ y) + e σ y)
    (hc : ∀ σ y, DifferentiableAt ℝ (c σ) y) (hb : ∀ i ∈ E, ∀ σ y, DifferentiableAt ℝ (b i σ) y)
    (he : ∀ σ y, DifferentiableAt ℝ (e σ) y) (σ : ℝ) (y : Space) :
    adjointTransport P W ζ σ y = adjointTransport Pc c ζ σ y
      + (∑ i ∈ E, q i • (advectionShift (b i) ζ σ y - rate i • timeDerivative ζ σ y))
      + advectionShift e ζ σ y - (∑ i ∈ Eᶜ, q i * rate i) • timeDerivative ζ σ y := by
  have hWf : W σ = fun y => c σ y + (∑ i ∈ E, q i • b i σ y) + e σ y := funext (hW σ)
  have hd : fderiv ℝ (W σ) y = fderiv ℝ (c σ) y + (∑ i ∈ E, q i • fderiv ℝ (b i σ) y) + fderiv ℝ (e σ) y := by
    rw [hWf]
    have H := (((hc σ y).hasFDerivAt.add (HasFDerivAt.sum (u := E) fun i hi =>
      ((hb i hi σ y).hasFDerivAt.const_smul (q i)))).add (he σ y).hasFDerivAt)
    have hfun : (c σ + (∑ i ∈ E, q i • b i σ) + e σ) = fun y => c σ y + (∑ i ∈ E, q i • b i σ y) + e σ y := by
      funext x
      simp [Finset.sum_apply]
    rw [hfun] at H
    exact H.fderiv
  have hsplit : (∑ i, q i * rate i) = (∑ i ∈ E, q i * rate i) + ∑ i ∈ Eᶜ, q i * rate i :=
    (Finset.sum_add_sum_compl E _).symm
  have hfit : (∑ i ∈ E, q i • (advectionShift (b i) ζ σ y - rate i • timeDerivative ζ σ y)) =
      (∑ i ∈ E, q i • transposeApply (fderiv ℝ (b i σ) y) (ζ σ y))
        - (∑ i ∈ E, q i • fderiv ℝ (ζ σ) y (b i σ y)) - (∑ i ∈ E, q i * rate i) • timeDerivative ζ σ y := by
    simp only [advectionShift, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
  rw [hfit]
  simp only [adjointTransport, advectionShift, hd, hP, hsplit, transposeApply_add, transposeApply_sum,
    hW σ y, map_add, map_sum, map_smul]
  module

theorem coord_le_bound {k : ℕ} (d : ExtendedCertificateData k) (j : Fin k) (r : AdjointDefectEntry k)
    (hcert : AdjointDefectBounded d j r) {q : Fin k → ℝ} (hq : q ∈ d.params) (i : Fin k) :
    |q i| ≤ r.coordBound i := by
  classical
  by_cases hi : i ∈ d.adjointSet
  · exact (hq.1 i hi).trans (hcert.coordBound_adjoint i hi)
  · have hic : i ∈ d.adjointSetᶜ := Finset.mem_compl.2 hi
    obtain ⟨hs, hR⟩ := hcert.coordBound_stiff i hic
    have h1 : (d.scale i * q i) ^ 2 ≤ d.stiffRadius ^ 2 :=
      (Finset.single_le_sum (f := fun j => (d.scale j * q j) ^ 2) (fun j _ => sq_nonneg _) hic).trans hq.2
    have h2 : |d.scale i * q i| ≤ |d.stiffRadius| := sq_le_sq.1 h1
    rw [abs_mul] at h2
    have hpos : 0 < |d.scale i| := abs_pos.2 hs
    exact le_of_mul_le_mul_left (h2.trans hR) hpos

theorem matrixPairing_add (G K M : Space →L[ℝ] Space) : matInner G (K + M) = matInner G K + matInner G M := by
  simp only [matInner, ContinuousLinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem matrixPairing_sub (G K M : Space →L[ℝ] Space) : matInner G (K - M) = matInner G K - matInner G M := by
  simp only [matInner, ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]

theorem matrixPairing_smul (G K : Space →L[ℝ] Space) (c : ℝ) : matInner G (c • K) = c * matInner G K := by
  simp only [matInner, ContinuousLinearMap.smul_apply, real_inner_smul_right, Finset.mul_sum]

theorem matrixPairing_zero (G : Space →L[ℝ] Space) : matInner G 0 = 0 := by
  simp [matInner]

theorem matrixPairing_sum {ι : Type*} (s : Finset ι) (G : Space →L[ℝ] Space) (c : ι → ℝ) (K : ι → Space →L[ℝ] Space) :
    matInner G (∑ i ∈ s, c i • K i) = ∑ i ∈ s, c i * matInner G (K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixPairing_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, matrixPairing_add, matrixPairing_smul, ih]

theorem matrixPairing_pin_split {k : ℕ} (r : AdjointDefectEntry k) (G : Space →L[ℝ] Space) (σ : ℝ) (y : Space) :
    matInner G (fderiv ℝ (r.field σ) y) = matInner G (r.pinFlux σ y)
      + ∑ l, r.pinCoef l * matInner G (fderiv ℝ (r.pins.generator l σ) y
        - ContinuousLinearMap.adjoint (fderiv ℝ (r.pins.generator l σ) y)) := by
  rw [← matrixPairing_sum, ← matrixPairing_add]
  congr 1
  simp [AdjointDefectEntry.pinFlux]

end Internal

end AdjointDefect

end Breakdown

import Breakdown.FracCert.DecayPressureParts

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert.DecayPressureModel

open Breakdown.Freq

private theorem multiplier_homogeneous (i j : Fin 3) : IsHomogeneousSymbol (pressureMultiplier i j) 0 := by
  refine ⟨?_, fun c hc ξ hξ => ?_⟩
  · intro ξ hξ
    have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hξ)
    have h1 : ContDiffAt ℝ ∞ (fun ζ : Space => -(ζ i * ζ j / ‖ζ‖ ^ 2)) ξ := by
      have hq : ContDiffAt ℝ ∞ (fun ζ : Space => ‖ζ‖ ^ 2) ξ := (contDiff_norm_sq ℝ).contDiffAt
      have hi : ContDiffAt ℝ ∞ (fun ζ : Space => ζ i) ξ :=
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt
      have hj : ContDiffAt ℝ ∞ (fun ζ : Space => ζ j) ξ :=
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.contDiffAt
      exact ((hi.mul hj).div hq hn).neg
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ h1).contDiffWithinAt
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    simp only [pressureMultiplier, Real.rpow_zero, Complex.ofReal_one, one_mul, PiLp.smul_apply,
      smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    congr 1
    field_simp

theorem modelPressureDecay_of (h1 : HomogeneousMultiplierStatement)
    (hP : ProductWeightedSmoothStatement) (hR : PressureRepresentationStatement) :
    ModelPressureDecayStatement := by
  intro α hα1 hα2 a U hU hM hD n
  obtain ⟨F, hT, hmo, hQ⟩ := hR α hα1 hα2 a U hU hM hD
  have hW : ∀ i j : Fin 3, IsWeightedSmooth
      (FourierTransform.fourierInv (fun ξ => pressureMultiplier i j ξ * F i j ξ)) (4 * α - 2 + 0) :=
    fun i j => h1 _ 0 (4 * α - 2) le_rfl (by linarith) (by linarith) (multiplier_homogeneous i j) _ _
      (hP α hα1 hα2 a U hU hM hD i j) (hT i j) (hmo i j)
  choose C hC using fun i j => (hW i j).2 (n + 1)
  set W := fun (i j : Fin 3) => FourierTransform.fourierInv (fun ξ => pressureMultiplier i j ξ * F i j ξ)
    with hWdef
  have hWs : ∀ i j, ContDiff ℝ ∞ (W i j) := fun i j => (hW i j).1
  have hWre : ∀ i j, ContDiff ℝ ∞ (fun y => (W i j y).re) := fun i j =>
    Complex.reCLM.contDiff.comp (hWs i j)
  have hQfun : profilePressure U = fun y => ∑ i, ∑ j, (W i j y).re := funext hQ
  refine ⟨∑ i, ∑ j, |C i j|, fun y => ?_⟩
  have hpos : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have hbound : ∀ i j, ‖iteratedFDeriv ℝ (n + 1) (fun y => (W i j y).re) y‖ ≤
      |C i j| * (1 + ‖y‖) ^ (-(4 * α - 1 + n)) := by
    intro i j
    have hle := Complex.reCLM.norm_iteratedFDeriv_comp_left (n := n + 1) ((hWs i j).contDiffAt (x := y))
      ENat.LEInfty.out
    have hc := hC i j y
    have hexp : (4 * α - 2 + 0 + ((n + 1 : ℕ) : ℝ)) = 4 * α - 1 + n := by push_cast; ring
    rw [hexp] at hc
    have hw : ‖iteratedFDeriv ℝ (n + 1) (W i j) y‖ ≤ |C i j| * (1 + ‖y‖) ^ (-(4 * α - 1 + n)) := by
      rw [Real.rpow_neg hpos.le]
      have hp2 : 0 < (1 + ‖y‖) ^ (4 * α - 1 + n) := Real.rpow_pos_of_pos hpos _
      rw [← div_eq_mul_inv, le_div_iff₀ hp2]
      calc ‖iteratedFDeriv ℝ (n + 1) (W i j) y‖ * (1 + ‖y‖) ^ (4 * α - 1 + n)
          = (1 + ‖y‖) ^ (4 * α - 1 + n) * ‖iteratedFDeriv ℝ (n + 1) (W i j) y‖ := by ring
        _ ≤ C i j := hc
        _ ≤ |C i j| := le_abs_self _
    have hre : ‖Complex.reCLM‖ ≤ 1 := by rw [Complex.reCLM_norm]
    calc ‖iteratedFDeriv ℝ (n + 1) (fun y => (W i j y).re) y‖
        ≤ ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ (n + 1) (W i j) y‖ := hle
      _ ≤ 1 * ‖iteratedFDeriv ℝ (n + 1) (W i j) y‖ :=
          mul_le_mul_of_nonneg_right hre (norm_nonneg _)
      _ ≤ |C i j| * (1 + ‖y‖) ^ (-(4 * α - 1 + n)) := by rw [one_mul]; exact hw
  rw [hQfun]
  have hsum1 : iteratedFDeriv ℝ (n + 1) (fun y => ∑ i, ∑ j, (W i j y).re) =
      ∑ i, iteratedFDeriv ℝ (n + 1) (fun y => ∑ j, (W i j y).re) :=
    iteratedFDeriv_sum fun i _ => ContDiff.sum fun j _ => ((hWre i j).of_le (by exact_mod_cast le_top))
  have hsum2 : ∀ i, iteratedFDeriv ℝ (n + 1) (fun y => ∑ j, (W i j y).re) =
      ∑ j, iteratedFDeriv ℝ (n + 1) (fun y => (W i j y).re) := fun i =>
    iteratedFDeriv_sum fun j _ => ((hWre i j).of_le (by exact_mod_cast le_top))
  rw [hsum1]
  simp only [hsum2, Finset.sum_apply]
  calc ‖∑ i, ∑ j, iteratedFDeriv ℝ (n + 1) (fun y => (W i j y).re) y‖
      ≤ ∑ i, ∑ j, ‖iteratedFDeriv ℝ (n + 1) (fun y => (W i j y).re) y‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, |C i j| * (1 + ‖y‖) ^ (-(4 * α - 1 + n)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hbound i j
    _ = (∑ i, ∑ j, |C i j|) * (1 + ‖y‖) ^ (-(4 * α - 1 + n)) := by
        rw [Finset.sum_mul]; simp only [Finset.sum_mul]

end Breakdown.FracCert.DecayPressureModel

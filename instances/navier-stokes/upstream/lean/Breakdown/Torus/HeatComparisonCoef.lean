import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic.ShellCoef.Internal

open Breakdown.Periodic Breakdown.Periodic.ShellDefs.Internal

theorem complexify_eq_vec (v : Space) : complexify v = Freq.complexifyVec v := rfl

theorem complexify_smul (c : ℝ) (v : Space) : complexify (c • v) = c • complexify v := by
  ext i
  simp [complexify]

theorem mem_cell_of_close {x : Space} (hx : ‖x - center‖ ≤ 1 / 4) : x ∈ cell := by
  intro i
  have h1 : ‖(x - center) i‖ ≤ ‖x - center‖ := PiLp.norm_apply_le _ _
  have h2 : (x - center) i = x i - 1 / 2 := by
    simp [center_apply]
  rw [h2, Real.norm_eq_abs] at h1
  have h3 := abs_le.1 (h1.trans hx)
  constructor <;> linarith [h3.1, h3.2]

theorem character_shift (k : Lattice) (s : ℝ) (y : Space) :
    character k (center + s • y) =
      character k center * Complex.exp (((-2 * π * inner ℝ y (s • freq k) : ℝ) : ℂ) * Complex.I) := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm y (freq k)]
  push_cast
  ring

theorem cell_integral_eq {μ b' : ℝ} (hμ : 0 < μ) (hb : Real.sqrt μ * b' ≤ 1 / 4) (g : Space → Space)
    (hg : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → g y = 0) (k : Lattice) :
    freqTrCoef (fun x => g (simCoord μ x)) k =
      (Real.sqrt μ) ^ 3 • (character k center •
        FourierTransform.fourier (fun x => Freq.complexifyVec (g x)) (Real.sqrt μ • freq k)) := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  unfold freqTrCoef
  have e1 : ∫ x in cell, character k x • complexify (g (simCoord μ x)) =
      ∫ x in cell, character k x • complexify (g (simLin μ x)) := by
    apply integral_congr_ae
    filter_upwards [simCoord_ae μ] with x hx
    rw [hx]
  have h2 : ∀ᵐ x ∂(volume : Measure Space), x ∉ cell →
      character k x • complexify (g (simLin μ x)) = 0 := by
    filter_upwards [(qmp_simLin hμ).ae hg] with x hx hxc
    rw [hx, complexify_eq_vec, map_zero, smul_zero]
    intro hmem
    apply hxc
    apply mem_cell_of_close
    rw [Metric.mem_closedBall, dist_zero_right, simLin, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hs] at hmem
    have h3 : ‖x - center‖ ≤ Real.sqrt μ * b' := by
      rw [inv_mul_le_iff₀ hs] at hmem
      exact hmem
    linarith
  rw [e1, setIntegral_eq_integral_of_ae_compl_eq_zero h2]
  set H : Space → Coef := fun y => character k (center + Real.sqrt μ • y) • Freq.complexifyVec (g y)
    with hH
  have e3 : (fun x => character k x • complexify (g (simLin μ x))) =
      fun x => (fun z => H ((Real.sqrt μ)⁻¹ • z)) (x - center) := by
    funext x
    simp only [hH, simLin, complexify_eq_vec]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
  rw [e3, integral_sub_right_eq_self (fun z => H ((Real.sqrt μ)⁻¹ • z)) center,
    Measure.integral_comp_inv_smul_of_nonneg volume H hs.le]
  have hd : Module.finrank ℝ Space = 3 := by simp
  rw [hd]
  congr 1
  rw [Real.fourier_eq', ← integral_smul]
  congr 1
  funext y
  simp only [hH]
  rw [character_shift, smul_smul]

theorem sqrt_cube {μ : ℝ} (hμ : 0 < μ) : (Real.sqrt μ) ^ 3 = μ ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
  norm_num

theorem sqrt_inv_cube {μ : ℝ} (hμ : 0 < μ) : (Real.sqrt μ)⁻¹ * (Real.sqrt μ) ^ 3 = μ := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul, Real.sq_sqrt hμ.le]

end Breakdown.Periodic.ShellCoef.Internal

namespace Breakdown.Periodic

open ShellCoef.Internal

theorem sourceCoefFormula : SourceCoefFormula := by
  intro b' μ hμ hb A hA k
  rw [cell_integral_eq hμ hb (A : Space → Space) hA k, sqrt_cube hμ]
  rfl

theorem transplantCoefFormula : TransplantCoefFormula := by
  intro φ _ b' μ hμ hb hsupp k
  have hg : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → φ y = 0 :=
    Filter.Eventually.of_forall fun y hy => image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)
  have e : freqTrCoef (transplantField μ φ) k =
      (Real.sqrt μ)⁻¹ • freqTrCoef (fun x => φ (simCoord μ x)) k := by
    unfold freqTrCoef transplantField
    simp_rw [complexify_smul, smul_comm (character k _) ((Real.sqrt μ)⁻¹ : ℝ)]
    rw [integral_smul]
  rw [e, cell_integral_eq hμ hb φ hg k, smul_smul, sqrt_inv_cube hμ]
  rfl

end Breakdown.Periodic

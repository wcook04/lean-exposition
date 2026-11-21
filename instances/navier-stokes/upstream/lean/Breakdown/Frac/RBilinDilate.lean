import Breakdown.Frac.StRealize
import Breakdown.FreqTr.FieldOp
import Breakdown.FreqTr.BilinDilate

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.BilinDilate

open Breakdown.Freq Breakdown.Freq.Internal.BilinDilate

theorem pow_three_eq {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (3 / (2 * α)) = (μ ^ (1 / (2 * α))) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
  congr 1
  push_cast
  ring

theorem pw_neg {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (-(1 / (2 * α))) = (μ ^ (1 / (2 * α)))⁻¹ :=
  Real.rpow_neg hμ.le _

theorem pw_main {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (1 - 3 / (2 * α)) = μ * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹ := by
  rw [Real.rpow_sub hμ, Real.rpow_one, pow_three_eq hμ, div_eq_mul_inv]

theorem pw_inv_neg {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ⁻¹ ^ (-(1 / (2 * α))) = μ ^ (1 / (2 * α)) := by
  rw [Real.inv_rpow hμ.le, pw_neg hμ, inv_inv]

theorem pw_inv_main {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ⁻¹ ^ (1 - 3 / (2 * α)) = μ⁻¹ * (μ ^ (1 / (2 * α))) ^ 3 := by
  rw [Real.inv_rpow hμ.le, pw_main hμ, mul_inv, inv_inv]

theorem pw_vel {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    μ ^ (1 - 1 / (2 * α)) = μ * (μ ^ (1 / (2 * α)))⁻¹ := by
  rw [Real.rpow_sub hμ, Real.rpow_one, div_eq_mul_inv]

theorem pw_back {μ α : ℝ} (hμ : 0 < μ) (hα : α ≠ 0) :
    (μ ^ (1 / (2 * α))) ^ (2 * α) = μ := by
  rw [← Real.rpow_mul hμ.le]
  have : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  rw [this, Real.rpow_one]

theorem fracDilX_coe {α : ℝ} (h2 : FracDilationAlgebra α) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    (fracDilX α μ x : L2C) =
      (μ ^ (1 - 3 / (2 * α))) • scaleOp (μ ^ (-(1 / (2 * α)))) (x : L2C) := by
  rw [h2.2.2.2.2 μ hμ x]
  have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  have hr := fieldOpRealized (scaleEquiv _ hc)
    (fun _ => (μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace)
    (‖(μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace‖) aestronglyMeasurable_const
    (fun _ => le_rfl)
  apply Lp.ext
  refine (hr (x : L2C)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  filter_upwards [scaleOp_ae fieldOpRealized hc (x : L2C)] with ξ h1
  rw [Pi.smul_apply, h1]
  rfl

theorem fracDilX_coe' {α : ℝ} (h2 : FracDilationAlgebra α) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    (fracDilX α μ x : L2C) =
      (μ * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹) • scaleOp (μ ^ (1 / (2 * α)))⁻¹ (x : L2C) := by
  rw [fracDilX_coe h2 hμ, pw_main hμ, pw_neg hμ]

theorem fracDilX_inv_coe {α : ℝ} (h2 : FracDilationAlgebra α) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    (fracDilX α μ⁻¹ x : L2C) =
      (μ⁻¹ * (μ ^ (1 / (2 * α))) ^ 3) • scaleOp (μ ^ (1 / (2 * α))) (x : L2C) := by
  rw [fracDilX_coe h2 (inv_pos.mpr hμ), pw_inv_main hμ, pw_inv_neg hμ]

theorem fracPhiFactor_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor; positivity

theorem fracPhiFactor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    fracPhiFactor α τ ξ ≤ 1 + τ⁻¹ := by
  unfold fracPhiFactor
  set s := 2 * π * ‖ξ‖ with hs_def
  have hs : 0 ≤ s := by positivity
  have he : Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs _
    nlinarith
  rcases le_or_gt s 1 with h1 | h1
  · have : s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
      calc s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 * 1 :=
            mul_le_mul h1 he (Real.exp_pos _).le zero_le_one
        _ = 1 := by ring
    have : 0 < τ⁻¹ := inv_pos.mpr hτ
    linarith
  · have hsp : s ≤ s ^ (2 * α) := by
      calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
        _ ≤ s ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have he2 : Real.exp (-(τ * s ^ (2 * α))) ≤ Real.exp (-(τ * s)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hex : τ * s ≤ Real.exp (τ * s) := by
      have := Real.add_one_le_exp (τ * s)
      linarith
    have hkey : τ * (s * Real.exp (-(τ * s))) ≤ 1 := by
      rw [Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      exact hex
    have hk2 : s * Real.exp (-(τ * s)) ≤ τ⁻¹ := by
      calc s * Real.exp (-(τ * s)) = τ⁻¹ * (τ * (s * Real.exp (-(τ * s)))) := by
            field_simp
        _ ≤ τ⁻¹ * 1 := mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hτ.le)
        _ = τ⁻¹ := mul_one _
    have : s * Real.exp (-(τ * s ^ (2 * α))) ≤ s * Real.exp (-(τ * s)) :=
      mul_le_mul_of_nonneg_left he2 hs
    linarith

theorem aesm_fracPhiOp (α τ : ℝ) :
    AEStronglyMeasurable (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) volume := by
  have hm : Measurable (fun ξ : Space => fracPhiFactor α τ ξ) := by
    unfold fracPhiFactor; fun_prop
  exact hm.aestronglyMeasurable.smul aestronglyMeasurable_const

theorem norm_fracPhiOp_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + τ⁻¹ := by
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (fracPhiFactor_nonneg α τ ξ)]
  have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := CSpace)
  have h2 := fracPhiFactor_le hα hτ ξ
  nlinarith [fracPhiFactor_nonneg α τ ξ]

theorem fracPhiFactor_scale {α c : ℝ} (hc : 0 < c) (τ : ℝ) (ξ : Space) :
    fracPhiFactor α (c ^ (2 * α) * τ) ξ = c⁻¹ * fracPhiFactor α τ (c • ξ) := by
  unfold fracPhiFactor
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have h1 : 2 * π * (c * ‖ξ‖) = c * (2 * π * ‖ξ‖) := by ring
  rw [h1, Real.mul_rpow hc.le (by positivity)]
  have h2 : -(c ^ (2 * α) * τ * (2 * π * ‖ξ‖) ^ (2 * α)) =
      -(τ * (c ^ (2 * α) * (2 * π * ‖ξ‖) ^ (2 * α))) := by ring
  rw [h2]
  field_simp

theorem fracPhiX_eq (α τ : ℝ) (z : X) :
    fracPhiX α τ z = toPhys (fieldOp id
      (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (z : L2C)) := rfl

theorem partialX_fracDilX {α : ℝ} (h2 : FracDilationAlgebra α) {μ : ℝ} (hμ : 0 < μ) (j : Fin 3)
    (x : X) :
    (partialX j (fracDilX α μ x) : Space → Space) =ᵐ[volume]
      fun y => μ • (partialX j x : Space → Space) (μ ^ (1 / (2 * α)) • y) := by
  have hc : 0 < μ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  have hci : 0 < (μ ^ (1 / (2 * α)))⁻¹ := inv_pos.mpr hc
  rw [partialX_eq, fracDilX_coe' h2 hμ, map_smul,
    fieldOp_id_scaleOp fieldOpRealized (aesm_derivOp j) (norm_derivOp_le j) (aesm_derivOp j)
      (norm_derivOp_le j) hci.ne' (k := 1) (fun ξ w => by rw [derivSymbol_smul j hci, one_smul]),
    one_smul, map_smul]
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [toPhys_scaleOp_ae fieldOpRealized hci
    (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (x : L2C))] with y hy
  rw [Pi.smul_apply, hy, inv_inv, smul_smul, partialX_eq]
  congr 1
  rw [inv_pow, inv_inv]
  field_simp

theorem fracPhiX_dil_inv {α : ℝ} (hα : 1 < α) (h2 : FracDilationAlgebra α) {μ τ : ℝ} (hμ : 0 < μ)
    (hτ : 0 < τ) (ψ : X) :
    (fracPhiX α (μ * τ) (fracDilX α μ⁻¹ ψ) : Space → Space) =ᵐ[volume]
      fun y => (μ * μ ^ (1 / (2 * α)))⁻¹ •
        (fracPhiX α τ ψ : Space → Space) ((μ ^ (1 / (2 * α)))⁻¹ • y) := by
  set c := μ ^ (1 / (2 * α)) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos hμ _
  have hα0 : α ≠ 0 := by linarith
  have hμ' : μ * τ = c ^ (2 * α) * τ := by rw [hc_def, pw_back hμ hα0]
  rw [fracPhiX_eq, fracDilX_inv_coe h2 hμ, ← hc_def, map_smul, hμ',
    fieldOp_id_scaleOp fieldOpRealized (aesm_fracPhiOp α _)
      (norm_fracPhiOp_le hα (by positivity)) (aesm_fracPhiOp α τ)
      (norm_fracPhiOp_le hα hτ) hc.ne' (k := c⁻¹)
      (fun ξ w => by
        show fracPhiFactor α _ ξ • w = c⁻¹ • (fracPhiFactor α τ (c • ξ) • w)
        rw [smul_smul, fracPhiFactor_scale hc]),
    map_smul, map_smul]
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [Lp.coeFn_smul c⁻¹ (toPhys (scaleOp c (fieldOp id
      (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C)))),
    toPhys_scaleOp_ae fieldOpRealized hc (fieldOp id
      (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C))] with y hy1 hy2
  rw [Pi.smul_apply, hy1, Pi.smul_apply, hy2, smul_smul, smul_smul, fracPhiX_eq]
  congr 1
  field_simp

theorem fracDilX_adjoint {α : ℝ} (h2 : FracDilationAlgebra α) {μ : ℝ} (hμ : 0 < μ) (x y : X) :
    inner ℝ (fracDilX α μ x) y =
      μ ^ 2 * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹ * inner ℝ x (fracDilX α μ⁻¹ y) := by
  have hc : 0 < μ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  change inner ℝ (fracDilX α μ x : L2C) (y : L2C) =
    μ ^ 2 * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹ * inner ℝ (x : L2C) (fracDilX α μ⁻¹ y : L2C)
  rw [fracDilX_coe' h2 hμ, fracDilX_inv_coe h2 hμ,
    real_inner_smul_left, real_inner_smul_right, inner_scaleOp fieldOpRealized (inv_pos.mpr hc),
    inv_inv]
  field_simp

theorem summand_scale' {a b d : ℝ} (U P W : Space) (j : Fin 3) :
    (a • U) j * inner ℝ (b • P) (d • W) = (a * b * d) * (U j * inner ℝ P W) := by
  rw [PiLp.smul_apply, smul_eq_mul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem summand_eq {U U' P P' W W' : Space} {a b d : ℝ} (hU : U = a • U') (hP : P = b • P')
    (hW : W = d • W') (j : Fin 3) :
    U j * inner ℝ P W = (a * b * d) * (U' j * inner ℝ P' W') := by
  rw [hU, hP, hW]
  exact summand_scale' U' P' W' j

theorem integral_scale' {c k : ℝ} (hc : 0 < c) (G : Space → ℝ) :
    ∫ x, k * G (c • x) = k * (c ^ 3)⁻¹ * ∫ x, G x := by
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul, abs_of_pos (by positivity)]
  ring

theorem trilinear_fracDilX {α : ℝ} (hα : 1 < α) (h2 : FracDilationAlgebra α)
    (h3 : FracVelocityDilate α) {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (u v ψ : X) :
    trilinear (fracDilX α μ u) (fracDilX α μ v) (fracPhiX α τ ψ) =
      μ ^ 3 * ((μ ^ (1 / (2 * α))) ^ 3)⁻¹ *
        trilinear u v (fracPhiX α (μ * τ) (fracDilX α μ⁻¹ ψ)) := by
  set c := μ ^ (1 / (2 * α)) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos hμ _
  unfold trilinear
  have hU := h3 μ hμ u
  have hV : ∀ᵐ y ∂volume, ∀ j : Fin 3, (partialX j (fracDilX α μ v) : Space → Space) y =
      μ • (partialX j v : Space → Space) (c • y) :=
    ae_all_iff.2 (fun j => partialX_fracDilX h2 hμ j v)
  have hw := comp_smul_ae (fracPhiX_dil_inv hα h2 hμ hτ ψ) hc.ne'
  have e1 : (fun x => ∑ j : Fin 3, (velocity (fracDilX α μ u) : Space → Space) x j *
      inner ℝ ((partialX j (fracDilX α μ v) : Space → Space) x)
        ((fracPhiX α τ ψ : Space → Space) x)) =ᵐ[volume]
      fun x => μ ^ 3 * (fun y => ∑ j : Fin 3, (velocity u : Space → Space) y j *
        inner ℝ ((partialX j v : Space → Space) y)
          ((fracPhiX α (μ * τ) (fracDilX α μ⁻¹ ψ) : Space → Space) y)) (c • x) := by
    filter_upwards [hU, hV, hw] with x hx1 hx2 hx3
    simp only [← hc_def, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hx3
    have hx3' : (fracPhiX α τ ψ : Space → Space) x =
        (μ * c) • (fracPhiX α (μ * τ) (fracDilX α μ⁻¹ ψ) : Space → Space) (c • x) := by
      rw [hx3, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    beta_reduce
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hU' : (velocity (fracDilX α μ u) : Space → Space) x =
        (μ ^ (1 - 1 / (2 * α))) • (velocity u : Space → Space) (c • x) := hx1
    refine (summand_eq hU' (hx2 j) hx3' j).trans ?_
    congr 1
    rw [pw_vel hμ, ← hc_def]
    field_simp
  exact (integral_congr_ae e1).trans (integral_scale' (k := μ ^ 3) hc (fun y => ∑ j : Fin 3,
    (velocity u : Space → Space) y j * inner ℝ ((partialX j v : Space → Space) y)
      ((fracPhiX α (μ * τ) (fracDilX α μ⁻¹ ψ) : Space → Space) y)))

theorem fracBilinX_spec {α : ℝ} (h1 : FracBilinExists α) {τ : ℝ} (hτ : 0 < τ) :
    FracBilinSpec α τ (fracBilinX α τ) := by
  have hh : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, h1 τ hτ⟩
  unfold fracBilinX
  rw [dif_pos hh]
  exact hh.2.choose_spec

end Breakdown.FracInternal.BilinDilate

namespace Breakdown.Freq

open Breakdown.FracInternal.BilinDilate

theorem fracBilinDilate (α : ℝ) (hα : 1 < α) (h1 : FracBilinExists α) (h2 : FracDilationAlgebra α)
    (h3 : FracVelocityDilate α) (_h4 : FracHeatSemigroup α) : FracBilinDilate α := by
  intro μ τ hμ hτ u v
  apply ext_inner_right ℝ
  intro ψ
  rw [real_inner_smul_left, fracDilX_adjoint h2 hμ, fracBilinX_spec h1 (mul_pos hμ hτ),
    fracBilinX_spec h1 hτ]
  unfold fracBilinForm
  rw [trilinear_fracDilX hα h2 h3 hμ hτ u v ψ, trilinear_fracDilX hα h2 h3 hμ hτ v u ψ]
  ring

end Breakdown.Freq

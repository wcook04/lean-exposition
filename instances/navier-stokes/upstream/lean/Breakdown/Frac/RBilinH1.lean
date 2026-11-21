import Breakdown.Frac.StBilinH1
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.BilinH1

open Breakdown.Freq

private theorem toLpOrZero_ae {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Space → F}
    (hf : MemLp f p volume) : (toLpOrZero p f : Space → F) =ᵐ[volume] f := by
  unfold toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

private theorem spec_of_exists {α : ℝ} (h1 : FracBilinExists α) {τ : ℝ} (hτ : 0 < τ) :
    FracBilinSpec α τ (fracBilinX α τ) := by
  have h : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, h1 τ hτ⟩
  unfold fracBilinX
  rw [dif_pos h]
  exact h.2.choose_spec

private theorem fieldOp_id_ae (F : Space → CSpace →L[ℝ] CSpace) (C : ℝ)
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    (fieldOp id F f : Space → CSpace) =ᵐ[volume] fun ξ => F ξ (f ξ) := by
  have h := fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) F C hF hC f
  simpa using h

private theorem inner_complexifyVec (a : Space) (b : CSpace) :
    inner ℝ (complexifyVec a) b = inner ℝ a (realVec b) := by
  simp [complexifyVec, realVec, PiLp.inner_apply, Complex.inner]

private theorem inner_complexify (g : L2R) (z : L2C) :
    inner ℝ (complexify g) z = inner ℝ g (realPart z) := by
  have hx : (complexify g : Space → CSpace) =ᵐ[volume] fun a => complexifyVec (g a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hy : (realPart z : Space → Space) =ᵐ[volume] fun a => realVec (z a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx, hy] with x hx hy
  rw [hx, hy, inner_complexifyVec]

private def transformIsometry : L2C ≃ₗᵢ[ℝ] L2C :=
  { freqTrL2.toLinearEquiv.restrictScalars ℝ with norm_map' := freqTrL2.norm_map }

private theorem inner_transform (a b : L2C) :
    inner ℝ (freqTrR a) b = inner ℝ a (freqTrInvR b) :=
  transformIsometry.inner_map_eq_flip a b

private theorem factor_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor; positivity

private theorem factor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    fracPhiFactor α τ ξ ≤ 1 + τ⁻¹ := by
  unfold fracPhiFactor
  set s := 2 * π * ‖ξ‖ with hs_def
  have hs : 0 ≤ s := by positivity
  have hq : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs _
  have he : Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hti : 0 < τ⁻¹ := inv_pos.mpr hτ
  rcases le_or_gt s 1 with h1 | h1
  · have : s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
      calc s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 * 1 :=
            mul_le_mul h1 he (Real.exp_pos _).le zero_le_one
        _ = 1 := by ring
    linarith
  · have hsp : s ≤ s ^ (2 * α) := by
      calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
        _ ≤ s ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have hex := Real.add_one_le_exp (τ * s ^ (2 * α))
    have hpos := Real.exp_pos (τ * s ^ (2 * α))
    have heq : Real.exp (-(τ * s ^ (2 * α))) * Real.exp (τ * s ^ (2 * α)) = 1 := by
      rw [← Real.exp_add]; simp
    have hk : τ * (s * Real.exp (-(τ * s ^ (2 * α)))) ≤ 1 := by
      have hE := Real.exp_pos (-(τ * s ^ (2 * α)))
      have h3 : τ * s ≤ Real.exp (τ * s ^ (2 * α)) := by nlinarith
      calc τ * (s * Real.exp (-(τ * s ^ (2 * α))))
          = (τ * s) * Real.exp (-(τ * s ^ (2 * α))) := by ring
        _ ≤ Real.exp (τ * s ^ (2 * α)) * Real.exp (-(τ * s ^ (2 * α))) :=
            mul_le_mul_of_nonneg_right h3 hE.le
        _ = 1 := by rw [mul_comm]; exact heq
    have hk2 : s * Real.exp (-(τ * s ^ (2 * α))) ≤ τ⁻¹ := by
      calc s * Real.exp (-(τ * s ^ (2 * α)))
          = τ⁻¹ * (τ * (s * Real.exp (-(τ * s ^ (2 * α))))) := by field_simp
        _ ≤ τ⁻¹ * 1 := mul_le_mul_of_nonneg_left hk hti.le
        _ = τ⁻¹ := mul_one _
    linarith

private theorem norm_factor_smul_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + τ⁻¹ := by
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (factor_nonneg α τ ξ)]
  have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := CSpace)
  have h2 := factor_le hα hτ ξ
  nlinarith [factor_nonneg α τ ξ]

private theorem aesm_factor (α τ : ℝ) :
    AEStronglyMeasurable (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
      volume := by
  have hm : Measurable (fun ξ : Space => fracPhiFactor α τ ξ) := by
    unfold fracPhiFactor; fun_prop
  exact hm.aestronglyMeasurable.smul aestronglyMeasurable_const

private theorem proj_inner {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (g : L2R) (ψ : X) :
    inner ℝ (fracHeatSolenoidal α τ g) ψ = inner ℝ g (fracPhiX α τ ψ) := by
  set M := fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
    with hMdef
  have hM : ∀ f : L2C, (M f : Space → CSpace) =ᵐ[volume] fun ξ => fracPhiFactor α τ ξ • f ξ := by
    intro f
    have := fieldOp_id_ae _ (1 + τ⁻¹) (aesm_factor α τ) (norm_factor_smul_le hα hτ) f
    simpa using this
  have hsa : ∀ a b : L2C, inner ℝ (M a) b = inner ℝ a (M b) := by
    intro a b
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hM a, hM b] with x ha hb
    rw [ha, hb, real_inner_smul_left, real_inner_smul_right]
  have hproj : ∀ w : L2C, inner ℝ (projX w) ψ = inner ℝ w (ψ : L2C) := fun w =>
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right ψ w
  show inner ℝ (projX (M (freqTrR (complexify g)))) ψ = inner ℝ g (realPart (freqTrInvR (M ψ)))
  rw [hproj, hsa, inner_transform, inner_complexify]

private theorem advectionAt_eq_sum (f : Space → Space) (x : Space) :
    advectionAt f x = ∑ j : Fin 3, f x j • partialField f j x := by
  unfold advectionAt partialField
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (f x)]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul]
  simp [unitVector]

private theorem advection_memLp {f : Space → Space} (hf : IsH1Field f)
    (hb : ∃ C, ∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C) :
    MemLp (fun x => advectionAt f x) 2 volume := by
  obtain ⟨C, hC⟩ := hb
  have hcont : Continuous f := hf.1.continuous
  have hco : ∀ j : Fin 3, MemLp (fun x => f x j) ⊤ volume := by
    intro j
    refine memLp_top_of_bound (C := C)
      ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _ |>.comp hcont)).aestronglyMeasurable ?_
    filter_upwards with x
    exact (PiLp.norm_apply_le (f x) j).trans (hC x).1
  have hs : MemLp (fun x => ∑ j : Fin 3, f x j • partialField f j x) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => (hf.2.2.2 j).smul (hco j))
  simpa only [advectionAt_eq_sum] using hs

theorem formula (α : ℝ) (hα : 1 < α) (h1 : FracBilinExists α) : FracBilinH1Formula α := by
  intro f hf hb τ hτ
  apply ext_inner_right ℝ
  intro ψ
  obtain ⟨_, hv, hp⟩ := h1Consistency_holds f hf
  have hA := toLpOrZero_ae (advection_memLp hf hb)
  rw [spec_of_exists h1 hτ, inner_neg_left, proj_inner hα hτ, fracBilinForm,
    MeasureTheory.L2.inner_def]
  have ht : trilinear (embedX f) (embedX f) (fracPhiX α τ ψ : Space → Space) =
      ∫ x, inner ℝ ((toLpOrZero 2 (fun x => advectionAt f x) : Space → Space) x)
        ((fracPhiX α τ ψ : Space → Space) x) := by
    unfold trilinear
    apply integral_congr_ae
    filter_upwards [hv, ae_all_iff.2 hp, hA] with x hx hpx hax
    rw [hax, advectionAt_eq_sum, sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hx, hpx j, real_inner_smul_left]
  rw [ht]
  ring

end Breakdown.FracInternal.BilinH1

namespace Breakdown.Freq

theorem fracBilinH1Formula (α : ℝ) (hα : 1 < α) (h1 : FracBilinExists α) :
    FracBilinH1Formula α :=
  Breakdown.FracInternal.BilinH1.formula α hα h1

end Breakdown.Freq

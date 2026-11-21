import Breakdown.FreqTr.Statements
import Breakdown.FreqTr.StatementsBilinFormula

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinH1

private theorem toLpOrZero_ae {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Space → F}
    (hf : MemLp f p volume) : (toLpOrZero p f : Space → F) =ᵐ[volume] f := by
  unfold toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

private theorem bilinX_spec (h1 : BilinExists) {τ : ℝ} (hτ : 0 < τ) : BilinSpec τ (bilinX τ) := by
  have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, h1 τ hτ⟩
  unfold bilinX
  rw [dif_pos h]
  exact h.2.choose_spec

private theorem fieldOp_id_ae (h3 : FieldOpRealized) (F : Space → CSpace →L[ℝ] CSpace) (C : ℝ)
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    (fieldOp id F f : Space → CSpace) =ᵐ[volume] fun ξ => F ξ (f ξ) := by
  have h := h3 (ContinuousLinearEquiv.refl ℝ Space) F C hF hC f
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

private def freqTrRealIsometry : L2C ≃ₗᵢ[ℝ] L2C :=
  { freqTrL2.toLinearEquiv.restrictScalars ℝ with norm_map' := freqTrL2.norm_map }

private theorem inner_freqTrR (a b : L2C) :
    inner ℝ (freqTrR a) b = inner ℝ a (freqTrInvR b) :=
  freqTrRealIsometry.inner_map_eq_flip a b

private theorem phiFactor_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ phiFactor τ ξ := by
  unfold phiFactor; positivity

private theorem norm_phiFactor_smul_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    ‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + 1 / τ := by
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg τ ξ)]
  unfold phiFactor
  have he := Real.add_one_le_exp (4 * π ^ 2 * τ * ‖ξ‖ ^ 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have h1 : (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) =
      4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1 + (2 * π * ‖ξ‖) ^ 2 + 1 / τ := by
    field_simp
    ring
  have h2 : 2 * π * ‖ξ‖ ≤ (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) := by
    rw [h1]
    have : 0 ≤ 1 / τ := by positivity
    have : 0 ≤ 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * π * ‖ξ‖ - 1)]
  calc 2 * π * ‖ξ‖ ≤ (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) := h2
    _ ≤ (1 + 1 / τ) * Real.exp (4 * π ^ 2 * τ * ‖ξ‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left he; positivity

private theorem heatDivFree_inner (h3 : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (g : L2R) (ψ : X) :
    inner ℝ (heatDivFree τ g) ψ = inner ℝ g (phiX τ ψ) := by
  set M := fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) with hMdef
  have hM : ∀ f : L2C, (M f : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • f ξ := by
    intro f
    have hc : Continuous (fun ξ : Space => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) := by
      unfold phiFactor; fun_prop
    have := fieldOp_id_ae h3 _ (1 + 1 / τ) hc.aestronglyMeasurable (norm_phiFactor_smul_le hτ) f
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
  rw [hproj, hsa, inner_freqTrR, inner_complexify]

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

end Internal.BilinH1

open Internal.BilinH1 in
theorem bilinH1Formula (h1 : BilinExists) (h2 : H1Consistency) (h3 : FieldOpRealized)
    (_h4 : TrilinearBound) : BilinH1Formula := by
  intro f hf hb τ hτ
  apply ext_inner_right ℝ
  intro ψ
  obtain ⟨_, hv, hp⟩ := h2 f hf
  have hA := toLpOrZero_ae (advection_memLp hf hb)
  rw [bilinX_spec h1 hτ, inner_neg_left, heatDivFree_inner h3 hτ, bilinForm,
    MeasureTheory.L2.inner_def]
  have ht : trilinear (embedX f) (embedX f) (phiX τ ψ : Space → Space) =
      ∫ x, inner ℝ ((toLpOrZero 2 (fun x => advectionAt f x) : Space → Space) x)
        ((phiX τ ψ : Space → Space) x) := by
    unfold trilinear
    apply integral_congr_ae
    filter_upwards [hv, ae_all_iff.2 hp, hA] with x hx hpx hax
    rw [hax, advectionAt_eq_sum, sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hx, hpx j, real_inner_smul_left]
  rw [ht]
  ring

end Breakdown.Freq

import Breakdown.FracCert.LinearStateClosed
import Breakdown.Frac.OpExports
import Breakdown.Uniqueness.PressureMollifyAux

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace DriftPowerSolenoidalInternal

open Internal.PressureMollify

variable {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
  {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem unit_inner (x : Space) (i : Fin 3) : inner ℝ x (unitVector i) = x i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem unit_inner' (x : Space) (i : Fin 3) : inner ℝ (unitVector i) x = x i := by
  rw [real_inner_comm, unit_inner]

theorem locInt_velocity (h : IsSecondOrderField m v G H) : LocallyIntegrable v volume :=
  h.velocity_six.locallyIntegrable (by norm_num)

theorem memLp_col (h : IsSecondOrderField m v G H) (j : Fin 3) :
    MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    h.measurable_gradient.apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine h.gradient_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun i : Fin 3 => ‖G y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ j)

theorem locInt_col (h : IsSecondOrderField m v G H) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume :=
  (memLp_col h j).locallyIntegrable (by norm_num)

theorem integrable_pair {f : Space → Space} (hf : LocallyIntegrable f volume) {ψ : Space → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (c : Space) :
    Integrable (fun y => ψ y * inner ℝ (f y) c) := by
  have := Integrable.inner_const (𝕜 := ℝ) (hf.integrable_smul_left_of_hasCompactSupport hψ hc) c
  simpa [real_inner_smul_left] using this

theorem weak_pair (h : IsSecondOrderField m v G H) {ψ : Space → ℝ} (hψ : IsTestScalar ψ) (i j : Fin 3) :
    ∫ y, fderiv ℝ ψ y (unitVector j) * v y i = -∫ y, ψ y * G y (unitVector j) i := by
  have e := congrArg (fun w : Space => inner ℝ w (unitVector i)) (h.weak_gradient ψ hψ j)
  have hv := (locInt_velocity h).integrable_smul_left_of_hasCompactSupport
    (contDiff_fderiv_apply hψ.1 (unitVector j)).continuous (hasCompactSupport_fderiv_apply hψ.2 (unitVector j))
  have hg := (locInt_col h j).integrable_smul_left_of_hasCompactSupport hψ.1.continuous hψ.2
  simp only [inner_neg_left] at e
  rw [real_inner_comm (unitVector i), real_inner_comm (unitVector i), ← integral_inner hv,
    ← integral_inner hg] at e
  simpa [real_inner_smul_right, unit_inner'] using e

theorem weak_div (h : IsSecondOrderField m v G H) {χ : Space → ℝ} (hχ : IsTestScalar χ) :
    ∫ y, inner ℝ (v y) (gradientAt χ y) = 0 := by
  have e1 : (fun y => inner ℝ (v y) (gradientAt χ y)) =
      fun y => ∑ i : Fin 3, fderiv ℝ χ y (unitVector i) * v y i := by
    funext y
    rw [real_inner_comm, inner_gradientAt]
  have hI : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ χ y (unitVector i) * v y i) := fun i => by
    have := integrable_pair (locInt_velocity h) (contDiff_fderiv_apply hχ.1 (unitVector i)).continuous
      (hasCompactSupport_fderiv_apply hχ.2 (unitVector i)) (unitVector i)
    simpa [unit_inner] using this
  have hJ : ∀ i : Fin 3, Integrable (fun y => χ y * G y (unitVector i) i) := fun i => by
    have := integrable_pair (locInt_col h i) hχ.1.continuous hχ.2 (unitVector i)
    simpa [unit_inner] using this
  rw [e1, integral_finsetSum _ (fun i _ => hI i), Finset.sum_congr rfl (fun i _ => weak_pair h hχ i i),
    Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hJ i)]
  have e2 : (fun y => ∑ i : Fin 3, χ y * G y (unitVector i) i) =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [h.divergence] with y hy
    rw [← Finset.mul_sum]
    simp only [unit_inner] at hy
    rw [hy, mul_zero]
  rw [integral_congr_ae e2]
  simp


theorem basis_sum (x : Space) : x = ∑ j : Fin 3, x j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem grad_inner (φ : Space → ℝ) (w y : Space) : inner ℝ w (gradientAt φ y) = fderiv ℝ φ y w := by
  rw [real_inner_comm, inner_gradientAt]
  conv_rhs => rw [basis_sum w]
  simp [map_sum, mul_comm]

theorem diff_fderiv {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (y : Space) :
    DifferentiableAt ℝ (fderiv ℝ φ) y :=
  ((contDiff_infty_iff_fderiv.1 hφ).2.differentiable infty_ne_zero) y

theorem symm2 {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (y a b : Space) :
    fderiv ℝ (fderiv ℝ φ) y a b = fderiv ℝ (fderiv ℝ φ) y b a := by
  have hs : IsSymmSndFDerivAt ℝ φ y := hφ.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast two_le_infty)
  exact hs a b

def coef (M : Space →L[ℝ] Space) (φ : Space → ℝ) (i j : Fin 3) : Space → ℝ :=
  fun y => M y j * fderiv ℝ φ y (unitVector i)

def flowTest (M : Space →L[ℝ] Space) (φ : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ φ y (M y)

theorem coord_hasFDerivAt (M : Space →L[ℝ] Space) (j : Fin 3) (y : Space) :
    HasFDerivAt (fun y => M y j) ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp M) y :=
  ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp M).hasFDerivAt

theorem test_coef (M : Space →L[ℝ] Space) {φ : Space → ℝ} (hφ : IsTestScalar φ) (i j : Fin 3) :
    IsTestScalar (coef M φ i j) := by
  refine ⟨?_, ?_⟩
  · exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp M).contDiff.mul
      (contDiff_fderiv_apply hφ.1 (unitVector i))
  · exact (hasCompactSupport_fderiv_apply hφ.2 (unitVector i)).mul_left

theorem test_flow (M : Space →L[ℝ] Space) {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    IsTestScalar (flowTest M φ) := by
  refine ⟨(contDiff_infty_iff_fderiv.1 hφ.1).2.clm_apply M.contDiff, ?_⟩
  refine (hφ.2.fderiv (𝕜 := ℝ)).mono fun y hy => ?_
  intro h0
  apply hy
  simp [flowTest, h0]

theorem deriv_coef (M : Space →L[ℝ] Space) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin 3) (y : Space) :
    fderiv ℝ (coef M φ i j) y (unitVector j) = M (unitVector j) j * fderiv ℝ φ y (unitVector i)
      + M y j * fderiv ℝ (fderiv ℝ φ) y (unitVector j) (unitVector i) := by
  have h2 := (diff_fderiv hφ y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector i) y)
  have h3 : HasFDerivAt (fun y => M y j * fderiv ℝ φ y (unitVector i)) _ y :=
    (coord_hasFDerivAt M j y).mul h2
  rw [show coef M φ i j = fun y => M y j * fderiv ℝ φ y (unitVector i) from rfl, h3.fderiv]
  simp
  ring

theorem deriv_flow (M : Space →L[ℝ] Space) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (y w : Space) :
    fderiv ℝ (flowTest M φ) y w = fderiv ℝ (fderiv ℝ φ) y w (M y) + fderiv ℝ φ y (M w) := by
  have h2 := (diff_fderiv hφ y).hasFDerivAt.clm_apply M.hasFDerivAt
  rw [show flowTest M φ = fun y => fderiv ℝ φ y (M y) from rfl, h2.fderiv]
  simp
  ring

theorem expand_left (M : Space →L[ℝ] Space) (φ : Space → ℝ) (K : Space →L[ℝ] Space) (y : Space) :
    fderiv ℝ φ y (K (M y)) = ∑ i : Fin 3, ∑ j : Fin 3, coef M φ i j y * K (unitVector j) i := by
  have e1 : K (M y) = ∑ j : Fin 3, M y j • K (unitVector j) := by
    conv_lhs => rw [basis_sum (M y)]
    simp only [map_sum, map_smul]
  have e2 : ∀ j : Fin 3, fderiv ℝ φ y (K (unitVector j)) =
      ∑ i : Fin 3, K (unitVector j) i * fderiv ℝ φ y (unitVector i) := by
    intro j
    conv_lhs => rw [basis_sum (K (unitVector j))]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [e1, map_sum]
  simp only [map_smul, smul_eq_mul, e2, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [coef]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem lin_expand (L : Space →L[ℝ] ℝ) (x : Space) : L x = ∑ i : Fin 3, x i * L (unitVector i) := by
  conv_lhs => rw [basis_sum x]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem pointwise_flow (M : Space →L[ℝ] Space) {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (x y : Space) :
    ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (coef M φ i j) y (unitVector j) * x i =
      (∑ j : Fin 3, M (unitVector j) j) * fderiv ℝ φ y x + fderiv ℝ (flowTest M φ) y x
        - fderiv ℝ φ y (M x) := by
  have hB : ∀ i : Fin 3, ∑ j : Fin 3, M y j * fderiv ℝ (fderiv ℝ φ) y (unitVector j) (unitVector i) =
      fderiv ℝ (fderiv ℝ φ) y (unitVector i) (M y) := by
    intro i
    rw [symm2 hφ y (unitVector i) (M y)]
    conv_rhs => rw [basis_sum (M y)]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hrow : ∀ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (coef M φ i j) y (unitVector j) =
      (∑ j : Fin 3, M (unitVector j) j) * fderiv ℝ φ y (unitVector i)
        + fderiv ℝ (fderiv ℝ φ) y (unitVector i) (M y) := by
    intro i
    simp only [deriv_coef M hφ, Finset.sum_add_distrib, hB, Finset.sum_mul]
  simp_rw [← Finset.sum_mul, hrow]
  have hM : fderiv ℝ φ y (M x) = ∑ i : Fin 3, x i * fderiv ℝ φ y (M (unitVector i)) := by
    rw [show fderiv ℝ φ y (M x) = ((fderiv ℝ φ y).comp M) x from rfl, lin_expand]
    rfl
  rw [lin_expand (fderiv ℝ φ y) x, lin_expand (fderiv ℝ (flowTest M φ) y) x, hM]
  simp only [deriv_flow M hφ, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem flow_identity (h : IsSecondOrderField m v G H) (M : Space →L[ℝ] Space) {φ : Space → ℝ}
    (hφ : IsTestScalar φ) :
    ∫ y, inner ℝ (G y (M y)) (gradientAt φ y) = ∫ y, inner ℝ (M (v y)) (gradientAt φ y) := by
  simp_rw [grad_inner]
  have hI : ∀ i j : Fin 3, Integrable (fun y => coef M φ i j y * G y (unitVector j) i) := fun i j => by
    have := integrable_pair (locInt_col h j) (test_coef M hφ i j).1.continuous (test_coef M hφ i j).2
      (unitVector i)
    simpa [unit_inner] using this
  have hJ : ∀ i j : Fin 3, Integrable (fun y => fderiv ℝ (coef M φ i j) y (unitVector j) * v y i) :=
    fun i j => by
      have := integrable_pair (locInt_velocity h)
        (contDiff_fderiv_apply (test_coef M hφ i j).1 (unitVector j)).continuous
        (hasCompactSupport_fderiv_apply (test_coef M hφ i j).2 (unitVector j)) (unitVector i)
      simpa [unit_inner] using this
  have hV : ∀ χ : Space → ℝ, IsTestScalar χ → Integrable (fun y => fderiv ℝ χ y (v y)) := by
    intro χ hχ
    have e : (fun y => fderiv ℝ χ y (v y)) = fun y => ∑ i : Fin 3, fderiv ℝ χ y (unitVector i) * v y i := by
      funext y
      rw [lin_expand (fderiv ℝ χ y) (v y)]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    refine integrable_finsetSum _ fun i _ => ?_
    have := integrable_pair (locInt_velocity h) (contDiff_fderiv_apply hχ.1 (unitVector i)).continuous
      (hasCompactSupport_fderiv_apply hχ.2 (unitVector i)) (unitVector i)
    simpa [unit_inner] using this
  have hW : ∀ χ : Space → ℝ, IsTestScalar χ → ∫ y, fderiv ℝ χ y (v y) = 0 := by
    intro χ hχ
    have := weak_div h hχ
    simpa [grad_inner] using this
  have hMv : Integrable (fun y => fderiv ℝ φ y (M (v y))) := by
    have e : (fun y => fderiv ℝ φ y (M (v y))) = fun y => ∑ i : Fin 3, v y i * fderiv ℝ φ y (M (unitVector i)) := by
      funext y
      rw [show fderiv ℝ φ y (M (v y)) = ((fderiv ℝ φ y).comp M) (v y) from rfl, lin_expand]
      rfl
    rw [e]
    refine integrable_finsetSum _ fun i _ => ?_
    have hc : Continuous (fun y => fderiv ℝ φ y (M (unitVector i))) :=
      (contDiff_fderiv_apply hφ.1 (M (unitVector i))).continuous
    have := integrable_pair (locInt_velocity h) hc
      (hasCompactSupport_fderiv_apply hφ.2 (M (unitVector i))) (unitVector i)
    simpa [unit_inner, mul_comm] using this
  have e1 : (fun y => fderiv ℝ φ y (G y (M y))) =
      fun y => ∑ i : Fin 3, ∑ j : Fin 3, coef M φ i j y * G y (unitVector j) i :=
    funext fun y => expand_left M φ (G y) y
  have e2 : (fun y => ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (coef M φ i j) y (unitVector j) * v y i) =
      fun y => (∑ j : Fin 3, M (unitVector j) j) * fderiv ℝ φ y (v y) + fderiv ℝ (flowTest M φ) y (v y)
        - fderiv ℝ φ y (M (v y)) :=
    funext fun y => pointwise_flow M hφ.1 (v y) y
  have e3 : ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, coef M φ i j y * G y (unitVector j) i =
      -∫ y, ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (coef M φ i j) y (unitVector j) * v y i := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hJ i j), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hI i j), integral_finsetSum _ (fun j _ => hJ i j),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [weak_pair h (test_coef M hφ i j) i j, neg_neg]
  have h0 : Integrable (fun y => (∑ j : Fin 3, M (unitVector j) j) * fderiv ℝ φ y (v y)) :=
    (hV φ hφ).const_mul _
  have h1 : Integrable (fun y => (∑ j : Fin 3, M (unitVector j) j) * fderiv ℝ φ y (v y)
      + fderiv ℝ (flowTest M φ) y (v y)) := h0.add (hV _ (test_flow M hφ))
  rw [e1, e3, e2, integral_sub h1 hMv, integral_add h0 (hV _ (test_flow M hφ)), integral_const_mul, hW φ hφ,
    hW _ (test_flow M hφ)]
  ring


theorem int_left (h : IsSecondOrderField m v G H) (M : Space →L[ℝ] Space) {φ : Space → ℝ}
    (hφ : IsTestScalar φ) : Integrable (fun y => inner ℝ (G y (M y)) (gradientAt φ y)) := by
  simp_rw [grad_inner]
  have e1 : (fun y => fderiv ℝ φ y (G y (M y))) =
      fun y => ∑ i : Fin 3, ∑ j : Fin 3, coef M φ i j y * G y (unitVector j) i :=
    funext fun y => expand_left M φ (G y) y
  rw [e1]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have := integrable_pair (locInt_col h j) (test_coef M hφ i j).1.continuous (test_coef M hφ i j).2
    (unitVector i)
  simpa [unit_inner] using this

theorem int_right (h : IsSecondOrderField m v G H) (M : Space →L[ℝ] Space) {φ : Space → ℝ}
    (hφ : IsTestScalar φ) : Integrable (fun y => inner ℝ (M (v y)) (gradientAt φ y)) := by
  simp_rw [grad_inner]
  have e : (fun y => fderiv ℝ φ y (M (v y))) = fun y => ∑ i : Fin 3, v y i * fderiv ℝ φ y (M (unitVector i)) := by
    funext y
    rw [show fderiv ℝ φ y (M (v y)) = ((fderiv ℝ φ y).comp M) (v y) from rfl, lin_expand]
    rfl
  rw [e]
  refine integrable_finsetSum _ fun i _ => ?_
  have hc : Continuous (fun y => fderiv ℝ φ y (M (unitVector i))) :=
    (contDiff_fderiv_apply hφ.1 (M (unitVector i))).continuous
  have := integrable_pair (locInt_velocity h) hc
    (hasCompactSupport_fderiv_apply hφ.2 (M (unitVector i))) (unitVector i)
  simpa [unit_inner, mul_comm] using this

def turnMap : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurn
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp [axialTurn]
        all_goals ring
      map_smul' := by
        intro c a
        ext i
        fin_cases i <;> simp [axialTurn] }

theorem turnMap_apply (y : Space) : turnMap y = axialTurn y := rfl

theorem integrable_inner_cpt {f g : Space → Space} (hf : LocallyIntegrable f volume) (hg : Continuous g)
    (hc : HasCompactSupport g) : Integrable (fun x => inner ℝ (f x) (g x)) := by
  have hs := hf.integrable_smul_left_of_hasCompactSupport hg.norm hc.norm
  refine hs.norm.mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_smul, norm_norm, Real.norm_eq_abs, mul_comm]
  exact abs_real_inner_le_norm _ _

theorem grad_smooth {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) : ContDiff ℝ ∞ (gradientAt ξ) := by
  show ContDiff ℝ ∞ (fun y => ∑ i : Fin 3, fderiv ℝ ξ y (unitVector i) • unitVector i)
  exact ContDiff.sum fun i _ => (contDiff_fderiv_apply hξ _).smul contDiff_const

theorem grad_support {ξ : Space → ℝ} (hc : HasCompactSupport ξ) : HasCompactSupport (gradientAt ξ) := by
  refine (hc.fderiv (𝕜 := ℝ)).mono fun y hy => ?_
  intro h0
  apply hy
  simp [gradientAt, h0]

theorem integrable_div (h : IsSecondOrderField m v G H) {χ : Space → ℝ} (hχ : IsTestScalar χ) :
    Integrable (fun y => inner ℝ (v y) (gradientAt χ y)) :=
  integrable_inner_cpt (locInt_velocity h) (grad_smooth hχ.1).continuous (grad_support hχ.2)

theorem drift_zero (α a : ℝ) (h : IsSecondOrderField m v G H) {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    ∫ y, inner ℝ (driftField α a v G y) (gradientAt φ y) = 0 := by
  have hI := flow_identity h (ContinuousLinearMap.id ℝ Space) hφ
  have hJ := flow_identity h turnMap hφ
  have iL1 := int_left h (ContinuousLinearMap.id ℝ Space) hφ
  have iL2 := int_left h turnMap hφ
  have iR2 := int_right h turnMap hφ
  have iv := integrable_div h hφ
  have hv0 := weak_div h hφ
  simp only [ContinuousLinearMap.id_apply] at hI iL1
  simp only [turnMap_apply] at hJ iL2 iR2
  have j1 : Integrable (fun y => (1 - 1 / (2 * α)) * inner ℝ (v y) (gradientAt φ y)) := iv.const_mul _
  have j2 : Integrable (fun y => (1 / (2 * α)) * inner ℝ (G y y) (gradientAt φ y)) := iL1.const_mul _
  have j3 : Integrable (fun y => inner ℝ (G y (axialTurn y)) (gradientAt φ y)
      - inner ℝ (axialTurn (v y)) (gradientAt φ y)) := iL2.sub iR2
  have j4 : Integrable (fun y => a * (inner ℝ (G y (axialTurn y)) (gradientAt φ y)
      - inner ℝ (axialTurn (v y)) (gradientAt φ y))) := j3.const_mul _
  have j12 : Integrable (fun y => (1 - 1 / (2 * α)) * inner ℝ (v y) (gradientAt φ y)
      + (1 / (2 * α)) * inner ℝ (G y y) (gradientAt φ y)) := j1.add j2
  have e : (fun y => inner ℝ (driftField α a v G y) (gradientAt φ y)) = fun y =>
      (1 - 1 / (2 * α)) * inner ℝ (v y) (gradientAt φ y) + (1 / (2 * α)) * inner ℝ (G y y) (gradientAt φ y)
        + a * (inner ℝ (G y (axialTurn y)) (gradientAt φ y) - inner ℝ (axialTurn (v y)) (gradientAt φ y)) := by
    funext y
    simp only [driftField, inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [e, integral_add j12 j4, integral_add j1 j2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub iL2 iR2, hI, hJ, hv0]
  ring

theorem dapp {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) (x c w : Space) :
    fderiv ℝ (fun y => fderiv ℝ ξ y c) x w = fderiv ℝ (fderiv ℝ ξ) x w c := by
  rw [((diff_fderiv hξ x).hasFDerivAt.clm_apply (hasFDerivAt_const c x)).fderiv]
  simp

theorem grad_fderiv {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) (x w : Space) :
    fderiv ℝ (gradientAt ξ) x w = gradientAt (fun y => fderiv ℝ ξ y w) x := by
  have hH : HasFDerivAt (gradientAt ξ)
      (∑ i : Fin 3, (fderiv ℝ (fun y => fderiv ℝ ξ y (unitVector i)) x).smulRight (unitVector i)) x := by
    show HasFDerivAt (fun y => ∑ i : Fin 3, fderiv ℝ ξ y (unitVector i) • unitVector i) _ x
    exact HasFDerivAt.fun_sum fun i _ =>
      (((contDiff_fderiv_apply hξ (unitVector i)).differentiable infty_ne_zero) x).hasFDerivAt.smul_const _
  rw [hH.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  show _ = ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ ξ y w) x (unitVector i) • unitVector i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dapp hξ, dapp hξ, symm2 hξ]

theorem remainder_grad {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) (x z : Space) :
    secondOrderRemainder (gradientAt ξ) x z = gradientAt (fun y => ξ (y + z)) x - gradientAt ξ x
      - gradientAt (fun y => fderiv ℝ ξ y z) x
      - (1 / 2 : ℝ) • gradientAt (fun y => fderiv ℝ (fun y' => fderiv ℝ ξ y' z) y z) x := by
  have hg := grad_smooth hξ
  have hη := contDiff_fderiv_apply hξ z
  have g0 : gradientAt ξ (x + z) = gradientAt (fun y => ξ (y + z)) x := by
    simp only [gradientAt, fderiv_comp_add_right]
  have g2 : iteratedFDeriv ℝ 2 (gradientAt ξ) x ![z, z] =
      gradientAt (fun y => fderiv ℝ (fun y' => fderiv ℝ ξ y' z) y z) x := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (gradientAt ξ)) x :=
      ((contDiff_infty_iff_fderiv.1 hg).2.differentiable infty_ne_zero) x
    rw [iteratedFDeriv_two_apply]
    show fderiv ℝ (fderiv ℝ (gradientAt ξ)) x z z = _
    have e1 : fderiv ℝ (fderiv ℝ (gradientAt ξ)) x z z =
        fderiv ℝ (fun y => fderiv ℝ (gradientAt ξ) y z) x z := by
      rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const z x)).fderiv]
      simp
    have e2 : (fun y => fderiv ℝ (gradientAt ξ) y z) = gradientAt (fun y => fderiv ℝ ξ y z) :=
      funext fun y => grad_fderiv hξ y z
    rw [e1, e2, grad_fderiv hη]
  rw [secondOrderRemainder, g0, grad_fderiv hξ, g2]

theorem test_shift {ξ : Space → ℝ} (hξ : IsTestScalar ξ) (z : Space) : IsTestScalar (fun y => ξ (y + z)) :=
  ⟨hξ.1.comp (contDiff_id.add contDiff_const), hξ.2.comp_homeomorph (Homeomorph.addRight z)⟩

theorem test_dir {ξ : Space → ℝ} (hξ : IsTestScalar ξ) (w : Space) : IsTestScalar (fun y => fderiv ℝ ξ y w) :=
  ⟨contDiff_fderiv_apply hξ.1 w, hasCompactSupport_fderiv_apply hξ.2 w⟩

theorem slice_zero (h : IsSecondOrderField m v G H) {ξ : Space → ℝ} (hξ : IsTestScalar ξ) (z : Space) :
    ∫ x, inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) = 0 := by
  have t0 := test_shift hξ z
  have t1 := test_dir hξ z
  have t2 := test_dir t1 z
  simp_rw [remainder_grad hξ.1, inner_sub_right, real_inner_smul_right]
  rw [integral_sub, integral_sub, integral_sub, integral_const_mul, weak_div h t0, weak_div h hξ,
    weak_div h t1, weak_div h t2]
  · ring
  all_goals first
    | exact integrable_div h t0 | exact integrable_div h hξ | exact integrable_div h t1
    | exact (integrable_div h t2).const_mul _
    | exact (integrable_div h t0).sub (integrable_div h hξ)
    | exact ((integrable_div h t0).sub (integrable_div h hξ)).sub (integrable_div h t1)

theorem far_bound (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
    ‖secondOrderRemainder f x z‖ ≤
      ‖f (x + z)‖ + (‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
  have hz2 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  have hD : ‖fderiv ℝ f x z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := (fderiv ℝ f x).le_opNorm z
  have hD2 : ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖z‖ ^ 2 := by
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two, sq] using this
  have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
    rw [norm_smul]
    have := norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z])
    norm_num
    nlinarith
  unfold secondOrderRemainder
  have n1 := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z) ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have n2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have n3 := norm_sub_le (f (x + z)) (f x)
  have p1 : ‖f x‖ ≤ ‖f x‖ * ‖z‖ ^ 2 := le_mul_of_one_le_right (norm_nonneg _) hz2
  have p2 : ‖fderiv ℝ f x‖ * ‖z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hz1 (norm_nonneg _)
  nlinarith

theorem zero_far (f : Space → Space) (x z : Space) {r : ℝ} (hz : ‖z‖ ≤ r)
    (hx : x ∉ Metric.cthickening r (tsupport f)) : secondOrderRemainder f x z = 0 := by
  have hx0 : x ∉ tsupport f := fun hm => hx (Metric.self_subset_cthickening _ hm)
  have e1 : f x = 0 := image_eq_zero_of_notMem_tsupport hx0
  have e2 : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport ℝ hx0
  have e3 : iteratedFDeriv ℝ 2 f x = 0 := by
    by_contra hne
    exact hx0 (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr hne))
  have e4 : f (x + z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    apply hx
    apply Metric.mem_cthickening_of_dist_le x (x + z) r _ hm
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact hz
  simp [secondOrderRemainder, e1, e2, e3, e4]

theorem cont_pair (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : Space × Space => secondOrderRemainder f p.1 p.2) := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 f) := hf.continuous_iteratedFDeriv (by norm_cast)
  have hm : Continuous (fun p : Space × Space => (![p.2, p.2] : Fin 2 → Space)) := by
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simpa using continuous_snd
  have h3 : Continuous (fun p : Space × Space => iteratedFDeriv ℝ 2 f p.1 ![p.2, p.2]) :=
    continuous_eval.comp ((h2.comp continuous_fst).prodMk hm)
  have h4 : Continuous (fun p : Space × Space => fderiv ℝ f p.1 p.2) :=
    (h1.comp continuous_fst).clm_apply continuous_snd
  have h6 : Continuous (fun p : Space × Space => f (p.1 + p.2)) :=
    hf.continuous.comp (continuous_fst.add continuous_snd)
  exact ((h6.sub (hf.continuous.comp continuous_fst)).sub h4).sub (h3.const_smul (1 / 2 : ℝ))

theorem cont_slice (f : Space → Space) (hf : ContDiff ℝ ∞ f) (z : Space) :
    Continuous (fun x : Space => secondOrderRemainder f x z) := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 f) := hf.continuous_iteratedFDeriv (by norm_cast)
  have h3 : Continuous (fun x : Space => iteratedFDeriv ℝ 2 f x ![z, z]) :=
    continuous_eval.comp (h2.prodMk continuous_const)
  have h4 : Continuous (fun x : Space => fderiv ℝ f x z) := h1.clm_apply continuous_const
  have h6 : Continuous (fun x : Space => f (x + z)) := hf.continuous.comp (continuous_add_const z)
  exact ((h6.sub hf.continuous).sub h4).sub (h3.const_smul (1 / 2 : ℝ))

theorem mul_le_pow_six {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ a ^ 6 + b ^ 2 + b := by
  have h6 : 0 ≤ a ^ 6 := pow_nonneg ha 6
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  rcases le_or_gt a 1 with h1 | h1
  · have : a * b ≤ 1 * b := mul_le_mul_of_nonneg_right h1 hb
    linarith
  · rcases le_or_gt b (a ^ 5) with h2 | h2
    · have e : a * a ^ 5 = a ^ 6 := by ring
      have : a * b ≤ a * a ^ 5 := mul_le_mul_of_nonneg_left h2 ha
      linarith
    · have h4 : 1 ≤ a ^ 4 := one_le_pow₀ h1.le
      have ha5 : a ≤ a ^ 5 := by
        have e : a ^ 5 = a * a ^ 4 := by ring
        rw [e]
        nlinarith
      have : a * b ≤ b * b := mul_le_mul_of_nonneg_right (by linarith) hb
      nlinarith

theorem translate_bound {u : Space → Space} (hum : AEStronglyMeasurable u volume)
    (hu6 : Integrable (fun x => ‖u x‖ ^ 6)) {φ : Space → Space} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (z : Space) :
    Integrable (fun x => ‖u x‖ * ‖φ (x + z)‖) ∧
      ∫ x, ‖u x‖ * ‖φ (x + z)‖ ≤ (∫ x, ‖u x‖ ^ 6) + (∫ x, ‖φ x‖ ^ 2) + ∫ x, ‖φ x‖ := by
  have hφ1 : Integrable (fun x => ‖φ x‖) := (hφ.integrable_of_hasCompactSupport hc).norm
  have hφL : MemLp φ ((2 : ℕ) : ENNReal) volume := hφ.memLp_of_hasCompactSupport hc
  have hφ2 : Integrable (fun x => ‖φ x‖ ^ 2) := hφL.integrable_norm_pow two_ne_zero
  have s1 : Integrable (fun x => ‖φ (x + z)‖) := hφ1.comp_add_right z
  have s2 : Integrable (fun x => ‖φ (x + z)‖ ^ 2) := hφ2.comp_add_right z
  have hsum : Integrable (fun x => ‖u x‖ ^ 6 + ‖φ (x + z)‖ ^ 2 + ‖φ (x + z)‖) := (hu6.add s2).add s1
  have hpt : ∀ x, ‖u x‖ * ‖φ (x + z)‖ ≤ ‖u x‖ ^ 6 + ‖φ (x + z)‖ ^ 2 + ‖φ (x + z)‖ := fun x =>
    mul_le_pow_six (norm_nonneg _) (norm_nonneg _)
  have hint : Integrable (fun x => ‖u x‖ * ‖φ (x + z)‖) := by
    refine hsum.mono' (hum.norm.mul (hφ.comp (continuous_add_const z)).aestronglyMeasurable.norm)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt x
  refine ⟨hint, ?_⟩
  calc ∫ x, ‖u x‖ * ‖φ (x + z)‖ ≤ ∫ x, (‖u x‖ ^ 6 + ‖φ (x + z)‖ ^ 2 + ‖φ (x + z)‖) :=
        integral_mono hint hsum hpt
    _ = (∫ x, ‖u x‖ ^ 6) + (∫ x, ‖φ x‖ ^ 2) + ∫ x, ‖φ x‖ := by
        have hs12 : Integrable (fun x => ‖u x‖ ^ 6 + ‖φ (x + z)‖ ^ 2) := hu6.add s2
        rw [integral_add hs12 s1, integral_add hu6 s2,
          integral_add_right_eq_self (fun x => ‖φ x‖ ^ 2) z, integral_add_right_eq_self (fun x => ‖φ x‖) z]

theorem near_far {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) {a b C : ℝ}
    (ha : a < 3) (hb : 3 < b) (hnear : ∀ z : Space, ‖z‖ ≤ 1 → ‖f z‖ ≤ C * ‖z‖ ^ (-a))
    (hfar : ∀ z : Space, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ (-b)) : Integrable f := by
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hC : 0 ≤ C := by
    have hn : ‖(EuclideanSpace.single 0 1 : Space)‖ = 1 := by simp
    have := hfar (EuclideanSpace.single 0 1) hn.ge
    rw [hn, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hball : IntegrableOn f (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := C) (by rw [hfin]; norm_num)
      (by rw [hfin]; exact_mod_cast ha) ?_ hf
    refine (ae_restrict_mem measurableSet_ball).mono fun z hz => hnear z ?_
    have : ‖z‖ < 1 := by simpa using hz
    exact this.le
  have hcomp : IntegrableOn f (Metric.ball (0 : Space) 1)ᶜ volume := by
    have hint : Integrable (fun z : Space => (1 + ‖z‖) ^ (-b)) :=
      integrable_one_add_norm (by rw [hfin]; exact_mod_cast hb)
    refine Integrable.mono' ((hint.const_mul (C * 2 ^ b)).integrableOn) hf.restrict ?_
    refine (ae_restrict_mem measurableSet_ball.compl).mono fun z hz => ?_
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hzpos : 0 < ‖z‖ := by linarith
    have key : ‖z‖ ^ (-b) ≤ 2 ^ b * (1 + ‖z‖) ^ (-b) := by
      rw [Real.rpow_neg hzpos.le, Real.rpow_neg (by positivity), ← div_eq_mul_inv]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      rw [div_mul_eq_mul_div, one_le_div (by positivity), ← Real.mul_rpow (by norm_num) hzpos.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc ‖f z‖ ≤ C * ‖z‖ ^ (-b) := hfar z hz1
      _ ≤ C * (2 ^ b * (1 + ‖z‖) ^ (-b)) := mul_le_mul_of_nonneg_left key hC
      _ = C * 2 ^ b * (1 + ‖z‖) ^ (-b) := by ring
  have := hball.union hcomp
  rwa [Set.union_compl_self, integrableOn_univ] at this

theorem rpow_pow_add (t r : ℝ) (ht : 0 ≤ t) (n : ℕ) (hr : r ≠ 0) (hrn : r + n ≠ 0) :
    t ^ r * t ^ n = t ^ (r + n) := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0, Real.zero_rpow hr, Real.zero_rpow hrn, zero_mul]
  · rw [← Real.rpow_natCast, ← Real.rpow_add h0]

theorem prod_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {u : Space → Space}
    (hu : LocallyIntegrable u volume) (hu6 : Integrable (fun x => ‖u x‖ ^ 6))
    {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (u p.1) (secondOrderRemainder φ p.1 p.2)) (volume.prod volume) := by
  have hRj := cont_pair φ hφ
  have hum : AEStronglyMeasurable u volume := hu.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (u p.1) (secondOrderRemainder φ p.1 p.2)) (volume.prod volume) :=
    (((measurable_snd.norm).pow_const _).aestronglyMeasurable).mul
      ((hum.comp_fst).inner hRj.aestronglyMeasurable)
  have hRc : ∀ z, Continuous (fun x => secondOrderRemainder φ x z) := cont_slice φ hφ
  have hSc : IsCompact (tsupport φ) := hφc
  have hRs : ∀ z, HasCompactSupport (fun x => secondOrderRemainder φ x z) := fun z =>
    HasCompactSupport.intro (hSc.cthickening (r := ‖z‖)) (fun x hx => zero_far φ x z le_rfl hx)
  have hsec : ∀ z : Space, Integrable (fun x =>
      ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (u x) (secondOrderRemainder φ x z)) :=
    fun z => (integrable_inner_cpt hu (hRc z) (hRs z)).const_mul _
  rw [integrable_prod_iff' hFm]
  refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
  have hT : IsCompact (Metric.cthickening 1 (tsupport φ)) := hSc.cthickening
  obtain ⟨C3, hC3⟩ := (hφ.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hφc.iteratedFDeriv 3)
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by norm_cast)
  have hvT : Integrable ((Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖u x‖)) :=
    IntegrableOn.integrable_indicator (Integrable.norm (hu.integrableOn_isCompact hT)) hT.measurableSet
  set Q : Space → ℝ := fun x => ‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖ with hQ
  have hQc : Continuous Q :=
    (hφ.continuous.norm.add (hφ.continuous_fderiv (by simp)).norm).add
      (hφ.continuous_iteratedFDeriv (m := 2) (by norm_cast)).norm
  have hQs : HasCompactSupport Q := by
    refine HasCompactSupport.intro hSc (fun x hx0 => ?_)
    have e1 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx0
    have e2 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx0
    have e3 : iteratedFDeriv ℝ 2 φ x = 0 := by
      by_contra hne
      exact hx0 (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr hne))
    simp [hQ, e1, e2, e3]
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => by simp only [hQ]; positivity
  have hPi : Integrable (fun x => ‖u x‖ * Q x) := by
    have := (hu.integrable_smul_left_of_hasCompactSupport hQc hQs).norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (hQ0 x)]
    ring
  set A := (∫ x, ‖u x‖ ^ 6) + (∫ x, ‖φ x‖ ^ 2) + ∫ x, ‖φ x‖ with hA
  have hA0 : 0 ≤ A := by
    have := (translate_bound hum hu6 hφ.continuous hφc 0).2
    exact le_trans (integral_nonneg (fun x => by positivity)) this
  set cP := ∫ x, ‖u x‖ * Q x with hcP
  set I1 := ∫ x, (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖u x‖) x with hI1
  have hcP0 : 0 ≤ cP := integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (by positivity))
  have hI10 : 0 ≤ I1 := integral_nonneg (fun x => Set.indicator_nonneg (fun y _ => norm_nonneg (u y)) x)
  set C3' := max C3 0 with hC3'
  have hC3'0 : 0 ≤ C3' := le_max_right _ _
  apply near_far (a := 2 * α) (b := 1 + 2 * α) (C := C3' * I1 + (A + cP))
  · exact hFm.prod_swap.norm.integral_prod_right'
  · linarith
  · linarith
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (u x) (secondOrderRemainder φ x z)‖ ≤
        (‖z‖ ^ (-(3 + 2 * α)) * C3' * ‖z‖ ^ 3) *
          (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖u x‖) x := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      by_cases hx : x ∈ Metric.cthickening 1 (tsupport φ)
      · rw [Set.indicator_of_mem hx]
        calc |inner ℝ (u x) (secondOrderRemainder φ x z)| ≤ ‖u x‖ * ‖secondOrderRemainder φ x z‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ ‖u x‖ * (C3' * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left
                (remainderBound φ hφ3 x z C3' (fun y _ => (hC3 y).trans (le_max_left _ _))) (norm_nonneg _)
          _ = C3' * (‖z‖ ^ 3 * ‖u x‖) := by ring
      · rw [Set.indicator_of_notMem hx, zero_far φ x z hz hx]
        simp
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (u x) (secondOrderRemainder φ x z)‖
        ≤ ∫ x, (‖z‖ ^ (-(3 + 2 * α)) * C3' * ‖z‖ ^ 3) *
          (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖u x‖) x :=
          integral_mono (hsec z).norm (hvT.const_mul _) hpt
      _ = (C3' * I1) * ‖z‖ ^ (-(2 * α)) := by
          rw [integral_const_mul]
          have := rpow_pow_add ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 3 (by linarith) (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((3 : ℕ) : ℝ) = -(2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
      _ ≤ (C3' * I1 + (A + cP)) * ‖z‖ ^ (-(2 * α)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    obtain ⟨hg, hgA⟩ := translate_bound hum hu6 hφ.continuous hφc z
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (u x) (secondOrderRemainder φ x z)‖ ≤
        ‖z‖ ^ (-(3 + 2 * α)) * (‖u x‖ * ‖φ (x + z)‖ + ‖u x‖ * Q x * ‖z‖ ^ 2) := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      have := mul_le_mul_of_nonneg_left (far_bound φ x z hz) (norm_nonneg (u x))
      refine le_trans this (le_of_eq ?_)
      simp only [hQ]
      ring
    have hz2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (u x) (secondOrderRemainder φ x z)‖
        ≤ ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * (‖u x‖ * ‖φ (x + z)‖ + ‖u x‖ * Q x * ‖z‖ ^ 2) :=
          integral_mono (hsec z).norm ((hg.add (hPi.mul_const _)).const_mul _) hpt
      _ = ‖z‖ ^ (-(3 + 2 * α)) * ((∫ x, ‖u x‖ * ‖φ (x + z)‖) + cP * ‖z‖ ^ 2) := by
          rw [integral_const_mul, integral_add hg (hPi.mul_const _), integral_mul_const]
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * ((A + cP) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          nlinarith
      _ = (A + cP) * ‖z‖ ^ (-(1 + 2 * α)) := by
          have := rpow_pow_add ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 2 (by linarith) (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((2 : ℕ) : ℝ) = -(1 + 2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
      _ ≤ (C3' * I1 + (A + cP)) * ‖z‖ ^ (-(1 + 2 * α)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (norm_nonneg _) _)

theorem power_zero {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) (h : IsSecondOrderField m v G H)
    {ξ : Space → ℝ} (hξ : IsTestScalar ξ) :
    ∫ x, inner ℝ (v x) (fractionalPowerAt α (gradientAt ξ) x) = 0 := by
  have hφ := grad_smooth hξ.1
  have hφc := grad_support hξ.2
  obtain ⟨Cφ, hCφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hRI := remainderIntegrable α hα1 hα2 (gradientAt ξ) hφ (Or.inr ⟨Cφ, hCφ⟩)
  have h6 : MemLp v ((6 : ℕ) : ENNReal) volume := by exact_mod_cast h.velocity_six
  have hv6 : Integrable (fun x => ‖v x‖ ^ 6) := h6.integrable_norm_pow (by norm_num)
  have hRx : ∀ x, inner ℝ (v x) (fractionalPowerAt α (gradientAt ξ) x) =
      (fractionalNormalizer α)⁻¹ *
        ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_right, ← integral_inner (hRI x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
  have hPR := prod_integrable hα1 hα2 (locInt_velocity h) hv6 hφ hφc
  have hfun : (fun x => inner ℝ (v x) (fractionalPowerAt α (gradientAt ξ) x)) = fun x =>
      (fractionalNormalizer α)⁻¹ *
        ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) :=
    funext hRx
  rw [hfun, integral_const_mul]
  rw [integral_integral_swap (f := fun x z : Space =>
    ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z)) hPR]
  have e : ∀ z : Space,
      ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) = 0 := by
    intro z
    rw [integral_const_mul, slice_zero h hξ z, mul_zero]
  simp only [e, integral_zero, mul_zero]

end DriftPowerSolenoidalInternal

open DriftPowerSolenoidalInternal in
theorem driftPowerSolenoidal : DriftPowerSolenoidalStatement := by
  intro α hα1 hα2 a m v G H P h hP hd
  refine ⟨hd.add hP.1, fun φ hφ => ?_⟩
  have hg := grad_smooth hφ.1
  have hgc := grad_support hφ.2
  have i1 : Integrable (fun y => inner ℝ (driftField α a v G y) (gradientAt φ y)) :=
    integrable_inner_cpt (hd.locallyIntegrable (by norm_num)) hg.continuous hgc
  have i2 : Integrable (fun y => inner ℝ (P y) (gradientAt φ y)) :=
    integrable_inner_cpt (hP.1.locallyIntegrable (by norm_num)) hg.continuous hgc
  simp only [inner_add_left]
  rw [integral_add i1 i2, drift_zero α a h hφ, hP.2 _ ⟨hg, hgc⟩, power_zero hα1 (by linarith) h hφ,
    add_zero]

end SteadyCert

end Breakdown

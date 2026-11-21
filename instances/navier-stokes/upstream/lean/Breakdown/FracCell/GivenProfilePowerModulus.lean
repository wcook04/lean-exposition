import Breakdown.FracCert.Defs
import Breakdown.FracCert.FreeExists
import Breakdown.Frac.OpExports
import Breakdown.FracCell.GivenProfilePowerModulusBound

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePower

open SteadyCert

private theorem test_memLp {φ : Space → Space} (hφ : IsTestVectorField φ) : MemLp φ 2 volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2

private theorem represent_of_bound (L : (Space → Space) → ℝ)
    (hadd : ∀ φ ψ, IsTestVectorField φ → IsTestVectorField ψ → L (φ + ψ) = L φ + L ψ)
    (hsmul : ∀ (c : ℝ) φ, IsTestVectorField φ → L (c • φ) = c * L φ) (K : ℝ)
    (hbd : ∀ φ, IsTestVectorField φ → |L φ| ≤ K * Real.sqrt (∫ y, ‖φ y‖ ^ 2)) :
    ∃ Q : Space → Space, MemLp Q 2 volume ∧
      ∀ φ, IsTestVectorField φ → ∫ y, inner ℝ (Q y) (φ y) = L φ := by
  classical
  let T : Submodule ℝ (Space → Space) :=
    { carrier := {φ | IsTestVectorField φ}
      add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
      zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
      smul_mem' := fun c _ hφ => ⟨hφ.1.const_smul c, hφ.2.smul_left (f := fun _ => c)⟩ }
  let j : T →ₗ[ℝ] Lp Space 2 (volume : Measure Space) :=
    { toFun := fun φ => (test_memLp φ.2).toLp _
      map_add' := fun φ ψ => MemLp.toLp_add (test_memLp φ.2) (test_memLp ψ.2)
      map_smul' := fun c φ => MemLp.toLp_const_smul c (test_memLp φ.2) }
  let L' : T →ₗ[ℝ] ℝ :=
    { toFun := fun φ => L φ.1
      map_add' := fun φ ψ => hadd φ.1 ψ.1 φ.2 ψ.2
      map_smul' := fun c φ => hsmul c φ.1 φ.2 }
  have hj : ∀ φ : T, ‖j φ‖ = Real.sqrt (∫ y, ‖φ.1 y‖ ^ 2) := fun φ =>
    (FreeExistsInternal.l2Norm_eq (test_memLp φ.2)).symm
  have hker : LinearMap.ker j ≤ LinearMap.ker L' := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h := hbd φ.1 φ.2
    rw [← hj, hφ, norm_zero, mul_zero] at h
    exact abs_nonpos_iff.1 h
  let ℓ₀ : LinearMap.range j →ₗ[ℝ] ℝ :=
    ((LinearMap.ker j).liftQ L' hker).comp j.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ φ : T, ℓ₀ ⟨j φ, LinearMap.mem_range_self j φ⟩ = L φ.1 := by
    intro φ
    simp only [ℓ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hℓ₀b : ∀ x : LinearMap.range j, ‖ℓ₀ x‖ ≤ K * ‖x‖ := by
    rintro ⟨_, φ, rfl⟩
    rw [hℓ₀ φ, Real.norm_eq_abs]
    refine (hbd φ.1 φ.2).trans_eq ?_
    rw [← hj]
    rfl
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range j) (ℓ₀.mkContinuous K hℓ₀b)
  let Q₀ := (InnerProductSpace.toDual ℝ (Lp Space 2 (volume : Measure Space))).symm g
  refine ⟨Q₀, Lp.memLp Q₀, fun φ hφ => ?_⟩
  have key : inner ℝ Q₀ (j ⟨φ, hφ⟩) = L φ := by
    rw [InnerProductSpace.toDual_symm_apply,
      hg (⟨j ⟨φ, hφ⟩, LinearMap.mem_range_self j _⟩ : LinearMap.range j),
      LinearMap.mkContinuous_apply, hℓ₀]
  rw [← key, L2.inner_def]
  refine integral_congr_ae ?_
  have hc : (j ⟨φ, hφ⟩ : Space → Space) =ᵐ[volume] φ := (test_memLp hφ).coeFn_toLp
  filter_upwards [hc] with y hy
  rw [hy]

private theorem power_add_test {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {φ ψ : Space → Space}
    (hφ : IsTestVectorField φ) (hψ : IsTestVectorField ψ) (y : Space) :
    fractionalPowerAt α (φ + ψ) y = fractionalPowerAt α φ y + fractionalPowerAt α ψ y :=
  additivity α φ ψ y (remainderIntegrable α h1 h2 φ hφ.1 (Or.inl (test_memLp hφ)) y)
    (remainderIntegrable α h1 h2 ψ hψ.1 (Or.inl (test_memLp hψ)) y)
    (hφ.1.differentiable (by simp) y) (hψ.1.differentiable (by simp) y)
    (show ContDiff ℝ 2 φ from hφ.1.of_le (by norm_cast)).contDiffAt
    (show ContDiff ℝ 2 ψ from hψ.1.of_le (by norm_cast)).contDiffAt

private theorem power_smul_test {α : ℝ} {φ : Space → Space} (hφ : IsTestVectorField φ) (c : ℝ)
    (y : Space) : fractionalPowerAt α (c • φ) y = c • fractionalPowerAt α φ y :=
  (covariance α φ (hφ.1.of_le (by norm_cast))).2.1 c y

private theorem test_add {φ ψ : Space → Space} (hφ : IsTestVectorField φ) (hψ : IsTestVectorField ψ) :
    IsTestVectorField (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

theorem weakPower_of_secondModulus {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) {v : Space → Space}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : ContDiff ℝ 1 v) (hv6 : MemLp v 6 volume)
    (hH : IsWeakSecondDerivOf (fun y => fderiv ℝ v y) H) (hH2 : MemLp H 2 volume)
    (hmod : ∃ C : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∫ y, ‖H (y + h) - H y‖ ^ 2 ≤ C * ‖h‖) :
    ∃ Q : Space → Space, IsWeakFractionalPower α v Q := by
  have h3 : α < 3 / 2 := by linarith
  obtain ⟨K, hK⟩ := pairing_bound_of_secondModulus h1 h2 hv hv6 hH hH2 hmod
  obtain ⟨Q, hQ, hQφ⟩ := represent_of_bound (fun φ => ∫ y, inner ℝ (v y) (fractionalPowerAt α φ y))
    (fun φ ψ hφ hψ => by
      simp only [power_add_test h1 h3 hφ hψ, inner_add_right]
      exact integral_add (FreeExistsInternal.pair_integrable h1 h3 hφ hv6)
        (FreeExistsInternal.pair_integrable h1 h3 hψ hv6))
    (fun c φ hφ => by
      simp only [power_smul_test hφ c, real_inner_smul_right]
      exact integral_const_mul c _)
    K hK
  exact ⟨Q, hQ, fun φ hφ => hQφ φ hφ⟩

end ProfilePower

end FracInternal

end Breakdown

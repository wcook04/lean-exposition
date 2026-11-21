import TorusEuler.Paper.Proofs.S5a.Library.MeanUnique
import TorusEuler.PaperAppendixDLifting
import TorusEuler.EndpointPhysicalJetEstimates

/-!
# S5a library: spaces of derivative towers for Lemma D.3 applied to the mean system (4.9)

The abstract Lemma D.3 (`Statement.lemma_D_3`) is applied (row Text eq_5_14,
`sections/06d_mean_estimates.tex:34-58`) to the integrated mean system (4.9) in the space of
*derivative towers*: a tower is a family `u : List (Fin 3) → ℝ → X` of curves indexed by words of label
derivatives (`u (i :: w)` stands for `∂_i u w`), invariant under permutations of the word, and
continuous in time. The spaces `E` (towers of solenoidal velocities with `∫_0^T u_w = 0`), `F`
(towers of forcings in `C^{0,1/2}`), `A` (towers of coefficients in `C^{0,1/2}(ℝ³;𝓛(ℝ³))`) carry the
derivations `ℓ ∂_i` = `ℓ • shift i`, and the zero-order seminorms `p u = sup_{t ∈ [0,T]} ‖u [] t‖`.
Leibniz' rule for the coefficient action is then *definitional*: `Tw (i :: w) a u = Tw w (∂_i a) u +
Tw w a (∂_i u)`.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- Words of label derivatives. -/
abbrev Wd := List (Fin 3)

section Spaces

variable (T : ℝ) (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Permutation-invariant towers, continuous in time on `[0,T]`. -/
def tower : Submodule ℝ (Wd → ℝ → X) where
  carrier := {u | (∀ p q : Wd, p.Perm q → u p = u q) ∧ ∀ w, ContinuousOn (u w) (Icc 0 T)}
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨fun p q h => by simp only [Pi.add_apply, hu p q h, hv p q h],
      fun w => (hu' w).add (hv' w)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => continuousOn_const⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨fun p q h => by simp only [Pi.smul_apply, hu p q h], fun w => (hu' w).const_smul c⟩

/-- The derivation `∂_i` on towers. -/
def shift (i : Fin 3) : (Wd → ℝ → X) →ₗ[ℝ] (Wd → ℝ → X) where
  toFun u := fun w => u (i :: w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {T X}

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `shift_mem`. -/
theorem shift_mem (i : Fin 3) {u : Wd → ℝ → X} (hu : u ∈ tower T X) : shift X i u ∈ tower T X :=
  ⟨fun _ _ h => hu.1 _ _ (h.cons i), fun _ => hu.2 _⟩

end Spaces

section EAndF

variable (T : ℝ) (hT : 0 ≤ T)

/-- Towers of solenoidal velocities `u_w` with `∫_0^T u_w = 0`. -/
def Esp : Submodule ℝ (Wd → ℝ → S) where
  carrier := {u | u ∈ tower T S ∧ ∀ w, endpointPrimitive (u w) T = 0}
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨add_mem hu hv, fun w => ?_⟩
    have h1 : IntervalIntegrable (u w) MeasureTheory.volume 0 T :=
      (hu.2 w).intervalIntegrable_of_Icc hT
    have h2 : IntervalIntegrable (v w) MeasureTheory.volume 0 T :=
      (hv.2 w).intervalIntegrable_of_Icc hT
    simp only [endpointPrimitive, Pi.add_apply] at hu' hv' ⊢
    rw [intervalIntegral.integral_add h1 h2, hu' w, hv' w, add_zero]
  zero_mem' := ⟨zero_mem _, fun _ => by simp [endpointPrimitive]⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    refine ⟨Submodule.smul_mem _ c hu, fun w => ?_⟩
    simp only [endpointPrimitive, Pi.smul_apply] at hu' ⊢
    rw [intervalIntegral.integral_smul, hu' w, smul_zero]

variable {T}

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `shift_mem_Esp`. -/
theorem shift_mem_Esp (i : Fin 3) {u : Wd → ℝ → S} (hu : u ∈ Esp T hT) :
    shift S i u ∈ Esp T hT :=
  ⟨shift_mem i hu.1, fun _ => hu.2 _⟩

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Esp_le_tower`. -/
theorem Esp_le_tower : Esp T hT ≤ tower T S := fun _ hu => hu.1

end EAndF

section Seminorms

variable {T : ℝ} (hT : 0 ≤ T) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The zero-order seminorm `sup_{t ∈ [0,T]} ‖u [] t‖` on a submodule of towers. -/
def zeroSemi (P : Submodule ℝ (Wd → ℝ → X)) (hP : P ≤ tower T X) : Seminorm ℝ P :=
  Seminorm.ofSMulLE (fun u => endpointClosedTimeNorm T (u.1 []))
    (by
      change endpointClosedTimeNorm T (fun _ : ℝ => (0 : X)) = 0
      unfold endpointClosedTimeNorm
      have h := (Set.nonempty_Icc.mpr hT).image_const (0 : ℝ)
      simp only [norm_zero]
      rw [h, csSup_singleton])
    (fun u v => by
      apply endpointClosedTimeNorm_le hT
      intro t ht
      have hu := (hP u.2).2 []
      have hv := (hP v.2).2 []
      calc ‖(u + v).1 [] t‖ = ‖u.1 [] t + v.1 [] t‖ := rfl
        _ ≤ ‖u.1 [] t‖ + ‖v.1 [] t‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_le_endpointClosedTimeNorm hu ht)
          (norm_le_endpointClosedTimeNorm hv ht))
    (fun c u => by
      apply endpointClosedTimeNorm_le hT
      intro t ht
      have hu := (hP u.2).2 []
      calc ‖(c • u).1 [] t‖ = ‖c‖ * ‖u.1 [] t‖ := by
            change ‖c • u.1 [] t‖ = _
            rw [norm_smul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_endpointClosedTimeNorm hu ht) (norm_nonneg c))

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `zeroSemi_apply`. -/
theorem zeroSemi_apply (P : Submodule ℝ (Wd → ℝ → X)) (hP : P ≤ tower T X) (u : P) :
    zeroSemi hT P hP u = endpointClosedTimeNorm T (u.1 []) := rfl

end Seminorms

end

end TorusEuler.Paper.Lib.S5a.Tower

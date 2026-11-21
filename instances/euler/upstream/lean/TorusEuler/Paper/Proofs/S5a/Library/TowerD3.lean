import TorusEuler.Paper.Proofs.S5a.Library.TowerOps
import TorusEuler.Paper.SBD.Statements

/-!
# S5a library: Lemma D.3 on derivative towers

`tower_lifting`: Lemma D.3 (`Statement.lemma_D_3`, abstract lifting lemma) instantiated in the spaces of
derivative towers (`Library/Tower.lean`, `Library/TowerOps.lean`): `E` = towers of solenoidal
velocities with zero time integral, `F` = towers of forcings, `A` = towers of coefficients, the system
being `K v - ∫ Ω v ≡ f` modulo the time-constant solenoidal part and gradients, written with the
projection `P` (`Tk a v + Tom a v = f`, see `TowerOps`). The sum norm of the conclusion is written as the
sum of closed-time norms over sorted words.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerD3SolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerD3SolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

section Words

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {T : ℝ}

/-- The derivation `∂_i` on a submodule of towers that is closed under it. -/
def shiftOn (P : Submodule ℝ (Wd → ℝ → X)) (hP : ∀ i, ∀ u ∈ P, shift X i u ∈ P) (i : Fin 3) :
    P →ₗ[ℝ] P :=
  (shift X i).restrict (fun u hu => hP i u hu)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `word_apply`. -/
theorem word_apply (P : Submodule ℝ (Wd → ℝ → X)) (hP : ∀ i, ∀ u ∈ P, shift X i u ∈ P)
    (w : Wd) (u : P) (p : Wd) :
    ((appendixDerivativeWord (shiftOn P hP) w u : P) : Wd → ℝ → X) p = u.1 (w.reverse ++ p) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    simp only [appendixDerivativeWord_cons]
    change ((appendixDerivativeWord (shiftOn P hP) w u : P) : Wd → ℝ → X) (i :: p) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `word_norm`. -/
theorem word_norm (hT : 0 ≤ T) (P : Submodule ℝ (Wd → ℝ → X)) (hP : P ≤ tower T X)
    (hS : ∀ i, ∀ u ∈ P, shift X i u ∈ P) (w : Wd) (u : P) :
    zeroSemi hT P hP (appendixDerivativeWord (shiftOn P hS) w u) =
      endpointClosedTimeNorm T (u.1 w) := by
  rw [zeroSemi_apply, word_apply]
  simp only [List.append_nil]
  rw [(hP u.2).1 _ _ (List.reverse_perm w)]

/-- The finite norm of Lemma D.3 is the weighted word norm (D.1) (scaling of derivations; TeX 52-58). -/
theorem finiteNorm_eq (hT : 0 ≤ T) (P : Submodule ℝ (Wd → ℝ → X)) (hP : P ≤ tower T X)
    (hS : ∀ i, ∀ u ∈ P, shift X i u ∈ P) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ) (u : P) :
    appendixFiniteDerivativeNorm (zeroSemi hT P hP) (fun i => ℓ • shiftOn P hS i) n u =
      ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (u.1 w) := by
  rw [appendixFiniteDerivativeNorm_scaled _ _ (fun _ => ℓ) (fun _ => hℓ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [List.map_const', List.prod_replicate, word_norm hT P hP hS]

/-- The exact-order norm of Lemma D.3 is the weighted word norm (D.1) (TeX 52-58). -/
theorem exactNorm_eq (hT : 0 ≤ T) (P : Submodule ℝ (Wd → ℝ → X)) (hP : P ≤ tower T X)
    (hS : ∀ i, ∀ u ∈ P, shift X i u ∈ P) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (m : ℕ) (u : P) :
    appendixExactOrderDerivativeNorm (zeroSemi hT P hP) (fun i => ℓ • shiftOn P hS i) m u =
      ∑ w ∈ (hierarchyAdmissibleWords (Fin 3) m).filter (fun w => w.length = m),
        ℓ ^ m * endpointClosedTimeNorm T (u.1 w) := by
  unfold appendixExactOrderDerivativeNorm
  refine Finset.sum_congr rfl fun w hw => ?_
  have hlen := (Finset.mem_filter.mp hw).2
  have hD := appendixDerivativeWord_scaled (shiftOn P hS) (fun _ => ℓ) w u
  have hD' : appendixDerivativeWord (fun i => ℓ • shiftOn P hS i) w u =
      (w.map (fun _ => ℓ)).prod • appendixDerivativeWord (shiftOn P hS) w u := hD
  rw [hD', map_smul_eq_mul, List.map_const', List.prod_replicate, word_norm hT P hP hS, hlen,
    Real.norm_of_nonneg (pow_nonneg hℓ _)]

end Words

section Actions

variable {T : ℝ}

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_add_left`. -/
theorem Tk_add_left (a a' : Wd → ℝ → K½) (u : Wd → ℝ → S) :
    Tk (a + a') u = Tk a u + Tk a' u := by
  funext w t
  simp only [Tk, Tw_add_left, Pi.add_apply, map_add]; abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_smul_left`. -/
theorem Tk_smul_left (c : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S) :
    Tk (c • a) u = c • Tk a u := by
  funext w t
  simp only [Tk, Tw_smul_left, Pi.smul_apply, map_smul, smul_sub]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_add_right`. -/
theorem Tk_add_right (a : Wd → ℝ → K½) (u u' : Wd → ℝ → S) :
    Tk a (u + u') = Tk a u + Tk a u' := by
  funext w t
  simp only [Tk, Tw_add_right, Pi.add_apply, map_add]; abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_smul_right`. -/
theorem Tk_smul_right (c : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S) :
    Tk a (c • u) = c • Tk a u := by
  funext w t
  simp only [Tk, Tw_smul_right, Pi.smul_apply, map_smul, smul_sub]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_leibniz`. -/
theorem Tk_leibniz (a : Wd → ℝ → K½) (u : Wd → ℝ → S) (i : Fin 3) :
    shift C½ i (Tk a u) = Tk (shift K½ i a) u + Tk a (shift S i u) := by
  funext w t
  simp only [shift, Tk, Tw, Pi.add_apply, map_add, LinearMap.coe_mk, AddHom.coe_mk]
  abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_add_left`. -/
theorem Tom_add_left (hT : 0 ≤ T) {a a' : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (ha' : a' ∈ tower T K½) (hu : u ∈ tower T S) :
    Tom T (a + a') u = Tom T a u + Tom T a' u := by
  funext w t
  simp only [Tom, Tw_add_left, Pi.add_apply]
  rw [primC_add hT (Tw_continuousOn ha hu w) (Tw_continuousOn ha' hu w)]
  simp only [Pi.add_apply, map_add]; abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_smul_left`. -/
theorem Tom_smul_left (c : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S) :
    Tom T (c • a) u = c • Tom T a u := by
  funext w t
  simp only [Tom, Tw_smul_left, primC_smul, Pi.smul_apply, map_smul, smul_neg]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_add_right`. -/
theorem Tom_add_right (hT : 0 ≤ T) {a : Wd → ℝ → K½} {u u' : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) (hu' : u' ∈ tower T S) :
    Tom T a (u + u') = Tom T a u + Tom T a u' := by
  funext w t
  simp only [Tom, Tw_add_right, Pi.add_apply]
  rw [primC_add hT (Tw_continuousOn ha hu w) (Tw_continuousOn ha hu' w)]
  simp only [Pi.add_apply, map_add]; abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_smul_right`. -/
theorem Tom_smul_right (c : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S) :
    Tom T a (c • u) = c • Tom T a u := by
  funext w t
  simp only [Tom, Tw_smul_right, primC_smul, Pi.smul_apply, map_smul, smul_neg]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_leibniz`. -/
theorem Tom_leibniz (hT : 0 ≤ T) {a : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) (i : Fin 3) :
    shift C½ i (Tom T a u) = Tom T (shift K½ i a) u + Tom T a (shift S i u) := by
  funext w t
  simp only [shift, Tom, Tw, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  have hp : primC T (Tw w (fun p => a (i :: p)) u + Tw w a (fun p => u (i :: p))) =
      primC T (Tw w (fun p => a (i :: p)) u) + primC T (Tw w a (fun p => u (i :: p))) :=
    primC_add hT (Tw_continuousOn (shift_mem i ha) hu w) (Tw_continuousOn ha (shift_mem i hu) w)
  rw [hp]
  simp only [Pi.add_apply, map_add]; abel

end Actions

end

end TorusEuler.Paper.Lib.S5a.Tower

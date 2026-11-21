import TorusEuler.Paper.Proofs.S5a.Library.TowerD3

/-!
# S5a library: Lemma D.3 on derivative towers (the instantiation)

See `Library/TowerD3.lean`. `tower_lifting` is the content of the lifting step of
`sections/06d_mean_estimates.tex:44-58`: Lemma D.3 (`hD3`) applied to the integrated system (4.9),
whose zero-order inverse estimate and (D.7) are the hypotheses `hZero`, `hD7`.
-/

open Set
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerLiftSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerLiftSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

variable {T : ℝ}

section Bilinear

variable (hT : 0 < T)

/-- The `K`-action as a bilinear map on the spaces of towers. -/
def TkB : ↥(tower T K½) →ₗ[ℝ] ↥(Esp T hT.le) →ₗ[ℝ] ↥(tower T C½) :=
  LinearMap.mk₂ ℝ (fun a u => ⟨Tk a.1 u.1, Tk_mem a.2 u.2.1⟩)
    (fun _ _ _ => Subtype.ext (Tk_add_left _ _ _))
    (fun _ _ _ => Subtype.ext (Tk_smul_left _ _ _))
    (fun _ _ _ => Subtype.ext (Tk_add_right _ _ _))
    (fun _ _ _ => Subtype.ext (Tk_smul_right _ _ _))

/-- The `Ω`-action as a bilinear map on the spaces of towers. -/
def TomB : ↥(tower T K½) →ₗ[ℝ] ↥(Esp T hT.le) →ₗ[ℝ] ↥(tower T C½) :=
  LinearMap.mk₂ ℝ (fun a u => ⟨Tom T a.1 u.1, Tom_mem hT a.2 u.2.1⟩)
    (fun a a' u => Subtype.ext (Tom_add_left hT.le a.2 a'.2 u.2.1))
    (fun _ _ _ => Subtype.ext (Tom_smul_left _ _ _))
    (fun a u u' => Subtype.ext (Tom_add_right hT.le a.2 u.2.1 u'.2.1))
    (fun _ _ _ => Subtype.ext (Tom_smul_right _ _ _))

end Bilinear

section Bounds

variable {a : Wd → ℝ → K½} {u : Wd → ℝ → S}

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw0_bound`. -/
theorem Tw0_bound (ha : a ∈ tower T K½) (hu : u ∈ tower T S) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖Tw [] a u t‖ ≤ 2 * endpointClosedTimeNorm T (a []) * endpointClosedTimeNorm T (u []) := by
  refine (Tw_bound t).trans ?_
  have h1 := norm_le_endpointClosedTimeNorm (ha.2 []) ht
  have h2 := norm_le_endpointClosedTimeNorm (hu.2 []) ht
  have h3 : 0 ≤ ‖u [] t‖ := norm_nonneg _
  have h4 : 0 ≤ ‖a [] t‖ := norm_nonneg _
  have h6 : 0 ≤ endpointClosedTimeNorm T (a []) := h4.trans h1
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) h2 h3 (by positivity)

/-- Operator bound for `Tk`: `Kv` enters directly, so the norm is at most `b_K = 4‖P‖` times that of `K` (TeX 49-51). -/
theorem N_Tk_le (hT : 0 < T) (ha : a ∈ tower T K½) (hu : u ∈ tower T S) :
    endpointClosedTimeNorm T (Tk a u []) ≤
      4 * ‖pjL‖ * endpointClosedTimeNorm T (a []) * endpointClosedTimeNorm T (u []) := by
  apply endpointClosedTimeNorm_le hT.le
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have h1 : ‖pjL (Tw [] a u t)‖ ≤ ‖pjL‖ * (2 * endpointClosedTimeNorm T (a []) *
      endpointClosedTimeNorm T (u [])) :=
    (pjL.le_opNorm _).trans (mul_le_mul_of_nonneg_left (Tw0_bound ha hu ht) (norm_nonneg _))
  have h2 : ‖pjL (Tw [] a u 0)‖ ≤ ‖pjL‖ * (2 * endpointClosedTimeNorm T (a []) *
      endpointClosedTimeNorm T (u [])) :=
    (pjL.le_opNorm _).trans (mul_le_mul_of_nonneg_left (Tw0_bound ha hu h0) (norm_nonneg _))
  calc ‖Tk a u [] t‖ = ‖pjL (Tw [] a u t) - pjL (Tw [] a u 0)‖ := rfl
    _ ≤ ‖pjL (Tw [] a u t)‖ + ‖pjL (Tw [] a u 0)‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith

/-- Operator bound for `Tom`: `Ωv` enters through time integration, so the norm is at most `b_Ω = 2‖P‖T` times that of `Ω` (TeX 49-51). -/
theorem N_Tom_le (hT : 0 < T) (ha : a ∈ tower T K½) (hu : u ∈ tower T S) :
    endpointClosedTimeNorm T (Tom T a u []) ≤
      2 * ‖pjL‖ * T * endpointClosedTimeNorm T (a []) * endpointClosedTimeNorm T (u []) := by
  apply endpointClosedTimeNorm_le hT.le
  intro t ht
  have hW : endpointClosedTimeNorm T (Tw [] a u) ≤
      2 * endpointClosedTimeNorm T (a []) * endpointClosedTimeNorm T (u []) :=
    endpointClosedTimeNorm_le hT.le fun s hs => Tw0_bound ha hu hs
  have h1 := norm_primC_le hT (Tw_continuousOn ha hu []) ht
  calc ‖Tom T a u [] t‖ = ‖pjL (primC T (Tw [] a u) t)‖ := by simp only [Tom, norm_neg]
    _ ≤ ‖pjL‖ * ‖primC T (Tw [] a u) t‖ := pjL.le_opNorm _
    _ ≤ ‖pjL‖ * (T * (2 * endpointClosedTimeNorm T (a []) * endpointClosedTimeNorm T (u []))) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hW hT.le)) (norm_nonneg pjL)
    _ = _ := by ring

end Bounds

section Comm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `shiftOn_comm`. -/
theorem shiftOn_comm (P : Submodule ℝ (Wd → ℝ → X)) (hP : P ≤ tower T X)
    (hS : ∀ i, ∀ u ∈ P, shift X i u ∈ P) (ℓ : ℝ) (i i' : Fin 3) (g : P) :
    (ℓ • shiftOn P hS i) ((ℓ • shiftOn P hS i') g) = (ℓ • shiftOn P hS i') ((ℓ • shiftOn P hS i) g) := by
  apply Subtype.ext
  funext w t
  change ℓ • (ℓ • g.1 (i' :: i :: w) t) = ℓ • (ℓ • g.1 (i :: i' :: w) t)
  rw [(hP g.2).1 _ _ (List.Perm.swap i i' w)]

end Comm

section Derivations

variable (hT : 0 < T) (ℓ : ℝ)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hSA`. -/
theorem hSA : ∀ i, ∀ u ∈ tower T K½, shift K½ i u ∈ tower T K½ := fun i _ hu => shift_mem i hu

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hSE`. -/
theorem hSE : ∀ i, ∀ u ∈ Esp T hT.le, shift S i u ∈ Esp T hT.le :=
  fun i _ hu => shift_mem_Esp hT.le i hu

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hSF`. -/
theorem hSF : ∀ i, ∀ u ∈ tower T C½, shift C½ i u ∈ tower T C½ := fun i _ hu => shift_mem i hu

/-- The weighted derivations `ℓ ∂_i` on the three spaces of towers. -/
def dA (i : Fin 3) : ↥(tower T K½) →ₗ[ℝ] ↥(tower T K½) := ℓ • shiftOn (tower T K½) (hSA) i

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `dE`. -/
def dE (i : Fin 3) : ↥(Esp T hT.le) →ₗ[ℝ] ↥(Esp T hT.le) := ℓ • shiftOn (Esp T hT.le) (hSE hT) i

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `dF`. -/
def dF (i : Fin 3) : ↥(tower T C½) →ₗ[ℝ] ↥(tower T C½) := ℓ • shiftOn (tower T C½) (hSF) i

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `dA_val`. -/
theorem dA_val (i : Fin 3) (a : ↥(tower T K½)) : (dA ℓ i a).1 = ℓ • shift K½ i a.1 := rfl

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `dE_val`. -/
theorem dE_val (i : Fin 3) (u : ↥(Esp T hT.le)) : (dE hT ℓ i u).1 = ℓ • shift S i u.1 := rfl

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `dF_val`. -/
theorem dF_val (i : Fin 3) (g : ↥(tower T C½)) : (dF ℓ i g).1 = ℓ • shift C½ i g.1 := rfl

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `TkB_val`. -/
theorem TkB_val (a : ↥(tower T K½)) (u : ↥(Esp T hT.le)) : (TkB hT a u).1 = Tk a.1 u.1 := rfl

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `TomB_val`. -/
theorem TomB_val (a : ↥(tower T K½)) (u : ↥(Esp T hT.le)) : (TomB hT a u).1 = Tom T a.1 u.1 := rfl

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `leibnizK`. -/
theorem leibnizK (i : Fin 3) (a : ↥(tower T K½)) (u : ↥(Esp T hT.le)) :
    dF ℓ i (TkB hT a u) = TkB hT (dA ℓ i a) u + TkB hT a (dE hT ℓ i u) := by
  apply Subtype.ext
  simp only [dF_val, TkB_val, Submodule.coe_add, dA_val, dE_val, Tk_smul_left, Tk_smul_right,
    Tk_leibniz, smul_add]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `leibnizOm`. -/
theorem leibnizOm (i : Fin 3) (a : ↥(tower T K½)) (u : ↥(Esp T hT.le)) :
    dF ℓ i (TomB hT a u) = TomB hT (dA ℓ i a) u + TomB hT a (dE hT ℓ i u) := by
  apply Subtype.ext
  simp only [dF_val, TomB_val, Submodule.coe_add, dA_val, dE_val, Tom_smul_left, Tom_smul_right,
    Tom_leibniz hT.le a.2 u.2.1, smul_add]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `exactNormA`. -/
theorem exactNormA (hℓ : 0 ≤ ℓ) (m : ℕ) (u : ↥(tower T K½)) :
    appendixExactOrderDerivativeNorm (zeroSemi hT.le (tower T K½) le_rfl) (dA ℓ) m u =
      ∑ w ∈ (hierarchyAdmissibleWords (Fin 3) m).filter (fun w => w.length = m),
        ℓ ^ m * endpointClosedTimeNorm T (u.1 w) :=
  exactNorm_eq hT.le _ le_rfl hSA hℓ m u

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `finiteNormE`. -/
theorem finiteNormE (hℓ : 0 ≤ ℓ) (n : ℕ) (u : ↥(Esp T hT.le)) :
    appendixFiniteDerivativeNorm (zeroSemi hT.le _ (Esp_le_tower hT.le)) (dE hT ℓ) n u =
      ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (u.1 w) :=
  finiteNorm_eq hT.le _ (Esp_le_tower hT.le) (hSE hT) hℓ n u

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `finiteNormF`. -/
theorem finiteNormF (hℓ : 0 ≤ ℓ) (n : ℕ) (u : ↥(tower T C½)) :
    appendixFiniteDerivativeNorm (zeroSemi hT.le _ le_rfl) (dF ℓ) n u =
      ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (u.1 w) :=
  finiteNorm_eq hT.le _ le_rfl hSF hℓ n u

end Derivations

/-- The constant of Lemma D.3 for the index type `Fin 3`, the order `n` and the constants `C_m`. -/
def Cn_of (hD3 : Statement.lemma_D_3) (n : ℕ) (Cm : ℕ → ℝ) : ℝ := Classical.choose (hD3 (Fin 3) n Cm)

set_option maxHeartbeats 1000000 in
/-- **Lemma D.3 on derivative towers** (`sections/06d_mean_estimates.tex:50-58`). -/
theorem tower_lifting (hD3 : Statement.lemma_D_3) (hT : 0 < T) (n : ℕ) (Cm : ℕ → ℝ) :
    0 ≤ Cn_of hD3 n Cm ∧ ∀ (ℓ Clow : ℝ), 0 ≤ ℓ → 0 ≤ Clow →
      ∀ aK aΩ : Wd → ℝ → K½, aK ∈ tower T K½ → aΩ ∈ tower T K½ →
      (∀ u ∈ Esp T hT.le, endpointClosedTimeNorm T (u []) ≤
          Clow * endpointClosedTimeNorm T (Tk aK u [] + Tom T aΩ u [])) →
      (∀ m, 1 ≤ m → m ≤ n →
        Clow * (4 * ‖pjL‖ * ∑ w ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
              (fun w => w.length = m), ℓ ^ m * endpointClosedTimeNorm T (aK w) +
            2 * ‖pjL‖ * T * ∑ w ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
              (fun w => w.length = m), ℓ ^ m * endpointClosedTimeNorm T (aΩ w)) ≤ Cm m) →
      ∀ v ∈ Esp T hT.le,
        ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w.length * endpointClosedTimeNorm T (v w) ≤
          Cn_of hD3 n Cm * Clow * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n,
            ℓ ^ w.length * endpointClosedTimeNorm T (Tk aK v w + Tom T aΩ v w) := by
  obtain ⟨hCn, H⟩ := Classical.choose_spec (hD3 (Fin 3) n Cm)
  refine ⟨hCn, fun ℓ Clow hℓ hClow aK aΩ haK haΩ hZero hD7 v hv => ?_⟩
  let f : ↥(tower T C½) := ⟨Tk aK v + Tom T aΩ v, add_mem (Tk_mem haK hv.1) (Tom_mem hT haΩ hv.1)⟩
  have hf : f = TkB hT ⟨aK, haK⟩ ⟨v, hv⟩ + TomB hT ⟨aΩ, haΩ⟩ ⟨v, hv⟩ := rfl
  have key := H (Fin 2) ↥(tower T K½) ↥(Esp T hT.le) ↥(tower T C½)
    (dA ℓ) (dE hT ℓ) (dF ℓ)
    (zeroSemi hT.le _ le_rfl) (zeroSemi hT.le _ (Esp_le_tower hT.le))
    (zeroSemi hT.le _ le_rfl) 0 ![TkB hT, TomB hT] ![⟨aK, haK⟩, ⟨aΩ, haΩ⟩]
    ![4 * ‖pjL‖, 2 * ‖pjL‖ * T] Clow
    (fun i u => by simp)
    (fun j i a u => by
      fin_cases j
      · exact leibnizK hT ℓ i a u
      · exact leibnizOm hT ℓ i a u)
    (fun i i' g => shiftOn_comm _ le_rfl (hSF) ℓ i i' g)
    (fun i i' a => shiftOn_comm _ le_rfl (hSA) ℓ i i' a)
    (fun j => by
      fin_cases j
      · exact mul_nonneg (by norm_num) (norm_nonneg pjL)
      · exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg pjL)) hT.le)
    (fun j a u => by
      fin_cases j
      · exact N_Tk_le hT a.2 u.2.1
      · exact N_Tom_le hT a.2 u.2.1)
    hClow
    (fun u => by
      have h := hZero u.1 u.2
      simp only [Fin.sum_univ_two, LinearMap.zero_apply, zero_add]
      exact h)
    (fun m hm1 hmn => by
      have := hD7 m hm1 hmn
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [exactNormA hT ℓ hℓ m, exactNormA hT ℓ hℓ m]
      exact this)
    ⟨v, hv⟩ f (by simp only [Fin.sum_univ_two, LinearMap.zero_apply, zero_add]; exact hf.symm)
  rw [finiteNormE hT ℓ hℓ, finiteNormF hT ℓ hℓ] at key
  exact key

end

end TorusEuler.Paper.Lib.S5a.Tower

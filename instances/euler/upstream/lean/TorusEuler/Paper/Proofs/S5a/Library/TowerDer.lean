import TorusEuler.Paper.Proofs.S5a.Library.TowerZero
import TorusEuler.TerminalMeanSpatialInverse
import TorusEuler.TerminalMeanSpatialWordProduct

/-!
# S5a library: derivative towers (the Leibniz expansion `Tw` differentiates the product)

A tower `X : List (Fin 3) → ℝ → HalfHolder 𝕋³ E` is a *derivative tower* (`IsDer`) if `X (i :: w) t` is
the derivative of `X w t` in the coordinate direction `i`, for `t ∈ [0,T]` (`endpointTorusHasSpatialDerivative`).
`Tw_der`: for symmetric derivative towers `a`, `u`, the expansion `Tw w a u` is again one (it is the tower of
words of the product `a u`); `Tk_der`; `eq_of_der`: derivative towers with equal base agree.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerDerSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerDerSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- `X` is a derivative tower on `[0,T]`. -/
def IsDer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    (X : Wd → ℝ → HalfHolder (UnitAddTorus (Fin 3)) E) : Prop :=
  ∀ (i : Fin 3) (w : Wd), ∀ t ∈ Icc 0 T,
    endpointTorusHasSpatialDerivative (coordinateDirection i) (X w t) (X (i :: w) t)

variable {T : ℝ}

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hasSD_unique`. -/
theorem hasSD_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Vec3}
    {f df dg : HalfHolder (UnitAddTorus (Fin 3)) E}
    (hf : endpointTorusHasSpatialDerivative u f df) (hg : endpointTorusHasSpatialDerivative u f dg) :
    df = dg := by
  apply HalfHolder.ext
  intro a
  simpa only [zero_smul, toUnitTorus_zero, add_zero] using (hf a 0).unique (hg a 0)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hasSD_coefMul`. -/
theorem hasSD_coefMul {u : Vec3} {K dK : K½} {y dy : C½}
    (hK : endpointTorusHasSpatialDerivative u K dK) (hy : endpointTorusHasSpatialDerivative u y dy) :
    endpointTorusHasSpatialDerivative u (K.coefficientMul y)
      (dK.coefficientMul y + K.coefficientMul dy) := by
  intro a s
  have h := (hK a s).clm_apply (hy a s)
  simpa only [HalfHolder.eval_coefficientMul, map_add] using h

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `hasSD_pjL`. -/
theorem hasSD_pjL {u : Vec3} {f df : C½} (h : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (pjL f) (pjL df) :=
  endpointStrongSpatialLeray_preservesSpatialDerivative h

/-- The Leibniz expansion of two symmetric derivative towers is a derivative tower (product rule). -/
theorem Tw_der {a : Wd → ℝ → K½} {u : Wd → ℝ → S} (hsa : Sym a) (hsu : Sym u) (hda : IsDer T a)
    (hdu : ∀ (i : Fin 3) (w : Wd), ∀ t ∈ Icc 0 T,
      endpointTorusHasSpatialDerivative (coordinateDirection i) (u w t : C½) (u (i :: w) t : C½))
    (w : Wd) : ∀ (i : Fin 3) (t : ℝ), t ∈ Icc 0 T →
    endpointTorusHasSpatialDerivative (coordinateDirection i) (Tw w a u t) (Tw (i :: w) a u t) := by
  induction w generalizing a u with
  | nil =>
    intro i t ht
    show endpointTorusHasSpatialDerivative _ ((a [] t).coefficientMul ((u [] t : S) : C½))
      ((a [i] t).coefficientMul ((u [] t : S) : C½) + (a [] t).coefficientMul ((u [i] t : S) : C½))
    exact hasSD_coefMul (hda i [] t ht) (hdu i [] t ht)
  | cons j w ih =>
    intro i t ht
    have e : Tw (i :: j :: w) a u = Tw (j :: i :: w) a u :=
      Tw_perm (List.Perm.swap j i w) a u hsa hsu
    rw [e]
    have h1 := ih (a := fun p => a (j :: p)) (u := u) (fun p q h => hsa _ _ (h.cons j)) hsu
      (fun i' w' t' ht' => by
        have h := hda i' (j :: w') t' ht'
        have e' := congrFun (hsa _ _ (List.Perm.swap j i' w')) t'
        rw [e'] at h
        exact h) hdu
    have h2 := ih (a := a) (u := fun p => u (j :: p)) hsa (fun p q h => hsu _ _ (h.cons j)) hda
      (fun i' w' t' ht' => by
        have h := hdu i' (j :: w') t' ht'
        have e' := congrFun (hsu _ _ (List.Perm.swap j i' w')) t'
        rw [e'] at h
        exact h)
    exact (h1 i t ht).add (h2 i t ht)

/-- `Tk a v` of a derivative tower is a derivative tower (Leibniz rule; TeX 46-48). -/
theorem Tk_der {a : Wd → ℝ → K½} {u : Wd → ℝ → S} (hsa : Sym a) (hsu : Sym u) (hda : IsDer T a)
    (hdu : ∀ (i : Fin 3) (w : Wd), ∀ t ∈ Icc 0 T,
      endpointTorusHasSpatialDerivative (coordinateDirection i) (u w t : C½) (u (i :: w) t : C½))
    (w : Wd) (i : Fin 3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    endpointTorusHasSpatialDerivative (coordinateDirection i) (Tk a u w t) (Tk a u (i :: w) t) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  exact (hasSD_pjL (Tw_der hsa hsu hda hdu w i t ht)).sub
    (hasSD_pjL (Tw_der hsa hsu hda hdu w i 0 h0))

/-- Two derivative towers with the same base and derivative relations coincide (TeX 46-48). -/
theorem eq_of_der {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X Y : Wd → ℝ → HalfHolder (UnitAddTorus (Fin 3)) E} (hX : IsDer T X) (hY : IsDer T Y)
    (h0 : ∀ t ∈ Icc 0 T, X [] t = Y [] t) (w : Wd) : ∀ t ∈ Icc 0 T, X w t = Y w t := by
  induction w with
  | nil => exact h0
  | cons i w ih =>
    intro t ht
    have h := hX i w t ht
    rw [ih t ht] at h
    exact hasSD_unique h (hY i w t ht)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `mem_solenoidal_of_der`. -/
theorem mem_solenoidal_of_der {X : Wd → ℝ → C½} (hX : IsDer T X)
    (h0 : ∀ t ∈ Icc 0 T, X [] t ∈ endpointHalfHolderSolenoidal) (w : Wd) :
    ∀ t ∈ Icc 0 T, X w t ∈ endpointHalfHolderSolenoidal := by
  induction w with
  | nil => exact h0
  | cons i w ih =>
    intro t ht
    have hfix := (endpointStrongSpatialLeray_fixed_iff _).mpr (ih t ht)
    have h1 := endpointStrongSpatialLeray_preservesSpatialDerivative (hX i w t ht)
    rw [hfix] at h1
    have h2 := hasSD_unique (hX i w t ht) h1
    exact (endpointStrongSpatialLeray_fixed_iff _).mp h2.symm

end

end TorusEuler.Paper.Lib.S5a.Tower

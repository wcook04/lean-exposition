import TorusEuler.Paper.Proofs.S5a.Library.Tower

/-!
# S5a library: the coefficient action on derivative towers

`Tw w a u` is the Leibniz expansion of `∂^w (a u)` (`a` a tower of coefficients in `C^{0,1/2}`, `u` a
tower of solenoidal velocities): `Tw [] a u = a_∅ u_∅` and `Tw (i :: w) a u = Tw w (∂_i a) u +
Tw w a (∂_i u)`. The two bilinear actions of the system (4.9) projected to the solenoidal part
(`sections/06d_mean_estimates.tex:44-58`) are `Tk a u = P(a u)(t) - P(a u)(0)` and
`Tom a u = -P ∫_0^t (a u)`.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance towerOpsSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance towerOpsSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- The Leray projection `P` of Theorem 4.2 as an endomorphism of `C^{0,1/2}`. -/
def pjL : C½ →L[ℝ] C½ := endpointHalfHolderSolenoidal.subtypeL.comp endpointStrongSpatialProjection

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `cm_add`. -/
theorem cm_add (K K' : K½) (y : C½) :
    (K + K').coefficientMul y = K.coefficientMul y + K'.coefficientMul y := by
  apply HalfHolder.ext; intro x
  simp only [HalfHolder.eval_coefficientMul, map_add, add_apply]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `cm_smul`. -/
theorem cm_smul (c : ℝ) (K : K½) (y : C½) :
    (c • K).coefficientMul y = c • K.coefficientMul y := by
  apply HalfHolder.ext; intro x
  simp only [HalfHolder.eval_coefficientMul, map_smul, smul_apply]

/-- The Leibniz expansion of `∂^w (a u)`. -/
def Tw : Wd → (Wd → ℝ → K½) → (Wd → ℝ → S) → ℝ → C½
  | [], a, u => fun t => (a [] t).coefficientMul ((u [] t : S) : C½)
  | i :: w, a, u => Tw w (fun p => a (i :: p)) u + Tw w a (fun p => u (i :: p))

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_add_left`. -/
theorem Tw_add_left (w : Wd) : ∀ (a a' : Wd → ℝ → K½) (u : Wd → ℝ → S),
    Tw w (a + a') u = Tw w a u + Tw w a' u := by
  induction w with
  | nil => intro a a' u; funext t; simp only [Tw, Pi.add_apply]; exact cm_add _ _ _
  | cons i w ih =>
    intro a a' u
    simp only [Tw]
    have e : (fun p => (a + a') (i :: p)) = (fun p => a (i :: p)) + fun p => a' (i :: p) := rfl
    rw [e, ih, ih]; abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_smul_left`. -/
theorem Tw_smul_left (w : Wd) : ∀ (c : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S),
    Tw w (c • a) u = c • Tw w a u := by
  induction w with
  | nil => intro c a u; funext t; simp only [Tw, Pi.smul_apply]; exact cm_smul _ _ _
  | cons i w ih =>
    intro c a u
    simp only [Tw]
    have e : (fun p => (c • a) (i :: p)) = c • fun p => a (i :: p) := rfl
    rw [e, ih, ih, smul_add]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_add_right`. -/
theorem Tw_add_right (w : Wd) : ∀ (a : Wd → ℝ → K½) (u u' : Wd → ℝ → S),
    Tw w a (u + u') = Tw w a u + Tw w a u' := by
  induction w with
  | nil =>
    intro a u u'; funext t
    simp only [Tw, Pi.add_apply, Submodule.coe_add]
    exact map_add _ _ _
  | cons i w ih =>
    intro a u u'
    simp only [Tw]
    have e : (fun p => (u + u') (i :: p)) = (fun p => u (i :: p)) + fun p => u' (i :: p) := rfl
    rw [e, ih, ih]; abel

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_smul_right`. -/
theorem Tw_smul_right (w : Wd) : ∀ (c : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S),
    Tw w a (c • u) = c • Tw w a u := by
  induction w with
  | nil =>
    intro c a u; funext t
    simp only [Tw, Pi.smul_apply]
    exact map_smul _ _ _
  | cons i w ih =>
    intro c a u
    simp only [Tw]
    have e : (fun p => (c • u) (i :: p)) = c • fun p => u (i :: p) := rfl
    rw [e, ih, ih, smul_add]

/-- Symmetric towers. -/
def Sym {X : Type*} (u : Wd → ℝ → X) : Prop := ∀ p q : Wd, p.Perm q → u p = u q

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_perm`. -/
theorem Tw_perm {p q : Wd} (h : p.Perm q) :
    ∀ (a : Wd → ℝ → K½) (u : Wd → ℝ → S), Sym a → Sym u → Tw p a u = Tw q a u := by
  induction h with
  | nil => intros; rfl
  | cons x _ ih =>
    intro a u ha hu
    simp only [Tw]
    rw [ih _ _ (fun p q h => ha _ _ (h.cons x)) hu, ih _ _ ha (fun p q h => hu _ _ (h.cons x))]
  | swap x y l =>
    intro a u ha hu
    simp only [Tw]
    have e1 : (fun p => a (x :: y :: p)) = fun p => a (y :: x :: p) :=
      funext fun p => ha _ _ (List.Perm.swap _ _ _)
    have e2 : (fun p => u (x :: y :: p)) = fun p => u (y :: x :: p) :=
      funext fun p => hu _ _ (List.Perm.swap _ _ _)
    rw [e1, e2]; abel
  | trans _ _ ih₁ ih₂ =>
    intro a u ha hu
    exact (ih₁ a u ha hu).trans (ih₂ a u ha hu)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_continuousOn`. -/
theorem Tw_continuousOn {T : ℝ} {a : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) (w : Wd) :
    ContinuousOn (Tw w a u) (Icc 0 T) := by
  induction w generalizing a u with
  | nil =>
    have hK : ContinuousOn (fun t => (a [] t).coefficientMul) (Icc 0 T) :=
      HalfHolder.lipschitzWith_coefficientMul.continuous.comp_continuousOn (ha.2 [])
    have hv : ContinuousOn (fun t => ((u [] t : S) : C½)) (Icc 0 T) :=
      endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn (hu.2 [])
    exact hK.clm_apply hv
  | cons i w ih =>
    simp only [Tw]
    exact (ih (shift_mem i ha) hu).add (ih ha (shift_mem i hu))

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tw_bound`. -/
theorem Tw_bound {a : Wd → ℝ → K½} {u : Wd → ℝ → S} (t : ℝ) :
    ‖Tw [] a u t‖ ≤ 2 * ‖a [] t‖ * ‖u [] t‖ := by
  simp only [Tw]
  calc ‖(a [] t).coefficientMul ((u [] t : S) : C½)‖
      ≤ ‖(a [] t).coefficientMul‖ * ‖((u [] t : S) : C½)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * ‖a [] t‖) * ‖u [] t‖ :=
      mul_le_mul (HalfHolder.norm_coefficientMul_le _) (le_of_eq rfl) (norm_nonneg _)
        (by positivity)
    _ = _ := by ring

/-- Time clamped to `[0,T]`, so that primitives only see the values on `[0,T]`. -/
def cl (T t : ℝ) : ℝ := max 0 (min t T)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `cl_mem`. -/
theorem cl_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : cl T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `cl_eq`. -/
theorem cl_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : cl T t = t := by
  unfold cl
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- The primitive in time, clamped to `[0,T]`. -/
def primC (T : ℝ) (f : ℝ → C½) (t : ℝ) : C½ := endpointPrimitive f (cl T t)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `primC_add`. -/
theorem primC_add {T : ℝ} (hT : 0 ≤ T) {f g : ℝ → C½} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) : primC T (f + g) = primC T f + primC T g := by
  funext t
  have h1 := (hf.mono (Icc_subset_Icc_right (cl_mem hT t).2)).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) (cl_mem hT t).1
  have h2 := (hg.mono (Icc_subset_Icc_right (cl_mem hT t).2)).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) (cl_mem hT t).1
  simp only [primC, endpointPrimitive, Pi.add_apply]
  exact intervalIntegral.integral_add h1 h2

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `primC_smul`. -/
theorem primC_smul (T c : ℝ) (f : ℝ → C½) : primC T (c • f) = c • primC T f := by
  funext t
  simp only [primC, endpointPrimitive, Pi.smul_apply]
  exact intervalIntegral.integral_smul _ _

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `primC_continuousOn`. -/
theorem primC_continuousOn {T : ℝ} (hT : 0 < T) {f : ℝ → C½} (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (primC T f) (Icc 0 T) := by
  have hp := (contDiffOn_endpointPrimitive_succ (n := 0) hT (contDiffOn_zero.mpr hf)).continuousOn
  exact hp.congr fun t ht => by simp only [primC, cl_eq ht]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `primC_eq`. -/
theorem primC_eq {T : ℝ} {f : ℝ → C½} {t : ℝ} (ht : t ∈ Icc 0 T) :
    primC T f t = endpointPrimitive f t := by simp only [primC, cl_eq ht]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `norm_primC_le`. -/
theorem norm_primC_le {T : ℝ} (hT : 0 < T) {f : ℝ → C½} (hf : ContinuousOn f (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ‖primC T f t‖ ≤ T * endpointClosedTimeNorm T f := by
  rw [primC_eq ht]
  have hp := (contDiffOn_endpointPrimitive_succ (n := 0) hT (contDiffOn_zero.mpr hf)).continuousOn
  exact (norm_le_endpointClosedTimeNorm hp ht).trans
    (endpointClosedTimeNorm_endpointPrimitive_le hT.le hf)

/-- The `K`-action `P(a u)(t) - P(a u)(0)`. -/
def Tk (a : Wd → ℝ → K½) (u : Wd → ℝ → S) : Wd → ℝ → C½ :=
  fun w t => pjL (Tw w a u t) - pjL (Tw w a u 0)

/-- The `Ω`-action `-P ∫_0^t (a u)`. -/
def Tom (T : ℝ) (a : Wd → ℝ → K½) (u : Wd → ℝ → S) : Wd → ℝ → C½ :=
  fun w t => -pjL (primC T (Tw w a u) t)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_perm`. -/
theorem Tk_perm {a : Wd → ℝ → K½} {u : Wd → ℝ → S} (ha : Sym a) (hu : Sym u) : Sym (Tk a u) := by
  intro p q h
  funext t
  simp only [Tk, Tw_perm h a u ha hu]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_perm`. -/
theorem Tom_perm {T : ℝ} {a : Wd → ℝ → K½} {u : Wd → ℝ → S} (ha : Sym a) (hu : Sym u) :
    Sym (Tom T a u) := by
  intro p q h
  funext t
  simp only [Tom, Tw_perm h a u ha hu]

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_continuousOn`. -/
theorem Tk_continuousOn {T : ℝ} {a : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) (w : Wd) : ContinuousOn (Tk a u w) (Icc 0 T) :=
  (pjL.continuous.comp_continuousOn (Tw_continuousOn ha hu w)).sub continuousOn_const

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_continuousOn`. -/
theorem Tom_continuousOn {T : ℝ} (hT : 0 < T) {a : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) (w : Wd) : ContinuousOn (Tom T a u w) (Icc 0 T) :=
  (pjL.continuous.comp_continuousOn (primC_continuousOn hT (Tw_continuousOn ha hu w))).neg

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tk_mem`. -/
theorem Tk_mem {T : ℝ} {a : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) : Tk a u ∈ tower T C½ :=
  ⟨Tk_perm ha.1 hu.1, Tk_continuousOn ha hu⟩

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `Tom_mem`. -/
theorem Tom_mem {T : ℝ} (hT : 0 < T) {a : Wd → ℝ → K½} {u : Wd → ℝ → S}
    (ha : a ∈ tower T K½) (hu : u ∈ tower T S) : Tom T a u ∈ tower T C½ :=
  ⟨Tom_perm ha.1 hu.1, Tom_continuousOn hT ha hu⟩

end

end TorusEuler.Paper.Lib.S5a.Tower

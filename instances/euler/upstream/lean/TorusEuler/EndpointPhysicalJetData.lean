import TorusEuler.EndpointJointHaarRegularity
import TorusEuler.PeriodicLerayHolderLift
import TorusEuler.SmoothPeriodicHolder
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The coefficients and source of Appendix A as compatible spatial and mixed jets. -/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Pointwise Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "C½" => HalfHolder A Vec3
local notation "Slab(" T ")" => (Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3))
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (μt T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))

section DirectionalWords

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Successive constant directional derivatives within a closed time slab.
The first letter is the outermost derivative. -/
def endpointSlabDirectionalWord {I : Type*} (T : ℝ) (dir : I → ℝ × Vec3)
    (f : ℝ × Vec3 → E) : List I → ℝ × Vec3 → E
  | [] => f
  | i :: w => fun p => fderivWithin ℝ (endpointSlabDirectionalWord T dir f w) (Slab(T)) p (dir i)

theorem endpointSlabDirectionalWord_contDiffOn {I : Type*} {T : ℝ} (hT : 0 < T)
    (dir : I → ℝ × Vec3) {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f (Slab(T))) (w : List I) :
    ContDiffOn ℝ ∞ (endpointSlabDirectionalWord T dir f w) (Slab(T)) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    have hS : UniqueDiffOn ℝ (Slab(T)) := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
    have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ (endpointSlabDirectionalWord T dir f w) (Slab(T)))
        (Slab(T)) := ih.fderivWithin hS (by simp)
    exact hD.clm_apply contDiffOn_const

private theorem endpointSlab_vadd_spatial {T : ℝ} (u : Vec3) :
    ((0, u) : ℝ × Vec3) +ᵥ Slab(T) = Slab(T) := by
  rw [← Set.image_vadd]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨by simpa using hq.1, mem_univ _⟩
  · intro hp
    refine ⟨p - (0, u), ⟨?_, mem_univ _⟩, ?_⟩
    · simpa using hp.1
    · change (0, u) + (p - (0, u)) = p
      abel

/-- Constant directional differentiation within the slab preserves periodicity
in the spatial variable, including for directions with a time component. -/
theorem endpointSlabDirectionalWord_periodic {I : Type*} {T : ℝ} (dir : I → ℝ × Vec3)
    {f : ℝ × Vec3 → E} (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic fun x => f (t, x))
    (w : List I) :
    ∀ t ∈ Icc 0 T, SpatiallyPeriodic fun x => endpointSlabDirectionalWord T dir f w (t, x) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
    intro t ht n x
    let g := endpointSlabDirectionalWord T dir f w
    let z : ℝ × Vec3 := (0, latticeVector n)
    have hshift : EqOn (fun q => g (q + z)) g (Slab(T)) := by
      rintro ⟨s, y⟩ hy
      change g (s + 0, y + latticeVector n) = g (s, y)
      simpa only [add_zero] using ih s hy.1 n y
    have hderiv := fderivWithin_congr' (𝕜 := ℝ) hshift
      (show (t, x) ∈ Slab(T) from ⟨ht, mem_univ x⟩)
    rw [fderivWithin_comp_add_right, endpointSlab_vadd_spatial (latticeVector n)] at hderiv
    simpa only [endpointSlabDirectionalWord, z, Prod.mk_add_mk, add_zero] using
      congrArg (fun L : (ℝ × Vec3) →L[ℝ] E => L (dir i)) hderiv

/-- At fixed slab time, the derivative along a translated spatial line is the
next word jet. This is an ordinary two-sided derivative even at endpoint times. -/
theorem endpointSlabDirectionalWord_hasDerivAt_spatial {I : Type*} {T : ℝ} (hT : 0 < T)
    (dir : I → ℝ × Vec3) {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    (w : List I) {i : I} {u : Vec3} (hi : dir i = (0, u))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
    HasDerivAt (fun r : ℝ => endpointSlabDirectionalWord T dir f w (t, x + r • u))
      (endpointSlabDirectionalWord T dir f (i :: w) (t, x + s • u)) s := by
  have hg := endpointSlabDirectionalWord_contDiffOn hT dir hf w
  have hd := (hg.differentiableOn (by simp) (t, x + s • u) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hspace : HasDerivAt (fun r : ℝ => x + r • u) u s := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const u).const_add x
  have hline : HasDerivAt (fun r : ℝ => (t, x + r • u)) ((0, u) : ℝ × Vec3) s :=
    (hasDerivAt_const s t).prodMk hspace
  simpa only [Function.comp_def, endpointSlabDirectionalWord, hi] using
    hd.comp_hasDerivAt s hline (Eventually.of_forall fun r =>
      show (t, x + r • u) ∈ Slab(T) from ⟨ht, mem_univ _⟩)

/-- At fixed spatial point, the slab time derivative is the next word jet.
The within-set derivative is valid at both temporal endpoints. -/
theorem endpointSlabDirectionalWord_hasDerivWithinAt_time {I : Type*} {T : ℝ} (hT : 0 < T)
    (dir : I → ℝ × Vec3) {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    (w : List I) {i : I} (hi : dir i = (1, 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    HasDerivWithinAt (fun r : ℝ => endpointSlabDirectionalWord T dir f w (r, x))
      (endpointSlabDirectionalWord T dir f (i :: w) (t, x)) (Icc 0 T) t := by
  have hg := endpointSlabDirectionalWord_contDiffOn hT dir hf w
  have hd := (hg.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
  have hline : HasDerivAt (fun r : ℝ => (r, x)) ((1, 0) : ℝ × Vec3) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  simpa only [Function.comp_def, endpointSlabDirectionalWord, hi] using
    hd.comp_hasDerivWithinAt t hline.hasDerivWithinAt
      (show MapsTo (fun r : ℝ => (r, x)) (Icc 0 T) (Slab(T)) from fun _ hr => ⟨hr, mem_univ x⟩)

/-- Pure spatial words agree with the existing derivative words of the lift. -/
theorem endpointSlabDirectionalWord_eq_phaseOperatorWord {I : Type*} {T : ℝ} (hT : 0 < T)
    (dir : I → Vec3) {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f (Slab(T))) (w : List I)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    endpointSlabDirectionalWord T (fun i => (0, dir i)) f w (t, x) =
      phaseOperatorWord (fun i _ => dir i) w (fun y => f (t, y)) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    let g := endpointSlabDirectionalWord T (fun i => (0, dir i)) f w
    have hg : ContDiffOn ℝ ∞ g (Slab(T)) :=
      endpointSlabDirectionalWord_contDiffOn hT (fun i => (0, dir i)) hf w
    have hd := (hg.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
    have hslice := hd.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
      (Eventually.of_forall fun y : Vec3 => show (t, y) ∈ Slab(T) from ⟨ht, mem_univ y⟩)
    have h := congrArg (fun L : Vec3 →L[ℝ] E => L (dir i)) hslice.fderiv
    change fderiv ℝ (fun y => g (t, y)) x (dir i) =
      fderivWithin ℝ g (Slab(T)) (t, x) (0, dir i) at h
    rw [show (fun y => g (t, y)) = phaseOperatorWord (fun i _ => dir i) w
      (fun y => f (t, y)) from funext ih] at h
    exact h.symm

end DirectionalWords

section TimeLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

set_option maxHeartbeats 800000 in
omit [CompleteSpace E] in
/-- Uniform half-Hölder bounds on pointwise time derivatives give a Lipschitz
curve in the spatial half-Hölder norm. -/
theorem lipschitzOnWith_halfHolder_of_eval_hasDerivWithinAt {T B : ℝ} (hB : 0 ≤ B)
    {f df : ℝ → HalfHolder A E}
    (hDt : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => HalfHolder.eval a (f r))
      (HalfHolder.eval a (df t)) (Icc 0 T) t)
    (hBound : ∀ t ∈ Icc 0 T, ‖df t‖ ≤ B) : LipschitzOnWith ⟨B, hB⟩ f (Icc 0 T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, dist_eq_norm]
  apply (HalfHolder.norm_le_iff (mul_nonneg hB (norm_nonneg (s - t)))).mpr
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) := (HalfHolder.norm_le_iff hB).mp (hBound r hr)
  constructor
  · intro a
    change ‖HalfHolder.eval a (f s - f t)‖ ≤ _
    rw [map_sub]
    exact (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le (hDt a)
      (fun r hr => (hd r hr).1 a) ht hs
  · intro a b
    change ‖HalfHolder.eval a (f s - f t) - HalfHolder.eval b (f s - f t)‖ ≤ _
    simp only [map_sub]
    rw [show (HalfHolder.eval a (f s) - HalfHolder.eval a (f t)) -
      (HalfHolder.eval b (f s) - HalfHolder.eval b (f t)) =
      (HalfHolder.eval a (f s) - HalfHolder.eval b (f s)) -
      (HalfHolder.eval a (f t) - HalfHolder.eval b (f t)) by abel]
    rw [mul_right_comm]
    exact (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hDt a r hr).sub (hDt b r hr)) (fun r hr => (hd r hr).2 a b) ht hs

set_option maxHeartbeats 800000 in
/-- Evaluation at all torus labels identifies the derivative of the entire
continuous half-Hölder trajectory on the closed slab. -/
theorem hasDerivWithinAt_halfHolder_of_eval_hasDerivWithinAt {T t : ℝ}
    {f df : ℝ → HalfHolder A E} (hf : ContinuousOn f (Icc 0 T))
    (hdf : ContinuousOn df (Icc 0 T))
    (hDt : ∀ a r, r ∈ Icc 0 T → HasDerivWithinAt (fun s => HalfHolder.eval a (f s))
      (HalfHolder.eval a (df r)) (Icc 0 T) r) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt f (df t) (Icc 0 T) t := by
  have heq (r : ℝ) (hr : r ∈ Icc 0 T) : f r = endpointPrimitive df r + f 0 := by
    apply HalfHolder.ext
    intro a
    let L := HalfHolder.eval (E := E) a
    have hi := (hdf.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc
      (μ := volume) hr.1
    have hc : ContinuousOn (fun s => L (f s)) (Icc 0 r) :=
      (L.continuous.comp_continuousOn hf).mono (Icc_subset_Icc_right hr.2)
    have hdfC : ContinuousOn (fun s => L (df s)) (Icc 0 r) :=
      (L.continuous.comp_continuousOn hdf).mono (Icc_subset_Icc_right hr.2)
    have hIeval := hdfC.intervalIntegrable_of_Icc (μ := volume) hr.1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hc
      (fun s hs => (hDt a s ⟨hs.1.le, hs.2.le.trans hr.2⟩).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le hr.2))) hIeval
    rw [L.intervalIntegral_comp_comm hi] at hFTC
    change L (f r) = L (endpointPrimitive df r + f 0)
    rw [map_add]
    exact (sub_eq_iff_eq_add.mp hFTC.symm)
  have hd := (hasDerivWithinAt_endpointPrimitive_of_continuousOn hdf ht).add_const (f 0)
  exact hd.congr_of_mem heq ht

set_option maxHeartbeats 1000000 in
/-- Descend jointly smooth periodic time jets to smooth curves in the torus
half-Hölder norm. The entire sequence of pointwise time derivatives can be
realized simultaneously on the closed interval. -/
theorem exists_halfHolder_timeCurves_of_periodic_jets {T : ℝ} (hT : 0 < T)
    (g : ℕ → ℝ → Vec3 → E)
    (hg : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (g j)) Slab(T))
    (hper : ∀ j t, t ∈ Icc 0 T → SpatiallyPeriodic (g j t))
    (hDt : ∀ j t, t ∈ Icc 0 T → ∀ x, HasDerivWithinAt (fun r => g j r x)
      (g (j + 1) t x) (Icc 0 T) t) :
    ∃ U : ℕ → ℝ → HalfHolder A E, (∀ j, ContDiffOn ℝ ∞ (U j) (Icc 0 T)) ∧
      (∀ j t, t ∈ Icc 0 T → ∀ x, HalfHolder.eval (toUnitTorus x) (U j t) = g j t x) ∧
      (∀ j, ∃ B ≥ 0, ∀ t ∈ Icc 0 T, ‖U j t‖ ≤ B) := by
  classical
  choose Q hQ using fun j => exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic
    hT (hg j) (hper j) 0
  choose V hV using fun j t (ht : t ∈ Icc 0 T) =>
    exists_halfHolder_of_spatialHolderHalf_zero (hper j t ht) (hQ j t ht).1
  let U (j : ℕ) (t : ℝ) := if ht : t ∈ Icc 0 T then V j t ht else 0
  have hEval (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (U j t) = g j t x := by
    simpa only [U, dite_eq_left ht] using (hV j t ht).1 x
  have hBound (j : ℕ) : ∃ B ≥ 0, ∀ t ∈ Icc 0 T, ‖U j t‖ ≤ B := by
    let B := Real.sqrt 2 * max 0 (Q j)
    refine ⟨B, mul_nonneg (Real.sqrt_nonneg _) (le_max_left _ _), fun t ht => ?_⟩
    simpa only [U, dite_eq_left ht] using (hV j t ht).2.trans
      (mul_le_mul_of_nonneg_left ((hQ j t ht).2.trans (le_max_right 0 (Q j))) (Real.sqrt_nonneg _))
  have hDEval (j : ℕ) (a : A) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun r => HalfHolder.eval a (U j r)) (HalfHolder.eval a (U (j + 1) t))
        (Icc 0 T) t := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hEval (j + 1) t ht x]
    exact (hDt j t ht x).congr_of_mem (fun r hr => hEval j r hr x) ht
  have hCont (j : ℕ) : ContinuousOn (U j) (Icc 0 T) := by
    obtain ⟨B, hB, hL⟩ := hBound (j + 1)
    exact (lipschitzOnWith_halfHolder_of_eval_hasDerivWithinAt hB (hDEval j) hL).continuousOn
  have hDU (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (U j) (U (j + 1) t) (Icc 0 T) t :=
    hasDerivWithinAt_halfHolder_of_eval_hasDerivWithinAt (hCont j) (hCont (j + 1)) (hDEval j) ht
  have hFinite (n : ℕ) : ∀ j, ContDiffOn ℝ n (U j) (Icc 0 T) := by
    induction n with
    | zero => exact fun j => contDiffOn_zero.mpr (hCont j)
    | succ n ih =>
      intro j
      rw [Nat.cast_succ]
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)).mpr
      refine ⟨fun t ht => (hDU j t ht).differentiableWithinAt, by simp, ?_⟩
      exact (ih (j + 1)).congr (fun t ht => (hDU j t ht).derivWithin (uniqueDiffOn_Icc hT t ht))
  exact ⟨U, fun j => contDiffOn_iff_forall_nat_le.mpr fun n _ => hFinite n j, hEval, hBound⟩

end TimeLift

section MixedSlopes

theorem endpointTorusHasSpatialDerivative_norm_slope_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : Vec3} {f df : HalfHolder A E} (hSpatial : endpointTorusHasSpatialDerivative u f df)
    (a : A) {h : ℝ} (hh : h ≠ 0) :
    ‖h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) f - HalfHolder.eval a f) -
      HalfHolder.eval a df‖ ≤ ‖df‖ * Real.sqrt (|h| * ‖u‖) := by
  have hData := (HalfHolder.torusDifference_bounds_of_hasDerivAt f df u hSpatial hh).2
  let e := halfHolderTorusDifference u h f - df
  have hEval : ‖HalfHolder.eval a e‖ ≤ ‖df‖ * Real.sqrt (|h| * ‖u‖) :=
    (e.val.1.norm_coe_le_norm a).trans hData
  simpa only [e, map_sub, eval_halfHolderTorusDifference] using hEval

/-- A quantitative finite difference remainder in the value norm gives the
actual derivative along each translated torus line. -/
theorem endpointTorusHasSpatialDerivative_of_sqrtRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Vec3) (f df : HalfHolder A E) (C : ℝ)
    (hResidual : ∀ (a : A) (h : ℝ), h ≠ 0 →
      ‖HalfHolder.eval a (halfHolderTorusDifference u h f - df)‖ ≤
        C * Real.sqrt (|h| * ‖u‖)) :
    endpointTorusHasSpatialDerivative u f df := by
  intro a s
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let b := a + toUnitTorus (s • u)
  let R (h : ℝ) := C * Real.sqrt (|h| * ‖u‖)
  have hR : Continuous R :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_abs.mul continuous_const))
  have hZero : R 0 = 0 := by simp only [R, abs_zero, zero_mul, Real.sqrt_zero, mul_zero]
  have hLim : Tendsto R (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (hR.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa only [hZero] using h
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hStep : a + toUnitTorus ((s + h) • u) = b + toUnitTorus (h • u) := by
    rw [add_smul, toUnitTorus_add, ← add_assoc]
  change ‖h⁻¹ • (HalfHolder.eval (a + toUnitTorus ((s + h) • u)) f -
    HalfHolder.eval b f) - HalfHolder.eval b df‖ ≤ R h
  rw [hStep, ← eval_halfHolderTorusDifference, ← map_sub]
  exact hResidual b h hh

set_option maxHeartbeats 800000 in
/-- Fixed-time coefficient derivatives are also derivatives of the mixed path
multipliers in operator norm. The derivative fields agree with their fixed-time
coefficients at every label, as almost-everywhere actions on time paths. -/
theorem endpointMixedCoefficient_hasSpatialDerivative_of_timeSlices {T C : ℝ}
    (u : Vec3) (K dK : ℝ → K½) (Kmix dKmix : MixedCoefficient(T))
    (hC : 0 ≤ C)
    (hBound : ∀ t ∈ Icc 0 T, ‖dK t‖ ≤ C)
    (hDerivative : ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (K t) (dK t))
    (hKmix : ∀ (a : A) (v : Paths(T)),
      (fun t => HalfHolder.eval a Kmix v t) =ᵐ[μt T] fun t => HalfHolder.eval a (K t) (v t))
    (hdKmix : ∀ (a : A) (v : Paths(T)),
      (fun t => HalfHolder.eval a dKmix v t) =ᵐ[μt T] fun t => HalfHolder.eval a (dK t) (v t)) :
    endpointTorusHasSpatialDerivative u Kmix dKmix := by
  apply endpointTorusHasSpatialDerivative_of_sqrtRemainder u Kmix dKmix C
  intro a h hh
  let b := a + toUnitTorus (h • u)
  let D := h⁻¹ • (HalfHolder.eval b Kmix - HalfHolder.eval a Kmix) - HalfHolder.eval a dKmix
  rw [map_sub, eval_halfHolderTorusDifference]
  change ‖D‖ ≤ C * Real.sqrt (|h| * ‖u‖)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Real.sqrt_nonneg _))
  intro v
  let V₁ := HalfHolder.eval b Kmix v
  let V₀ := HalfHolder.eval a Kmix v
  let Vd := HalfHolder.eval a dKmix v
  have hD : D v = h⁻¹ • (V₁ - V₀) - Vd := by
    simp only [D, V₁, V₀, Vd, _root_.sub_apply, smul_apply]
  rw [hD]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hKmix b v, hKmix a v, hdKmix a v,
    Lp.coeFn_sub V₁ V₀, Lp.coeFn_smul h⁻¹ (V₁ - V₀),
    Lp.coeFn_sub (h⁻¹ • (V₁ - V₀)) Vd,
    ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))]
    with t h₁ h₀ hd hs hsmul hsub ht
  change V₁ t = _ at h₁
  change V₀ t = _ at h₀
  change Vd t = _ at hd
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hs, Pi.sub_apply, h₁, h₀, hd]
  have hTime := Ioc_subset_Icc_self ht
  let Q := h⁻¹ • (HalfHolder.eval b (K t) - HalfHolder.eval a (K t)) - HalfHolder.eval a (dK t)
  have hVal : ‖Q‖ ≤ C * Real.sqrt (|h| * ‖u‖) :=
    (endpointTorusHasSpatialDerivative_norm_slope_sub_le (hDerivative t hTime) a hh).trans
      (mul_le_mul_of_nonneg_right (hBound t hTime) (Real.sqrt_nonneg _))
  have hOp := (Q.le_opNorm (v t)).trans
    (mul_le_mul_of_nonneg_right hVal (norm_nonneg _))
  simpa only [Q, _root_.sub_apply, smul_apply] using hOp

private theorem endpointMixedSourceJetLp_norm_le {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (v : Paths(T)) (hv : ∀ᵐ t ∂μt T, ‖v t‖ ≤ C) : ‖v‖ ≤ Real.sqrt T * C := by
  have h := Lp.norm_le_of_ae_bound hC hv
  have hmeasure : (measureUnivNNReal (μt T) : ℝ) = T := by
    rw [measureUnivNNReal, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hT]
  simpa [hmeasure, Real.sqrt_eq_rpow, one_div] using h

theorem endpointMixedSource_hasSpatialDerivative_of_pathAction {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (u : Vec3) (F dF : ℝ → C½)
    (Fmix dFmix : HalfHolder A Paths(T))
    (hSpatial : ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (F t) (dF t))
    (hBound : ∀ t ∈ Icc 0 T, ‖dF t‖ ≤ C)
    (hF : ∀ a, (fun t => HalfHolder.eval a Fmix t) =ᵐ[μt T] fun t => HalfHolder.eval a (F t))
    (hdF : ∀ a, (fun t => HalfHolder.eval a dFmix t) =ᵐ[μt T] fun t => HalfHolder.eval a (dF t)) :
    endpointTorusHasSpatialDerivative u Fmix dFmix := by
  apply endpointTorusHasSpatialDerivative_of_sqrtRemainder u Fmix dFmix (Real.sqrt T * C)
  intro b h hh
  rw [map_sub, eval_halfHolderTorusDifference, mul_assoc]
  let x := HalfHolder.eval (b + toUnitTorus (h • u)) Fmix
  let y := HalfHolder.eval b Fmix
  let z := HalfHolder.eval b dFmix
  change ‖h⁻¹ • (x - y) - z‖ ≤ Real.sqrt T * (C * Real.sqrt (|h| * ‖u‖))
  apply endpointMixedSourceJetLp_norm_le hT (mul_nonneg hC (Real.sqrt_nonneg _))
  filter_upwards [hF (b + toUnitTorus (h • u)), hF b, hdF b,
    ae_restrict_mem (μ := volume) measurableSet_Ioc, Lp.coeFn_sub x y,
    Lp.coeFn_smul h⁻¹ (x - y), Lp.coeFn_sub (h⁻¹ • (x - y)) z]
    with t hx hy hz ht hSub hSmul hErr
  rw [hErr, Pi.sub_apply, hSmul, Pi.smul_apply, hSub, Pi.sub_apply]
  change ‖h⁻¹ • (x t - y t) - z t‖ ≤ _
  rw [hx, hy, hz]
  have ht' := Ioc_subset_Icc_self ht
  exact (endpointTorusHasSpatialDerivative_norm_slope_sub_le (hSpatial t ht') b hh).trans
    (mul_le_mul_of_nonneg_right (hBound t ht') (Real.sqrt_nonneg _))

end MixedSlopes

section StrongSpatialJets

/-- The time direction and the chosen spatial directions in the lift. -/
def endpointSlabLiftDirections {I : Type*} (u : I → Vec3) : Sum Unit I → ℝ × Vec3 :=
  Sum.elim (fun _ => (1, 0)) (fun i => (0, u i))

/-- The spatial derivative words, evaluated on the Euclidean lift. -/
def endpointSlabSpatialWord {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (u : I → Vec3) (f : ℝ × Vec3 → E) (q : List I) : ℝ × Vec3 → E :=
  endpointSlabDirectionalWord T (endpointSlabLiftDirections u) f (q.map Sum.inr)

/-- The quotient fields for the spatial derivative words of a periodic lift.
Every word is a smooth time curve in the actual half-Hölder norm. -/
structure EndpointSlabHalfHolderJets {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (u : I → Vec3) (f : ℝ × Vec3 → E) where
  curve : List I → ℝ → HalfHolder A E
  smooth : ∀ q, ContDiffOn ℝ ∞ (curve q) (Icc 0 T)
  eval_lift : ∀ q t, t ∈ Icc 0 T → ∀ x,
    HalfHolder.eval (toUnitTorus x) (curve q t) = endpointSlabSpatialWord T u f q (t, x)
  spatialDerivative : ∀ i q t, t ∈ Icc 0 T →
    endpointTorusHasSpatialDerivative (u i) (curve q t) (curve (i :: q) t)
  norm_bound : ∀ q, ∃ C ≥ 0, ∀ t ∈ Icc 0 T, ‖curve q t‖ ≤ C

set_option maxHeartbeats 1000000 in
/-- Realize the actual derivative words of a jointly smooth periodic lift in
the torus half-Hölder space, with smooth time dependence on the closed slab. -/
theorem exists_endpointSlabHalfHolderJets {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {T : ℝ} (hT : 0 < T) (u : I → Vec3) (f : ℝ × Vec3 → E)
    (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => f (t, x))) :
    Nonempty (EndpointSlabHalfHolderJets T u f) := by
  classical
  let dir := endpointSlabLiftDirections u
  let τ : Sum Unit I := Sum.inl ()
  let word (q : List I) (j : ℕ) := List.replicate j τ ++ q.map Sum.inr
  let g (q : List I) (j : ℕ) (t : ℝ) (x : Vec3) :=
    endpointSlabDirectionalWord T dir f (word q j) (t, x)
  have hg (q : List I) (j : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (g q j)) (Slab(T)) :=
    endpointSlabDirectionalWord_contDiffOn hT dir hf (word q j)
  have hPeriodic (q : List I) (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      SpatiallyPeriodic (g q j t) :=
    endpointSlabDirectionalWord_periodic dir hper (word q j) t ht
  have hDt (q : List I) (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      HasDerivWithinAt (fun r => g q j r x) (g q (j + 1) t x) (Icc 0 T) t := by
    have h := endpointSlabDirectionalWord_hasDerivWithinAt_time hT dir hf (word q j)
      (i := τ) rfl ht x
    simpa only [g, word, List.replicate_succ, List.cons_append] using h
  choose U hU using fun q => exists_halfHolder_timeCurves_of_periodic_jets
    hT (g q) (hg q) (hPeriodic q) (hDt q)
  let V (q : List I) (t : ℝ) := U q 0 t
  have hEval (q : List I) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (V q t) = endpointSlabSpatialWord T u f q (t, x) :=
    (hU q).2.1 0 t ht x
  refine ⟨⟨V, fun q => (hU q).1 0, hEval, ?_, fun q => (hU q).2.2 0⟩⟩
  intro i q t ht
  apply (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt (V q t) (V (i :: q) t) (u i)).mp
  intro x
  change HasDerivAt (fun r : ℝ => HalfHolder.eval (toUnitTorus (x + r • u i)) (V q t))
    (HalfHolder.eval (toUnitTorus x) (V (i :: q) t)) 0
  simp_rw [hEval q t ht, hEval (i :: q) t ht]
  simpa only [endpointSlabSpatialWord, List.map_cons, zero_smul, add_zero] using
    endpointSlabDirectionalWord_hasDerivAt_spatial hT dir hf (q.map Sum.inr)
      (i := Sum.inr i) (u := u i) rfl ht x 0

end StrongSpatialJets

section MixedJetRealization

/-- A continuous torus coefficient curve has a canonical mixed realization.
The operator at each label acts by pointwise multiplication in time. -/
theorem exists_endpointMixedCoefficient_of_timeCurve {T C : ℝ} (hC : 0 ≤ C)
    (K : ℝ → K½) (hK : ContinuousOn K (Icc 0 T)) (hBound : ∀ t ∈ Icc 0 T, ‖K t‖ ≤ C) :
    ∃ Kmix : MixedCoefficient(T), ‖Kmix‖ ≤ C ∧
      ∀ (a : A) (v : Paths(T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[μt T]
        fun t => HalfHolder.eval a (K t) (v t) := by
  let Kjoint (q : ℝ × A) := HalfHolder.eval q.2 (K q.1)
  have hKt (a : A) : AEStronglyMeasurable (fun t => Kjoint (t, a)) (μt T) :=
    ((HalfHolder.eval a).continuous.comp_continuousOn hK).aestronglyMeasurable_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have bK (t : ℝ) (ht : t ∈ Icc 0 T) := (HalfHolder.norm_le_iff hC).mp (hBound t ht)
  let Kmix := endpointMixedCoefficient Kjoint hKt (fun t ht => (bK t ht).1)
    (fun t ht => (bK t ht).2) hC
  exact ⟨Kmix, norm_endpointMixedCoefficient_le Kjoint hKt _ _ hC,
    endpointMixedCoefficient_apply_ae Kjoint hKt _ _ hC⟩

/-- Realize all coefficient words on the common temporal L² space. -/
theorem exists_endpointMixedCoefficient_jets {I : Type*} {T : ℝ} {u : I → Vec3}
    {f : ℝ × Vec3 → Vec3 →L[ℝ] Vec3} (K : EndpointSlabHalfHolderJets T u f) :
    ∃ Kmix : List I → MixedCoefficient(T),
      (∀ (q : List I) (a : A) (v : Paths(T)),
        (fun t => HalfHolder.eval a (Kmix q) v t) =ᵐ[μt T] fun t => HalfHolder.eval a (K.curve q t) (v t)) ∧
      (∀ (i : I) (q : List I), endpointTorusHasSpatialDerivative (u i) (Kmix q) (Kmix (i :: q))) := by
  classical
  choose C hC hBound using K.norm_bound
  choose Kmix hKmix using fun q => exists_endpointMixedCoefficient_of_timeCurve (hC q)
    (K.curve q) (K.smooth q).continuousOn (hBound q)
  refine ⟨Kmix, fun q => (hKmix q).2, fun i q => ?_⟩
  exact endpointMixedCoefficient_hasSpatialDerivative_of_timeSlices (u i)
    (K.curve q) (K.curve (i :: q)) (Kmix q) (Kmix (i :: q)) (hC (i :: q)) (hBound (i :: q))
    (K.spatialDerivative i q) (hKmix q).2 (hKmix (i :: q)).2

/-- Realize all source words as temporal L² paths with the same strong time slices. -/
theorem exists_endpointMixedSource_jets {I : Type*} {T : ℝ} (hT : 0 ≤ T) {u : I → Vec3}
    {f : ℝ × Vec3 → Vec3} (F : EndpointSlabHalfHolderJets T u f) :
    ∃ Fmix : List I → Mixed(T),
      (∀ (q : List I) (a : A),
        (fun t => HalfHolder.eval a (Fmix q) t) =ᵐ[μt T] fun t => HalfHolder.eval a (F.curve q t)) ∧
      (∀ (i : I) (q : List I), endpointTorusHasSpatialDerivative (u i) (Fmix q) (Fmix (i :: q))) := by
  classical
  choose C hC hBound using F.norm_bound
  choose Fmix hFmix using fun q => exists_endpointMixedSource hT (hC q)
    (F.curve q) (F.smooth q).continuousOn (hBound q)
  refine ⟨Fmix, fun q => (hFmix q).2.1, fun i q => ?_⟩
  exact endpointMixedSource_hasSpatialDerivative_of_pathAction hT (hC (i :: q)) (u i)
    (F.curve q) (F.curve (i :: q)) (Fmix q) (Fmix (i :: q)) (F.spatialDerivative i q)
    (hBound (i :: q)) (hFmix q).2.1 (hFmix (i :: q)).2.1

end MixedJetRealization

section PhysicalData

/-- A uniform spatial gradient bound on the smooth lift yields a uniform
Lipschitz bound on its undifferentiated torus curve. -/
theorem EndpointSlabHalfHolderJets.base_lipschitz {I E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 < T) {u : I → Vec3}
    {f : ℝ × Vec3 → E} (J : EndpointSlabHalfHolderJets T u f)
    (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => f (t, x))) :
    ∃ B ≥ 0, ∀ t ∈ Icc 0 T, ∀ a b : A,
      ‖HalfHolder.eval a (J.curve [] t) - HalfHolder.eval b (J.curve [] t)‖ ≤ B * dist a b := by
  obtain ⟨B, hB⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT
    (F := fun t x => f (t, x)) hf hper 1
  have hb : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT.le⟩ 0)
  refine ⟨2 * B, mul_nonneg zero_le_two hb, ?_⟩
  intro t ht a b
  have hSlice : ContDiff ℝ ∞ (fun x : Vec3 => f (t, x)) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  obtain ⟨x, y, hx, hy, hxy⟩ := holderBridge_exists_close_lifts a b
  have ha : HalfHolder.eval a (J.curve [] t) = f (t, x) := by
    rw [← hx]
    exact J.eval_lift [] t ht x
  have hEvalB : HalfHolder.eval b (J.curve [] t) = f (t, y) := by
    rw [← hy]
    exact J.eval_lift [] t ht y
  rw [ha, hEvalB]
  calc
    _ ≤ B * ‖x - y‖ := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hSlice.differentiable (by simp) z)
      (fun z _ => by simpa only [norm_iteratedFDeriv_one] using hB t ht z)
      (convex_univ : Convex ℝ (univ : Set Vec3)) (mem_univ y) (mem_univ x)
    _ ≤ B * (2 * dist a b) := mul_le_mul_of_nonneg_left hxy hb
    _ = _ := by ring

/-- Physical coefficient and forcing jets with compatible realizations in the
strong spatial half-Hölder space and on temporal L² paths. -/
structure EndpointPhysicalJets {I : Type*} (T : ℝ) (u : I → Vec3)
    (F M : ℝ × Vec3 → Vec3 →L[ℝ] Vec3) (L : ℝ × Vec3 → Vec3) where
  kinetic : EndpointSlabHalfHolderJets T u (fun q => kineticForm (F q))
  vorticity : EndpointSlabHalfHolderJets T u (fun q => vorticityForm (F q) (M q))
  source : EndpointSlabHalfHolderJets T u L
  kineticMixed : List I → MixedCoefficient(T)
  vorticityMixed : List I → MixedCoefficient(T)
  sourceMixed : List I → Mixed(T)
  kinetic_action : ∀ q (a : A) (v : Paths(T)),
    (fun t => HalfHolder.eval a (kineticMixed q) v t) =ᵐ[μt T]
      fun t => HalfHolder.eval a (kinetic.curve q t) (v t)
  vorticity_action : ∀ q (a : A) (v : Paths(T)),
    (fun t => HalfHolder.eval a (vorticityMixed q) v t) =ᵐ[μt T]
      fun t => HalfHolder.eval a (vorticity.curve q t) (v t)
  source_action : ∀ q (a : A),
    (fun t => HalfHolder.eval a (sourceMixed q) t) =ᵐ[μt T] fun t => HalfHolder.eval a (source.curve q t)
  kinetic_mixed_derivative : ∀ i q,
    endpointTorusHasSpatialDerivative (u i) (kineticMixed q) (kineticMixed (i :: q))
  vorticity_mixed_derivative : ∀ i q,
    endpointTorusHasSpatialDerivative (u i) (vorticityMixed q) (vorticityMixed (i :: q))
  source_mixed_derivative : ∀ i q,
    endpointTorusHasSpatialDerivative (u i) (sourceMixed q) (sourceMixed (i :: q))
  kinetic_lipschitz : ∃ B ≥ 0, ∀ t ∈ Icc 0 T, ∀ a b : A,
    ‖HalfHolder.eval a (kinetic.curve [] t) - HalfHolder.eval b (kinetic.curve [] t)‖ ≤ B * dist a b
  vorticity_lipschitz : ∃ B ≥ 0, ∀ t ∈ Icc 0 T, ∀ a b : A,
    ‖HalfHolder.eval a (vorticity.curve [] t) - HalfHolder.eval b (vorticity.curve [] t)‖ ≤ B * dist a b

set_option maxHeartbeats 1000000 in
/-- The physical coefficients `F* F` and `F* (M* - M) F` and the source have
actual compatible jets for all words of spatial directions on the closed slab. -/
theorem exists_endpointPhysicalJetData {I : Type*} {T : ℝ} (hT : 0 < T) (u : I → Vec3)
    (F M : ℝ × Vec3 → Vec3 →L[ℝ] Vec3) (L : ℝ × Vec3 → Vec3)
    (hF : ContDiffOn ℝ ∞ F (Slab(T))) (hM : ContDiffOn ℝ ∞ M (Slab(T)))
    (hL : ContDiffOn ℝ ∞ L (Slab(T)))
    (hFper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => F (t, x)))
    (hMper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => M (t, x)))
    (hLper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => L (t, x))) :
    Nonempty (EndpointPhysicalJets T u F M L) := by
  let K (q : ℝ × Vec3) := kineticForm (F q)
  let Ω (q : ℝ × Vec3) := vorticityForm (F q) (M q)
  let adj : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ[ℝ] (Vec3 →L[ℝ] Vec3) :=
    ContinuousLinearMap.adjoint
  have hFa : ContDiffOn ℝ ∞ (fun q => (F q).adjoint) (Slab(T)) := by
    change ContDiffOn ℝ ∞ (adj ∘ F) (Slab(T))
    exact adj.contDiff.comp_contDiffOn hF
  have hMa : ContDiffOn ℝ ∞ (fun q => (M q).adjoint) (Slab(T)) := by
    change ContDiffOn ℝ ∞ (adj ∘ M) (Slab(T))
    exact adj.contDiff.comp_contDiffOn hM
  have hK : ContDiffOn ℝ ∞ K (Slab(T)) := hFa.clm_comp hF
  have hΩ : ContDiffOn ℝ ∞ Ω (Slab(T)) := hFa.clm_comp ((hMa.sub hM).clm_comp hF)
  have hKper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (fun x => K (t, x)) := by
    intro n x
    exact congrArg kineticForm (hFper t ht n x)
  have hΩper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (fun x => Ω (t, x)) := by
    intro n x
    exact congrArg₂ vorticityForm (hFper t ht n x) (hMper t ht n x)
  obtain ⟨Kjet⟩ := exists_endpointSlabHalfHolderJets hT u K hK hKper
  obtain ⟨Ωjet⟩ := exists_endpointSlabHalfHolderJets hT u Ω hΩ hΩper
  obtain ⟨Ljet⟩ := exists_endpointSlabHalfHolderJets hT u L hL hLper
  obtain ⟨Kmix, hKa, hKd⟩ := exists_endpointMixedCoefficient_jets Kjet
  obtain ⟨Ωmix, hΩa, hΩd⟩ := exists_endpointMixedCoefficient_jets Ωjet
  obtain ⟨Lmix, hLa, hLd⟩ := exists_endpointMixedSource_jets hT.le Ljet
  exact ⟨⟨Kjet, Ωjet, Ljet, Kmix, Ωmix, Lmix, hKa, hΩa, hLa, hKd, hΩd, hLd,
    Kjet.base_lipschitz hT hK hKper, Ωjet.base_lipschitz hT hΩ hΩper⟩⟩

end PhysicalData

end

end TorusEuler

import TorusEuler.EndpointConcreteSpatialBootstrap
import TorusEuler.EndpointTimeRegularity
import TorusEuler.EndpointMixedConcreteOperator
import TorusEuler.EndpointMixedSource
import TorusEuler.EndpointMixedTimeRecovery
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Spatial differentiation of a continuous time representative of a mixed field. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (μt T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)

/-- A time curve of spatial fields gives the same time path at almost every label. -/
def EndpointMixedRepresents {T : ℝ} (w : Mixed(T)) (f : ℝ → C½) : Prop :=
  ∀ᵐ a ∂unitTorusMeasure, (fun t => HalfHolder.eval a w t) =ᵐ[μt T]
    fun t => HalfHolder.eval a (f t)

theorem EndpointMixedRepresents.of_spatialSlice {T : ℝ} (hT : 0 ≤ T)
    {w : Mixed(T)} {f : ℝ → C½} (hf : ContinuousOn f (Icc 0 T))
    (h : ∀ᵐ t ∂μt T, endpointHalfHolderToL2 (f t) =
      endpointSpatialSlice (endpointMixedToJoint T w) t) : EndpointMixedRepresents w f := by
  filter_upwards [endpointMixedToJoint_apply_ae w,
    ae_endpointTimeSlice_of_continuous_spatialSlice hT (endpointMixedToJoint T w) hf h]
    with a hw hf'
  exact hw.trans hf'.symm

/-- A mixed field and its continuous time representative have the same
primitive in the spatial half-Hölder space, throughout the closed slab. -/
theorem endpointMixedPrimitive_eq_of_spatialRepresentative {T : ℝ} (hT : 0 ≤ T)
    (w : Mixed(T)) {f : ℝ → C½} (hf : ContinuousOn f (Icc 0 T))
    (hRep : ∀ᵐ t ∂μt T, endpointHalfHolderToL2 (f t) =
      endpointSpatialSlice (endpointMixedToJoint T w) t) (t : Icc (0 : ℝ) T) :
    HalfHolder.map (endpointPrimitiveEvaluation t) w = endpointPrimitive f t :=
  endpointMixedPrimitive_eq_endpointPrimitive w hf
    (EndpointMixedRepresents.of_spatialSlice hT hf hRep) t

private theorem continuous_endpointSpatialSegmentEval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : HalfHolder A E) (a : A) (u : Vec3) (h : ℝ) :
    Continuous (fun s : ℝ => HalfHolder.eval (a + toUnitTorus ((s * h) • u)) z) :=
  z.val.1.continuous.comp
    (continuous_const.add (lipschitzWith_toUnitTorus.continuous.comp
      ((continuous_id.mul continuous_const).smul continuous_const)))

/-- Average the evaluation operators along the torus segment with lifted displacement
`h • u`, using its affine parameter on the unit interval. -/
def endpointSpatialSegmentAverage (a : A) (u : Vec3) (h : ℝ) :
    HalfHolder A Vec3 →L[ℝ] Vec3 := by
  let avg : HalfHolder A Vec3 →ₗ[ℝ] Vec3 :=
    { toFun := fun f => ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f
      map_add' := by
        intro f g
        simp only [map_add]
        exact intervalIntegral.integral_add
          ((continuous_endpointSpatialSegmentEval f a u h).intervalIntegrable 0 1)
          ((continuous_endpointSpatialSegmentEval g a u h).intervalIntegrable 0 1)
      map_smul' := by
        intro c f
        simp only [map_smul, RingHom.id_apply, intervalIntegral.integral_smul] }
  refine avg.mkContinuous 1 fun f => ?_
  change ‖∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f‖ ≤ 1 * ‖f‖
  have hbound := (HalfHolder.norm_le_iff (norm_nonneg f)).mp (le_refl ‖f‖)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun s => HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f)
    (fun s _ => hbound.1 (a + toUnitTorus ((s * h) • u)))
  simpa only [one_mul, sub_zero, abs_one, mul_one] using hb

theorem endpointSpatialSegmentAverage_apply (a : A) (u : Vec3) (h : ℝ) (f : HalfHolder A Vec3) :
    endpointSpatialSegmentAverage a u h f =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f :=
  rfl

private theorem norm_interval_average_sub_le (z : C½) (a : A) (u : Vec3) (h : ℝ) :
    ‖(∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) z) -
        HalfHolder.eval a z‖ ≤ ‖z‖ * Real.sqrt (|h| * ‖u‖) := by
  have hZ := (continuous_endpointSpatialSegmentEval z a u h).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have heval : (∫ _s in (0 : ℝ)..1, HalfHolder.eval a z) = HalfHolder.eval a z := by simp
  nth_rw 1 [← heval]
  rw [← intervalIntegral.integral_sub hZ intervalIntegrable_const]
  have hbound (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) :
      ‖HalfHolder.eval (a + toUnitTorus ((s * h) • u)) z - HalfHolder.eval a z‖ ≤
        ‖z‖ * Real.sqrt (|h| * ‖u‖) := by
    rw [uIoc_of_le zero_le_one] at hs
    have hstep : ‖(s * h) • u‖ ≤ |h| * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1.le]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 (abs_nonneg h))
        (norm_nonneg u)
    exact (HalfHolder.norm_eval_torusTranslate_lift_sub_le z ((s * h) • u) a).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (norm_nonneg z))
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

set_option maxHeartbeats 800000 in
/-- On the full closed slab, the spatial difference quotient of a recovered
field is the segment average of the recovered derivative field. -/
theorem endpointRecoveredTimeSlice_difference_eq_segmentAverage {T : ℝ} (hT : 0 < T)
    (w dw : Mixed(T)) (u : Vec3) (hDw : endpointTorusHasSpatialDerivative u w dw)
    {f df : ℝ → C½} (hf : ContinuousOn f (Icc 0 T)) (hdf : ContinuousOn df (Icc 0 T))
    (hFRep : ∀ᵐ t ∂μt T, endpointHalfHolderToL2 (f t) =
      endpointSpatialSlice (endpointMixedToJoint T w) t)
    (hDFRep : ∀ᵐ t ∂μt T, endpointHalfHolderToL2 (df t) =
      endpointSpatialSlice (endpointMixedToJoint T dw) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) (a : A) {h : ℝ} (hh : h ≠ 0) :
    h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) (f t) - HalfHolder.eval a (f t)) =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) (df t) := by
  let D : C½ →L[ℝ] Vec3 :=
    h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) - HalfHolder.eval a)
  let J := endpointSpatialSegmentAverage a u h
  have hD (z : C½) :
      D z = h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) z - HalfHolder.eval a z) := rfl
  have hJ (z : C½) : J z =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) z :=
    endpointSpatialSegmentAverage_apply a u h z
  have heq (r : ℝ) (hr : r ∈ Icc 0 T) :
      D (endpointPrimitive f r) = J (endpointPrimitive df r) := by
    let r' : Icc (0 : ℝ) T := ⟨r, hr⟩
    let L : Paths(T) →L[ℝ] Vec3 := endpointPrimitiveEvaluation r'
    have hF := endpointMixedPrimitive_eq_of_spatialRepresentative hT.le w hf hFRep r'
    have hDF := endpointMixedPrimitive_eq_of_spatialRepresentative hT.le dw hdf hDFRep r'
    change D (endpointPrimitive f r') = J (endpointPrimitive df r')
    rw [← hF, ← hDF, hD, hJ]
    change h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) (HalfHolder.map L w) -
        HalfHolder.eval a (HalfHolder.map L w)) =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) (HalfHolder.map L dw)
    simp only [HalfHolder.eval_map, ← map_sub, ← map_smul]
    rw [← eval_halfHolderTorusDifference,
      HalfHolder.eval_torusDifference_eq_integral w dw u hDw hh a,
      ← L.intervalIntegral_comp_comm
        ((continuous_endpointSpatialSegmentEval dw a u h).intervalIntegrable (0 : ℝ) 1)]
  have hFDer := D.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_endpointPrimitive_of_continuousOn hf ht)
  have hDFDer := J.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_endpointPrimitive_of_continuousOn hdf ht)
  have hDFDer' := hDFDer.congr_of_mem heq ht
  have hunique := uniqueDiffOn_Icc hT t ht
  have htEq : D (f t) = J (df t) :=
    ((hFDer.derivWithin hunique).symm.trans (hDFDer'.derivWithin hunique))
  rwa [hD, hJ] at htEq

set_option maxHeartbeats 800000 in
private theorem endpointTorusHasSpatialDerivative_of_segmentAverage (u : Vec3) (f df : C½)
    (hAverage : ∀ (a : A) (h : ℝ), h ≠ 0 →
      h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) f - HalfHolder.eval a f) =
        ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) df) :
    endpointTorusHasSpatialDerivative u f df := by
  intro a s
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let b := a + toUnitTorus (s • u)
  let R (h : ℝ) := ‖df‖ * Real.sqrt (|h| * ‖u‖)
  have hR : Continuous R :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_abs.mul continuous_const))
  have hZero : R 0 = 0 := by simp only [R, abs_zero, zero_mul, Real.sqrt_zero, mul_zero]
  have hLim : Tendsto R (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (hR.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa only [hZero] using h
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hstep : a + toUnitTorus ((s + h) • u) = b + toUnitTorus (h • u) := by
    rw [add_smul, toUnitTorus_add, ← add_assoc]
  change ‖h⁻¹ • (HalfHolder.eval (a + toUnitTorus ((s + h) • u)) f -
    HalfHolder.eval b f) - HalfHolder.eval b df‖ ≤ R h
  rw [hstep, hAverage b h hh]
  exact norm_interval_average_sub_le df b u h

/-- A pair of continuous representatives of a mixed field and its derivative
retains the actual spatial derivative at every time, including both endpoints. -/
theorem endpointRecoveredTimeSlice_hasSpatialDerivative {T : ℝ} (hT : 0 < T)
    (w dw : Mixed(T)) (u : Vec3) (hDw : endpointTorusHasSpatialDerivative u w dw)
    {f df : ℝ → C½} (hf : ContinuousOn f (Icc 0 T)) (hdf : ContinuousOn df (Icc 0 T))
    (hFRep : ∀ᵐ t ∂μt T, endpointHalfHolderToL2 (f t) =
      endpointSpatialSlice (endpointMixedToJoint T w) t)
    (hDFRep : ∀ᵐ t ∂μt T, endpointHalfHolderToL2 (df t) =
      endpointSpatialSlice (endpointMixedToJoint T dw) t) :
    ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (f t) (df t) := by
  intro t ht
  apply endpointTorusHasSpatialDerivative_of_segmentAverage u (f t) (df t)
  exact fun a _ hh => endpointRecoveredTimeSlice_difference_eq_segmentAverage hT w dw u hDw
    hf hdf hFRep hDFRep t ht a hh

set_option maxHeartbeats 800000 in
/-- Temporal differentiation within the closed slab preserves spatial derivative
relations of time curves valued in the spatial half-Hölder space. -/
theorem endpointTorusHasSpatialDerivative_of_hasDerivWithinAt {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (u : Vec3) {f df : ℝ → C½} {ft dft : C½}
    (hSpatial : ∀ r ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (f r) (df r))
    (hF : HasDerivWithinAt f ft (Icc 0 T) t) (hDF : HasDerivWithinAt df dft (Icc 0 T) t) :
    endpointTorusHasSpatialDerivative u ft dft := by
  apply endpointTorusHasSpatialDerivative_of_segmentAverage u ft dft
  intro a h hh
  let D : C½ →L[ℝ] Vec3 :=
    h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) - HalfHolder.eval a)
  let J := endpointSpatialSegmentAverage a u h
  have heq (r : ℝ) (hr : r ∈ Icc 0 T) : D (f r) = J (df r) := by
    change h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) (f r) - HalfHolder.eval a (f r)) =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) (df r)
    rw [← eval_halfHolderTorusDifference, HalfHolder.eval_torusDifference_eq_integral (f r)
      (df r) u (hSpatial r hr) hh a]
  have hFDer := D.hasFDerivAt.comp_hasDerivWithinAt t hF
  have hDFDer := (J.hasFDerivAt.comp_hasDerivWithinAt t hDF).congr_of_mem heq ht
  have hunique := uniqueDiffOn_Icc hT t ht
  exact ((hFDer.derivWithin hunique).symm.trans (hDFDer.derivWithin hunique))

/-- Spatial derivatives commute with every available order of differentiation
in time, with time derivatives taken within the closed slab. -/
theorem endpointTorusHasSpatialDerivative_iteratedDerivWithin {T : ℝ} (hT : 0 < T)
    {n : ℕ} (u : Vec3) {f df : ℝ → C½}
    (hf : ContDiffOn ℝ n f (Icc 0 T)) (hdf : ContDiffOn ℝ n df (Icc 0 T))
    (hSpatial : ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (f t) (df t)) :
    ∀ m ≤ n, ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u
      (iteratedDerivWithin m f (Icc 0 T) t) (iteratedDerivWithin m df (Icc 0 T) t) := by
  have hdiffF := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Icc hT)).mp hf).2
  have hdiffDF := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Icc hT)).mp hdf).2
  intro m
  induction m with
  | zero =>
    intro _ t ht
    simpa only [iteratedDerivWithin_zero] using hSpatial t ht
  | succ m ih =>
    intro hm t ht
    rw [iteratedDerivWithin_succ, iteratedDerivWithin_succ]
    exact endpointTorusHasSpatialDerivative_of_hasDerivWithinAt hT ht u (ih (Nat.le_of_succ_le hm))
      ((hdiffF m (Nat.lt_of_succ_le hm) t ht).hasDerivWithinAt)
      ((hdiffDF m (Nat.lt_of_succ_le hm) t ht).hasDerivWithinAt)

/-- The compatibility result applies to every edge of a recovered spatial
derivative hierarchy, including mixed edges. -/
theorem endpointRecoveredSpatialHierarchy {T : ℝ} (hT : 0 < T) {I : Type*}
    (w : List I → Mixed(T)) (f : List I → ℝ → C½) (u : I → Vec3) (N : ℕ)
    (hDw : ∀ (i : I) (k : List I), k.length < N →
      endpointTorusHasSpatialDerivative (u i) (w k) (w (i :: k)))
    (hf : ∀ (k : List I), k.length ≤ N → ContinuousOn (f k) (Icc 0 T))
    (hRep : ∀ (k : List I), k.length ≤ N → ∀ᵐ t ∂μt T,
      endpointHalfHolderToL2 (f k t) = endpointSpatialSlice (endpointMixedToJoint T (w k)) t) :
    ∀ (t : ℝ), t ∈ Icc 0 T → ∀ (i : I) (k : List I), k.length < N →
      endpointTorusHasSpatialDerivative (u i) (f k t) (f (i :: k) t) := by
  intro t ht i k hk
  have hk' : (i :: k).length ≤ N := Nat.succ_le_of_lt hk
  exact endpointRecoveredTimeSlice_hasSpatialDerivative hT (w k) (w (i :: k)) (u i) (hDw i k hk)
    (hf k hk.le) (hf (i :: k) hk') (hRep k hk.le) (hRep (i :: k) hk') t ht

section TemporalBootstrap

variable {I X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The terms in a differentiated product in which at least one spatial
direction hits the coefficient, evaluated at a fixed time. -/
def endpointTemporalSpatialCorrection
    (C : List I → ℝ → X →L[ℝ] B) (v : List I → ℝ → X) (q : List I) (t : ℝ) : B :=
  ((endpointMixedCorrectionPairs q).map fun p => C p.1 t (v p.2 t)).sum

private theorem contDiffOn_endpointTemporalListCorrection
    {n : ℕ∞ω} {s : Set ℝ}
    (C : List I → ℝ → X →L[ℝ] B) (v : List I → ℝ → X) (l : List (List I × List I))
    (hC : ∀ p ∈ l, ContDiffOn ℝ n (C p.1) s)
    (hv : ∀ p ∈ l, ContDiffOn ℝ n (v p.2) s) :
    ContDiffOn ℝ n (fun t => (l.map fun p => C p.1 t (v p.2 t)).sum) s := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ => (0 : B)) s)
  | cons p l ih =>
    have hhead := (hC p List.mem_cons_self).clm_apply (hv p List.mem_cons_self)
    have htail := ih (fun r hr => hC r (List.mem_cons_of_mem _ hr))
      (fun r hr => hv r (List.mem_cons_of_mem _ hr))
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.add_def] using hhead.add htail

theorem contDiffOn_endpointTemporalSpatialCorrection
    {n : ℕ∞ω} {s : Set ℝ}
    (C : List I → ℝ → X →L[ℝ] B) (v : List I → ℝ → X) (q : List I)
    (hC : ∀ l : List I, l.length ≤ q.length → ContDiffOn ℝ n (C l) s)
    (hv : ∀ l : List I, l.length < q.length → ContDiffOn ℝ n (v l) s) :
    ContDiffOn ℝ n (endpointTemporalSpatialCorrection C v q) s := by
  apply contDiffOn_endpointTemporalListCorrection C v (endpointMixedCorrectionPairs q)
  · intro p hp
    have h := (endpointMixedCorrectionPairs_mem hp).2.1
    exact hC p.1 (by omega)
  · intro p hp
    exact hv p.2 (endpointMixedCorrectionPairs_mem hp).2.2

variable [CompleteSpace X] [CompleteSpace B]

/-- Recover time differentiability of all represented spatial derivatives
through the spatial cutoff. At each order the undifferentiated Volterra
coefficient acts on the current derivative, while all commutators involve
representatives of strictly lower spatial order. -/
theorem contDiffOn_endpointSpatialJets_of_integrated {T : ℝ} (hT : 0 < T) {n N : ℕ}
    {S : ℝ → X ≃L[ℝ] X} (P : B →L[ℝ] X) (c : List I → X)
    {K Ω : List I → ℝ → X →L[ℝ] B} {f : List I → ℝ → B} {v : List I → ℝ → X}
    (hS : ContDiffOn ℝ n (fun t => (S t : X →L[ℝ] X)) (Icc 0 T))
    (hK : ∀ l : List I, l.length ≤ N → ContDiffOn ℝ n (K l) (Icc 0 T))
    (hΩ : ∀ l : List I, l.length ≤ N → ContDiffOn ℝ n (Ω l) (Icc 0 T))
    (hf : ∀ l : List I, l.length ≤ N → ContDiffOn ℝ n (f l) (Icc 0 T))
    (hv : ∀ l : List I, l.length ≤ N → ContinuousOn (v l) (Icc 0 T))
    (hEq : ∀ (l : List I), l.length ≤ N → ∀ t ∈ Icc 0 T,
      S t (v l t) = c l + P (endpointPrimitive (fun r => Ω [] r (v l r)) t) -
        P (f l t + endpointTemporalSpatialCorrection K v l t -
          endpointPrimitive (endpointTemporalSpatialCorrection Ω v l) t)) :
    ∀ l : List I, l.length ≤ N → ContDiffOn ℝ n (v l) (Icc 0 T) := by
  have hMain (m : ℕ) : ∀ l : List I, l.length = m → l.length ≤ N →
      ContDiffOn ℝ n (v l) (Icc 0 T) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro l hl hN
      have hLower (q : List I) (hq : q.length < l.length) :
          ContDiffOn ℝ n (v q) (Icc 0 T) :=
        ih q.length (by omega) q rfl (by omega)
      have hCorrK := contDiffOn_endpointTemporalSpatialCorrection K v l
        (fun q hq => hK q (hq.trans hN)) hLower
      have hCorrΩ := contDiffOn_endpointTemporalSpatialCorrection Ω v l
        (fun q hq => hΩ q (hq.trans hN)) hLower
      have hPrim : ContDiffOn ℝ n (endpointPrimitive (endpointTemporalSpatialCorrection Ω v l))
          (Icc 0 T) := (contDiffOn_endpointPrimitive_succ hT hCorrΩ).of_le le_self_add
      exact contDiffOn_endpointVelocity_of_integrated hT P (c l) hS
        (hΩ [] (Nat.zero_le N)) (((hf l hN).add hCorrK).sub hPrim) (hv l hN) (hEq l hN)
  exact fun l hl => hMain l.length l rfl hl

end TemporalBootstrap

theorem EndpointMixedRepresents.spatialSlice {T : ℝ} (hT : 0 ≤ T)
    {w : Mixed(T)} {f : ℝ → C½} (h : EndpointMixedRepresents w f)
    (hf : ContinuousOn f (Icc 0 T)) : ∀ᵐ t ∂μt T,
    endpointSpatialSlice (endpointMixedToJoint T w) t = endpointHalfHolderToL2 (f t) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨z, _, hz, hzs⟩ := exists_endpointMixedSource hT (le_max_left 0 M) f hf
    (fun t ht => (hM t ht).trans (le_max_right 0 M))
  have hEq : endpointMixedToJoint T w = endpointMixedToJoint T z := by
    apply endpointJoint_eq_of_slices
    filter_upwards [h, endpointMixedToJoint_apply_ae w, endpointMixedToJoint_apply_ae z]
      with a hwa hwj hzj
    exact hwj.symm.trans (hwa.trans ((hz a).symm.trans hzj))
  rwa [hEq]

theorem EndpointMixedRepresents.zero {T : ℝ} :
    EndpointMixedRepresents (0 : Mixed(T)) (fun _ => 0) := by
  apply ae_of_all
  intro a
  filter_upwards [Lp.coeFn_zero (E := Vec3) (p := 2) (μ := μt T)] with t ht
  simpa only [map_zero, Pi.zero_apply] using ht

theorem EndpointMixedRepresents.add {T : ℝ} {v w : Mixed(T)} {f g : ℝ → C½}
    (hv : EndpointMixedRepresents v f) (hw : EndpointMixedRepresents w g) :
    EndpointMixedRepresents (v + w) (fun t => f t + g t) := by
  filter_upwards [hv, hw] with a hv' hw'
  have hAdd := Lp.coeFn_add (HalfHolder.eval a v) (HalfHolder.eval a w)
  filter_upwards [hv', hw', hAdd] with t ht hs ha
  simpa only [map_add, Pi.add_apply, ht, hs] using ha

theorem EndpointMixedRepresents.sub {T : ℝ} {v w : Mixed(T)} {f g : ℝ → C½}
    (hv : EndpointMixedRepresents v f) (hw : EndpointMixedRepresents w g) :
    EndpointMixedRepresents (v - w) (fun t => f t - g t) := by
  filter_upwards [hv, hw] with a hv' hw'
  have hSub := Lp.coeFn_sub (HalfHolder.eval a v) (HalfHolder.eval a w)
  filter_upwards [hv', hw', hSub] with t ht hs ha
  simpa only [map_sub, Pi.sub_apply, ht, hs] using ha

theorem EndpointMixedRepresents.coefficientMul {T : ℝ} {w : Mixed(T)} {f : ℝ → C½}
    {Cmix : MixedCoefficient(T)} {C : ℝ → K½}
    (hw : EndpointMixedRepresents w f)
    (hC : ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a Cmix v r) =ᵐ[μt T]
        fun r => HalfHolder.eval a (C r) (v r)) :
    EndpointMixedRepresents (Cmix.coefficientMul w) (fun t => (C t).coefficientMul (f t)) := by
  filter_upwards [hw, hC] with a hwa hCa
  filter_upwards [hwa, hCa (HalfHolder.eval a w)] with t hwt hCt
  rw [HalfHolder.eval_coefficientMul, hCt, hwt, HalfHolder.eval_coefficientMul]

theorem EndpointMixedRepresents.integration {T : ℝ} (hT : 0 ≤ T)
    {w : Mixed(T)} {f : ℝ → C½} (hw : EndpointMixedRepresents w f)
    (hf : ContinuousOn f (Icc 0 T)) :
    EndpointMixedRepresents (endpointMixedIntegration hT w) (endpointPrimitive f) := by
  filter_upwards [hw] with a hwa
  filter_upwards [endpointPrimitiveLp_apply_ae hT (HalfHolder.eval a w),
    ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))] with t ht htmem
  have hs := Ioc_subset_Icc_self htmem
  have hInt := (hf.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc (μ := volume) hs.1
  rw [endpointMixedIntegration, HalfHolder.eval_map, ht, endpointPrimitive_congr_ae hwa hs]
  exact (HalfHolder.eval a).intervalIntegral_comp_comm hInt

theorem ae_endpointMixedCoefficient_spatialSlice_of_pathAction {T : ℝ}
    (K : ℝ → K½) (Kmix : MixedCoefficient(T)) (hK : ContinuousOn K (Icc 0 T))
    (hMix : ∀ᵐ a ∂unitTorusMeasure, ∀ f : Paths(T),
      (fun r => HalfHolder.eval a Kmix f r) =ᵐ[μt T]
        fun r => HalfHolder.eval a (K r) (f r))
    (v : Mixed(T)) :
    ∀ᵐ t ∂μt T, endpointSpatialSlice (endpointMixedToJoint T (Kmix.coefficientMul v)) t =
      endpointWeakCoefficient (K t) (endpointSpatialSlice (endpointMixedToJoint T v) t) := by
  let Kjoint (q : ℝ × A) := HalfHolder.eval q.2 (K q.1)
  let slab := Icc (0 : ℝ) T ×ˢ (univ : Set A)
  have hKslab : ContinuousOn Kjoint slab := by
    have hs : ContinuousOn (fun q : ℝ × A => K q.1) slab :=
      hK.comp continuous_fst.continuousOn (fun _ hq => hq.1)
    have hb : ContinuousOn (fun q : ℝ × A => (K q.1).val.1) slab :=
      continuous_subtype_val.fst.comp_continuousOn hs
    exact hb.eval continuous_snd.continuousOn
  have hCompact : IsCompact slab := isCompact_Icc.prod isCompact_univ
  have hTime : ∀ᵐ q ∂endpointTorusMeasure T, q.1 ∈ Ioc (0 : ℝ) T :=
    (Measure.quasiMeasurePreserving_fst (μ := μt T) (ν := unitTorusMeasure)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hSlab : ∀ᵐ q ∂endpointTorusMeasure T, q ∈ slab :=
    hTime.mono fun q hq => ⟨Ioc_subset_Icc_self hq, mem_univ q.2⟩
  have hMeas := hKslab.aestronglyMeasurable_of_isCompact (μ := endpointTorusMeasure T)
    hCompact (measurableSet_Icc.prod MeasurableSet.univ)
  rw [Measure.restrict_eq_self_of_ae_mem hSlab] at hMeas
  obtain ⟨C, hBound⟩ := hCompact.exists_bound_of_continuousOn hKslab
  exact ae_endpointMixedCoefficient_spatialSlice K Kjoint Kmix hMeas (hSlab.mono hBound)
    (Filter.Eventually.of_forall (fun _ => rfl)) hMix v

theorem endpointMixedCorrection_pathCoefficient {I : Type*} {T : ℝ} (hT : 0 ≤ T)
    (K Ω : List I → MixedCoefficient(T)) (v : List I → Mixed(T)) (q : List I) :
    endpointMixedCorrection (fun t => endpointMixedPathCoefficient hT (K t) (Ω t)) v q =
      endpointMixedCorrection K v q - endpointMixedIntegration hT (endpointMixedCorrection Ω v q) := by
  simp only [endpointMixedCorrection, endpointMixedPathCoefficient_coefficientMul,
    endpointMixedProductOperator, _root_.sub_apply, ContinuousLinearMap.comp_apply]
  generalize endpointMixedCorrectionPairs q = pairs
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    simp only [List.map_cons, List.sum_cons, ih, map_add]
    abel

/-- The differentiated equation with the projected forcing is precisely the
vanishing projected residual needed for time recovery of the derivative. -/
theorem endpointProjectedMixedResidual_zero_of_spatialHierarchy {I : Type*} {T : ℝ}
    (hT : 0 ≤ T) (K Ω : List I → MixedCoefficient(T)) (w F : List I → Mixed(T))
    (q : List I)
    (hEq : endpointStrongMixedLeray T
      ((endpointMixedPathCoefficient hT (K []) (Ω [])).coefficientMul (w q)) =
        -endpointStrongMixedLeray T (F q) - endpointStrongMixedLeray T
          (endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT (K r) (Ω r)) w q)) :
    endpointStrongMixedLeray T
      (endpointMixedProductOperator hT (K []) (Ω []) (w q) + F q +
        endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT (K r) (Ω r)) w q) = 0 := by
  rw [← endpointMixedPathCoefficient_coefficientMul hT (K []) (Ω []), map_add, map_add, hEq]
  abel

section MixedSolveSpatialJets

local notation "PathOp(" T ")" => (Paths(T) →L[ℝ] Paths(T))
local notation "P[" T "]" => endpointStrongMixedLeray T

private theorem endpointMixedPathCoefficient_hasSpatialDerivative {T : ℝ} (hT : 0 ≤ T)
    (u : Vec3) (K Ω dK dΩ : MixedCoefficient(T))
    (hK : endpointTorusHasSpatialDerivative u K dK)
    (hΩ : endpointTorusHasSpatialDerivative u Ω dΩ) :
    endpointTorusHasSpatialDerivative u (endpointMixedPathCoefficient hT K Ω)
      (endpointMixedPathCoefficient hT dK dΩ) := by
  intro a s
  let J := (ContinuousLinearMap.mul ℝ (PathOp(T))) (endpointPrimitiveLp hT)
  have hJ : HasDerivAt (fun r : ℝ =>
      HalfHolder.eval (a + toUnitTorus (r • u)) (HalfHolder.map J Ω))
      (HalfHolder.eval (a + toUnitTorus (s • u)) (HalfHolder.map J dΩ)) s := by
    simpa only [HalfHolder.eval_map, Function.comp_def] using
      J.hasFDerivAt.comp_hasDerivAt s (hΩ a s)
  have h := (hK a s).sub hJ
  change HasDerivAt (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) K -
    HalfHolder.eval (a + toUnitTorus (r • u)) (HalfHolder.map J Ω)) _ s at h
  simpa only [endpointMixedPathCoefficient, map_sub, J] using h

private theorem endpointStrongMixedLeray_neg_hasSpatialDerivative {T : ℝ} (hT : 0 < T)
    (u : Vec3) (f df : Mixed(T)) (h : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (-(P[T] f)) (-(P[T] df)) := by
  intro a s
  have hp := freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound
    (H := Paths(T)) P[T] 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le hT z)
    u (fun r z => endpointStrongMixedLeray_torusTranslate T (toUnitTorus (r • u)) z) f df h
  have hn := (hp a s).neg
  change HasDerivAt
    (fun r : ℝ => -(HalfHolder.eval (a + toUnitTorus (r • u)) (P[T] f))) _ s at hn
  simpa only [map_neg] using hn

set_option maxHeartbeats 800000 in
/-- The spatial derivative words of a base mixed solve satisfy the projected
path residual with the kinetic and vorticity commutators. -/
theorem exists_endpointMixedSolveSpatialJets {I : Type*} {T : ℝ} (hT : 0 < T)
    (K Ω : List I → MixedCoefficient(T)) (F : List I → Mixed(T)) (v : Mixed(T)) (u : I → Vec3)
    (hv : P[T] v = v)
    (hProjected : P[T] (endpointMixedProductOperator hT.le (K []) (Ω []) v + F []) = 0)
    (S : freezingFixedSpace P[T] ≃L[ℝ] freezingFixedSpace P[T])
    (hS : (S : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T]) =
      freezingCompression P[T] (endpointMixedPathCoefficient hT.le (K []) (Ω [])).coefficientMul
        (endpointStrongMixedLeray_idempotent hT))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P[T]) a,
      μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
        ⟪HalfHolder.eval a (endpointMixedPathCoefficient hT.le (K []) (Ω []))
          (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (N : ℕ)
    (hK : ∀ (i : I) (q : List I), q.length < N →
      endpointTorusHasSpatialDerivative (u i) (K q) (K (i :: q)))
    (hΩ : ∀ (i : I) (q : List I), q.length < N →
      endpointTorusHasSpatialDerivative (u i) (Ω q) (Ω (i :: q)))
    (hF : ∀ (i : I) (q : List I), q.length < N →
      endpointTorusHasSpatialDerivative (u i) (F q) (F (i :: q))) :
    ∃ w : List I → Mixed(T), w [] = v ∧ (∀ q : List I, q.length ≤ N → P[T] (w q) = w q) ∧
      (∀ q : List I, q.length ≤ N → P[T]
        (endpointMixedProductOperator hT.le (K []) (Ω []) (w q) + F q +
          endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT.le (K r) (Ω r)) w q) = 0) ∧
      (∀ (i : I) (q : List I), q.length < N →
        endpointTorusHasSpatialDerivative (u i) (w q) (w (i :: q))) ∧
      (∀ q : List I, q.length ≤ N →
        ‖w q‖ ≤ ‖(S.symm : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T])‖ *
          (‖P[T] (F q)‖ + ‖P[T]‖ * ((endpointMixedCorrectionPairs q).map fun p =>
            2 * ‖endpointMixedPathCoefficient hT.le (K p.1) (Ω p.1)‖ * ‖w p.2‖).sum)) := by
  let B (q : List I) := endpointMixedPathCoefficient hT.le (K q) (Ω q)
  let f (q : List I) := -(P[T] (F q))
  have hBase : P[T] ((B []).coefficientMul v) = f [] := by
    rw [map_add] at hProjected
    change P[T] ((endpointMixedPathCoefficient hT.le (K []) (Ω [])).coefficientMul v) = f []
    rw [endpointMixedPathCoefficient_coefficientMul]
    exact eq_neg_of_add_eq_zero_left hProjected
  have hB (i : I) (q : List I) (hq : q.length < N) :
      endpointTorusHasSpatialDerivative (u i) (B q) (B (i :: q)) :=
    endpointMixedPathCoefficient_hasSpatialDerivative hT.le (u i) _ _ _ _ (hK i q hq) (hΩ i q hq)
  have hf (i : I) (q : List I) (hq : q.length < N) :
      endpointTorusHasSpatialDerivative (u i) (f q) (f (i :: q)) :=
    endpointStrongMixedLeray_neg_hasSpatialDerivative hT (u i) _ _ (hF i q hq)
  obtain ⟨w, hw, hFixed, hEq, hD, hBound⟩ :=
    endpointStrongMixedLeray_allSpatialDerivatives hT B f v u hv hBase S hS hμ hcoercive N hB hf
  refine ⟨w, hw, hFixed, ?_, hD, ?_⟩
  · intro q hq
    exact endpointProjectedMixedResidual_zero_of_spatialHierarchy hT.le K Ω w F q (hEq q hq)
  · intro q hq
    simpa only [f, B, norm_neg] using hBound q hq

end MixedSolveSpatialJets

section MixedJetRecovery

local notation "S" => endpointHalfHolderSolenoidal

local instance jetSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance jetSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem EndpointMixedRepresents.list_sum {I : Type*} {T : ℝ}
    (l : List I) (w : I → Mixed(T)) (g : I → ℝ → C½)
    (h : ∀ i ∈ l, EndpointMixedRepresents (w i) (g i)) :
    EndpointMixedRepresents (l.map w).sum (fun t => (l.map fun i => g i t).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using EndpointMixedRepresents.zero (T := T)
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (h i List.mem_cons_self).add (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem EndpointMixedRepresents.spatialCorrection {I : Type*} {T : ℝ}
    (Cmix : List I → MixedCoefficient(T)) (C : List I → ℝ → K½)
    (w : List I → Mixed(T)) (g : List I → ℝ → S) (q : List I)
    (hg : ∀ r : List I, r.length < q.length → EndpointMixedRepresents (w r) (fun t => (g r t).val))
    (hC : ∀ r : List I, r.length ≤ q.length → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun t => HalfHolder.eval a (Cmix r) v t) =ᵐ[μt T]
        fun t => HalfHolder.eval a (C r t) (v t)) :
    EndpointMixedRepresents (endpointMixedCorrection Cmix w q)
      (endpointTemporalSpatialCorrection
        (fun r t => (C r t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL) g q) := by
  apply EndpointMixedRepresents.list_sum
  intro p hp
  have hpair := endpointMixedCorrectionPairs_mem hp
  exact (hg p.2 hpair.2.2).coefficientMul (hC p.1 (by omega))

set_option maxHeartbeats 2400000 in
/-- The mixed projected equations of spatial derivative words recover
time-smooth representatives on the full slab, including zero displacement
at both endpoints. The recovered time jets retain the spatial derivative
relations, and lower spatial derivatives supply the commutator sources. -/
theorem exists_endpointSpatialJetTimeRecovery {I : Type*} {T μ L M : ℝ} (hT : 0 < T)
    {n : ℕ∞} {N : ℕ}
    (Kmix Ωmix : List I → MixedCoefficient(T)) (w Fmix : List I → Mixed(T)) (u : I → Vec3)
    (hDw : ∀ (i : I) (q : List I), q.length < N →
      endpointTorusHasSpatialDerivative (u i) (w q) (w (i :: q)))
    (K Ω : List I → ℝ → K½) (F : List I → ℝ → C½)
    (hK : ∀ q : List I, q.length ≤ N → ContDiffOn ℝ n (K q) (Icc 0 T))
    (hΩ : ∀ q : List I, q.length ≤ N → ContDiffOn ℝ n (Ω q) (Icc 0 T))
    (hF : ∀ q : List I, q.length ≤ N → ContDiffOn ℝ n (F q) (Icc 0 T))
    (hFmix : ∀ q : List I, q.length ≤ N → EndpointMixedRepresents (Fmix q) (F q))
    (hKmix : ∀ q : List I, q.length ≤ N → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun t => HalfHolder.eval a (Kmix q) v t) =ᵐ[μt T]
        fun t => HalfHolder.eval a (K q t) (v t))
    (hΩmix : ∀ q : List I, q.length ≤ N → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun t => HalfHolder.eval a (Ωmix q) v t) =ᵐ[μt T]
        fun t => HalfHolder.eval a (Ω q t) (v t))
    (hFixed : ∀ q : List I, q.length ≤ N → endpointStrongMixedLeray T (w q) = w q)
    (hProjected : ∀ q : List I, q.length ≤ N → endpointStrongMixedLeray T
      (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + Fmix q +
        endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT.le (Kmix r) (Ωmix r)) w q) = 0)
    (hμ : 0 < μ) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ Icc 0 T, ∀ a b,
      ‖HalfHolder.eval a (K [] t) - HalfHolder.eval b (K [] t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ Icc 0 T, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) v, v⟫_ℝ)
    (hM : ∀ t ∈ Icc 0 T, ‖(K [] t).val.1‖ ≤ M) :
    ∃ g : List I → ℝ → S,
      (∀ q : List I, q.length ≤ N →
        ContDiffOn ℝ n (g q) (Icc 0 T) ∧
        (∀ᵐ t ∂μt T, endpointHalfHolderToL2 (g q t).val =
          endpointSpatialSlice (endpointMixedToJoint T (w q)) t) ∧
        endpointPrimitive (g q) 0 = 0 ∧ endpointPrimitive (g q) T = 0) ∧
      ∀ (m : ℕ), (m : ℕ∞) ≤ n → ∀ t ∈ Icc 0 T, ∀ (i : I) (q : List I), q.length < N →
        endpointTorusHasSpatialDerivative (u i)
          (iteratedDerivWithin m (fun r => (g q r).val) (Icc 0 T) t)
          (iteratedDerivWithin m (fun r => (g (i :: q) r).val) (Icc 0 T) t) := by
  classical
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  let P := endpointStrongSpatialProjection
  let Kops (q : List I) (t : ℝ) : S →L[ℝ] C½ :=
    (K q t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL
  let Ωops (q : List I) (t : ℝ) : S →L[ℝ] C½ :=
    (Ω q t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL
  have hKops (q : List I) (hq : q.length ≤ N) : ContDiffOn ℝ n (Kops q) (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul (hK q hq)).clm_comp contDiffOn_const
  have hΩops (q : List I) (hq : q.length ≤ N) : ContDiffOn ℝ n (Ωops q) (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul (hΩ q hq)).clm_comp contDiffOn_const
  have hK0 := hK [] (Nat.zero_le N)
  obtain ⟨_, _, e, he, _, _⟩ := exists_endpointInstantaneousInverseFamily hμ hL hK0 hLip hPos hM
  have heC := contDiffOn_endpointCompressedCoefficient hK0 P he
  let Good (q : List I) (g : ℝ → S) : Prop :=
    ContDiffOn ℝ n g (Icc 0 T) ∧
      (∀ᵐ t ∂μt T, endpointHalfHolderToL2 (g t).val =
        endpointSpatialSlice (endpointMixedToJoint T (w q)) t) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0
  have hMain (m : ℕ) : ∀ q : List I, q.length = m → q.length ≤ N → ∃ g, Good q g := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro q hqm hq
      have hLower (l : List I) (hl : l.length < q.length) : ∃ g, Good l g :=
        ih l.length (by omega) l rfl (by omega)
      let g (l : List I) : ℝ → S :=
        if hl : l.length < q.length then Classical.choose (hLower l hl) else fun _ => 0
      have hg (l : List I) (hl : l.length < q.length) : Good l (g l) := by
        simpa only [g, dite_eq_left hl] using Classical.choose_spec (hLower l hl)
      have hgrep (l : List I) (hl : l.length < q.length) :
          EndpointMixedRepresents (w l) (fun t => (g l t).val) :=
        EndpointMixedRepresents.of_spatialSlice hT.le
          (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn
            (hg l hl).1.continuousOn) (hg l hl).2.1
      let corrK := endpointTemporalSpatialCorrection Kops g q
      let corrΩ := endpointTemporalSpatialCorrection Ωops g q
      have hkc : ContDiffOn ℝ n corrK (Icc 0 T) :=
        contDiffOn_endpointTemporalSpatialCorrection Kops g q
          (fun l hl => hKops l (hl.trans hq)) (fun l hl => (hg l hl).1)
      have hωc : ContDiffOn ℝ n corrΩ (Icc 0 T) :=
        contDiffOn_endpointTemporalSpatialCorrection Ωops g q
          (fun l hl => hΩops l (hl.trans hq)) (fun l hl => (hg l hl).1)
      have hKrep : EndpointMixedRepresents (endpointMixedCorrection Kmix w q) corrK :=
        EndpointMixedRepresents.spatialCorrection Kmix K w g q hgrep
          (fun l hl => hKmix l (hl.trans hq))
      have hΩrep : EndpointMixedRepresents (endpointMixedCorrection Ωmix w q) corrΩ :=
        EndpointMixedRepresents.spatialCorrection Ωmix Ω w g q hgrep
          (fun l hl => hΩmix l (hl.trans hq))
      let F₁ (t : ℝ) := F q t + corrK t - endpointPrimitive corrΩ t
      let Fmix₁ := Fmix q + endpointMixedCorrection Kmix w q -
        endpointMixedIntegration hT.le (endpointMixedCorrection Ωmix w q)
      have hΩPrimitive : ContDiffOn ℝ n (endpointPrimitive corrΩ) (Icc 0 T) := by
        refine contDiffOn_iff_forall_nat_le.mpr fun m hm => ?_
        exact (contDiffOn_endpointPrimitive_succ hT
          (contDiffOn_iff_forall_nat_le.mp hωc m hm)).of_le le_self_add
      have hF₁ : ContDiffOn ℝ n F₁ (Icc 0 T) :=
        ((hF q hq).add hkc).sub hΩPrimitive
      have hF₁rep : EndpointMixedRepresents Fmix₁ F₁ :=
        ((hFmix q hq).add hKrep).sub (hΩrep.integration hT.le hωc.continuousOn)
      have hProjected₁ : endpointStrongMixedLeray T
          (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + Fmix₁) = 0 := by
        have hProj := hProjected q hq
        rw [endpointMixedCorrection_pathCoefficient hT.le Kmix Ωmix w q] at hProj
        convert hProj using 2
        dsimp only [Fmix₁]
        abel
      obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hF₁.continuousOn
      obtain ⟨z, hzc, hzEq, hzRep, hz0, hzT, _⟩ := exists_endpointMixedTimeRecovery hT
        (Kmix []) (Ωmix []) (w q) Fmix₁ (K []) F₁ (hFixed q hq) hProjected₁
        hμ hL (contDiffOn_zero.mpr hK0.continuousOn) hLip hPos hM hF₁.continuousOn hM₁
        (ae_endpointMixedCoefficient_spatialSlice_of_pathAction (K []) (Kmix [])
          hK0.continuousOn (hKmix [] (Nat.zero_le N)) (w q))
        (hF₁rep.spatialSlice hT.le hF₁.continuousOn)
      let Jz := (Ωmix []).coefficientMul (w q)
      let residual := endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + Fmix₁
      let c := P (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) residual)
      have hΩzC : ContinuousOn (fun t => Ωops [] t (z t)) (Icc 0 T) :=
        (hΩops [] (Nat.zero_le N)).continuousOn.clm_apply hzc
      have hzPath : EndpointMixedRepresents (w q) (fun t => (z t).val) :=
        EndpointMixedRepresents.of_spatialSlice hT.le
          (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hzc) hzRep
      have hΩzPath : EndpointMixedRepresents Jz (fun t => Ωops [] t (z t)) :=
        hzPath.coefficientMul (hΩmix [] (Nat.zero_le N))
      have hzCn : ContDiffOn ℝ n z (Icc 0 T) := by
        refine contDiffOn_iff_forall_nat_le.mpr fun m hm => ?_
        apply contDiffOn_endpointVelocity_of_integrated hT P c
          (contDiffOn_iff_forall_nat_le.mp heC m hm)
          (contDiffOn_iff_forall_nat_le.mp (hΩops [] (Nat.zero_le N)) m hm)
          (contDiffOn_iff_forall_nat_le.mp hF₁ m hm) hzc
        intro t ht
        rw [he t ht, ← endpointMixedPrimitive_eq_endpointPrimitive Jz hΩzC hΩzPath ⟨t, ht⟩]
        exact hzEq ⟨t, ht⟩
      exact ⟨z, hzCn, hzRep, hz0, hzT⟩
  choose g hg using fun q (hq : q.length ≤ N) => hMain q.length q rfl hq
  let G (q : List I) (t : ℝ) := if hq : q.length ≤ N then g q hq t else 0
  have hG (q : List I) (hq : q.length ≤ N) : Good q (G q) := by
    simpa only [G, dite_eq_left hq] using hg q hq
  let V (q : List I) (t : ℝ) : C½ := (G q t).val
  have hV (q : List I) (hq : q.length ≤ N) : ContDiffOn ℝ n (V q) (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn (hG q hq).1
  have hSpatial := endpointRecoveredSpatialHierarchy hT w V u N hDw
    (fun q hq => (hV q hq).continuousOn) (fun q hq => (hG q hq).2.1)
  refine ⟨G, hG, ?_⟩
  intro m hm t ht i q hq
  exact endpointTorusHasSpatialDerivative_iteratedDerivWithin hT (u i)
    (contDiffOn_iff_forall_nat_le.mp (hV q hq.le) m hm)
    (contDiffOn_iff_forall_nat_le.mp (hV (i :: q) (Nat.succ_le_of_lt hq)) m hm)
    (fun r hr => hSpatial r hr i q hq) m le_rfl t ht

end MixedJetRecovery

end

end TorusEuler

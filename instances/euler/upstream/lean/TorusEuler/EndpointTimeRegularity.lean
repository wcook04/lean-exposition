import TorusEuler.EndpointCoefficientCompatibility
import TorusEuler.EndpointMeanFubini
import TorusEuler.EndpointPressureRecovery
import TorusEuler.EndpointRecoverTime
import TorusEuler.EndpointWeakInstantaneous
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The temporal regularity step of Appendix A.2, on the closed time slab. -/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TorusEuler

noncomputable section

section Temporal

variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- A continuous Banach-valued integrand is the derivative of its primitive on
the whole closed slab. At the endpoints this is the derivative within the slab. -/
theorem hasDerivWithinAt_endpointPrimitive_of_continuousOn {T t : ℝ} {f : ℝ → B}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (endpointPrimitive f) (f t) (Icc 0 T) t := by
  let _ : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hInt := (hf.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1
  exact intervalIntegral.integral_hasDerivWithinAt_right hInt
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- Taking the primitive gains one derivative in the Banach norm on a positive
closed interval. -/
theorem contDiffOn_endpointPrimitive_succ {T : ℝ} (hT : 0 < T) {n : ℕ} {f : ℝ → B}
    (hf : ContDiffOn ℝ n f (Icc 0 T)) :
    ContDiffOn ℝ ((n : ℕ∞ω) + 1) (endpointPrimitive f) (Icc 0 T) := by
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (endpointPrimitive f) (f t) (Icc 0 T) t :=
    hasDerivWithinAt_endpointPrimitive_of_continuousOn hf.continuousOn ht
  apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)).mpr
  refine ⟨fun t ht => (hderiv t ht).differentiableWithinAt, by simp, ?_⟩
  exact hf.congr (fun t ht => (hderiv t ht).derivWithin (uniqueDiffOn_Icc hT t ht))

/-- The operator-norm smoothness of the fixed-time isomorphism passes to its
inverse, even when the family is given only on a closed interval. -/
theorem contDiffOn_endpointFixedInverse {I : Set ℝ} {n : ℕ∞ω} {S : ℝ → X ≃L[ℝ] X}
    (hS : ContDiffOn ℝ n (fun t => (S t : X →L[ℝ] X)) I) :
    ContDiffOn ℝ n (fun t => ((S t).symm : X →L[ℝ] X)) I := by
  have h (t : ℝ) : Ring.inverse ((S t : X →L[ℝ] X)) = ((S t).symm : X →L[ℝ] X) :=
    Ring.inverse_unit (S t).toUnit
  intro t ht
  have hInv : ContDiffAt ℝ n (Ring.inverse : (X →L[ℝ] X) → (X →L[ℝ] X))
      (S t : X →L[ℝ] X) := contDiffAt_ringInverse ℝ (S t).toUnit
  have hComp : ContDiffWithinAt ℝ n (fun r => Ring.inverse (S r : X →L[ℝ] X)) I t :=
    ContDiffAt.comp_contDiffWithinAt (g := Ring.inverse) (f := fun r => (S r : X →L[ℝ] X))
      t hInv (hS t ht)
  exact hComp.congr_of_mem (fun r _ => (h r).symm) ht

/-- In the integrated instantaneous equation of Appendix A, the time primitive of
the velocity term supplies one more derivative. The coefficient of that term only
needs the previous order of time regularity. -/
theorem contDiffOn_endpointVelocity_succ {T : ℝ} (hT : 0 < T) {n : ℕ}
    {S : ℝ → X ≃L[ℝ] X} (P : B →L[ℝ] X) (c : X)
    {Ω : ℝ → X →L[ℝ] B} {v : ℝ → X} {L : ℝ → B}
    (hS : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (fun t => (S t : X →L[ℝ] X)) (Icc 0 T))
    (hΩ : ContDiffOn ℝ n Ω (Icc 0 T))
    (hL : ContDiffOn ℝ ((n : ℕ∞ω) + 1) L (Icc 0 T))
    (hv : ContDiffOn ℝ n v (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, S t (v t) =
      c + P (endpointPrimitive (fun r => Ω r (v r)) t) - P (L t)) :
    ContDiffOn ℝ ((n : ℕ∞ω) + 1) v (Icc 0 T) := by
  let F (t : ℝ) := c + P (endpointPrimitive (fun r => Ω r (v r)) t) - P (L t)
  have hJ := contDiffOn_endpointPrimitive_succ hT (hΩ.clm_apply hv)
  have hF : ContDiffOn ℝ ((n : ℕ∞ω) + 1) F (Icc 0 T) :=
    (contDiffOn_const.add (P.contDiff.comp_contDiffOn hJ)).sub (P.contDiff.comp_contDiffOn hL)
  refine ((contDiffOn_endpointFixedInverse hS).clm_apply hF).congr ?_
  intro t ht
  change v t = (S t).symm (F t)
  have hFt : S t (v t) = F t := hEq t ht
  rw [← hFt, ContinuousLinearEquiv.symm_apply_apply]

/-- All finite time orders of the recovered velocity follow from the corresponding
orders of its fixed-time coefficient and forcing on the same closed interval. -/
theorem contDiffOn_endpointVelocity_of_integrated {T : ℝ} (hT : 0 < T) {n : ℕ}
    {S : ℝ → X ≃L[ℝ] X} (P : B →L[ℝ] X) (c : X)
    {Ω : ℝ → X →L[ℝ] B} {v : ℝ → X} {L : ℝ → B}
    (hS : ContDiffOn ℝ n (fun t => (S t : X →L[ℝ] X)) (Icc 0 T))
    (hΩ : ContDiffOn ℝ n Ω (Icc 0 T)) (hL : ContDiffOn ℝ n L (Icc 0 T))
    (hv : ContinuousOn v (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, S t (v t) =
      c + P (endpointPrimitive (fun r => Ω r (v r)) t) - P (L t)) :
    ContDiffOn ℝ n v (Icc 0 T) := by
  induction n with
  | zero => exact contDiffOn_zero.mpr hv
  | succ n ih =>
    have hn : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    have hvn := ih (hS.of_le hn) (hΩ.of_le hn) (hL.of_le hn)
    rw [Nat.cast_succ] at hS hL ⊢
    exact contDiffOn_endpointVelocity_succ hT P c hS (hΩ.of_le hn) hL hvn hEq

/-- Smooth time-dependence of the supplied coefficients gives smooth velocity and
displacement in the spatial Banach norm, including at both ends of the slab. -/
theorem contDiffOn_endpointVelocity_and_displacement_of_integrated {T : ℝ} (hT : 0 < T)
    {S : ℝ → X ≃L[ℝ] X} (P : B →L[ℝ] X) (c : X)
    {Ω : ℝ → X →L[ℝ] B} {v : ℝ → X} {L : ℝ → B}
    (hS : ContDiffOn ℝ ∞ (fun t => (S t : X →L[ℝ] X)) (Icc 0 T))
    (hΩ : ContDiffOn ℝ ∞ Ω (Icc 0 T)) (hL : ContDiffOn ℝ ∞ L (Icc 0 T))
    (hv : ContinuousOn v (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, S t (v t) =
      c + P (endpointPrimitive (fun r => Ω r (v r)) t) - P (L t)) :
    ContDiffOn ℝ ∞ v (Icc 0 T) ∧ ContDiffOn ℝ ∞ (endpointPrimitive v) (Icc 0 T) := by
  have hV : ∀ n : ℕ, ContDiffOn ℝ n v (Icc 0 T) := fun n =>
    contDiffOn_endpointVelocity_of_integrated hT P c
      (contDiffOn_infty.mp hS n) (contDiffOn_infty.mp hΩ n) (contDiffOn_infty.mp hL n) hv hEq
  refine ⟨contDiffOn_infty.mpr hV, contDiffOn_infty.mpr fun n => ?_⟩
  exact (contDiffOn_endpointPrimitive_succ hT (hV n)).of_le le_self_add

omit [CompleteSpace X] in
/-- Differentiating the instantaneous equation yields the explicit time derivative,
with the sign of the inverse-coefficient contribution fixed by (S(t)v(t)). -/
theorem hasDerivWithinAt_endpointVelocity_of_integrated {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) {S : ℝ → X ≃L[ℝ] X} (P : B →L[ℝ] X) (c : X)
    {Ω : ℝ → X →L[ℝ] B} {v : ℝ → X} {L : ℝ → B} {dS : X →L[ℝ] X} {dL : B}
    (hS : HasDerivWithinAt (fun r => (S r : X →L[ℝ] X)) dS (Icc 0 T) t)
    (hL : HasDerivWithinAt L dL (Icc 0 T) t)
    (hΩ : ContinuousOn Ω (Icc 0 T)) (hvc : ContinuousOn v (Icc 0 T))
    (hv : DifferentiableWithinAt ℝ v (Icc 0 T) t)
    (hEq : ∀ r ∈ Icc 0 T, S r (v r) =
      c + P (endpointPrimitive (fun s => Ω s (v s)) r) - P (L r)) :
    HasDerivWithinAt v ((S t).symm (P (Ω t (v t)) - P dL - dS (v t))) (Icc 0 T) t := by
  let dv := derivWithin v (Icc 0 T) t
  have hV : HasDerivWithinAt v dv (Icc 0 T) t := hv.hasDerivWithinAt
  have hJ := hasDerivWithinAt_endpointPrimitive_of_continuousOn (hΩ.clm_apply hvc) ht
  have hRHS :
      HasDerivWithinAt (fun r => c + P (endpointPrimitive (fun s => Ω s (v s)) r) - P (L r))
        (P (Ω t (v t)) - P dL) (Icc 0 T) t :=
    ((P.hasFDerivAt.comp_hasDerivWithinAt t hJ).const_add c).sub
      (P.hasFDerivAt.comp_hasDerivWithinAt t hL)
  have hLeft := hRHS.congr hEq (hEq t ht)
  have hd := hS.clm_apply hV
  have hu := uniqueDiffOn_Icc hT t ht
  have heq : dS (v t) + S t dv = P (Ω t (v t)) - P dL :=
    (hd.derivWithin hu).symm.trans (hLeft.derivWithin hu)
  have hsolve : dv = (S t).symm (P (Ω t (v t)) - P dL - dS (v t)) := by
    apply (S t).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ← heq]
    abel
  rwa [← hsolve]

end Temporal

section CoefficientMultiplication

variable {A E F : Type*} [MetricSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise multiplication is a bounded linear map in the half-Hölder coefficient. -/
noncomputable def HalfHolder.coefficientMulL :
    HalfHolder A (E →L[ℝ] F) →L[ℝ] (HalfHolder A E →L[ℝ] HalfHolder A F) := by
  let L : HalfHolder A (E →L[ℝ] F) →ₗ[ℝ] (HalfHolder A E →L[ℝ] HalfHolder A F) :=
    { toFun := HalfHolder.coefficientMul
      map_add' := fun K J => ContinuousLinearMap.ext fun v =>
        HalfHolder.ext fun a => by
          simp only [_root_.add_apply, map_add, HalfHolder.eval_coefficientMul]
      map_smul' := fun c K => ContinuousLinearMap.ext fun v =>
        HalfHolder.ext fun a => by
          simp only [_root_.smul_apply, map_smul, RingHom.id_apply, HalfHolder.eval_coefficientMul] }
  have hL (K : HalfHolder A (E →L[ℝ] F)) : ‖L K‖ ≤ 2 * ‖K‖ :=
    HalfHolder.norm_coefficientMul_le K
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := HalfHolder A (E →L[ℝ] F))
    (F := HalfHolder A E →L[ℝ] HalfHolder A F) (σ := RingHom.id ℝ) L 2 hL

@[simp] theorem HalfHolder.coefficientMulL_apply (K : HalfHolder A (E →L[ℝ] F)) :
    HalfHolder.coefficientMulL K = K.coefficientMul := rfl

/-- Time regularity in the spatial half-Hölder norm passes to the induced
operator family in its operator norm. -/
theorem HalfHolder.contDiffOn_coefficientMul {n : ℕ∞ω} {I : Set ℝ}
    {K : ℝ → HalfHolder A (E →L[ℝ] F)} (hK : ContDiffOn ℝ n K I) :
    ContDiffOn ℝ n (fun t => (K t).coefficientMul) I := by
  let L : HalfHolder A (E →L[ℝ] F) →L[ℝ] (HalfHolder A E →L[ℝ] HalfHolder A F) :=
    HalfHolder.coefficientMulL
  have hL : ContDiff ℝ n L :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (E := HalfHolder A (E →L[ℝ] F))
      (F := HalfHolder A E →L[ℝ] HalfHolder A F) L
  exact hL.comp_contDiffOn hK

end CoefficientMultiplication

section MixedRepresentative

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "Xs" => endpointHalfHolderSolenoidal

local instance endpointTimeHolderNormedGroup : NormedAddCommGroup C½ := inferInstance
local instance endpointTimeSolenoidalNormedGroup : NormedAddCommGroup Xs := inferInstance
local instance endpointTimeHolderNormedSpace : NormedSpace ℝ C½ := inferInstance
local instance endpointTimeSolenoidalNormedSpace : NormedSpace ℝ Xs := inferInstance

/-- An almost-everywhere equality of spatial representatives of a continuous path
can also be read on almost every fixed-label time slice. -/
theorem ae_endpointTimeSlice_of_continuous_spatialSlice {T : ℝ} (hT : 0 ≤ T)
    (v : EndpointTorusL2 T) {f : ℝ → C½} (hf : ContinuousOn f (Icc 0 T))
    (hae : ∀ᵐ t ∂timeMeasure T, endpointHalfHolderToL2 (f t) = endpointSpatialSlice v t) :
    ∀ᵐ a ∂unitTorusMeasure,
      (fun t => HalfHolder.eval a (f t)) =ᵐ[timeMeasure T] fun t => v (t, a) := by
  let τ (t : ℝ) := min (max t 0) T
  have hτ : Continuous τ := (continuous_id.max continuous_const).min continuous_const
  have hτmem (t : ℝ) : τ t ∈ Icc 0 T :=
    ⟨le_min (le_max_right t 0) hT, min_le_right _ _⟩
  have hτeq (t : ℝ) (ht : t ∈ Icc 0 T) : τ t = t := by
    dsimp [τ]
    rw [max_eq_left ht.1, min_eq_left ht.2]
  let F (q : ℝ × A) := HalfHolder.eval q.2 (f (τ q.1))
  have hF : Continuous F := by
    have hc : Continuous (fun t => f (τ t)) := hf.comp_continuous hτ hτmem
    have hfst : Continuous (fun q : ℝ × A => (f (τ q.1)).val.1) :=
      continuous_fst.comp (continuous_subtype_val.comp (hc.comp continuous_fst))
    exact continuous_eval.comp (hfst.prodMk continuous_snd)
  have hMeas : MeasurableSet {q : ℝ × A | F q = v q} :=
    measurableSet_eq_fun hF.measurable (Lp.stronglyMeasurable v).measurable
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
    (ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))).mono
      fun _ ht => Ioc_subset_Icc_self ht
  have hjoint : F =ᵐ[(timeMeasure T).prod unitTorusMeasure] v := by
    apply (Measure.ae_prod_iff_ae_ae hMeas).mpr
    filter_upwards [hae, endpointSpatialSlice_apply_ae v, htime] with t ht hslice hmem
    have heval := endpointHalfHolderToL2_apply_ae (f t)
    rw [ht] at heval
    filter_upwards [heval, hslice] with a h₁ h₂
    change HalfHolder.eval a (f (τ t)) = v (t, a)
    rw [hτeq t hmem]
    exact h₁.symm.trans h₂
  filter_upwards [ae_endpointTimeSlice_congr hjoint] with a ha
  filter_upwards [ha, htime] with t ht hmem
  change F (t, a) = v (t, a) at ht
  simpa only [F, hτeq t hmem] using ht

/-- The primitive of the mixed half-Hölder field coincides in the spatial Banach
space with the primitive of any continuous, almost-everywhere matching time field. -/
theorem endpointMixedPrimitive_eq_endpointPrimitive {T : ℝ}
    (w : HalfHolder A (Lp Vec3 2 (timeMeasure T))) {f : ℝ → C½}
    (hf : ContinuousOn f (Icc 0 T))
    (hw : ∀ᵐ a ∂unitTorusMeasure,
      (fun r => HalfHolder.eval a w r) =ᵐ[timeMeasure T] fun r => HalfHolder.eval a (f r))
    (t : Icc (0 : ℝ) T) :
    HalfHolder.map (endpointPrimitiveEvaluation t) w = endpointPrimitive f t := by
  apply endpointHalfHolderToL2_injective
  apply Lp.ext
  have hInt := (hf.mono (Icc_subset_Icc_right t.property.2)).intervalIntegrable_of_Icc
    (μ := volume) t.property.1
  filter_upwards [endpointHalfHolderToL2_apply_ae (HalfHolder.map (endpointPrimitiveEvaluation t) w),
    endpointHalfHolderToL2_apply_ae (endpointPrimitive f t), hw] with a ha hb hw'
  rw [ha, hb, HalfHolder.eval_map, endpointPrimitiveEvaluation_apply,
    endpointPrimitive_congr_ae hw' t.property]
  exact (HalfHolder.eval a).intervalIntegral_comp_comm hInt

/-- A family of fixed-time compressed kinetic maps inherits the time regularity
of its half-Hölder multiplier coefficient. -/
theorem contDiffOn_endpointCompressedCoefficient {I : Set ℝ} {n : ℕ∞ω}
    {K : ℝ → K½} (hK : ContDiffOn ℝ n K I)
    (P : C½ →L[ℝ] Xs) {S : ℝ → Xs ≃L[ℝ] Xs}
    (hS : ∀ t ∈ I, ∀ y : Xs, S t y = P ((K t).coefficientMul (y : C½))) :
    ContDiffOn ℝ n (fun t => (S t : Xs →L[ℝ] Xs)) I := by
  have hmul := HalfHolder.contDiffOn_coefficientMul hK
  have hres : ContDiffOn ℝ n (fun t =>
      (K t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL) I :=
    hmul.clm_comp contDiffOn_const
  have hcomp : ContDiffOn ℝ n (fun t =>
      P.comp ((K t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL)) I :=
    contDiffOn_const.clm_comp hres
  refine hcomp.congr fun t ht => ContinuousLinearMap.ext fun y => ?_
  exact hS t ht y

/-- A product `L²` multiplier preserves agreement between the weak time slices
and the strong half-Hölder velocity. -/
theorem ae_endpointSpatialSlice_coefficientMul_of_rep {T : ℝ}
    (Ω : ℝ → K½) (Ωjoint : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hω : AEStronglyMeasurable Ωjoint (endpointTorusMeasure T)) {Cω : ℝ}
    (bω : ∀ᵐ q ∂endpointTorusMeasure T, ‖Ωjoint q‖ ≤ Cω)
    (hcoef : ∀ᵐ q ∂endpointTorusMeasure T, Ωjoint q = HalfHolder.eval q.2 (Ω q.1))
    (v : EndpointTorusL2 T) {g : ℝ → Xs}
    (hg : ∀ᵐ t ∂timeMeasure T, endpointHalfHolderToL2 (g t : C½) = endpointSpatialSlice v t) :
    ∀ᵐ t ∂timeMeasure T, endpointHalfHolderToL2 ((Ω t).coefficientMul (g t : C½)) =
      endpointSpatialSlice (endpointL2Multiplier Ωjoint hω bω v) t := by
  filter_upwards [hg, ae_endpointSpatialSlice_l2Multiplier Ωjoint hω bω v,
    Measure.ae_ae_of_ae_prod hcoef] with t ht hslice hωt
  obtain ⟨hωmeas, hωbound, hslice⟩ := hslice
  rw [endpointHalfHolderToL2_coefficientMul, ht, hslice]
  apply Lp.ext
  filter_upwards [endpointWeakCoefficient_apply_ae (Ω t) (endpointSpatialSlice v t),
    endpointL2Multiplier_apply_ae (fun a => Ωjoint (t, a)) hωmeas hωbound (endpointSpatialSlice v t),
    hωt] with a ha hb h
  exact ha.trans ((congrArg (fun F : Vec3 →L[ℝ] Vec3 => F (endpointSpatialSlice v t a))
    h.symm).trans hb.symm)

/-- The mixed-space instantaneous equation gives the full closed-interval
time regularity in the spatial half-Hölder norm. The two representatives of
the multiplier term are identified through their common product field. -/
theorem contDiffOn_endpointTorusVelocity_of_mixed_integrated {T : ℝ} (hT : 0 < T) {n : ℕ}
    (P : C½ →L[ℝ] Xs) (c : Xs) {S : ℝ → Xs ≃L[ℝ] Xs}
    {K Ω : ℝ → K½} {L : ℝ → C½} {g : ℝ → Xs}
    (hK : ContDiffOn ℝ n K (Icc 0 T)) (hΩ : ContDiffOn ℝ n Ω (Icc 0 T))
    (hL : ContDiffOn ℝ n L (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hS : ∀ t ∈ Icc 0 T, ∀ y : Xs, S t y = P ((K t).coefficientMul (y : C½)))
    (w : HalfHolder A (Lp Vec3 2 (timeMeasure T))) (joint : EndpointTorusL2 T)
    (hw : ∀ᵐ a ∂unitTorusMeasure,
      (fun r => HalfHolder.eval a w r) =ᵐ[timeMeasure T] fun r => joint (r, a))
    (hjoint : ∀ᵐ t ∂timeMeasure T, endpointHalfHolderToL2 ((Ω t).coefficientMul (g t : C½)) =
      endpointSpatialSlice joint t)
    (hEq : ∀ t : Icc (0 : ℝ) T, S t (g t) =
      c + P (HalfHolder.map (endpointPrimitiveEvaluation t) w) - P (L t)) :
    ContDiffOn ℝ n g (Icc 0 T) := by
  let : CompleteSpace Xs := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  let Ωs (t : ℝ) : Xs →L[ℝ] C½ :=
    (Ω t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL
  have hΩs : ContDiffOn ℝ n Ωs (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul hΩ).clm_comp contDiffOn_const
  have hf : ContinuousOn (fun r => Ωs r (g r)) (Icc 0 T) :=
    hΩs.continuousOn.clm_apply hg
  have hpath := ae_endpointTimeSlice_of_continuous_spatialSlice hT.le joint hf hjoint
  have hmatch : ∀ᵐ a ∂unitTorusMeasure,
      (fun r => HalfHolder.eval a w r) =ᵐ[timeMeasure T] fun r => HalfHolder.eval a (Ωs r (g r)) := by
    filter_upwards [hw, hpath] with a ha hb
    exact ha.trans hb.symm
  refine contDiffOn_endpointVelocity_of_integrated hT P c
    (contDiffOn_endpointCompressedCoefficient hK P hS) hΩs hL hg ?_
  intro t ht
  rw [← endpointMixedPrimitive_eq_endpointPrimitive w hf hmatch ⟨t, ht⟩]
  exact hEq ⟨t, ht⟩

/-- The continuous representative of a half-Hölder field depends boundedly and
linearly on the field. -/
def endpointHalfHolderToContinuous : C½ →L[ℝ] C(A, Vec3) := by
  let L := BoundedContinuousFunction.toContinuousMapLinearMap (α := A) (β := Vec3) (𝕜 := ℝ)
  let E : BoundedContinuousFunction A Vec3 →L[ℝ] C(A, Vec3) :=
    L.mkContinuous 1 (fun f => by
      change ‖f.toContinuousMap‖ ≤ 1 * ‖f‖
      rw [BoundedContinuousFunction.norm_toContinuousMap_eq, one_mul])
  exact E.comp ((ContinuousLinearMap.fst ℝ (BoundedContinuousFunction A Vec3)
    (BoundedContinuousFunction (DistinctPairs A) Vec3)).comp (halfHolderSubspace A Vec3).toSubmodule.subtypeL)

@[simp]
theorem endpointHalfHolderToContinuous_apply (f : C½) (a : A) :
    endpointHalfHolderToContinuous f a = HalfHolder.eval a f := rfl

theorem endpointHalfHolderToContinuous_toLp (f : C½) :
    (endpointHalfHolderToContinuous f).toLp 2 unitTorusMeasure ℝ = endpointHalfHolderToL2 f := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure
    (endpointHalfHolderToContinuous f), endpointHalfHolderToL2_apply_ae f] with a ha hb
  exact ha.trans ((endpointHalfHolderToContinuous_apply f a).trans hb.symm)

/-- The integrated pressure residual has the same time regularity as the
coefficients and recovered velocity. It remains in the spatial nullspace
at every time, so it is an input to differentiated pressure recovery. -/
theorem contDiffOn_endpointIntegratedPressureResidual {T : ℝ} (hT : 0 < T) {n : ℕ}
    (P : C½ →L[ℝ] Xs) (c : Xs)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    {K Ω : ℝ → K½} {L : ℝ → C½} {g : ℝ → Xs}
    (hK : ContDiffOn ℝ n K (Icc 0 T)) (hΩ : ContDiffOn ℝ n Ω (Icc 0 T))
    (hL : ContDiffOn ℝ n L (Icc 0 T)) (hg : ContDiffOn ℝ n g (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, P ((K t).coefficientMul (g t : C½)) =
      c + P (endpointPrimitive (fun r => (Ω r).coefficientMul (g r : C½)) t) - P (L t)) :
    let G (t : ℝ) := endpointHalfHolderToContinuous
      ((K t).coefficientMul (g t : C½) -
        endpointPrimitive (fun r => (Ω r).coefficientMul (g r : C½)) t + L t - (c : C½))
    ContDiffOn ℝ n G (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, endpointWeakSpatialProjection ((G t).toLp 2 unitTorusMeasure ℝ) = 0 := by
  intro G
  let F (t : ℝ) := (K t).coefficientMul (g t : C½) -
    endpointPrimitive (fun r => (Ω r).coefficientMul (g r : C½)) t + L t
  have hg' : ContDiffOn ℝ n (fun r => (g r : C½)) (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn hg
  have hKvg := (HalfHolder.contDiffOn_coefficientMul hK).clm_apply hg'
  have hJ := contDiffOn_endpointPrimitive_succ hT ((HalfHolder.contDiffOn_coefficientMul hΩ).clm_apply hg')
  have hF : ContDiffOn ℝ n F (Icc 0 T) := (hKvg.sub (hJ.of_le le_self_add)).add hL
  refine ⟨endpointHalfHolderToContinuous.contDiff.comp_contDiffOn (hF.sub contDiffOn_const), ?_⟩
  intro t ht
  have hf : P (F t) = c := by
    dsimp only [F]
    rw [map_add, map_sub, hEq t ht]
    abel
  change endpointWeakSpatialProjection ((endpointHalfHolderToContinuous
    (F t - (c : C½))).toLp 2 unitTorusMeasure ℝ) = 0
  rw [endpointHalfHolderToContinuous_toLp]
  exact endpointProjection_residual_eq_zero (F t) c ((hP _).trans (congrArg endpointSolenoidalEmbedding hf))

end MixedRepresentative

end

end TorusEuler

import TorusEuler.EndpointCoefficientCompatibility
import TorusEuler.EndpointMixedEmbedding

/-! Mixed coefficient multiplication and time integration in Appendix A.2. -/

open Filter MeasureTheory Set
open scoped Topology

namespace TorusEuler

local notation "A" => UnitAddTorus (Fin 3)
local notation "ν" => unitTorusMeasure
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Vt(" T ")" => Lp Vec3 2 (μt T)
local notation "W(" T ")" => HalfHolder A (Vt(T))
local notation "HOp(" T ")" => Vt(T) →L[ℝ] Vt(T)

section Coefficient

variable {T : ℝ} (K : ℝ × A → Vec3 →L[ℝ] Vec3)
  (hK : ∀ a, AEStronglyMeasurable (fun t => K (t, a)) (μt T))
  {M : ℝ}
  (hKsup : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖K (t, a)‖ ≤ M)
  (hKdif : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖K (t, a) - K (t, b)‖ ≤ M * Real.sqrt (dist a b))

include hKsup in
private theorem endpointTimeCoefficient_ae_bound (a : A) :
    ∀ᵐ t ∂μt T, ‖K (t, a)‖ ≤ M :=
  (ae_restrict_mem measurableSet_Ioc).mono fun t ht => hKsup t (Ioc_subset_Icc_self ht) a

private noncomputable def endpointTimeCoefficient (a : A) : HOp(T) :=
  endpointL2Multiplier (fun t => K (t, a)) (hK a) (endpointTimeCoefficient_ae_bound K hKsup a)

private theorem endpointTimeCoefficient_apply_ae (a : A) (f : Vt(T)) :
    (fun t => endpointTimeCoefficient K hK hKsup a f t) =ᵐ[μt T] fun t => K (t, a) (f t) :=
  endpointL2Multiplier_apply_ae (fun t => K (t, a)) (hK a)
    (endpointTimeCoefficient_ae_bound K hKsup a) f

private theorem endpointTimeCoefficient_norm_le (hM : 0 ≤ M) (a : A) :
    ‖endpointTimeCoefficient K hK hKsup a‖ ≤ M :=
  norm_endpointL2Multiplier_le _ (hK a) (endpointTimeCoefficient_ae_bound K hKsup a) hM

include hKdif in
private theorem endpointTimeCoefficient_norm_sub_le (hM : 0 ≤ M) (a b : A) :
    ‖endpointTimeCoefficient K hK hKsup a - endpointTimeCoefficient K hK hKsup b‖ ≤
      M * Real.sqrt (dist a b) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (Real.sqrt_nonneg _))
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [endpointTimeCoefficient_apply_ae K hK hKsup a f,
    endpointTimeCoefficient_apply_ae K hK hKsup b f, ae_restrict_mem (μ := volume) measurableSet_Ioc,
    Lp.coeFn_sub (endpointTimeCoefficient K hK hKsup a f) (endpointTimeCoefficient K hK hKsup b f)]
    with t hat hbt ht hsub
  rw [_root_.sub_apply, hsub, Pi.sub_apply, hat, hbt, ← _root_.sub_apply]
  exact ((K (t, a) - K (t, b)).le_opNorm _).trans <|
    mul_le_mul_of_nonneg_right (hKdif t (Ioc_subset_Icc_self ht) a b) (norm_nonneg _)

include hKdif in
private theorem continuous_endpointTimeCoefficient (hM : 0 ≤ M) :
    Continuous (endpointTimeCoefficient K hK hKsup) := by
  refine continuous_iff_continuousAt.mpr fun a => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun b => endpointTimeCoefficient_norm_sub_le K hK hKsup hKdif hM b a) ?_
  have hc : Continuous (fun b : A => M * Real.sqrt (dist b a)) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.dist continuous_const))
  simpa only [dist_self, Real.sqrt_zero, mul_zero] using hc.continuousAt (x := a).tendsto

/-- An operator bounded uniformly on the closed time slab with a uniform spatial
half-Hölder estimate defines a spatial half-Hölder field of temporal (L^2) operators. -/
noncomputable def endpointMixedCoefficient (hM : 0 ≤ M) : HalfHolder A (HOp(T)) :=
  HalfHolder.ofBound
    ⟨endpointTimeCoefficient K hK hKsup, continuous_endpointTimeCoefficient K hK hKsup hKdif hM⟩
    (endpointTimeCoefficient_norm_le K hK hKsup hM)
    (endpointTimeCoefficient_norm_sub_le K hK hKsup hKdif hM)

theorem endpointMixedCoefficient_apply_ae (hM : 0 ≤ M) (a : A) (f : Vt(T)) :
    (fun t => HalfHolder.eval a (endpointMixedCoefficient K hK hKsup hKdif hM) f t) =ᵐ[μt T]
      fun t => K (t, a) (f t) :=
  endpointTimeCoefficient_apply_ae K hK hKsup a f

theorem norm_endpointMixedCoefficient_le (hM : 0 ≤ M) :
    ‖endpointMixedCoefficient K hK hKsup hKdif hM‖ ≤ M := by
  apply (HalfHolder.norm_le_iff hM).mpr
  exact ⟨endpointTimeCoefficient_norm_le K hK hKsup hM,
    endpointTimeCoefficient_norm_sub_le K hK hKsup hKdif hM⟩

include hKsup in
theorem endpointJointCoefficient_ae_bound :
    ∀ᵐ q ∂endpointTorusMeasure T, ‖K q‖ ≤ M := by
  have hf : Measure.QuasiMeasurePreserving (Prod.fst : ℝ × A → ℝ)
      (endpointTorusMeasure T) (μt T) :=
    Measure.quasiMeasurePreserving_fst
  exact (hf.ae (ae_restrict_mem measurableSet_Ioc)).mono fun q hq =>
    hKsup q.1 (Ioc_subset_Icc_self hq) q.2

/-- Multiplication by the labelwise (L^2) coefficient commutes with the
mixed-to-joint embedding. The same result applies to (K) and (Omega). -/
theorem endpointMixedToJoint_coefficientMul (hM : 0 ≤ M)
    (hKjoint : AEStronglyMeasurable K (endpointTorusMeasure T)) (w : W(T)) :
    endpointMixedToJoint T ((endpointMixedCoefficient K hK hKsup hKdif hM).coefficientMul w) =
      endpointL2Multiplier K hKjoint (endpointJointCoefficient_ae_bound K hKsup)
        (endpointMixedToJoint T w) := by
  let Kmix := endpointMixedCoefficient K hK hKsup hKdif hM
  have hKa : ∀ᵐ a ∂ν, ∀ f : Vt(T), (fun t => HalfHolder.eval a Kmix f t) =ᵐ[μt T]
      fun t => K (t, a) (f t) :=
    ae_of_all _ (endpointMixedCoefficient_apply_ae K hK hKsup hKdif hM)
  have hrep := endpointMixedCoefficientMul_represents Kmix K hKjoint
    (endpointJointCoefficient_ae_bound K hKsup) hKa w (endpointMixedToJoint T w)
    (endpointMixedToJoint_apply_ae w)
  apply endpointJoint_eq_of_slices
  filter_upwards [endpointMixedToJoint_apply_ae (Kmix.coefficientMul w), hrep] with a ha hb
  exact ha.symm.trans hb

end Coefficient

/-- A uniform spatial Lipschitz bound implies the half-Hölder bound on the same
slab once the spatial diameter is bounded by (R^2). -/
theorem endpointCoefficient_halfHolder_of_lipschitz {T M R : ℝ}
    (K : ℝ × A → Vec3 →L[ℝ] Vec3) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hdiam : ∀ a b : A, dist a b ≤ R ^ 2)
    (hK : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b : A, ‖K (t, a) - K (t, b)‖ ≤ M * dist a b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a b : A) :
    ‖K (t, a) - K (t, b)‖ ≤ (M * R) * Real.sqrt (dist a b) := by
  have hroot := (Real.sqrt_le_sqrt (hdiam a b)).trans_eq (Real.sqrt_sq_eq_abs R)
  rw [abs_of_nonneg hR] at hroot
  calc
    ‖K (t, a) - K (t, b)‖ ≤ M * dist a b := hK t ht a b
    _ = M * (Real.sqrt (dist a b) * Real.sqrt (dist a b)) := by
      rw [← pow_two, Real.sq_sqrt dist_nonneg]
    _ ≤ M * (R * Real.sqrt (dist a b)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)) hM
    _ = _ := by ring

/-- The mixed-space path integration operator applies the temporal (L^2)
primitive at each label. -/
noncomputable def endpointMixedIntegration {T : ℝ} (hT : 0 ≤ T) : W(T) →L[ℝ] W(T) :=
  HalfHolder.map (endpointPrimitiveLp hT)

theorem norm_endpointMixedIntegration_le {T : ℝ} (hT : 0 ≤ T) :
    ‖endpointMixedIntegration hT‖ ≤ T :=
  (HalfHolder.norm_map_le (X := A) (endpointPrimitiveLp (E := Vec3) hT)).trans
    (norm_endpointPrimitiveLp_le (E := Vec3) hT)

/-- Applying the mixed integration operator and embedding gives exactly the
joint (L^2) primitive. -/
theorem endpointMixedToJoint_integration {T : ℝ} (hT : 0 ≤ T) (w : W(T)) :
    endpointMixedToJoint T (endpointMixedIntegration hT w) =
      endpointProductPrimitive ν hT (endpointMixedToJoint T w) := by
  let u := endpointMixedToJoint T w
  let Jw := endpointMixedIntegration hT w
  have hj := ae_endpointTimeSlice_congr (endpointProductPrimitive_apply_ae ν hT u)
  apply endpointJoint_eq_of_slices
  filter_upwards [endpointMixedToJoint_apply_ae w, endpointMixedToJoint_apply_ae Jw, hj] with a ha hJ hw
  have hf := endpointPrimitiveLp_apply_ae hT (HalfHolder.eval a w)
  filter_upwards [hJ, hf, hw, ae_restrict_mem (μ := volume) measurableSet_Ioc] with t hJt hft hwt ht
  calc
    endpointMixedToJoint T Jw (t, a) = HalfHolder.eval a Jw t := hJt.symm
    _ = endpointPrimitiveLp hT (HalfHolder.eval a w) t := by
      rw [show Jw = HalfHolder.map (endpointPrimitiveLp hT) w from rfl, HalfHolder.eval_map]
    _ = endpointPrimitive (fun s => HalfHolder.eval a w s) t := hft
    _ = endpointPrimitive (fun s => u (s, a)) t :=
      endpointPrimitive_congr_ae ha (Ioc_subset_Icc_self ht)
    _ = _ := hwt.symm

/-- Integrating on the entire slab agrees with the weak time integral after
embedding the spatial field. -/
theorem endpointMixedToJoint_terminal {T : ℝ} (hT : 0 ≤ T) (w : W(T)) :
    endpointHalfHolderToL2 (HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT, le_rfl⟩) w) =
      endpointTorusTimeIntegral hT (endpointMixedToJoint T w) :=
  endpointMixedPrimitive_terminal_eq_timeIntegral hT w (endpointMixedToJoint T w)
    (endpointMixedToJoint_apply_ae w)

end TorusEuler

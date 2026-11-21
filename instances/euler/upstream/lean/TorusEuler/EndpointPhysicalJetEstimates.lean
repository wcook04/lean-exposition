import TorusEuler.EndpointPhysicalJetData
import TorusEuler.MeanDerivativeLifting
import TorusEuler.MeanCoefficientBudgets

/-! A single zeroth-order inverse bound in the physical norm of the differentiated mean solve. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (μt T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))
local notation "P[" T "]" => endpointStrongMixedLeray T
local notation "W[" T "]" => freezingFixedSpace (endpointStrongMixedLeray T)

local instance physicalJetSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance physicalJetSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

section TimeNorm

variable {E : Type*} [NormedAddCommGroup E]

/-- The supremum of the norm on the closed time interval. -/
def endpointClosedTimeNorm (T : ℝ) (f : ℝ → E) : ℝ :=
  sSup ((fun t => ‖f t‖) '' Icc 0 T)

theorem norm_le_endpointClosedTimeNorm {T t : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    ‖f t‖ ≤ endpointClosedTimeNorm T f := by
  unfold endpointClosedTimeNorm
  apply le_csSup _ (mem_image_of_mem (fun r => ‖f r‖) ht)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨B, ?_⟩
  intro x hx
  obtain ⟨r, hr, hEq⟩ := hx
  rw [← hEq]
  exact hB r hr

theorem endpointClosedTimeNorm_le {T C : ℝ} (hT : 0 ≤ T) {f : ℝ → E}
    (hB : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ C) : endpointClosedTimeNorm T f ≤ C := by
  unfold endpointClosedTimeNorm
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  apply csSup_le ⟨‖f 0‖, mem_image_of_mem (fun r => ‖f r‖) h0⟩
  intro x hx
  obtain ⟨r, hr, hEq⟩ := hx
  rw [← hEq]
  exact hB r hr

theorem endpointClosedTimeNorm_nonneg {T : ℝ} (hT : 0 ≤ T) (f : ℝ → E) :
    0 ≤ endpointClosedTimeNorm T f := by
  unfold endpointClosedTimeNorm
  by_cases h : BddAbove ((fun t => ‖f t‖) '' Icc 0 T)
  · exact (norm_nonneg (f 0)).trans (le_csSup h (mem_image_of_mem _ ⟨le_rfl, hT⟩))
  · rw [Real.sSup_of_not_bddAbove h]

end TimeNorm

/-- Taking the physical source primitive costs at most the slab duration in
the closed-time norm. -/
theorem endpointClosedTimeNorm_endpointPrimitive_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → E} (hf : ContinuousOn f (Icc 0 T)) :
    endpointClosedTimeNorm T (endpointPrimitive f) ≤ T * endpointClosedTimeNorm T f := by
  apply endpointClosedTimeNorm_le hT
  intro t ht
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t) (f := f)
    (fun r hr => norm_le_endpointClosedTimeNorm hf
      (Ioc_subset_Icc_self (Ioc_subset_Ioc_right ht.2 (by simpa only [uIoc_of_le ht.1] using hr))))
  rw [sub_zero, abs_of_nonneg ht.1] at h
  exact h.trans ((mul_le_mul_of_nonneg_left ht.2 (endpointClosedTimeNorm_nonneg hT f)).trans_eq
    (mul_comm _ _))

section Representatives

/-- Any two continuous time curves representing a common mixed field agree at
all slab times. Their equal primitives have unique within-slab derivatives. -/
theorem EndpointMixedRepresents.eqOn {T : ℝ} (hT : 0 < T)
    {w : Mixed(T)} {f g : ℝ → C½} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) (hF : EndpointMixedRepresents w f)
    (hG : EndpointMixedRepresents w g) : EqOn f g (Icc 0 T) := by
  have hEq (t : ℝ) (ht : t ∈ Icc 0 T) : endpointPrimitive f t = endpointPrimitive g t :=
    (endpointMixedPrimitive_eq_endpointPrimitive w hf hF ⟨t, ht⟩).symm.trans
      (endpointMixedPrimitive_eq_endpointPrimitive w hg hG ⟨t, ht⟩)
  intro t ht
  have dF := hasDerivWithinAt_endpointPrimitive_of_continuousOn hf ht
  have dG := (hasDerivWithinAt_endpointPrimitive_of_continuousOn hg ht).congr_of_mem hEq ht
  exact (dF.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (dG.derivWithin (uniqueDiffOn_Icc hT t ht))

theorem EndpointMixedRepresents.norm_le_of_continuousOn {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    {w : Mixed(T)} {f : ℝ → C½} (hw : EndpointMixedRepresents w f)
    (hf : ContinuousOn f (Icc 0 T)) (hBound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) :
    ‖w‖ ≤ Real.sqrt T * M := by
  obtain ⟨z, hNorm, hRep, _⟩ := exists_endpointMixedSource hT hM f hf hBound
  have hEq : w = z := by
    apply endpointMixedToJoint_injective T
    apply endpointJoint_eq_of_slices
    filter_upwards [hw, endpointMixedToJoint_apply_ae w, endpointMixedToJoint_apply_ae z]
      with a hwa hwj hzj
    exact hwj.symm.trans (hwa.trans ((hRep a).symm.trans hzj))
  simpa only [hEq] using hNorm

end Representatives

section CorrectionNorm

/-- The coefficient family acts on the spatial solenoidal subspace without
changing the field multiplication. -/
def endpointSpatialWordCoefficient (K : ℝ → K½) (t : ℝ) : S →L[ℝ] C½ :=
  (K t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL

private theorem norm_list_map_sum_le {I E : Type*} [NormedAddCommGroup E]
    (l : List I) (f : I → E) : ‖(l.map f).sum‖ ≤ (l.map fun i => ‖f i‖).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, norm_zero, le_refl]
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The temporal correction is controlled by the actual lower-order velocity
norms and the differentiated half-Hölder coefficient norms. -/
theorem norm_endpointTemporalSpatialCorrection_of_halfHolder {I : Type*} {T : ℝ}
    (K : List I → ℝ → K½) (g : List I → ℝ → S) (q : List I)
    (hK : ∀ p : List I, p.length ≤ q.length → ContinuousOn (K p) (Icc 0 T))
    (hg : ∀ p : List I, p.length < q.length → ContinuousOn (g p) (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (K p)) g q t‖ ≤
      ((endpointMixedCorrectionPairs q).map fun p =>
        2 * endpointClosedTimeNorm T (K p.1) * endpointClosedTimeNorm T (g p.2)).sum := by
  unfold endpointTemporalSpatialCorrection
  refine (norm_list_map_sum_le _ _).trans (List.sum_le_sum fun p hp => ?_)
  have hc := endpointMixedCorrectionPairs_mem hp
  have hk := norm_le_endpointClosedTimeNorm (hK p.1 (by omega)) ht
  have hv := norm_le_endpointClosedTimeNorm (hg p.2 hc.2.2) ht
  change ‖(K p.1 t).coefficientMul (g p.2 t).val‖ ≤ _
  exact ((K p.1 t).coefficientMul.le_of_opNorm_le (HalfHolder.norm_coefficientMul_le _) _).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hk zero_le_two) hv (norm_nonneg _)
      (mul_nonneg zero_le_two ((norm_nonneg _).trans hk)))

/-- Integrating a vorticity correction costs at most the actual slab length. -/
theorem norm_endpointPrimitive_spatialCorrection_of_halfHolder {I : Type*} {T : ℝ}
    (K : List I → ℝ → K½) (g : List I → ℝ → S) (q : List I)
    (hK : ∀ p : List I, p.length ≤ q.length → ContinuousOn (K p) (Icc 0 T))
    (hg : ∀ p : List I, p.length < q.length → ContinuousOn (g p) (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖endpointPrimitive
      (endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (K p)) g q) t‖ ≤
      T * ((endpointMixedCorrectionPairs q).map fun p =>
        2 * endpointClosedTimeNorm T (K p.1) * endpointClosedTimeNorm T (g p.2)).sum := by
  let H := ((endpointMixedCorrectionPairs q).map fun p =>
    2 * endpointClosedTimeNorm T (K p.1) * endpointClosedTimeNorm T (g p.2)).sum
  have hb (r : ℝ) (hr : r ∈ Icc 0 T) :
      ‖endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (K p)) g q r‖ ≤ H :=
    norm_endpointTemporalSpatialCorrection_of_halfHolder K g q hK hg r hr
  have hH : 0 ≤ H := (norm_nonneg _).trans (hb t ht)
  have hP := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (f := endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (K p)) g q)
    (fun r hr => hb r (Ioc_subset_Icc_self (Ioc_subset_Ioc_right ht.2
      (by simpa only [uIoc_of_le ht.1] using hr))))
  rw [sub_zero, abs_of_nonneg ht.1] at hP
  exact hP.trans ((mul_le_mul_of_nonneg_left ht.2 hH).trans_eq (mul_comm _ _))

end CorrectionNorm

section RecoveryInequalities

variable {Labels E X : Type*} [MetricSpace Labels]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "Path(" T ")" => Lp E 2 (μt T)
local notation "MixedOf(" T ")" => HalfHolder Labels Path(T)
local notation "Spatial" => HalfHolder Labels E

/-- The endpoint primitive in the spatial Hölder norm has the square-root
gain of the temporal (L^2) primitive evaluation. -/
theorem norm_endpointMixedPrimitive_apply_le {T : ℝ}
    (t : Icc (0 : ℝ) T) (R : MixedOf(T)) :
    ‖HalfHolder.map (endpointPrimitiveEvaluation t) R‖ ≤ Real.sqrt (t : ℝ) * ‖R‖ := by
  let J : MixedOf(T) →L[ℝ] Spatial := HalfHolder.map (endpointPrimitiveEvaluation t)
  change ‖J R‖ ≤ Real.sqrt (t : ℝ) * ‖R‖
  have hJ : ‖J‖ ≤ Real.sqrt (t : ℝ) :=
    (HalfHolder.norm_map_le (X := Labels) (endpointPrimitiveEvaluation (E := E) t)).trans
      (norm_endpointPrimitiveEvaluation_le t)
  exact J.le_of_opNorm_le hJ R

/-- Averaging a residual with its (L^2) time scaling removes the duration
from the bound on the projected constant. -/
theorem norm_endpointMixedProjectedMean_le_of_sqrt_bound {T D : ℝ}
    (hT : 0 < T) (P : Spatial →L[ℝ] X) (R : MixedOf(T)) (hR : ‖R‖ ≤ Real.sqrt T * D) :
    ‖P (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) R)‖ ≤
      ‖P‖ * D := by
  let J := HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) R
  have hJ : ‖J‖ ≤ T * D := by
    calc
      ‖J‖ ≤ Real.sqrt T * ‖R‖ :=
        norm_endpointMixedPrimitive_apply_le ⟨T, hT.le, le_rfl⟩ R
      _ ≤ Real.sqrt T * (Real.sqrt T * D) :=
        mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)
      _ = T * D := by rw [← mul_assoc, Real.mul_self_sqrt hT.le]
  change ‖P (T⁻¹ • J)‖ ≤ ‖P‖ * D
  calc
    _ ≤ ‖P‖ * ‖T⁻¹ • J‖ := P.le_opNorm _
    _ = ‖P‖ * (T⁻¹ * ‖J‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
    _ ≤ ‖P‖ * (T⁻¹ * (T * D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hT.le))
        (norm_nonneg P)
    _ = _ := by rw [← mul_assoc T⁻¹, inv_mul_cancel₀ hT.ne', one_mul]

/-- Pointwise recovery from the instantaneous coefficient equation. -/
theorem norm_endpointRecoveredVelocity_le_of_equation {T Inv : ℝ}
    (P : Spatial →L[ℝ] X) (e : X ≃L[ℝ] X) (hInv : ‖(e.symm : X →L[ℝ] X)‖ ≤ Inv)
    (t : Icc (0 : ℝ) T) (c g : X) (Jw : MixedOf(T)) (F : Spatial)
    (hEq : e g = c + P (HalfHolder.map (endpointPrimitiveEvaluation t) Jw) - P F) :
    ‖g‖ ≤ Inv * (‖c‖ + ‖P‖ * (Real.sqrt T * ‖Jw‖ + ‖F‖)) := by
  let J := HalfHolder.map (endpointPrimitiveEvaluation t) Jw
  have hJ : ‖J‖ ≤ Real.sqrt T * ‖Jw‖ :=
    (norm_endpointMixedPrimitive_apply_le t Jw).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt t.property.2) (norm_nonneg _))
  have hInv₀ : 0 ≤ Inv := (norm_nonneg _).trans hInv
  change e g = c + P J - P F at hEq
  calc
    ‖g‖ = ‖e.symm (c + P J - P F)‖ := by rw [← hEq, e.symm_apply_apply]
    _ ≤ Inv * ‖c + P J - P F‖ := (e.symm : X →L[ℝ] X).le_of_opNorm_le hInv _
    _ ≤ Inv * ((‖c‖ + ‖P J‖) + ‖P F‖) :=
      mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) hInv₀
    _ ≤ Inv * ((‖c‖ + ‖P‖ * (Real.sqrt T * ‖Jw‖)) + ‖P‖ * ‖F‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add le_rfl ((P.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)))) (P.le_opNorm _)) hInv₀
    _ = _ := by ring

/-- The time-average and Volterra terms use the path scaling of the mixed
solution and source, so no inverse power of the slab duration is needed. -/
theorem norm_endpointRecoveredVelocity_le_of_mixed_sqrt_bounds {T Inv V F₀ : ℝ}
    (hT : 0 < T) (P : Spatial →L[ℝ] X) (e : X ≃L[ℝ] X)
    (hInv : ‖(e.symm : X →L[ℝ] X)‖ ≤ Inv)
    (B Ω : MixedOf(T) →L[ℝ] MixedOf(T)) (t : Icc (0 : ℝ) T) (g : X)
    (w Fmix : MixedOf(T)) (F : Spatial)
    (hw : ‖w‖ ≤ Real.sqrt T * V) (hFmix : ‖Fmix‖ ≤ Real.sqrt T * F₀)
    (hEq : e g = P (T⁻¹ • HalfHolder.map
      (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) (B w + Fmix)) +
      P (HalfHolder.map (endpointPrimitiveEvaluation t) (Ω w)) - P F) :
    ‖g‖ ≤ Inv * (‖P‖ * ((‖B‖ + T * ‖Ω‖) * V + F₀ + ‖F‖)) := by
  let R := B w + Fmix
  let c := P (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) R)
  have hR : ‖R‖ ≤ Real.sqrt T * (‖B‖ * V + F₀) := by
    calc
      ‖R‖ ≤ ‖B w‖ + ‖Fmix‖ := norm_add_le _ _
      _ ≤ ‖B‖ * (Real.sqrt T * V) + Real.sqrt T * F₀ :=
        add_le_add ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))) hFmix
      _ = _ := by ring
  have hc : ‖c‖ ≤ ‖P‖ * (‖B‖ * V + F₀) :=
    norm_endpointMixedProjectedMean_le_of_sqrt_bound hT P R hR
  have hΩ : Real.sqrt T * ‖Ω w‖ ≤ T * ‖Ω‖ * V := by
    calc
      _ ≤ Real.sqrt T * (‖Ω‖ * (Real.sqrt T * V)) :=
        mul_le_mul_of_nonneg_left
          ((Ω.le_opNorm _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _)))
          (Real.sqrt_nonneg _)
      _ = (Real.sqrt T * Real.sqrt T) * ‖Ω‖ * V := by ring
      _ = _ := by rw [Real.mul_self_sqrt hT.le]
  calc
    ‖g‖ ≤ Inv * (‖c‖ + ‖P‖ * (Real.sqrt T * ‖Ω w‖ + ‖F‖)) :=
      norm_endpointRecoveredVelocity_le_of_equation P e hInv t c g (Ω w) F hEq
    _ ≤ Inv * (‖P‖ * (‖B‖ * V + F₀) + ‖P‖ * (T * ‖Ω‖ * V + ‖F‖)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hc (mul_le_mul_of_nonneg_left (add_le_add hΩ le_rfl) (norm_nonneg P)))
        ((norm_nonneg _).trans hInv)
    _ = _ := by ring

/-- The mixed kinetic–Volterra operator has the usual (O(T)) vorticity
contribution in path operator norm. -/
theorem norm_endpointMixedProductOperator_le {T : ℝ} (hT : 0 ≤ T)
    (K Ω : HalfHolder (UnitAddTorus (Fin 3))
      (Lp Vec3 2 (μt T) →L[ℝ] Lp Vec3 2 (μt T))) :
    ‖endpointMixedProductOperator hT K Ω‖ ≤ ‖K.coefficientMul‖ + T * ‖Ω.coefficientMul‖ := by
  rw [endpointMixedProductOperator]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    (((endpointMixedIntegration hT).opNorm_comp_le Ω.coefficientMul).trans
      (mul_le_mul_of_nonneg_right (norm_endpointMixedIntegration_le hT) (norm_nonneg _))))

end RecoveryInequalities

section RecoveryBudget

set_option maxHeartbeats 1000000 in
/-- The mixed compression gives a norm bound for any fixed solution of the
projected equation, with the same inverse cap used in its construction. -/
theorem norm_endpointMixed_of_projectedResidual {T M : ℝ} (hT : 0 < T)
    (Kmix Ωmix : MixedCoefficient(T)) (w f : Mixed(T))
    (E : W[T] ≃L[ℝ] W[T])
    (hE : (E : W[T] →L[ℝ] W[T]) = freezingCompression P[T]
      (endpointMixedPathCoefficient hT.le Kmix Ωmix).coefficientMul (endpointStrongMixedLeray_idempotent hT))
    (hM : ‖(E.symm : W[T] →L[ℝ] W[T])‖ ≤ M)
    (hw : P[T] w = w) (hEq : P[T] (endpointMixedProductOperator hT.le Kmix Ωmix w + f) = 0) :
    ‖w‖ ≤ M * (‖P[T]‖ * ‖f‖) := by
  let z : W[T] := ⟨w, (mem_freezingFixedSpace P[T] w).mpr hw⟩
  have hr : P[T] (-(P[T] f)) = -(P[T] f) := by
    rw [map_neg, endpointStrongMixedLeray_idempotent hT]
  let r : W[T] := ⟨-(P[T] f), (mem_freezingFixedSpace P[T] _).mpr hr⟩
  have hProd : P[T] (endpointMixedProductOperator hT.le Kmix Ωmix w) = -(P[T] f) := by
    rw [map_add] at hEq
    exact eq_neg_of_add_eq_zero_left hEq
  have hz : E z = r := by
    apply Subtype.ext
    have hm := congrArg (fun x : W[T] => x.val) (DFunLike.congr_fun hE z)
    have hc := DFunLike.congr_fun (endpointMixedPathCoefficient_coefficientMul hT.le Kmix Ωmix) w
    exact hm.trans ((congrArg (P[T]) hc).trans hProd)
  have hIn : E.symm r = z := by rw [← hz, E.symm_apply_apply]
  have h := (E.symm : W[T] →L[ℝ] W[T]).le_of_opNorm_le hM r
  change ‖E.symm r‖ ≤ M * ‖r‖ at h
  rw [hIn] at h
  change ‖w‖ ≤ M * ‖-(P[T] f)‖ at h
  rw [norm_neg] at h
  exact h.trans (mul_le_mul_of_nonneg_left ((P[T]).le_opNorm f)
    ((E.symm : W[T] →L[ℝ] W[T]).opNorm_nonneg.trans hM))

/-- The common zeroth-order cap from the two half-Hölder inverses and the
mixed coefficient norms. The terminal normalization has no inverse time factor. -/
def endpointPhysicalInverseBudget {T : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) (As Am : ℝ) : ℝ :=
  As * ‖endpointStrongSpatialProjection‖ *
    (2 + (‖endpointMixedProductOperator hT Kmix Ωmix‖ + T * ‖Ωmix.coefficientMul‖) *
      (Am * ‖P[T]‖))

theorem endpointPhysicalInverseBudget_nonneg {T As Am : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) (hAs : 0 ≤ As) (hAm : 0 ≤ Am) :
    0 ≤ endpointPhysicalInverseBudget hT Kmix Ωmix As Am := by
  unfold endpointPhysicalInverseBudget
  exact mul_nonneg (mul_nonneg hAs endpointStrongSpatialProjection.opNorm_nonneg)
    (add_nonneg zero_le_two (mul_nonneg (add_nonneg
      (endpointMixedProductOperator hT Kmix Ωmix).opNorm_nonneg
      (mul_nonneg hT Ωmix.coefficientMul.opNorm_nonneg)) (mul_nonneg hAm (P[T]).opNorm_nonneg)))

set_option maxHeartbeats 2200000 in
/-- The zeroth-order inverse estimate applies to the actual continuous time
representative of any mixed projected solution with matching physical source. -/
theorem norm_endpointPhysicalTimeRepresentative_le {T μ L M As Am C : ℝ} (hT : 0 < T)
    (Kmix Ωmix : MixedCoefficient(T)) (w f : Mixed(T)) (K : ℝ → K½) (F : ℝ → C½) (g : ℝ → S)
    (hK : ContinuousOn K (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hKmix : ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a Kmix v r) =ᵐ[μt T] fun r => HalfHolder.eval a (K r) (v r))
    (hFmix : EndpointMixedRepresents f F) (hRep : EndpointMixedRepresents w (fun r => (g r).val))
    (hw : P[T] w = w) (hProjected : P[T] (endpointMixedProductOperator hT.le Kmix Ωmix w + f) = 0)
    (hμ : 0 < μ) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ Icc 0 T, ∀ a b, ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ Icc 0 T, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (hSup : ∀ t ∈ Icc 0 T, ‖(K t).val.1‖ ≤ M)
    (eS : ℝ → S ≃L[ℝ] S)
    (heS : ∀ t ∈ Icc 0 T, ∀ v : S, eS t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val))
    (hAs : ∀ t ∈ Icc 0 T, ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As)
    (eM : W[T] ≃L[ℝ] W[T])
    (heM : (eM : W[T] →L[ℝ] W[T]) = freezingCompression P[T]
      (endpointMixedPathCoefficient hT.le Kmix Ωmix).coefficientMul (endpointStrongMixedLeray_idempotent hT))
    (hAm : ‖(eM.symm : W[T] →L[ℝ] W[T])‖ ≤ Am)
    (hC : 0 ≤ C) (hFc : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ C) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖g t‖ ≤ endpointPhysicalInverseBudget hT.le Kmix Ωmix As Am * C := by
  have hFbound := hFmix.norm_le_of_continuousOn hT.le hC hF hFc
  have hAm₀ : 0 ≤ Am := (eM.symm : W[T] →L[ℝ] W[T]).opNorm_nonneg.trans hAm
  have hW : ‖w‖ ≤ Real.sqrt T * ((Am * ‖P[T]‖) * C) := by
    calc
      _ ≤ Am * (‖P[T]‖ * ‖f‖) := norm_endpointMixed_of_projectedResidual hT Kmix Ωmix w f eM heM hAm hw hProjected
      _ ≤ Am * (‖P[T]‖ * (Real.sqrt T * C)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hFbound (P[T]).opNorm_nonneg) hAm₀
      _ = _ := by ring
  obtain ⟨g₀, hg₀, hEq, hRep₀, _, _, _⟩ := exists_endpointMixedTimeRecovery hT Kmix Ωmix w f K F
    hw hProjected hμ hL (contDiffOn_zero.mpr hK) hLip hPos hSup hF hFc
    (ae_endpointMixedCoefficient_spatialSlice_of_pathAction K Kmix hK hKmix w)
    (hFmix.spatialSlice hT.le hF)
  have hgc := endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg
  have hg₀c := endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg₀
  have hRep₀' := EndpointMixedRepresents.of_spatialSlice hT.le hg₀c hRep₀
  have hEqg : g t = g₀ t := Subtype.ext ((hRep.eqOn hT hgc hg₀c hRep₀') ht)
  let B := endpointMixedProductOperator hT.le Kmix Ωmix
  let O := Ωmix.coefficientMul
  have hInst := (heS t ht (g₀ t)).trans (hEq ⟨t, ht⟩)
  have hNorm := norm_endpointRecoveredVelocity_le_of_mixed_sqrt_bounds hT
    endpointStrongSpatialProjection (eS t) (hAs t ht) B O ⟨t, ht⟩ (g₀ t) w f (F t) hW hFbound hInst
  rw [hEqg]
  refine hNorm.trans ?_
  calc
    _ ≤ As * (‖endpointStrongSpatialProjection‖ *
          ((‖B‖ + T * ‖O‖) * ((Am * ‖P[T]‖) * C) + C + C)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hFc t ht))
        endpointStrongSpatialProjection.opNorm_nonneg)
        (((eS t).symm : S →L[ℝ] S).opNorm_nonneg.trans (hAs t ht))
    _ = _ := by unfold endpointPhysicalInverseBudget; dsimp only [B, O]; ring

end RecoveryBudget

section PhysicalRecurrence

/-- The coefficient cost of one Leibniz term. The vorticity part includes the
actual length of the time integral. -/
def endpointPhysicalCoefficientWordNorm {I : Type*} (T : ℝ)
    (K Ω : List I → ℝ → K½) (q : List I) : ℝ :=
  2 * (endpointClosedTimeNorm T (K q) + T * endpointClosedTimeNorm T (Ω q))

/-- A weighted bound for the kinetic and vorticity words pays for the common
inverse cap in the derivative recurrence. -/
theorem endpointPhysicalCoefficientWordNorm_threshold {I : Type*} {T ℓ Ainv H D : ℝ}
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ Ainv) (hH : 0 ≤ H)
    (K Ω : List I → ℝ → K½) (q : List I)
    (hB : ℓ ^ q.length * (endpointClosedTimeNorm T (K q) + endpointClosedTimeNorm T (Ω q)) ≤
      H * D ^ 9 * Real.sqrt ℓ)
    (hSmall : Ainv * D ^ 9 * Real.sqrt ℓ ≤ 1) :
    Ainv * (ℓ ^ q.length * endpointPhysicalCoefficientWordNorm T K Ω q) ≤ 2 * H := by
  have hΩ : T * endpointClosedTimeNorm T (Ω q) ≤ endpointClosedTimeNorm T (Ω q) :=
    mul_le_of_le_one_left (endpointClosedTimeNorm_nonneg hT (Ω q)) hT₁
  calc
    _ ≤ Ainv * (ℓ ^ q.length * (2 * (endpointClosedTimeNorm T (K q) + endpointClosedTimeNorm T (Ω q)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hΩ) zero_le_two) (pow_nonneg hℓ _)) hA
    _ = (2 * Ainv) * (ℓ ^ q.length * (endpointClosedTimeNorm T (K q) + endpointClosedTimeNorm T (Ω q))) :=
      by ring
    _ ≤ (2 * Ainv) * (H * D ^ 9 * Real.sqrt ℓ) := mul_le_mul_of_nonneg_left hB (mul_nonneg zero_le_two hA)
    _ = (Ainv * D ^ 9 * Real.sqrt ℓ) * (2 * H) := by ring
    _ ≤ 2 * H := mul_le_of_le_one_left (mul_nonneg zero_le_two hH) hSmall

private theorem sum_physical_coefficient_costs {I : Type*} (T : ℝ)
    (K Ω : List I → ℝ → K½) (g : List I → ℝ → S) (l : List (List I × List I)) :
    (l.map fun p => 2 * endpointClosedTimeNorm T (K p.1) * endpointClosedTimeNorm T (g p.2)).sum +
        T * (l.map fun p => 2 * endpointClosedTimeNorm T (Ω p.1) * endpointClosedTimeNorm T (g p.2)).sum =
      (l.map fun p => endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero, add_zero]
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, endpointPhysicalCoefficientWordNorm]
    ring

set_option maxHeartbeats 3000000 in
/-- Each recovered physical derivative obeys the same zeroth-order inverse
bound, applied to its actual differentiated source. This is the half-Hölder
recurrence of the finite-order mean estimate. -/
theorem endpointPhysicalJetNormRecurrence {I : Type*} {T μ L M As Am : ℝ} {N : ℕ}
    (hT : 0 < T) (Kmix Ωmix : List I → MixedCoefficient(T)) (w srcMix : List I → Mixed(T))
    (K Ω : List I → ℝ → K½) (src : List I → ℝ → C½) (g : List I → ℝ → S)
    (hK : ∀ q, q.length ≤ N → ContinuousOn (K q) (Icc 0 T))
    (hΩ : ∀ q, q.length ≤ N → ContinuousOn (Ω q) (Icc 0 T))
    (hSrc : ∀ q, q.length ≤ N → ContinuousOn (src q) (Icc 0 T))
    (hg : ∀ q, q.length ≤ N → ContinuousOn (g q) (Icc 0 T))
    (hSrcMix : ∀ q, q.length ≤ N → EndpointMixedRepresents (srcMix q) (src q))
    (hRep : ∀ q, q.length ≤ N → EndpointMixedRepresents (w q) (fun r => (g q r).val))
    (hKmix : ∀ q, q.length ≤ N → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a (Kmix q) v r) =ᵐ[μt T] fun r => HalfHolder.eval a (K q r) (v r))
    (hΩmix : ∀ q, q.length ≤ N → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a (Ωmix q) v r) =ᵐ[μt T] fun r => HalfHolder.eval a (Ω q r) (v r))
    (hFixed : ∀ q, q.length ≤ N → P[T] (w q) = w q)
    (hProjected : ∀ q, q.length ≤ N → P[T]
      (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + srcMix q +
        endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT.le (Kmix r) (Ωmix r)) w q) = 0)
    (hμ : 0 < μ) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ Icc 0 T, ∀ a b,
      ‖HalfHolder.eval a (K [] t) - HalfHolder.eval b (K [] t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ Icc 0 T, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) v, v⟫_ℝ)
    (hSup : ∀ t ∈ Icc 0 T, ‖(K [] t).val.1‖ ≤ M)
    (eS : ℝ → S ≃L[ℝ] S)
    (heS : ∀ t ∈ Icc 0 T, ∀ v : S, eS t v = endpointStrongSpatialProjection ((K [] t).coefficientMul v.val))
    (hAs : ∀ t ∈ Icc 0 T, ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As)
    (eM : W[T] ≃L[ℝ] W[T])
    (heM : (eM : W[T] →L[ℝ] W[T]) = freezingCompression P[T]
      (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix [])).coefficientMul (endpointStrongMixedLeray_idempotent hT))
    (hAm : ‖(eM.symm : W[T] →L[ℝ] W[T])‖ ≤ Am) :
    ∀ q, q.length ≤ N → endpointClosedTimeNorm T (g q) ≤
      endpointPhysicalInverseBudget hT.le (Kmix []) (Ωmix []) As Am *
        (endpointClosedTimeNorm T (src q) + ((endpointMixedCorrectionPairs q).map fun p =>
          endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)).sum) := by
  intro q hq
  let CK := endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (K p)) g q
  let CΩ := endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (Ω p)) g q
  let f (t : ℝ) := src q t + CK t - endpointPrimitive CΩ t
  let fm := srcMix q + endpointMixedCorrection Kmix w q -
    endpointMixedIntegration hT.le (endpointMixedCorrection Ωmix w q)
  let C := endpointClosedTimeNorm T (src q) + ((endpointMixedCorrectionPairs q).map fun p =>
    endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)).sum
  have hCont (H : List I → ℝ → K½)
      (hH : ∀ p, p.length ≤ N → ContinuousOn (H p) (Icc 0 T)) :
      ContinuousOn (endpointTemporalSpatialCorrection (fun p => endpointSpatialWordCoefficient (H p)) g q)
        (Icc 0 T) := by
    have hOps (p : List I) (hp : p.length ≤ q.length) :
        ContDiffOn ℝ 0 (endpointSpatialWordCoefficient (H p)) (Icc 0 T) := by
      have h := HalfHolder.contDiffOn_coefficientMul (contDiffOn_zero.mpr (hH p (hp.trans hq)))
      exact h.clm_comp contDiffOn_const
    exact (contDiffOn_endpointTemporalSpatialCorrection _ g q hOps
      (fun p hp => contDiffOn_zero.mpr (hg p (hp.le.trans hq)))).continuousOn
  have hCK := hCont K hK
  have hCΩ := hCont Ω hΩ
  have hf : ContinuousOn f (Icc 0 T) := ((hSrc q hq).add hCK).sub
    (contDiffOn_endpointPrimitive_succ hT (contDiffOn_zero.mpr hCΩ)).continuousOn
  have hCKrep : EndpointMixedRepresents (endpointMixedCorrection Kmix w q) CK :=
    EndpointMixedRepresents.spatialCorrection Kmix K w g q
      (fun p hp => hRep p (hp.le.trans hq)) (fun p hp => hKmix p (hp.trans hq))
  have hCΩrep : EndpointMixedRepresents (endpointMixedCorrection Ωmix w q) CΩ :=
    EndpointMixedRepresents.spatialCorrection Ωmix Ω w g q
      (fun p hp => hRep p (hp.le.trans hq)) (fun p hp => hΩmix p (hp.trans hq))
  have hfm : EndpointMixedRepresents fm f :=
    ((hSrcMix q hq).add hCKrep).sub (hCΩrep.integration hT.le hCΩ)
  have hfmProj : P[T] (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + fm) = 0 := by
    have h := hProjected q hq
    rw [endpointMixedCorrection_pathCoefficient hT.le Kmix Ωmix w q] at h
    convert h using 2
    dsimp only [fm]
    abel
  have hFC (r : ℝ) (hr : r ∈ Icc 0 T) : ‖f r‖ ≤ C := by
    have hFK := norm_endpointTemporalSpatialCorrection_of_halfHolder K g q
      (fun p hp => hK p (hp.trans hq)) (fun p hp => hg p (hp.le.trans hq)) r hr
    have hFΩ := norm_endpointPrimitive_spatialCorrection_of_halfHolder Ω g q
      (fun p hp => hΩ p (hp.trans hq)) (fun p hp => hg p (hp.le.trans hq)) r hr
    dsimp only [f]
    calc
      _ ≤ (‖src q r‖ + ‖CK r‖) + ‖endpointPrimitive CΩ r‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (endpointClosedTimeNorm T (src q) + _ ) + _ :=
        add_le_add (add_le_add (norm_le_endpointClosedTimeNorm (hSrc q hq) hr) hFK) hFΩ
      _ = C := by
        dsimp only [C]
        rw [add_assoc, sum_physical_coefficient_costs T K Ω g]
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hFC 0 ⟨le_rfl, hT.le⟩)
  apply endpointClosedTimeNorm_le hT.le
  intro t ht
  exact norm_endpointPhysicalTimeRepresentative_le hT (Kmix []) (Ωmix []) (w q) fm
    (K []) f (g q) (hK [] (Nat.zero_le N)) hf (hg q hq) (hKmix [] (Nat.zero_le N)) hfm
    (hRep q hq) (hFixed q hq) hfmProj hμ hL hLip hPos hSup eS heS hAs eM heM hAm hC hFC t ht

/-- The weighted mean-source estimate from the actual physical recurrence and
the scaled bounds on positive-order coefficient words. -/
theorem endpointWeightedPhysicalMeanEstimate {I : Type*} {T ℓ Ainv Mf C : ℝ} {N : ℕ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ Ainv) (hM : 0 ≤ Mf) (hC : 0 ≤ C)
    (K Ω : List I → ℝ → K½) (src : List I → ℝ → C½) (g : List I → ℝ → S)
    (hF : ∀ q, q.length ≤ N → ℓ ^ q.length * endpointClosedTimeNorm T (src q) ≤ Mf)
    (hB : ∀ q, 1 ≤ q.length → q.length ≤ N →
      Ainv * (ℓ ^ q.length * endpointPhysicalCoefficientWordNorm T K Ω q) ≤ C)
    (hRec : ∀ q, q.length ≤ N → endpointClosedTimeNorm T (g q) ≤ Ainv *
      (endpointClosedTimeNorm T (src q) + ((endpointMixedCorrectionPairs q).map fun p =>
        endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)).sum)) :
    ∀ q, q.length ≤ N → ℓ ^ q.length * endpointClosedTimeNorm T (g q) ≤
      Ainv * Mf * (1 + (2 : ℝ) ^ N * C) ^ q.length :=
  meanDerivativeLifting N (fun q => endpointClosedTimeNorm T (g q))
    (fun q => endpointClosedTimeNorm T (src q)) (endpointPhysicalCoefficientWordNorm T K Ω)
    hℓ hA hM hC (fun q => endpointClosedTimeNorm_nonneg hT (g q)) hF hB hRec

end PhysicalRecurrence

section LiftNorm

/-- The lift of a recovered half-Hölder word has the expected scaled norm.
This converts the endpoint estimate to the actual label norm used in §5. -/
theorem hierarchyJetValues_le_of_recovered_halfHolder {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T ℓ : ℝ} (hT : 0 ≤ T) (hℓ : 0 ≤ ℓ)
    (w : List (Fin 3)) {v : ℝ → Vec3 → E} {g : ℝ → HalfHolder A E}
    (hv : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (v t)) (hg : ContinuousOn g (Icc 0 T))
    (hLift : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (g t) =
      spatialDerivativeWord w (v t) x) :
    let J := hierarchyJetValues True (hierarchyLabelDirection ℓ) w
      (fun t : Icc (0 : ℝ) T => v t)
    BddAbove J ∧ sSup J ≤ ℓ ^ w.length * endpointClosedTimeNorm T g := by
  let M := ℓ ^ w.length * endpointClosedTimeNorm T g
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg hℓ _) (endpointClosedTimeNorm_nonneg hT g)
  let J := hierarchyJetValues True (hierarchyLabelDirection ℓ) w
    (fun t : Icc (0 : ℝ) T => v t)
  have heval (t : Icc (0 : ℝ) T) (x : Vec3) :
      phaseOperatorWord (hierarchyLabelDirection ℓ) w (v t) x =
        ℓ ^ w.length • HalfHolder.eval (toUnitTorus x) (g t) := by
    rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ℓ (hv t t.property), hLift t t.property x]
  have hBounds : ∀ r ∈ J, r ≤ M := by
    intro r hr
    rcases hr with hzero | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩
    · rwa [hzero]
    · rw [heval, norm_smul, Real.norm_of_nonneg (pow_nonneg hℓ _)]
      have he := ((HalfHolder.norm_le_iff (norm_nonneg (g (t : ℝ)))).mp le_rfl).1 (toUnitTorus x)
      exact mul_le_mul_of_nonneg_left (he.trans (norm_le_endpointClosedTimeNorm hg t.property))
        (pow_nonneg hℓ _)
    · by_cases hxy : x = y
      · simpa only [hxy, sub_self, norm_zero, zero_div] using hM
      · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.2 hxy))).2
        rw [heval, heval, ← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg hℓ _), mul_assoc]
        have hh := ((HalfHolder.norm_le_iff (norm_nonneg (g (t : ℝ)))).mp le_rfl).2
          (toUnitTorus x) (toUnitTorus y)
        have hd : dist (toUnitTorus x) (toUnitTorus y) ≤ dist x y := by
          simpa only [NNReal.coe_one, one_mul] using lipschitzWith_toUnitTorus.dist_le_mul x y
        exact mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul
          (norm_le_endpointClosedTimeNorm hg t.property) (Real.sqrt_le_sqrt hd)
          (Real.sqrt_nonneg _) (endpointClosedTimeNorm_nonneg hT g))) (pow_nonneg hℓ _)
  exact ⟨⟨M, hBounds⟩, csSup_le ⟨0, Or.inl rfl⟩ hBounds⟩

/-- A uniform weighted bound on the actual recovered words controls the
finite weighted label norm of the same velocity. -/
theorem hierarchyFiniteWordNorm_le_of_recovered_halfHolder {T ℓ B : ℝ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ ℓ) (N : ℕ) {v : ℝ → Vec3 → Vec3} {g : List (Fin 3) → ℝ → S}
    (hv : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (v t))
    (hg : ∀ q, q.length ≤ N → ContinuousOn (g q) (Icc 0 T))
    (hLift : ∀ q, q.length ≤ N → ∀ t ∈ Icc 0 T, ∀ x,
      HalfHolder.eval (toUnitTorus x) (g q t).val = spatialDerivativeWord q (v t) x)
    (hBound : ∀ q, q.length ≤ N → ℓ ^ q.length * endpointClosedTimeNorm T (g q) ≤ B) :
    hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) N (fun t : Icc (0 : ℝ) T => v t) ≤
      (hierarchyAdmissibleWords (Fin 3) N).card * B := by
  unfold hierarchyFiniteWordNorm
  calc
    _ ≤ ∑ _q ∈ hierarchyAdmissibleWords (Fin 3) N, B := by
      apply Finset.sum_le_sum
      intro q hq
      have hqN := (mem_hierarchyAdmissibleWords.mp hq).1
      have hc := endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn (hg q hqN)
      exact (hierarchyJetValues_le_of_recovered_halfHolder hT hℓ q hv hc
        (hLift q hqN)).2.trans (hBound q hqN)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end LiftNorm

section CoefficientCaps

/-- The norm of the actual temporal multiplier is controlled by the supremum
of the strong coefficient time slices. -/
theorem norm_endpointMixedCoefficient_le_of_timeSlices {T C : ℝ} (hC : 0 ≤ C)
    (Kmix : MixedCoefficient(T)) (K : ℝ → K½) (hK : ContinuousOn K (Icc 0 T))
    (hBound : ∀ t ∈ Icc 0 T, ‖K t‖ ≤ C)
    (hMix : ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a Kmix v r) =ᵐ[μt T] fun r => HalfHolder.eval a (K r) (v r)) :
    ‖Kmix‖ ≤ C := by
  obtain ⟨z, hNorm, hAction⟩ := exists_endpointMixedCoefficient_of_timeCurve hC K hK hBound
  have hae : (fun a => HalfHolder.eval a Kmix) =ᵐ[unitTorusMeasure] fun a => HalfHolder.eval a z := by
    filter_upwards [hMix] with a ha
    apply ContinuousLinearMap.ext
    intro v
    exact Lp.ext ((ha v).trans (hAction a v).symm)
  have hEq := (Continuous.ae_eq_iff_eq unitTorusMeasure Kmix.val.1.continuous z.val.1.continuous).mp hae
  have hz : Kmix = z := HalfHolder.ext (congrFun hEq)
  simpa only [hz] using hNorm

/-- The base recovery budget is controlled by the actual strong zeroth-order
coefficient time norms and the two inverse and projection caps. -/
theorem endpointPhysicalInverseBudget_le_of_timeSlices {T As Am : ℝ} (hT : 0 ≤ T)
    (hAs : 0 ≤ As) (hAm : 0 ≤ Am) (Kmix Ωmix : MixedCoefficient(T)) (K Ω : ℝ → K½)
    (hK : ContinuousOn K (Icc 0 T)) (hΩ : ContinuousOn Ω (Icc 0 T))
    (hKmix : ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a Kmix v r) =ᵐ[μt T] fun r => HalfHolder.eval a (K r) (v r))
    (hΩmix : ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun r => HalfHolder.eval a Ωmix v r) =ᵐ[μt T] fun r => HalfHolder.eval a (Ω r) (v r)) :
    endpointPhysicalInverseBudget hT Kmix Ωmix As Am ≤
      As * ‖endpointStrongSpatialProjection‖ *
        (2 + (2 * endpointClosedTimeNorm T K + 4 * T * endpointClosedTimeNorm T Ω) * (Am * ‖P[T]‖)) := by
  have hK₀ := norm_endpointMixedCoefficient_le_of_timeSlices
    (endpointClosedTimeNorm_nonneg hT K) Kmix K hK (fun t ht => norm_le_endpointClosedTimeNorm hK ht) hKmix
  have hΩ₀ := norm_endpointMixedCoefficient_le_of_timeSlices
    (endpointClosedTimeNorm_nonneg hT Ω) Ωmix Ω hΩ (fun t ht => norm_le_endpointClosedTimeNorm hΩ ht) hΩmix
  have hk := (HalfHolder.norm_coefficientMul_le Kmix).trans (mul_le_mul_of_nonneg_left hK₀ zero_le_two)
  have hω := (HalfHolder.norm_coefficientMul_le Ωmix).trans (mul_le_mul_of_nonneg_left hΩ₀ zero_le_two)
  unfold endpointPhysicalInverseBudget
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hAs endpointStrongSpatialProjection.opNorm_nonneg)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hAm (P[T]).opNorm_nonneg)
  calc
    _ ≤ (‖Kmix.coefficientMul‖ + T * ‖Ωmix.coefficientMul‖) + T * ‖Ωmix.coefficientMul‖ :=
      add_le_add (norm_endpointMixedProductOperator_le hT Kmix Ωmix) le_rfl
    _ ≤ (2 * endpointClosedTimeNorm T K + T * (2 * endpointClosedTimeNorm T Ω)) +
        T * (2 * endpointClosedTimeNorm T Ω) :=
      add_le_add (add_le_add hk (mul_le_mul_of_nonneg_left hω hT)) (mul_le_mul_of_nonneg_left hω hT)
    _ = _ := by ring

end CoefficientCaps

section LiftMatching

private theorem endpointSlabDirectionalWord_map {I J E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ) (D : J → ℝ × Vec3)
    (d : I → J) (f : ℝ × Vec3 → E) (q : List I) :
    endpointSlabDirectionalWord T D f (q.map d) =
      endpointSlabDirectionalWord T (D ∘ d) f q := by
  induction q with
  | nil => rfl
  | cons i q ih => simp only [List.map_cons, endpointSlabDirectionalWord, ih, Function.comp_apply]

/-- The coordinate words in the geometric jet data are the ordinary spatial
partial derivatives of the lift. -/
theorem endpointSlabSpatialWord_eq_spatialDerivativeWord {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 < T)
    {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) T ×ˢ (univ : Set Vec3)))
    (q : List (Fin 3)) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
    endpointSlabSpatialWord T coordinateDirection f q (t, x) =
      spatialDerivativeWord q (fun y => f (t, y)) x := by
  rw [endpointSlabSpatialWord, endpointSlabDirectionalWord_map]
  exact endpointSlabDirectionalWord_eq_phaseOperatorWord hT coordinateDirection hf q ht x

/-- The actual recovered torus derivative words agree with the ordered lift
partials of their common smooth base velocity. -/
theorem eval_lift_recoveredSpatialWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {f : Vec3 → E} (hf : ContDiff ℝ ∞ f)
    (g : List (Fin 3) → HalfHolder A E)
    (hBase : ∀ x, HalfHolder.eval (toUnitTorus x) (g []) = f x)
    (hD : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (coordinateDirection i) (g q) (g (i :: q))) :
    ∀ q, q.length ≤ N → ∀ x, HalfHolder.eval (toUnitTorus x) (g q) = spatialDerivativeWord q f x := by
  intro q
  induction q with
  | nil => exact fun _ => hBase
  | cons i q ih =>
    intro hq x
    have hq' : q.length < N := Nat.lt_of_succ_le hq
    have hb := (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt
      (g q) (g (i :: q)) (coordinateDirection i)).mpr (hD i q hq') x
    rw [funext (ih hq'.le)] at hb
    have hs : ContDiff ℝ ∞ (spatialDerivativeWord q f) :=
      contDiff_phaseOperatorWord (fun _ => contDiff_const) hf q
    have hx := ((hs.differentiable (by simp) x).hasFDerivAt).hasLineDerivAt (coordinateDirection i)
    exact hb.unique hx

/-- Uniform weighted lift bounds also control the closed-time torus norm of
the corresponding actual derivative word. -/
theorem mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T ℓ : ℝ} (hT : 0 ≤ T) (hℓ : 0 < ℓ)
    (q : List (Fin 3)) {f : ℝ → Vec3 → E} (g : ℝ → HalfHolder A E)
    (hf : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (f t))
    (hbdd : BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
      (fun t : Icc (0 : ℝ) T => f t)))
    (hLift : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (g t) = spatialDerivativeWord q (f t) x) :
    ℓ ^ q.length * endpointClosedTimeNorm T g ≤ Real.sqrt 2 *
      sSup (hierarchyJetValues True (hierarchyLabelDirection ℓ) q (fun t : Icc (0 : ℝ) T => f t)) := by
  have hp : 0 < ℓ ^ q.length := pow_pos hℓ _
  let B := Real.sqrt 2 * sSup (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
    (fun t : Icc (0 : ℝ) T => f t))
  have hNorm : endpointClosedTimeNorm T g ≤ B / ℓ ^ q.length := by
    apply endpointClosedTimeNorm_le hT
    intro t ht
    apply (le_div_iff₀ hp).2
    rw [mul_comm]
    exact mul_norm_halfHolder_le_of_hierarchyLabelWord hℓ.le q ⟨t, ht⟩ (hf t ht) hbdd (g t)
      (hLift t ht)
  rw [mul_comm]
  exact (le_div_iff₀ hp).1 hNorm

end LiftMatching

section SortedWeights

/-- Both words in each differentiated coefficient term are sublists of the
original word. The canonical sorted multi-index family is therefore closed
under the exact Leibniz recurrence. -/
theorem endpointMixedCorrectionPairs_sublist {I : Type*} {q : List I} {p : List I × List I}
    (hp : p ∈ endpointMixedCorrectionPairs q) : p.1.Sublist q ∧ p.2.Sublist q := by
  induction q generalizing p with
  | nil => simp [endpointMixedCorrectionPairs] at hp
  | cons i q ih =>
    simp only [endpointMixedCorrectionPairs, List.mem_cons, List.mem_flatMap] at hp
    rcases hp with rfl | ⟨r, hr, hp⟩
    · exact ⟨(List.nil_sublist q).cons_cons i, (List.Sublist.refl q).cons i⟩
    · obtain ⟨h₁, h₂⟩ := ih hr
      simp only [List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨h₁.cons_cons i, h₂.cons i⟩
      · exact ⟨h₁.cons i, h₂.cons_cons i⟩

set_option maxHeartbeats 1000000 in
/-- The weighted estimate needs coefficient and forcing bounds only on the
canonical sorted words used in the finite label norm. -/
theorem endpointWeightedPhysicalMeanEstimate_sorted {I : Type*} [LinearOrder I]
    {T ℓ Ainv Mf C : ℝ} {N : ℕ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ Ainv) (hM : 0 ≤ Mf) (hC : 0 ≤ C)
    (K Ω : List I → ℝ → K½) (src : List I → ℝ → C½) (g : List I → ℝ → S)
    (hF : ∀ q, q.length ≤ N → q.Pairwise (· ≤ ·) → ℓ ^ q.length * endpointClosedTimeNorm T (src q) ≤ Mf)
    (hB : ∀ q, 1 ≤ q.length → q.length ≤ N → q.Pairwise (· ≤ ·) →
      Ainv * (ℓ ^ q.length * endpointPhysicalCoefficientWordNorm T K Ω q) ≤ C)
    (hRec : ∀ q, q.length ≤ N → q.Pairwise (· ≤ ·) → endpointClosedTimeNorm T (g q) ≤ Ainv *
      (endpointClosedTimeNorm T (src q) + ((endpointMixedCorrectionPairs q).map fun p =>
        endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)).sum)) :
    ∀ q, q.length ≤ N → q.Pairwise (· ≤ ·) → ℓ ^ q.length * endpointClosedTimeNorm T (g q) ≤
      Ainv * Mf * (1 + (2 : ℝ) ^ N * C) ^ q.length := by
  classical
  let V (q : List I) := if q.Pairwise (· ≤ ·) then endpointClosedTimeNorm T (g q) else 0
  let F (q : List I) := if q.Pairwise (· ≤ ·) then endpointClosedTimeNorm T (src q) else 0
  let B (q : List I) := if q.Pairwise (· ≤ ·) then endpointPhysicalCoefficientWordNorm T K Ω q else 0
  have hv (q : List I) : 0 ≤ V q := by
    simp only [V]
    split
    · exact endpointClosedTimeNorm_nonneg hT (g q)
    · exact le_rfl
  have hb (q : List I) : 0 ≤ B q := by
    simp only [B]
    split
    · exact mul_nonneg zero_le_two (add_nonneg (endpointClosedTimeNorm_nonneg hT (K q))
        (mul_nonneg hT (endpointClosedTimeNorm_nonneg hT (Ω q))))
    · exact le_rfl
  have hforcing (q : List I) (hq : q.length ≤ N) : ℓ ^ q.length * F q ≤ Mf := by
    by_cases hs : q.Pairwise (· ≤ ·)
    · simpa only [F, ite_eq_left hs] using hF q hq hs
    · simpa only [F, ite_eq_right hs, mul_zero] using hM
  have hcoefficient (q : List I) (hq : 1 ≤ q.length) (hqn : q.length ≤ N) :
      Ainv * (ℓ ^ q.length * B q) ≤ C := by
    by_cases hs : q.Pairwise (· ≤ ·)
    · simpa only [B, ite_eq_left hs] using hB q hq hqn hs
    · simpa only [B, ite_eq_right hs, mul_zero] using hC
  have hrec (q : List I) (hq : q.length ≤ N) : V q ≤ Ainv *
      (F q + ((endpointMixedCorrectionPairs q).map fun p => B p.1 * V p.2).sum) := by
    by_cases hs : q.Pairwise (· ≤ ·)
    · have hLists : (endpointMixedCorrectionPairs q).map (fun p => B p.1 * V p.2) =
          (endpointMixedCorrectionPairs q).map (fun p =>
            endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)) := by
        apply List.map_congr_left
        intro p hp
        obtain ⟨h₁, h₂⟩ := endpointMixedCorrectionPairs_sublist hp
        simp only [V, B, ite_eq_left (hs.sublist h₁), ite_eq_left (hs.sublist h₂)]
      simpa only [V, F, ite_eq_left hs, hLists] using hRec q hq hs
    · have hsumnonneg : 0 ≤ ((endpointMixedCorrectionPairs q).map fun p => B p.1 * V p.2).sum := by
        apply List.sum_nonneg
        intro r hr
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
        exact mul_nonneg (hb p.1) (hv p.2)
      simp only [V, F, ite_eq_right hs, zero_add]
      exact mul_nonneg hA hsumnonneg
  intro q hq hs
  have h := meanDerivativeLifting N V F B hℓ hA hM hC hv hforcing hcoefficient hrec q hq
  simpa only [V, ite_eq_left hs] using h

end SortedWeights

section PhysicalSource

private theorem endpointTorusHasSpatialDerivative_unique_values {u : Vec3} {f df dg : C½}
    (hf : endpointTorusHasSpatialDerivative u f df)
    (hg : endpointTorusHasSpatialDerivative u f dg) : df = dg := by
  apply HalfHolder.ext
  intro a
  simpa only [zero_smul, toUnitTorus_zero, add_zero] using (hf a 0).unique (hg a 0)

private theorem endpointTorusHasSpatialDerivative_neg_values {u : Vec3} {f df : C½}
    (h : endpointTorusHasSpatialDerivative u f df) : endpointTorusHasSpatialDerivative u (-f) (-df) := by
  intro a s
  have hn := (h a s).neg
  change HasDerivAt (fun r : ℝ => -(HalfHolder.eval (a + toUnitTorus (r • u)) f)) _ s at hn
  simpa only [map_neg] using hn

/-- For families of actual spatial derivatives, the integrated source identity
passes from the base fields to every derivative word. The time derivative at
an endpoint is taken within the closed slab. -/
theorem endpointSourceWords_eq_negPrimitive {I : Type*} {T : ℝ} (hT : 0 < T)
    (src force : List I → ℝ → C½) (u : I → Vec3) (N : ℕ)
    (hSrc : ∀ q : List I, q.length ≤ N → DifferentiableOn ℝ (src q) (Icc 0 T))
    (hForce : ∀ q : List I, q.length ≤ N → ContinuousOn (force q) (Icc 0 T))
    (hSrcSpace : ∀ (i : I) (q : List I), q.length < N → ∀ t ∈ Icc 0 T,
      endpointTorusHasSpatialDerivative (u i) (src q t) (src (i :: q) t))
    (hForceSpace : ∀ (i : I) (q : List I), q.length < N → ∀ t ∈ Icc 0 T,
      endpointTorusHasSpatialDerivative (u i) (force q t) (force (i :: q) t))
    (hBase : EqOn (src []) (fun t => -endpointPrimitive (force []) t) (Icc 0 T)) :
    ∀ q : List I, q.length ≤ N →
      EqOn (src q) (fun t => -endpointPrimitive (force q) t) (Icc 0 T) := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hData (q : List I) (hq : q.length ≤ N) :
      src q 0 = 0 ∧ (∀ t ∈ Icc 0 T, HasDerivWithinAt (src q) (-force q t) (Icc 0 T) t) := by
    induction q with
    | nil =>
      constructor
      · simpa only [endpointPrimitive_zero, neg_zero] using hBase h₀
      · intro t ht
        have h := (hasDerivWithinAt_endpointPrimitive_of_continuousOn (hForce [] hq) ht).neg
        exact h.congr_of_mem (fun _ hr => hBase hr) ht
    | cons i q ih =>
      have hq' : q.length < N := by
        simpa only [List.length_cons, Nat.succ_le_iff] using hq
      obtain ⟨hz, hd⟩ := ih hq'.le
      constructor
      · have hs := hSrcSpace i q hq' 0 h₀
        rw [hz] at hs
        have hzero : endpointTorusHasSpatialDerivative (u i) (0 : C½) 0 := by
          intro a s
          simpa only [map_zero] using (hasDerivAt_const s (0 : Vec3))
        exact endpointTorusHasSpatialDerivative_unique_values hs hzero
      · intro t ht
        have hcur := (hSrc (i :: q) hq t ht).hasDerivWithinAt
        have hsp := endpointTorusHasSpatialDerivative_of_hasDerivWithinAt hT ht (u i)
          (hSrcSpace i q hq') (hd t ht) hcur
        have hn := endpointTorusHasSpatialDerivative_neg_values (hForceSpace i q hq' t ht)
        have heq := endpointTorusHasSpatialDerivative_unique_values hsp hn
        rwa [heq] at hcur
  intro q hq
  obtain ⟨hz, hd⟩ := hData q hq
  have hJ (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun r => -endpointPrimitive (force q) r) (-force q t) (Icc 0 T) t :=
    (hasDerivWithinAt_endpointPrimitive_of_continuousOn (hForce q hq) ht).neg
  apply eq_of_derivWithin_eq (hSrc q hq)
    (fun t ht => (hJ t ht).differentiableWithinAt)
  · intro t ht
    have ht' := mem_Icc_of_Ico ht
    have hu := uniqueDiffOn_Icc hT t ht'
    exact ((hd t ht').derivWithin hu).trans ((hJ t ht').derivWithin hu).symm
  · rwa [endpointPrimitive_zero, neg_zero]

/-- A lifted pointwise source formula is the Banach-valued primitive formula
for the corresponding periodic half-Hölder curves. -/
theorem endpointSourceCurve_eq_negPrimitive_of_lift {T : ℝ}
    (src force : ℝ → C½) (F : ℝ → Vec3 → Vec3)
    (hForce : ContinuousOn force (Icc 0 T))
    (hForceEval : ∀ t ∈ Icc 0 T, ∀ x : Vec3, HalfHolder.eval (toUnitTorus x) (force t) = F t x)
    (hSrcEval : ∀ t ∈ Icc 0 T, ∀ x : Vec3,
      HalfHolder.eval (toUnitTorus x) (src t) = -endpointPrimitive (fun r => F r x) t) :
    EqOn src (fun t => -endpointPrimitive force t) (Icc 0 T) := by
  intro t ht
  apply HalfHolder.ext
  intro a
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
  have hInt := (hForce.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) ht.1
  rw [hSrcEval t ht x, map_neg]
  apply congrArg Neg.neg
  simp only [endpointPrimitive]
  rw [← (HalfHolder.eval (toUnitTorus x)).intervalIntegral_comp_comm hInt]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  exact (hForceEval r (Icc_subset_Icc_right ht.2 hr) x).symm

/-- A differentiated source that agrees with the negative force primitive
satisfies the same duration bound as the base word. -/
theorem endpointClosedTimeNorm_le_of_negPrimitive {T : ℝ} (hT : 0 < T) {src force : ℝ → C½}
    (hf : ContinuousOn force (Icc 0 T)) (hEq : EqOn src (fun t => -endpointPrimitive force t) (Icc 0 T)) :
    endpointClosedTimeNorm T src ≤ T * endpointClosedTimeNorm T force := by
  have hp := (contDiffOn_endpointPrimitive_succ (n := 0) hT (contDiffOn_zero.mpr hf)).continuousOn
  apply endpointClosedTimeNorm_le hT.le
  intro t ht
  rw [hEq ht, norm_neg]
  exact (norm_le_endpointClosedTimeNorm hp ht).trans (endpointClosedTimeNorm_endpointPrimitive_le hT.le hf)


/-- The physical integrated source costs the time length times the weighted
product norm of the coframe and the unintegrated forcing. -/
theorem weighted_endpointIntegratedForce_le {T ℓ : ℝ} (hT : 0 < T) (hℓ : 0 < ℓ) (N : ℕ)
    (coframe : ℝ → Vec3 → Vec3 →L[ℝ] Vec3) (force : ℝ → Vec3 → Vec3)
    (src pull : List (Fin 3) → ℝ → C½)
    (hc : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (coframe t)) (hf : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (force t))
    (hcB : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
        (fun t : Icc (0 : ℝ) T => coframe t)))
    (hfB : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
        (fun t : Icc (0 : ℝ) T => force t)))
    (hPull : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N, ContinuousOn (pull q) (Icc 0 T))
    (hEq : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      EqOn (src q) (fun t => -endpointPrimitive (pull q) t) (Icc 0 T))
    (hLift : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N, ∀ t ∈ Icc 0 T, ∀ x,
      HalfHolder.eval (toUnitTorus x) (pull q t) =
        spatialDerivativeWord q (fun y => coframe t y (force t y)) x) :
    ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      ℓ ^ q.length * endpointClosedTimeNorm T (src q) ≤ T * Real.sqrt 2 *
        ((hierarchyAdmissibleWords (Fin 3) N).card * (2 : ℝ) ^ N *
          (2 * hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) N
              (fun t : Icc (0 : ℝ) T => coframe t) *
            hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) N
              (fun t : Icc (0 : ℝ) T => force t))) := by
  let v (t : ℝ) (x : Vec3) := coframe t x (force t x)
  let dir := hierarchyLabelDirection ℓ
  have hv (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (v t) := (hc t ht).clm_apply (hf t ht)
  have hvB (p : List (Fin 3)) (hp : p ∈ hierarchyAdmissibleWords (Fin 3) N) :
      BddAbove (hierarchyJetValues True dir p (fun t : Icc (0 : ℝ) T => v t)) :=
    (hierarchyJetValues_le_of_recovered_halfHolder hT.le hℓ.le p hv (hPull p hp) (hLift p hp)).1
  intro q hq
  have hSingle : sSup (hierarchyJetValues True dir q (fun t : Icc (0 : ℝ) T => v t)) ≤
      hierarchyFiniteWordNorm True dir N (fun t : Icc (0 : ℝ) T => v t) := by
    unfold hierarchyFiniteWordNorm
    apply Finset.single_le_sum _ hq
    intro p hp
    exact le_csSup (hvB p hp) (Or.inl rfl)
  have hProd := hierarchyFiniteWordNorm_clm_apply_le True (D := dir)
    (fun _ => contDiff_const) N (fun (t : Icc (0 : ℝ) T) => hc t t.property)
    (fun (t : Icc (0 : ℝ) T) => hf t t.property) hcB hfB
  have hp := pow_nonneg hℓ.le q.length
  calc
    _ ≤ ℓ ^ q.length * (T * endpointClosedTimeNorm T (pull q)) :=
      mul_le_mul_of_nonneg_left (endpointClosedTimeNorm_le_of_negPrimitive hT (hPull q hq) (hEq q hq)) hp
    _ = T * (ℓ ^ q.length * endpointClosedTimeNorm T (pull q)) := by ring
    _ ≤ T * (Real.sqrt 2 * sSup (hierarchyJetValues True dir q (fun t : Icc (0 : ℝ) T => v t))) :=
      mul_le_mul_of_nonneg_left (mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord hT.le hℓ q
        (pull q) hv (hvB q hq) (hLift q hq)) hT.le
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hSingle.trans hProd) (Real.sqrt_nonneg 2)) hT.le

end PhysicalSource

section PhysicalOutput

/-- Multiplication by the physical coframe converts the recovered label
velocity bound into the supremum word norm of the physical mean. -/
theorem hierarchyFiniteWordNorm_physicalMeanVelocity_le {T ℓ B : ℝ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ ℓ) (N : ℕ)
    (coframe : ℝ → Vec3 → Vec3 →L[ℝ] Vec3) (v : ℝ → Vec3 → Vec3)
    (g : List (Fin 3) → ℝ → S)
    (hc : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (coframe t))
    (hv : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (v t))
    (hcB : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
        (fun t : Icc (0 : ℝ) T => coframe t)))
    (hg : ∀ q, q.length ≤ N → ContinuousOn (g q) (Icc 0 T))
    (hLift : ∀ q, q.length ≤ N → ∀ t ∈ Icc 0 T, ∀ x,
      HalfHolder.eval (toUnitTorus x) (g q t).val = spatialDerivativeWord q (v t) x)
    (hBound : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      ℓ ^ q.length * endpointClosedTimeNorm T (g q) ≤ B) :
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) N
      (fun (t : Icc (0 : ℝ) T) x => coframe t x (v t x)) ≤
      (hierarchyAdmissibleWords (Fin 3) N).card * (2 : ℝ) ^ N *
        (2 * hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) N
            (fun t : Icc (0 : ℝ) T => coframe t) *
          ((hierarchyAdmissibleWords (Fin 3) N).card * B)) := by
  let dir := hierarchyLabelDirection ℓ
  let U := fun t : Icc (0 : ℝ) T => v t
  let F := fun t : Icc (0 : ℝ) T => coframe t
  have hSubset {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (q : List (Fin 3)) (f : Icc (0 : ℝ) T → Vec3 → E) :
      hierarchyJetValues False dir q f ⊆ hierarchyJetValues True dir q f := by
    intro r hr
    rcases hr with h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact h.elim
  have hvq (q : List (Fin 3)) (hq : q ∈ hierarchyAdmissibleWords (Fin 3) N) :
      let J := hierarchyJetValues True dir q U
      BddAbove J ∧ sSup J ≤ ℓ ^ q.length * endpointClosedTimeNorm T (g q) := by
    have hn := (mem_hierarchyAdmissibleWords.mp hq).1
    exact hierarchyJetValues_le_of_recovered_halfHolder hT hℓ q hv
      (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn (hg q hn)) (hLift q hn)
  have hcF (q : List (Fin 3)) (hq : q ∈ hierarchyAdmissibleWords (Fin 3) N) :
      BddAbove (hierarchyJetValues False dir q F) := (hcB q hq).mono (hSubset q F)
  have hvF (q : List (Fin 3)) (hq : q ∈ hierarchyAdmissibleWords (Fin 3) N) :
      BddAbove (hierarchyJetValues False dir q U) := (hvq q hq).1.mono (hSubset q U)
  have hCs : hierarchyFiniteWordNorm False dir N F ≤ hierarchyFiniteWordNorm True dir N F := by
    apply Finset.sum_le_sum
    intro q hq
    exact csSup_le_csSup (hcB q hq) ⟨0, Or.inl rfl⟩ (hSubset q F)
  have hVs : hierarchyFiniteWordNorm False dir N U ≤ (hierarchyAdmissibleWords (Fin 3) N).card * B := by
    unfold hierarchyFiniteWordNorm
    calc
      _ ≤ ∑ _q ∈ hierarchyAdmissibleWords (Fin 3) N, B := by
        apply Finset.sum_le_sum
        intro q hq
        exact (csSup_le_csSup (hvq q hq).1 ⟨0, Or.inl rfl⟩ (hSubset q U)).trans
          ((hvq q hq).2.trans (hBound q hq))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hProd := hierarchyFiniteWordNorm_clm_apply_le False (D := dir) (fun _ => contDiff_const) N
    (fun t : Icc (0 : ℝ) T => hc t t.property) (fun t : Icc (0 : ℝ) T => hv t t.property) hcF hvF
  have hF₀ : 0 ≤ hierarchyFiniteWordNorm True dir N F :=
    Finset.sum_nonneg fun q hq => le_csSup (hcB q hq) (Or.inl rfl)
  have hV₀ : 0 ≤ hierarchyFiniteWordNorm False dir N U :=
    Finset.sum_nonneg fun q hq => le_csSup (hvF q hq) (Or.inl rfl)
  exact hProd.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul_of_nonneg_left hCs zero_le_two) hVs hV₀ (mul_nonneg zero_le_two hF₀))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)))

/-- The two inverse powers and the zeroth-order coefficient cost give one
fixed polynomial degree for the full recovery budget. -/
theorem endpointRecoveryBudget_scalar_le_power {Q Cs Cm Ps Pm As Am pS pM B : ℝ}
    (hQ : 1 ≤ Q) (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hPs : 0 ≤ Ps)
    (hAm : 0 ≤ Am) (hpS : 0 ≤ pS) (hpM : 0 ≤ pM) (hB : 0 ≤ B)
    (hs : As ≤ Cs * Q ^ 145) (hm : Am ≤ Cm * Q ^ 145) (hps : pS ≤ Ps) (hpm : pM ≤ Pm)
    (hb : B ≤ 6 * Q) :
    As * pS * (2 + B * (Am * pM)) ≤ (Cs * Ps * (2 + 6 * Cm * Pm)) * Q ^ 291 := by
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hS : As * pS ≤ Cs * Ps * Q ^ 145 := by
    calc
      _ ≤ (Cs * Q ^ 145) * Ps := mul_le_mul hs hps hpS (mul_nonneg hCs (pow_nonneg hQ₀ _))
      _ = _ := by ring
  have hM : Am * pM ≤ Cm * Pm * Q ^ 145 := by
    calc
      _ ≤ (Cm * Q ^ 145) * Pm := mul_le_mul hm hpm hpM (mul_nonneg hCm (pow_nonneg hQ₀ _))
      _ = _ := by ring
  have hBcost : 2 + B * (Am * pM) ≤ (2 + 6 * Cm * Pm) * Q ^ 146 := by
    calc
      _ ≤ 2 + (6 * Q) * (Cm * Pm * Q ^ 145) := add_le_add le_rfl
        (mul_le_mul hb hM (mul_nonneg hAm hpM) (mul_nonneg (by norm_num) hQ₀))
      _ = 2 + (6 * Cm * Pm) * Q ^ 146 := by rw [show Q ^ 146 = Q ^ 145 * Q from pow_succ Q 145]; ring
      _ ≤ 2 * Q ^ 146 + (6 * Cm * Pm) * Q ^ 146 :=
        add_le_add (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hQ)) le_rfl
      _ = _ := by ring
  calc
    _ ≤ (Cs * Ps * Q ^ 145) * ((2 + 6 * Cm * Pm) * Q ^ 146) :=
      mul_le_mul hS hBcost (add_nonneg zero_le_two (mul_nonneg hB (mul_nonneg hAm hpM)))
        (mul_nonneg (mul_nonneg hCs hPs) (pow_nonneg hQ₀ _))
    _ = _ := by rw [show Q ^ 291 = Q ^ 145 * Q ^ 146 from pow_add Q 145 146]; ring

end PhysicalOutput

end

end TorusEuler

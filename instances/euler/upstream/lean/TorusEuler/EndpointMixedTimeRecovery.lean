import TorusEuler.EndpointInstantaneousInverse
import TorusEuler.EndpointRecoveryAssembly
import TorusEuler.EndpointStrongWeakAgreement

/-! Recovering the pointwise time equation of Appendix A from the mixed solve. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "S" => endpointHalfHolderSolenoidal
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "timeμ" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (timeμ T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))

local instance mixedTimeSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance mixedTimeSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem ae_endpointSpatialSlice_sub_add {T : ℝ}
    (u v w : EndpointTorusL2 T) :
    ∀ᵐ t ∂timeμ T, endpointSpatialSlice (u - v + w) t =
      endpointSpatialSlice u t - endpointSpatialSlice v t + endpointSpatialSlice w t := by
  have huv := Lp.coeFn_sub u v
  have hall := Lp.coeFn_add (u - v) w
  filter_upwards [endpointSpatialSlice_apply_ae (u - v + w), endpointSpatialSlice_apply_ae u,
    endpointSpatialSlice_apply_ae v, endpointSpatialSlice_apply_ae w,
    Measure.ae_ae_of_ae_prod huv, Measure.ae_ae_of_ae_prod hall] with t h₁ hu hv hw hsub hadd
  apply Lp.ext
  filter_upwards [h₁, hu, hv, hw, hsub, hadd,
    Lp.coeFn_sub (endpointSpatialSlice u t) (endpointSpatialSlice v t),
    Lp.coeFn_add (endpointSpatialSlice u t - endpointSpatialSlice v t) (endpointSpatialSlice w t)]
    with a h₁a hua hva hwa hsuba hadda hSub hAdd
  rw [h₁a, hadda, hAdd]
  simp only [Pi.add_apply]
  rw [hsuba, hSub]
  simp only [Pi.sub_apply, hua, hva, hwa]

/-- Compatibility of the mixed coefficient in the instantaneous equation,
when the mixed and fixed-time coefficients represent the same field. -/
theorem ae_endpointMixedCoefficient_spatialSlice {T C : ℝ}
    (K : ℝ → K½) (Kjoint : ℝ × A → Vec3 →L[ℝ] Vec3) (Kmix : MixedCoefficient(T))
    (hKjoint : AEStronglyMeasurable Kjoint (endpointTorusMeasure T))
    (hJointBound : ∀ᵐ q ∂endpointTorusMeasure T, ‖Kjoint q‖ ≤ C)
    (hSame : ∀ᵐ q ∂endpointTorusMeasure T, Kjoint q = HalfHolder.eval q.2 (K q.1))
    (hMix : ∀ᵐ a ∂unitTorusMeasure, ∀ f : Paths(T),
      (fun r => HalfHolder.eval a Kmix f r) =ᵐ[timeμ T] fun r => Kjoint (r, a) (f r))
    (v : Mixed(T)) :
    ∀ᵐ t ∂timeμ T, endpointSpatialSlice (endpointMixedToJoint T (Kmix.coefficientMul v)) t =
      endpointWeakCoefficient (K t) (endpointSpatialSlice (endpointMixedToJoint T v) t) := by
  rw [endpointMixedToJoint_mul_of_action Kjoint hKjoint hJointBound Kmix hMix]
  filter_upwards [ae_endpointSpatialSlice_l2Multiplier Kjoint hKjoint hJointBound
    (endpointMixedToJoint T v), Measure.ae_ae_of_ae_prod hSame] with t hSlice hSame
  obtain ⟨hM, hB, hSlice⟩ := hSlice
  rw [hSlice]
  apply Lp.ext
  filter_upwards [endpointL2Multiplier_apply_ae (fun a => Kjoint (t, a)) hM hB
    (endpointSpatialSlice (endpointMixedToJoint T v) t),
    endpointWeakCoefficient_apply_ae (K t) (endpointSpatialSlice (endpointMixedToJoint T v) t),
    hSame] with a ha hb hc
  exact ha.trans ((congrArg (fun B : Vec3 →L[ℝ] Vec3 => B
    (endpointSpatialSlice (endpointMixedToJoint T v) t a)) hc).trans hb.symm)

set_option maxHeartbeats 2400000 in
/-- The mixed solution has a continuous spatial half-Hölder representative on
the full slab. The instantaneous equation recovers the time-independent
solenoidal constant from the mixed residual. -/
theorem exists_endpointMixedTimeRecovery {T μ L M CL : ℝ} (hT : 0 < T)
    (Kmix Ωmix : MixedCoefficient(T)) (w Fmix : Mixed(T)) (K : ℝ → K½) (F : ℝ → C½)
    (hFixed : endpointStrongMixedLeray T w = w)
    (hProjected : endpointStrongMixedLeray T
      (endpointMixedProductOperator hT.le Kmix Ωmix w + Fmix) = 0)
    (hμ : 0 < μ) (hL : 0 ≤ L) (hK : ContDiffOn ℝ 0 K (Icc 0 T))
    (hLip : ∀ t ∈ Icc 0 T, ∀ a b, ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ Icc 0 T, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (hM : ∀ t ∈ Icc 0 T, ‖(K t).val.1‖ ≤ M)
    (hF : ContinuousOn F (Icc 0 T)) (hFBound : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ CL)
    (hKSlice : ∀ᵐ t ∂timeμ T,
      endpointSpatialSlice (endpointMixedToJoint T (Kmix.coefficientMul w)) t =
        endpointWeakCoefficient (K t) (endpointSpatialSlice (endpointMixedToJoint T w) t))
    (hFSlice : ∀ᵐ t ∂timeμ T,
      endpointSpatialSlice (endpointMixedToJoint T Fmix) t = endpointHalfHolderToL2 (F t)) :
    let Jw := Ωmix.coefficientMul w
    let R := endpointMixedProductOperator hT.le Kmix Ωmix w + Fmix
    let c := endpointStrongSpatialProjection
      (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) R)
    ∃ g : ℝ → S, ContinuousOn g (Icc 0 T) ∧
      (∀ t : Icc (0 : ℝ) T,
        endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
          c + endpointStrongSpatialProjection (HalfHolder.map (endpointPrimitiveEvaluation t) Jw) -
            endpointStrongSpatialProjection (F t)) ∧
      ((fun t => endpointHalfHolderToL2 (g t).val) =ᵐ[timeμ T]
        endpointSpatialSlice (endpointMixedToJoint T w)) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (endpointPrimitive g) (g t) (Icc 0 T) t) := by
  classical
  intro Jw R c
  let P := endpointStrongSpatialProjection
  let joint := endpointMixedToJoint T
  let Ja : EndpointTorusL2 T := endpointProductPrimitive unitTorusMeasure hT.le (joint Jw)
  let ra : EndpointTorusL2 T := joint R
  have hFixedWeak : joint w ∈ endpointTorusSpace T := by
    rw [← hFixed]
    exact endpointStrongMixedLeray_mem_weak hT w
  let u : endpointTorusSpace T := ⟨joint w, hFixedWeak⟩
  have hra : ra = joint (Kmix.coefficientMul w) - Ja + joint Fmix := by
    change joint ((Kmix.coefficientMul w -
      endpointMixedIntegration hT.le (Ωmix.coefficientMul w)) + Fmix) = _
    rw [map_add, map_sub, endpointMixedToJoint_integration hT.le]
  have hrZero : endpointJointConstraintProjection T ra = 0 := by
    rw [← endpointStrongMixedLeray_agrees_L2 hT, hProjected, map_zero]
  have hrTest (z : endpointTorusSpace T) : ⟪ra, (z : EndpointTorusL2 T)⟫_ℝ = 0 := by
    let : CompleteSpace (endpointTorusSpace T) := (isClosed_endpointTorusSpace T).completeSpace_coe
    have hp : ⟪endpointJointConstraintProjection T ra, (z : EndpointTorusL2 T)⟫_ℝ =
        ⟪ra, (z : EndpointTorusL2 T)⟫_ℝ :=
      (endpointTorusSpace T).inner_orthogonalProjectionOnto_eq_of_mem_right z _
    rw [hrZero, inner_zero_left] at hp
    exact hp.symm
  let J (t : ℝ) : C½ :=
    if ht : t ∈ Icc 0 T then HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Jw else 0
  have hJ (t : Icc (0 : ℝ) T) : J t = HalfHolder.map (endpointPrimitiveEvaluation t) Jw := by
    simp only [J, dite_eq_left t.property]
  let post : (Paths(T) →L[ℝ] Vec3) →L[ℝ] (Mixed(T) →L[ℝ] C½) := HalfHolder.postcomp
  have ⟨hJc, hJB⟩ :=
    endpointMixedPrimitive_continuousOn_and_bound (T := T) (JΩ := J) post Jw hJ
  have hWeak : ∀ᵐ t ∂timeμ T,
      endpointWeakSpatialProjection (endpointWeakCoefficient (K t) (endpointSpatialSlice (joint w) t)) =
        endpointSolenoidalEmbedding (c + P (J t) - P (F t)) := by
    have hsl := ae_endpointSpatialSlice_sub_add (joint (Kmix.coefficientMul w)) Ja (joint Fmix)
    rw [← hra] at hsl
    have hmean := endpointWeakResidualProjected_eq_mean hT ra hrTest
    have hJa := endpointMixedProjectedPrimitive_compat hT.le P
      endpointStrongSpatialProjection_agrees_weak Jw
    have hma := endpointMixedResidual_projectedMean_compat hT.le P
      endpointStrongSpatialProjection_agrees_weak R
    filter_upwards [hsl, hmean, hJa, hKSlice, hFSlice] with t hsl hmean hJa hKs hFs
    obtain ⟨ht, hJa⟩ := hJa
    rw [hsl, map_add, map_sub, hKs, hJa, hFs, endpointStrongSpatialProjection_agrees_weak,
      hma] at hmean
    rw [hJ ⟨t, ht⟩, map_sub, map_add]
    let x := endpointWeakSpatialProjection
      (endpointWeakCoefficient (K t) (endpointSpatialSlice (joint w) t))
    let y := endpointSolenoidalEmbedding (P (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Jw))
    let z := endpointSolenoidalEmbedding (P (F t))
    change x - y + z = endpointSolenoidalEmbedding c at hmean
    change x = endpointSolenoidalEmbedding c + y - z
    calc
      _ = (x - y + z) + y - z := by abel
      _ = _ := by rw [hmean]
  obtain ⟨C, _, e, he, hE, hEc⟩ :=
    exists_endpointInstantaneousInverseFamily hμ hL hK hLip hPos hM
  have hBudget : 0 ≤ C * (4 + μ⁻¹ + M + L) ^ 145 := by
    exact (norm_nonneg ((e 0).symm : S →L[ℝ] S)).trans (hE 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨g, hgc, hEq, hRep, _, hStart, hFinish, hDeriv⟩ :=
    exists_endpointTorusContinuousRepresentative hT u P endpointStrongSpatialProjection_agrees_weak
      K hμ hPos e he hEc.continuousOn c hJc hF hBudget hE hJB hFBound hWeak
  refine ⟨g, hgc, ?_, hRep, hStart, hFinish, hDeriv⟩
  intro t
  rw [← he t t.property, hEq t t.property, hJ t]

end

end TorusEuler

import TorusEuler.EndpointDensity
import TorusEuler.EndpointMeanFubini
import TorusEuler.EndpointMixedEmbedding
import TorusEuler.EndpointSpaceCompatibility
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! The joint time-mean projection and its compatibility with the spatial
projection and the mixed Hölder embedding in Appendix A. -/

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "H" => Lp Vec3 2 unitTorusMeasure
local notation "τ(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "μ(" T ")" => Measure.prod (τ(T)) unitTorusMeasure
local notation "J(" T ")" => Lp Vec3 2 (μ(T))

private def jointConstantCandidate (T : ℝ) (v : H) : J(T) :=
  ((Lp.memLp v).comp_snd (τ(T))).toLp (fun q : ℝ × A => v q.2)

private theorem jointConstantCandidate_apply_ae (T : ℝ) (v : H) :
    jointConstantCandidate T v =ᵐ[μ(T)] fun q => v q.2 :=
  ((Lp.memLp v).comp_snd (τ(T))).coeFn_toLp

/-- The adjoint of partial time integration lifts a spatial field constantly in time. -/
theorem endpointTorusTimeIntegral_adjoint_apply_ae {T : ℝ} (hT : 0 ≤ T) (v : H) :
    (endpointTorusTimeIntegral hT).adjoint v =ᵐ[μ(T)] fun q => v q.2 := by
  suffices (endpointTorusTimeIntegral hT).adjoint v = jointConstantCandidate T v by
    rw [this]
    exact jointConstantCandidate_apply_ae T v
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
  have hu : Integrable u (μ(T)) := (Lp.memLp u).integrable one_le_two
  have hInner : Integrable (fun q : ℝ × A => ⟪v q.2, u q⟫_ℝ) (μ(T)) :=
    (L2.integrable_inner (jointConstantCandidate T v) u).congr
      ((jointConstantCandidate_apply_ae T v).mono fun q hq =>
        congrArg (fun y : Vec3 => ⟪y, u q⟫_ℝ) hq)
  have hTime : endpointTorusTimeIntegral hT u =ᵐ[unitTorusMeasure]
      fun a => ∫ t, u (t, a) ∂τ(T) :=
    endpointTimeIntegral_apply_ae hT u
  have hleft := integral_congr_ae (hTime.mono fun a ha =>
    congrArg (fun y : Vec3 => ⟪v a, y⟫_ℝ) ha)
  have hright := integral_congr_ae ((jointConstantCandidate_apply_ae T v).mono fun q hq =>
    congrArg (fun y : Vec3 => ⟪y, u q⟫_ℝ) hq)
  rw [hleft, hright, integral_prod_symm _ hInner]
  apply integral_congr_ae
  filter_upwards [hu.prod_left_ae] with a ha
  exact ((innerSL ℝ (v a)).integral_comp_comm ha).symm

/-- Integrating a constant-in-time lift multiplies the spatial field by the slab length. -/
theorem endpointTorusTimeIntegral_adjoint_integral {T : ℝ} (hT : 0 ≤ T) (v : H) :
    endpointTorusTimeIntegral hT ((endpointTorusTimeIntegral hT).adjoint v) = T • v := by
  let u := (endpointTorusTimeIntegral hT).adjoint v
  have hTime : endpointTorusTimeIntegral hT u =ᵐ[unitTorusMeasure]
      fun a => ∫ t, u (t, a) ∂τ(T) :=
    endpointTimeIntegral_apply_ae hT u
  have hSlice := ae_endpointTimeSlice_congr (ν := unitTorusMeasure) (T := T)
    (endpointTorusTimeIntegral_adjoint_apply_ae hT v)
  apply Lp.ext
  filter_upwards [hTime, hSlice, Lp.coeFn_smul T v] with a ht hs hsmul
  change endpointTorusTimeIntegral hT u a = (T • v) a
  rw [ht, hsmul, Pi.smul_apply, integral_congr_ae hs]
  rw [integral_const, measureReal_def, Measure.restrict_apply_univ, ← measureReal_def,
    Real.volume_real_Ioc_of_le hT, sub_zero]

/-- Time-mean removal on the joint time–torus L² space. -/
def endpointJointSubtractMean {T : ℝ} (hT : 0 ≤ T) : J(T) →L[ℝ] J(T) :=
  1 - T⁻¹ • (endpointTorusTimeIntegral hT).adjoint.comp (endpointTorusTimeIntegral hT)

theorem endpointJointSubtractMean_apply {T : ℝ} (hT : 0 ≤ T) (u : J(T)) :
    endpointJointSubtractMean hT u =
      u - T⁻¹ • ((endpointTorusTimeIntegral hT).adjoint (endpointTorusTimeIntegral hT u)) := rfl

theorem endpointTorusTimeIntegral_endpointJointSubtractMean {T : ℝ} (hT : 0 < T) (u : J(T)) :
    endpointTorusTimeIntegral hT.le (endpointJointSubtractMean hT.le u) = 0 := by
  rw [endpointJointSubtractMean_apply, map_sub, map_smul,
    endpointTorusTimeIntegral_adjoint_integral, smul_smul, inv_mul_cancel₀ hT.ne', one_smul, sub_self]

theorem endpointJointSubtractMean_isSymmetricProjection {T : ℝ} (hT : 0 < T) :
    (endpointJointSubtractMean hT.le : J(T) →ₗ[ℝ] J(T)).IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro x
    change endpointJointSubtractMean hT.le (endpointJointSubtractMean hT.le x) =
      endpointJointSubtractMean hT.le x
    rw [endpointJointSubtractMean_apply,
      endpointTorusTimeIntegral_endpointJointSubtractMean hT, map_zero, smul_zero, sub_zero]
  · intro x y
    change ⟪endpointJointSubtractMean hT.le x, y⟫_ℝ =
      ⟪x, endpointJointSubtractMean hT.le y⟫_ℝ
    rw [endpointJointSubtractMean_apply hT.le x, endpointJointSubtractMean_apply hT.le y,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem range_endpointJointSubtractMean {T : ℝ} (hT : 0 < T) :
    (endpointJointSubtractMean hT.le).range =
      (endpointTorusTimeIntegral hT.le : J(T) →ₗ[ℝ] H).ker := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact endpointTorusTimeIntegral_endpointJointSubtractMean hT u
  · intro hx
    have hx' : endpointTorusTimeIntegral hT.le x = 0 := hx
    refine ⟨x, ?_⟩
    change endpointJointSubtractMean hT.le x = x
    rw [endpointJointSubtractMean_apply, hx', map_zero, smul_zero, sub_zero]


theorem endpointJointSubtractMean_apply_ae {T : ℝ} (hT : 0 ≤ T) (u : J(T)) :
    endpointJointSubtractMean hT u =ᵐ[μ(T)]
      fun q => u q - T⁻¹ • (endpointTorusTimeIntegral hT u) q.2 := by
  rw [endpointJointSubtractMean_apply]
  let C := (endpointTorusTimeIntegral hT).adjoint (endpointTorusTimeIntegral hT u)
  filter_upwards [Lp.coeFn_sub u (T⁻¹ • C), Lp.coeFn_smul T⁻¹ C,
    endpointTorusTimeIntegral_adjoint_apply_ae hT (endpointTorusTimeIntegral hT u)] with q hq hs hc
  change (u - T⁻¹ • C) q = _
  change C q = _ at hc
  rw [hq, Pi.sub_apply, hs, Pi.smul_apply, hc]

/-- The joint spatial weak divergence constraint, before imposing the zero time mean. -/
def endpointJointSpatialSolenoidal (T : ℝ) : Submodule ℝ J(T) :=
  ⨅ η : EndpointBoundedTest ℝ, ⨅ p : EndpointSmoothPotential,
    (show J(T) →L[ℝ] ℝ from endpointTorusDivergenceTest T η p).ker

theorem isClosed_endpointJointSpatialSolenoidal (T : ℝ) :
    IsClosed (endpointJointSpatialSolenoidal T : Set J(T)) := by
  simp only [endpointJointSpatialSolenoidal, Submodule.coe_iInf]
  exact isClosed_iInter fun η => isClosed_iInter fun p =>
    (show J(T) →L[ℝ] ℝ from endpointTorusDivergenceTest T η p).isClosed_ker

theorem mem_endpointJointSpatialSolenoidal (T : ℝ) (u : J(T)) :
    u ∈ endpointJointSpatialSolenoidal T ↔
      ∀ η p, endpointTorusDivergenceTest T η p u = 0 := by
  simp only [endpointJointSpatialSolenoidal, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

theorem mem_endpointJointSpatialSolenoidal_iff_spatialSlices (T : ℝ) (u : J(T)) :
    u ∈ endpointJointSpatialSolenoidal T ↔ ∀ p : EndpointSmoothPotential,
      (fun t => ∫ a, ⟪endpointPotentialGradient p a, u (t, a)⟫_ℝ ∂unitTorusMeasure) =ᵐ[
        τ(T)] 0 := by
  rw [mem_endpointJointSpatialSolenoidal, forall_comm]
  exact forall_congr' (endpointTorusDivergenceTests_iff_ae_zero T u)

theorem endpointTorusTimeIntegral_mem_spatialSolenoidal {T : ℝ} (hT : 0 ≤ T)
    {u : J(T)} (hu : u ∈ endpointJointSpatialSolenoidal T) :
    endpointTorusTimeIntegral hT u ∈ endpointSpatialSolenoidal := by
  rw [mem_endpointSpatialSolenoidal]
  intro p
  rw [← endpointSpatialDivergenceTest_apply]
  let g := (endpointPotentialGradient p).toLp 2 unitTorusMeasure ℝ
  let one : EndpointBoundedTest ℝ := ⟨fun _ => 1, measurable_const, 1, fun _ => by simp⟩
  have hTest := (mem_endpointJointSpatialSolenoidal T u).mp hu one p
  have hTest' :=
    (endpointTorusDivergenceTest_apply T one p (show EndpointTorusL2 T from u)).symm.trans hTest
  change (∫ q, one.val q.1 * ⟪endpointPotentialGradient p q.2, u q⟫_ℝ ∂μ(T)) = 0 at hTest'
  change ⟪g, endpointTorusTimeIntegral hT u⟫_ℝ = 0
  rw [← ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  have hG := (Measure.quasiMeasurePreserving_snd (μ := τ(T)) (ν := unitTorusMeasure)).ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure (endpointPotentialGradient p))
  have hEq : (fun q : ℝ × A => ⟪(endpointTorusTimeIntegral hT).adjoint g q, u q⟫_ℝ)
      =ᵐ[μ(T)] fun q => ⟪endpointPotentialGradient p q.2, u q⟫_ℝ := by
    filter_upwards [endpointTorusTimeIntegral_adjoint_apply_ae hT g, hG] with q hAdj hq
    change g q.2 = endpointPotentialGradient p q.2 at hq
    rw [hAdj, hq]
  rw [integral_congr_ae hEq]
  simpa only [one, one_mul] using hTest'

theorem endpointTorusTimeIntegral_adjoint_mem_jointSpatialSolenoidal {T : ℝ} (hT : 0 ≤ T)
    {w : H} (hw : w ∈ endpointSpatialSolenoidal) :
    (endpointTorusTimeIntegral hT).adjoint w ∈ endpointJointSpatialSolenoidal T := by
  rw [mem_endpointJointSpatialSolenoidal_iff_spatialSlices]
  intro p
  have hSlice := Measure.ae_ae_of_ae_prod (endpointTorusTimeIntegral_adjoint_apply_ae hT w)
  filter_upwards [hSlice] with t ht
  change (∫ a, ⟪endpointPotentialGradient p a, (endpointTorusTimeIntegral hT).adjoint w (t, a)⟫_ℝ
    ∂unitTorusMeasure) = 0
  exact (integral_congr_ae (ht.mono fun a ha =>
    congrArg (fun y => ⟪endpointPotentialGradient p a, y⟫_ℝ) ha)).trans
      ((mem_endpointSpatialSolenoidal w).mp hw p)

theorem endpointJointSubtractMean_preserves_jointSpatialSolenoidal {T : ℝ} (hT : 0 ≤ T)
    {u : J(T)} (hu : u ∈ endpointJointSpatialSolenoidal T) :
    endpointJointSubtractMean hT u ∈ endpointJointSpatialSolenoidal T := by
  rw [endpointJointSubtractMean_apply]
  exact (endpointJointSpatialSolenoidal T).sub_mem hu
    ((endpointJointSpatialSolenoidal T).smul_mem T⁻¹ <|
      endpointTorusTimeIntegral_adjoint_mem_jointSpatialSolenoidal hT
        (endpointTorusTimeIntegral_mem_spatialSolenoidal hT hu))

theorem endpointTorusSpace_eq_timeKernel_inf_jointSpatialSolenoidal {T : ℝ} (hT : 0 ≤ T) :
    (show Submodule ℝ J(T) from endpointTorusSpace T) =
      (endpointTorusTimeIntegral hT : J(T) →ₗ[ℝ] H).ker ⊓ endpointJointSpatialSolenoidal T := by
  ext u
  rw [Submodule.mem_inf, LinearMap.mem_ker]
  change u ∈ endpointTorusSpace T ↔ endpointTorusTimeIntegral hT u = 0 ∧ _
  exact (mem_endpointTorusSpace_iff_slices T (show EndpointTorusL2 T from u)).trans
    (and_congr (endpointTimeIntegral_eq_zero_iff hT u).symm
      (mem_endpointJointSpatialSolenoidal_iff_spatialSlices T u).symm)

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem commute_starProjection_of_symmetric_preserves (U : Submodule ℝ E)
    [U.HasOrthogonalProjection] (Q : E →L[ℝ] E)
    (hQ : (Q : E →ₗ[ℝ] E).IsSymmetric)
    (hPres : ∀ x ∈ U, Q x ∈ U) :
    Commute U.starProjection Q := by
  show U.starProjection * Q = Q * U.starProjection
  ext x
  change U.starProjection (Q x) = Q (U.starProjection x)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hPres _ (U.starProjection_apply_mem x)) ?_
  intro w hw
  rw [← map_sub]
  change ⟪(Q : E →ₗ[ℝ] E) (x - U.starProjection x), w⟫_ℝ = 0
  rw [hQ]
  exact U.starProjection_inner_eq_zero _ _ (hPres w hw)

end


private instance endpointJointSpatialSolenoidal_hasOrthogonalProjection (T : ℝ) :
    (endpointJointSpatialSolenoidal T).HasOrthogonalProjection :=
  let : CompleteSpace (endpointJointSpatialSolenoidal T) :=
    (isClosed_endpointJointSpatialSolenoidal T).completeSpace_coe
  inferInstance

private instance endpointJointSpace_hasOrthogonalProjection (T : ℝ) :
    (show Submodule ℝ J(T) from endpointTorusSpace T).HasOrthogonalProjection :=
  let : CompleteSpace (show Submodule ℝ J(T) from endpointTorusSpace T) :=
    (isClosed_endpointTorusSpace T).completeSpace_coe
  inferInstance

theorem endpointJointSpatialProjection_commutes_subtractMean {T : ℝ} (hT : 0 < T) :
    Commute (endpointJointSpatialSolenoidal T).starProjection (endpointJointSubtractMean hT.le) :=
  commute_starProjection_of_symmetric_preserves _
    _ (endpointJointSubtractMean_isSymmetricProjection hT).isSymmetric
    (fun _ hx => endpointJointSubtractMean_preserves_jointSpatialSolenoidal hT.le hx)

/-- The orthogonal projection onto the endpoint constraints is the joint spatial
projection composed with time-mean removal. -/
theorem endpointTorusSpace_starProjection_eq_spatial_mul_subtractMean {T : ℝ} (hT : 0 < T) :
    (show Submodule ℝ J(T) from endpointTorusSpace T).starProjection =
      (endpointJointSpatialSolenoidal T).starProjection * endpointJointSubtractMean hT.le := by
  let P := (endpointJointSpatialSolenoidal T).starProjection
  let Q := endpointJointSubtractMean hT.le
  let U : Submodule ℝ J(T) := endpointTorusSpace T
  have hU : U = (endpointTorusTimeIntegral hT.le : J(T) →ₗ[ℝ] H).ker ⊓
      endpointJointSpatialSolenoidal T := endpointTorusSpace_eq_timeKernel_inf_jointSpatialSolenoidal hT.le
  have hcomm (x : J(T)) : P (Q x) = Q (P x) :=
    DFunLike.congr_fun (endpointJointSpatialProjection_commutes_subtractMean hT).eq x
  apply ContinuousLinearMap.ext
  intro x
  change U.starProjection x = P (Q x)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [hU, Submodule.mem_inf]
    refine ⟨?_, (endpointJointSpatialSolenoidal T).starProjection_apply_mem _⟩
    change endpointTorusTimeIntegral hT.le (P (Q x)) = 0
    rw [hcomm]
    exact endpointTorusTimeIntegral_endpointJointSubtractMean hT _
  · intro w hw
    rw [hU, Submodule.mem_inf, LinearMap.mem_ker] at hw
    have hP : P w = w := (endpointJointSpatialSolenoidal T).starProjection_eq_self_iff.mpr hw.2
    have hQ : Q w = w := by
      have hzero : endpointTorusTimeIntegral hT.le w = 0 := hw.1
      change endpointJointSubtractMean hT.le w = w
      rw [endpointJointSubtractMean_apply, hzero, map_zero, smul_zero, sub_zero]
    rw [inner_sub_left]
    change ⟪x, w⟫_ℝ - ⟪(endpointJointSpatialSolenoidal T).starProjection (Q x), w⟫_ℝ = 0
    rw [Submodule.inner_starProjection_left_eq_right]
    change ⟪x, w⟫_ℝ - ⟪Q x, P w⟫_ℝ = 0
    rw [hP]
    have hsym := (endpointJointSubtractMean_isSymmetricProjection hT).isSymmetric x w
    change ⟪Q x, w⟫_ℝ = ⟪x, Q w⟫_ℝ at hsym
    rw [hsym, hQ, sub_self]


private theorem endpointSubtractMean_apply_ae_mixed {T : ℝ}
    (f : Lp Vec3 2 (τ(T))) :
    endpointSubtractMean T f =ᵐ[τ(T)] fun t => f t - T⁻¹ • endpointIntegral T f := by
  rw [endpointSubtractMean_apply]
  let c := T⁻¹ • endpointIntegral T f
  have h := Lp.coeFn_sub f (Lp.const 2 (τ(T)) c)
  filter_upwards [h, Lp.coeFn_const 2 (τ(T)) c] with t ht hc
  change (f - Lp.const 2 (τ(T)) c) t = f t - c
  rw [ht, Pi.sub_apply, hc, Function.const_apply]

/-- Removing the time mean commutes with the embedding of spatial half-Hölder
fields of time paths into the joint Hilbert space. -/
theorem endpointJointSubtractMean_endpointMixedToJoint {T : ℝ} (hT : 0 ≤ T)
    (w : HalfHolder A (Lp Vec3 2 (τ(T)))) :
    endpointJointSubtractMean hT (endpointMixedToJoint T w) =
      endpointMixedToJoint T (HalfHolder.map (endpointSubtractMean T) w) := by
  let u : J(T) := endpointMixedToJoint T w
  let w' := HalfHolder.map (endpointSubtractMean T) w
  let v : J(T) := endpointMixedToJoint T w'
  change endpointJointSubtractMean hT u = v
  have hU : ∀ᵐ a ∂unitTorusMeasure, (fun t => HalfHolder.eval a w t) =ᵐ[τ(T)] fun t => u (t, a) :=
    endpointMixedToJoint_apply_ae w
  have hV : ∀ᵐ a ∂unitTorusMeasure, (fun t => HalfHolder.eval a w' t) =ᵐ[τ(T)] fun t => v (t, a) :=
    endpointMixedToJoint_apply_ae w'
  have hQ := ae_endpointTimeSlice_congr (ν := unitTorusMeasure) (T := T)
    (endpointJointSubtractMean_apply_ae hT u)
  have hJ := endpointTimeIntegral_apply_ae (ν := unitTorusMeasure) hT u
  have hSlice : ∀ᵐ a ∂unitTorusMeasure, (fun t => endpointJointSubtractMean hT u (t, a)) =ᵐ[τ(T)]
      fun t => v (t, a) := by
    filter_upwards [hU, hV, hQ, hJ] with a hu hv hq hj
    have hmean : endpointTorusTimeIntegral hT u a = endpointIntegral T (HalfHolder.eval a w) := by
      calc
        _ = ∫ t, u (t, a) ∂τ(T) := hj
        _ = _ := (integral_congr_ae hu).symm
    have hv' : (fun t => endpointSubtractMean T (HalfHolder.eval a w) t) =ᵐ[τ(T)] fun t => v (t, a) := by
      change (fun t => HalfHolder.eval a (HalfHolder.map (endpointSubtractMean T) w) t) =ᵐ[τ(T)]
        fun t => v (t, a) at hv
      simpa only [HalfHolder.eval_map] using hv
    filter_upwards [hu, hv', hq, endpointSubtractMean_apply_ae_mixed (HalfHolder.eval a w)]
      with t hui hvi hqi hpath
    exact hqi.trans (by
      rw [← hui, hmean, ← hpath]
      exact hvi)
  apply Lp.ext
  change ∀ᵐ q ∂μ(T), endpointJointSubtractMean hT u q = v q
  have hmeas : MeasurableSet {q : ℝ × A | endpointJointSubtractMean hT u q = v q} :=
    (Lp.stronglyMeasurable (endpointJointSubtractMean hT u)).measurableSet_eq_fun
      (Lp.stronglyMeasurable v)
  exact (Measure.ae_prod_iff_ae_ae hmeas).2 ((Measure.ae_ae_comm hmeas).2 hSlice)

end

end TorusEuler

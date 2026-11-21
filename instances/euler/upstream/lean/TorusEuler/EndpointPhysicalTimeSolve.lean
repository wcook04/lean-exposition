import TorusEuler.EndpointMixedSource
import TorusEuler.EndpointMixedTimeRecovery
import TorusEuler.EndpointPhysicalMixedSolve

/-! The base temporal solution for the physical endpoint coefficients. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "S" => endpointHalfHolderSolenoidal
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "Mixed(" T ")" => HalfHolder A (Path(T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (Path(T) →L[ℝ] Path(T))
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "Slab(" T ")" => (Set.prod (Icc (0 : ℝ) T) (univ : Set A))

local instance physicalTimeSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance physicalTimeSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem ae_endpointPhysicalCoefficient_spatialSlice {T C : ℝ}
    (K : ℝ → K½) (Kjoint : ℝ × A → Coefficient) (Kmix : MixedCoefficient(T))
    (hCont : ContinuousOn Kjoint Slab(T))
    (hBound : ∀ q ∈ Slab(T), ‖Kjoint q‖ ≤ C)
    (hSame : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HalfHolder.eval a (K t) = Kjoint (t, a))
    (hMix : ∀ (a : A) (v : Path(T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
      fun t => Kjoint (t, a) (v t)) (w : Mixed(T)) :
    ∀ᵐ t ∂TimeMeasure(T), endpointSpatialSlice (endpointMixedToJoint T (Kmix.coefficientMul w)) t =
      endpointWeakCoefficient (K t) (endpointSpatialSlice (endpointMixedToJoint T w) t) := by
  have hTime : ∀ᵐ q ∂endpointTorusMeasure T, q.1 ∈ Ioc (0 : ℝ) T :=
    (Measure.quasiMeasurePreserving_fst (μ := TimeMeasure(T)) (ν := unitTorusMeasure)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hSlab : ∀ᵐ q ∂endpointTorusMeasure T, q ∈ Slab(T) :=
    hTime.mono fun q hq => ⟨Ioc_subset_Icc_self hq, mem_univ q.2⟩
  have hMeas := hCont.aestronglyMeasurable_of_isCompact (μ := endpointTorusMeasure T)
    (isCompact_Icc.prod isCompact_univ) (measurableSet_Icc.prod MeasurableSet.univ)
  rw [Measure.restrict_eq_self_of_ae_mem hSlab] at hMeas
  exact ae_endpointMixedCoefficient_spatialSlice K Kjoint Kmix hMeas (hSlab.mono hBound)
    (hSlab.mono fun q hq => (hSame q.1 hq.1 q.2).symm) (ae_of_all _ hMix) w

set_option maxHeartbeats 4000000 in
/-- The physical effective coefficients with their exact half-Hölder time
representatives give a solenoidal velocity and its displacement on the closed
slab. The projected instantaneous equation uses the actual time primitive
of the vorticity term. Both endpoint conditions hold in the spatial norm. -/
theorem exists_endpointPhysicalTimeSolve {T D L B F₁ M₁ Csrc : ℝ} {n : ℕ∞}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hM₁ : 0 ≤ M₁) (hCsrc : 0 ≤ Csrc)
    (F G M Mt : ℝ × A → Coefficient)
    (cF : ContinuousOn F Slab(T)) (cM : ContinuousOn M Slab(T))
    (hF : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => F (r, a))
      ((M (t, a)).comp (F (t, a))) (Icc 0 T) t)
    (hM : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) (Icc 0 T) t)
    (hMt : ∀ a, ContinuousOn (fun t => Mt (t, a)) (Icc 0 T))
    (hGF : ∀ q ∈ Slab(T), (G q).comp (F q) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ q ∈ Slab(T), ‖G q‖ ≤ D)
    (hFbound : ∀ q ∈ Slab(T), ‖F q‖ ≤ B)
    (hMbound : ∀ q ∈ Slab(T), ‖M q‖ ≤ L)
    (hFlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖F (t, a) - F (t, b)‖ ≤ F₁ * dist a b)
    (hMlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖M (t, a) - M (t, b)‖ ≤ M₁ * dist a b)
    (hupper : ∀ q ∈ Slab(T), ∀ x : Vec3, ⟪endpointHessian (M q) (Mt q) x, x⟫_ℝ ≤ ‖x‖ ^ 2)
    (K Ω : ℝ → K½) (src : ℝ → C½)
    (hKrep : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HalfHolder.eval a (K t) = kineticForm (F (t, a)))
    (hΩrep : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, HalfHolder.eval a (Ω t) = vorticityForm (F (t, a)) (M (t, a)))
    (hKc : ContDiffOn ℝ n K (Icc 0 T)) (hΩc : ContDiffOn ℝ n Ω (Icc 0 T))
    (hSrc : ContDiffOn ℝ n src (Icc 0 T)) (hSrcBound : ∀ t ∈ Icc 0 T, ‖src t‖ ≤ Csrc) :
    ∃ (g : ℝ → S) (c : S), ContDiffOn ℝ n g (Icc 0 T) ∧
      ContDiffOn ℝ ((n : ℕ∞ω) + 1) (endpointPrimitive g) (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
        c + endpointStrongSpatialProjection
          (endpointPrimitive (fun r => (Ω r).coefficientMul (g r).val) t) -
        endpointStrongSpatialProjection (src t)) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (endpointPrimitive g) (g t) (Icc 0 T) t := by
  obtain ⟨srcMix, _, _, hSrcSlice⟩ :=
    exists_endpointMixedSource hT.le hCsrc src hSrc.continuousOn hSrcBound
  obtain ⟨_, _, hMixedSolve⟩ := exists_endpointPhysicalMixedSolve hT hT₁
  obtain ⟨Kmix, Ωmix, w, _, hKmix, hΩmix, hwFixed, hwProjected, _, _, _, _, _⟩ :=
    hMixedSolve hD hL hB hF₁ hM₁ F G M Mt cF cM hF hM hMt hGF hGbound hFbound
      hMbound hFlip hMlip hupper srcMix
  let Kjoint (q : ℝ × A) := kineticForm (F q)
  let Ωjoint (q : ℝ × A) := vorticityForm (F q) (M q)
  have cAdj : Continuous (fun P : Coefficient => P.adjoint) := ContinuousLinearMap.adjoint.continuous
  have cKjoint : ContinuousOn Kjoint Slab(T) := (cAdj.comp_continuousOn cF).clm_comp cF
  have cΩjoint : ContinuousOn Ωjoint Slab(T) := (cAdj.comp_continuousOn cF).clm_comp
    (((cAdj.comp_continuousOn cM).sub cM).clm_comp cF)
  have hKjoint (q : ℝ × A) (hq : q ∈ Slab(T)) : ‖Kjoint q‖ ≤ B ^ 2 :=
    norm_kineticForm_le (hFbound q hq)
  have hΩjoint (q : ℝ × A) (hq : q ∈ Slab(T)) : ‖Ωjoint q‖ ≤ 2 * B ^ 2 * L :=
    norm_vorticityForm_le (hFbound q hq) (hMbound q hq)
  have hKslice := ae_endpointPhysicalCoefficient_spatialSlice K Kjoint Kmix cKjoint hKjoint
    hKrep hKmix w
  have hΩslice := ae_endpointPhysicalCoefficient_spatialSlice Ω Ωjoint Ωmix cΩjoint hΩjoint
    hΩrep hΩmix w
  let μ := (D ^ 2)⁻¹
  let Lkin := 2 * B * F₁
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hμ : 0 < μ := inv_pos.mpr (pow_pos hDpos _)
  have hLkin : 0 ≤ Lkin := by dsimp only [Lkin]; positivity
  have hLip (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a b : A) :
      ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ Lkin * dist a b := by
    rw [hKrep t ht a, hKrep t ht b]
    exact norm_kineticForm_sub_le (hFbound _ ⟨ht, mem_univ a⟩) (hFbound _ ⟨ht, mem_univ b⟩)
      (hFlip t ht a b)
  have hPos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : A) (z : Vec3) :
      μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) z, z⟫_ℝ := by
    rw [hKrep t ht a]
    exact kineticForm_elliptic hDpos (hGF _ ⟨ht, mem_univ a⟩) (hGbound _ ⟨ht, mem_univ a⟩) z
  have hSup (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖(K t).val.1‖ ≤ B ^ 2 := by
    refine (BoundedContinuousFunction.norm_le (sq_nonneg B)).mpr (fun a => ?_)
    change ‖HalfHolder.eval a (K t)‖ ≤ B ^ 2
    rw [hKrep t ht a]
    exact hKjoint (t, a) ⟨ht, mem_univ a⟩
  obtain ⟨g, hg, hEq, hRep, hStart, hFinish, hDeriv⟩ :=
    exists_endpointMixedTimeRecovery hT Kmix Ωmix w srcMix K src hwFixed hwProjected
      hμ hLkin (contDiffOn_zero.mpr hKc.continuousOn) hLip hPos hSup hSrc.continuousOn hSrcBound
      hKslice hSrcSlice
  let Jw := Ωmix.coefficientMul w
  let c := endpointStrongSpatialProjection
    (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩)
      (endpointMixedProductOperator hT.le Kmix Ωmix w + srcMix))
  let Ωg (r : ℝ) := (Ω r).coefficientMul (g r).val
  have hΩg : ContinuousOn Ωg (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul hΩc).continuousOn.clm_apply
      (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg)
  have hΩrepJoint : ∀ᵐ t ∂TimeMeasure(T),
      endpointHalfHolderToL2 (Ωg t) = endpointSpatialSlice (endpointMixedToJoint T Jw) t := by
    filter_upwards [hRep, hΩslice] with t hRep hΩt
    change endpointHalfHolderToL2 ((Ω t).coefficientMul (g t).val) = _
    rw [endpointHalfHolderToL2_coefficientMul, hRep]
    exact hΩt.symm
  have hΩpath := ae_endpointTimeSlice_of_continuous_spatialSlice hT.le
    (endpointMixedToJoint T Jw) hΩg hΩrepJoint
  have hΩmatch : ∀ᵐ a ∂unitTorusMeasure,
      (fun r => HalfHolder.eval a Jw r) =ᵐ[TimeMeasure(T)] fun r => HalfHolder.eval a (Ωg r) := by
    filter_upwards [endpointMixedToJoint_apply_ae Jw, hΩpath] with a ha hb
    exact ha.trans hb.symm
  have hPrimitive (t : Icc (0 : ℝ) T) :
      HalfHolder.map (endpointPrimitiveEvaluation t) Jw = endpointPrimitive Ωg t :=
    endpointMixedPrimitive_eq_endpointPrimitive Jw hΩg hΩmatch t
  have hEq' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
        c + endpointStrongSpatialProjection (endpointPrimitive Ωg t) -
          endpointStrongSpatialProjection (src t) := by
    have h := hEq ⟨t, ht⟩
    change endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
      c + endpointStrongSpatialProjection (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Jw) -
        endpointStrongSpatialProjection (src t) at h
    rw [hPrimitive ⟨t, ht⟩] at h
    exact h
  obtain ⟨_, _, e, he, _, _⟩ := exists_endpointInstantaneousInverseFamily hμ hLkin hKc hLip hPos hSup
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  let Ωs (t : ℝ) : S →L[ℝ] C½ := (Ω t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL
  have hΩs : ContDiffOn ℝ n Ωs (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul hΩc).clm_comp contDiffOn_const
  have hec := contDiffOn_endpointCompressedCoefficient hKc endpointStrongSpatialProjection he
  have hEqEquiv (t : ℝ) (ht : t ∈ Icc 0 T) :
      e t (g t) = c + endpointStrongSpatialProjection (endpointPrimitive (fun r => Ωs r (g r)) t) -
        endpointStrongSpatialProjection (src t) :=
    (he t ht (g t)).trans (hEq' t ht)
  have hSmooth : ContDiffOn ℝ n g (Icc 0 T) ∧
      ContDiffOn ℝ ((n : ℕ∞ω) + 1) (endpointPrimitive g) (Icc 0 T) := by
    cases n using ENat.recTopCoe with
    | top =>
        have h := contDiffOn_endpointVelocity_and_displacement_of_integrated hT
          endpointStrongSpatialProjection c hec hΩs hSrc hg hEqEquiv
        have hinfty : (∞ : ℕ∞ω) + 1 = ∞ := rfl
        rwa [hinfty]
    | coe m =>
        have h := contDiffOn_endpointVelocity_of_integrated (n := m) hT
          endpointStrongSpatialProjection c hec hΩs hSrc hg hEqEquiv
        exact ⟨h, contDiffOn_endpointPrimitive_succ hT h⟩
  exact ⟨g, c, hSmooth.1, hSmooth.2, hEq', hStart, hFinish, hDeriv⟩

section Pressure

open ContinuousLinearMap

local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T

/-- The residual of the integrated physical equation after the solenoidal constant
has been removed, as a time curve of continuous periodic fields. -/
def endpointPhysicalIntegratedResidual
    (K Ω : ℝ → K½) (L : ℝ → C½) (g : ℝ → S) (c : S) : ℝ → C(A, Vec3) :=
  fun t => endpointHalfHolderToContinuous
    ((K t).coefficientMul (g t : C½) -
      endpointPrimitive (fun r => (Ω r).coefficientMul (g r : C½)) t + L t - (c : C½))

/-- The differentiated physical residual whose negative is the momentum pressure gradient. -/
def endpointPhysicalMomentumResidual
    (K Ω : K½) (g : S) (dK : K½) (dg : S) (dL : C½) : C(A, Vec3) :=
  endpointHalfHolderToContinuous
    (dK.coefficientMul (g : C½) + K.coefficientMul (dg : C½) -
      Ω.coefficientMul (g : C½) + dL)

/-- Differentiation on the closed slab retains the exact instantaneous integrand
from the primitive, including the one-sided derivatives at both endpoints. -/
theorem hasDerivWithinAt_endpointPhysicalIntegratedResidual
    {T t : ℝ} (ht : t ∈ TimeSlab(T)) (c : S)
    {K Ω : ℝ → K½} {L : ℝ → C½} {g : ℝ → S}
    {dK : K½} {dg : S} {dL : C½}
    (hK : HasDerivWithinAt K dK TimeSlab(T) t)
    (hg : HasDerivWithinAt g dg TimeSlab(T) t)
    (hL : HasDerivWithinAt L dL TimeSlab(T) t)
    (hΩ : ContinuousOn Ω TimeSlab(T)) (hgc : ContinuousOn g TimeSlab(T)) :
    HasDerivWithinAt (endpointPhysicalIntegratedResidual K Ω L g c)
      (endpointPhysicalMomentumResidual (K t) (Ω t) (g t) dK dg dL) TimeSlab(T) t := by
  let B : K½ →L[ℝ] (C½ →L[ℝ] C½) := HalfHolder.coefficientMulL
  have hB : HasFDerivAt (⇑B) B (K t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := K½) (F := C½ →L[ℝ] C½) B
  have hKg : HasDerivWithinAt (fun r => (K r).coefficientMul) dK.coefficientMul TimeSlab(T) t := by
    change HasDerivWithinAt ((⇑B) ∘ K) (B dK) TimeSlab(T) t
    exact HasFDerivAt.comp_hasDerivWithinAt (E := C½ →L[ℝ] C½) (F := K½) t hB hK
  have hgv : HasDerivWithinAt (fun r => (g r : C½)) (dg : C½) TimeSlab(T) t :=
    endpointHalfHolderSolenoidal.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t hg
  have hΩg : ContinuousOn (fun r => (Ω r).coefficientMul (g r : C½)) TimeSlab(T) :=
    (B.continuous.comp_continuousOn hΩ).clm_apply
      (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hgc)
  have hJ := hasDerivWithinAt_endpointPrimitive_of_continuousOn hΩg ht
  have hR := (((hKg.clm_apply hgv).sub hJ).add hL).sub_const (c : C½)
  exact endpointHalfHolderToContinuous.hasFDerivAt.comp_hasDerivWithinAt t hR

/-- The projected physical equation gives a periodic mean-zero momentum pressure
from any supplied slab derivatives of the three factor curves. -/
theorem exists_endpointPhysicalMomentumPressure_of_derivatives
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ TimeSlab(T))
    (P : C½ →L[ℝ] S) (c : S)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    {K Ω : ℝ → K½} {L : ℝ → C½} {g : ℝ → S}
    (hK : ContinuousOn K TimeSlab(T)) (hΩ : ContinuousOn Ω TimeSlab(T))
    (hL : ContinuousOn L TimeSlab(T)) (hg : ContinuousOn g TimeSlab(T))
    (hEq : ∀ r ∈ TimeSlab(T), P ((K r).coefficientMul (g r : C½)) =
      c + P (endpointPrimitive (fun s => (Ω s).coefficientMul (g s : C½)) r) - P (L r))
    {dK : K½} {dg : S} {dL : C½}
    (hdK : HasDerivWithinAt K dK TimeSlab(T) t)
    (hdg : HasDerivWithinAt g dg TimeSlab(T) t)
    (hdL : HasDerivWithinAt L dL TimeSlab(T) t) :
    let G := endpointPhysicalIntegratedResidual K Ω L g c
    let dG := endpointPhysicalMomentumResidual (K t) (Ω t) (g t) dK dg dL
    HasDerivWithinAt G dG TimeSlab(T) t ∧
      ∃ q : Vec3 → ℝ, SpatiallyPeriodic q ∧ (∫ x in centeredCell, q x) = 0 ∧
        (∀ x, HasGradientAt q (-(dG (toUnitTorus x))) x) ∧
        ∀ x, HasDerivWithinAt (fun r => G r (toUnitTorus x)) (-(gradient q x)) TimeSlab(T) t := by
  intro G dG
  have h := contDiffOn_endpointIntegratedPressureResidual (n := 0) hT P c hP
    (contDiffOn_zero.mpr hK) (contDiffOn_zero.mpr hΩ)
    (contDiffOn_zero.mpr hL) (contDiffOn_zero.mpr hg) hEq
  have hD : HasDerivWithinAt G dG TimeSlab(T) t :=
    hasDerivWithinAt_endpointPhysicalIntegratedResidual ht c hdK hdg hdL hΩ hg
  exact ⟨hD, exists_endpointMomentumPressure_of_projection_eq_zero hT ht hD h.2⟩

/-- Every time in the closed slab has a periodic mean-zero momentum pressure
from the time derivative of the physical projected equation. -/
theorem exists_endpointPhysicalMomentumPressure
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ TimeSlab(T))
    (P : C½ →L[ℝ] S) (c : S)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    {K Ω : ℝ → K½} {L : ℝ → C½} {g : ℝ → S}
    (hK : ContDiffOn ℝ 1 K TimeSlab(T)) (hΩ : ContinuousOn Ω TimeSlab(T))
    (hL : ContDiffOn ℝ 1 L TimeSlab(T)) (hg : ContDiffOn ℝ 1 g TimeSlab(T))
    (hEq : ∀ r ∈ TimeSlab(T), P ((K r).coefficientMul (g r : C½)) =
      c + P (endpointPrimitive (fun s => (Ω s).coefficientMul (g s : C½)) r) - P (L r)) :
    let G := endpointPhysicalIntegratedResidual K Ω L g c
    let dG := endpointPhysicalMomentumResidual (K t) (Ω t) (g t)
      (derivWithin K TimeSlab(T) t) (derivWithin g TimeSlab(T) t) (derivWithin L TimeSlab(T) t)
    HasDerivWithinAt G dG TimeSlab(T) t ∧
      ∃ q : Vec3 → ℝ, SpatiallyPeriodic q ∧ (∫ x in centeredCell, q x) = 0 ∧
        (∀ x, HasGradientAt q (-(dG (toUnitTorus x))) x) ∧
        ∀ x, HasDerivWithinAt (fun r => G r (toUnitTorus x)) (-(gradient q x)) TimeSlab(T) t :=
  exists_endpointPhysicalMomentumPressure_of_derivatives hT ht P c hP hK.continuousOn hΩ
    hL.continuousOn hg.continuousOn hEq
    (hK.differentiableOn_one t ht).hasDerivWithinAt
    (hg.differentiableOn_one t ht).hasDerivWithinAt
    (hL.differentiableOn_one t ht).hasDerivWithinAt

set_option maxHeartbeats 1000000 in
/-- The exact kinetic and vorticity coefficients turn the differentiated residual
into the pulled-back momentum equation at every label. The source can be any
time curve with a prescribed derivative at the time in question. -/
theorem exists_endpointPhysicalPulledBackMomentumPressure
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ TimeSlab(T))
    (P : C½ →L[ℝ] S) (c : S)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    {K Ω : ℝ → K½} {L : ℝ → C½} {g : ℝ → S}
    (hK : ContinuousOn K TimeSlab(T)) (hΩ : ContinuousOn Ω TimeSlab(T))
    (hL : ContinuousOn L TimeSlab(T)) (hg : ContinuousOn g TimeSlab(T))
    (hEq : ∀ r ∈ TimeSlab(T), P ((K r).coefficientMul (g r : C½)) =
      c + P (endpointPrimitive (fun s => (Ω s).coefficientMul (g s : C½)) r) - P (L r))
    {dK : K½} {dg : S} {dL : C½}
    (hdK : HasDerivWithinAt K dK TimeSlab(T) t)
    (hdg : HasDerivWithinAt g dg TimeSlab(T) t)
    (hdL : HasDerivWithinAt L dL TimeSlab(T) t)
    (F M : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hKeval : ∀ r ∈ TimeSlab(T), ∀ a, HalfHolder.eval a (K r) = kineticForm (F (r, a)))
    (hΩeval : ∀ a, HalfHolder.eval a (Ω t) = vorticityForm (F (t, a)) (M (t, a)))
    (hF : ∀ a, HasDerivWithinAt (fun r => F (r, a))
      ((M (t, a)).comp (F (t, a))) TimeSlab(T) t) :
    ∃ q : Vec3 → ℝ, SpatiallyPeriodic q ∧ (∫ x in centeredCell, q x) = 0 ∧
      (∀ x, HasGradientAt q (-(endpointPhysicalMomentumResidual (K t) (Ω t) (g t) dK dg dL
        (toUnitTorus x))) x) ∧
      ∀ x, let a := toUnitTorus x
        kineticForm (F (t, a)) (HalfHolder.eval a (dg : C½)) + gradient q x =
          -HalfHolder.eval a dL -
            (2 : ℝ) • (F (t, a)).adjoint (M (t, a) (F (t, a) (HalfHolder.eval a (g t : C½)))) := by
  obtain ⟨_, q, hqper, hqmean, hqgrad, _⟩ := exists_endpointPhysicalMomentumPressure_of_derivatives
    hT ht P c hP hK hΩ hL hg hEq hdK hdg hdL
  refine ⟨q, hqper, hqmean, hqgrad, fun x => ?_⟩
  intro a
  have hEval : HasDerivWithinAt (fun r => HalfHolder.eval a (K r)) (HalfHolder.eval a dK) TimeSlab(T) t :=
    (HalfHolder.eval a).hasFDerivAt.comp_hasDerivWithinAt t hdK
  have hD := hEval.congr (fun r hr => (hKeval r hr a).symm) (hKeval t ht a).symm
  have hu := uniqueDiffOn_Icc hT t ht
  have hExact := (hD.derivWithin hu).symm.trans
    ((hasDerivWithinAt_kineticForm (hF a)).derivWithin hu)
  rw [(hqgrad x).gradient]
  change _ + -(HalfHolder.eval a (dK.coefficientMul (g t : C½) +
    (K t).coefficientMul (dg : C½) - (Ω t).coefficientMul (g t : C½) + dL)) = _
  simp only [map_add, map_sub, HalfHolder.eval_coefficientMul, hKeval t ht a, hΩeval a,
    hExact, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply]
  abel


end Pressure

end

end TorusEuler

import TorusEuler.PaperMeanStatements
import TorusEuler.EndpointPhysicalJetData
import TorusEuler.PeriodicLerayHigherJets

/-! The endpoint inverse in Theorem A.1 on a normalized time interval. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "Path" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "TM" => volume.restrict (Ioc (0 : ℝ) 1)
local notation "I" => Icc (0 : ℝ) 1
local notation "LSlab" => Set.prod (Icc (0 : ℝ) 1) (univ : Set Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "V½" => HalfHolder A Vec3
local notation "KMix" => HalfHolder A (Path →L[ℝ] Path)
local notation "P" => endpointStrongSpatialProjection

local instance : NormedAddCommGroup S := inferInstance
local instance : NormedSpace ℝ S := inferInstance

/-- The coefficient norm bound supplied by one value and one spatial
derivative bound on the periodic lift. -/
def EndpointCoefficientC1Bound (K : ℝ → K½) (C₀ C₁ : ℝ) : Prop :=
  0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ContinuousOn K I ∧
  ∀ t ∈ I,
    let k := fun x => HalfHolder.eval (toUnitTorus x) (K t)
    Differentiable ℝ k ∧ ∀ x, ‖k x‖ ≤ C₀ ∧ ‖fderiv ℝ k x‖ ≤ C₁

/-- The zero-trace Sobolev test path is represented by the primitive of
its mean-zero square-integrable derivative. -/
def EndpointSobolevEnergyBound (K Ω : ℝ → K½) (μ : ℝ) : Prop :=
  ∀ a (v : Path), endpointIntegral 1 v = 0 →
    μ * ‖v‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1,
      (⟪HalfHolder.eval a (K t) (v t), v t⟫_ℝ +
       ⟪HalfHolder.eval a (Ω t) (v t), endpointPrimitive v t⟫_ℝ)

set_option maxHeartbeats 1800000 in
/-- Integration by parts identifies the mixed compression energy with
the Sobolev quadratic form in (A.2). -/
theorem endpointMixedPathCoefficient_inner_eq_sobolevEnergy
    (K Ω : ℝ → K½) (Kmix Ωmix : KMix) (a : A) (v : Path)
    (hv : endpointIntegral 1 v = 0)
    (hK : (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TM]
      fun t => HalfHolder.eval a (K t) (v t))
    (hΩ : (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[TM]
      fun t => HalfHolder.eval a (Ω t) (v t)) :
    ⟪HalfHolder.eval a (endpointMixedPathCoefficient zero_le_one Kmix Ωmix) v, v⟫_ℝ =
      ∫ t in (0 : ℝ)..1,
        (⟪HalfHolder.eval a (K t) (v t), v t⟫_ℝ +
         ⟪HalfHolder.eval a (Ω t) (v t), endpointPrimitive v t⟫_ℝ) := by
  rw [endpointMixedPathCoefficient_eval, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, endpointPrimitiveLp_inner_eq_neg_inner zero_le_one _ _ hv, sub_neg_eq_add]
  let Jv := endpointPrimitiveLp zero_le_one v
  let Kv := HalfHolder.eval a Kmix v
  let Ωv := HalfHolder.eval a Ωmix v
  change ⟪Kv, v⟫_ℝ + ⟪Ωv, Jv⟫_ℝ = _
  rw [L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner Kv v)
    (L2.integrable_inner Ωv Jv), intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [hK, hΩ, endpointPrimitiveLp_apply_ae zero_le_one v] with t hk hω hj
  change ⟪Kv t, v t⟫_ℝ + ⟪Ωv t, Jv t⟫_ℝ = _
  rw [show Kv t = _ from hk, show Ωv t = _ from hω, show Jv t = _ from hj]

private theorem appendixCoefficient_caps {K : ℝ → K½} {C₀ C₁ : ℝ}
    (h : EndpointCoefficientC1Bound K C₀ C₁) :
    (∀ t ∈ I, ‖K t‖ ≤ C₀ + 2 * C₁) ∧
    ∀ t ∈ I, ∀ a b : A, ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ 2 * C₁ * dist a b := by
  exact endpointHalfHolderCaps_of_lift_gradient (T := 1) h.1 h.2.1 K
    (fun t x => HalfHolder.eval (toUnitTorus x) (K t)) (fun _ _ _ => rfl)
    (fun t ht => (h.2.2.2 t ht).1)
    (fun t ht x => ((h.2.2.2 t ht).2 x).1)
    (fun t ht x => ((h.2.2.2 t ht).2 x).2)

private theorem integratedMomentAgreement {v : ℝ → S} {Ω Ω' : ℝ → K½}
    (hΩ : EqOn Ω' Ω I) {t : ℝ} (ht : t ∈ I) :
    endpointPrimitive (fun r => (Ω' r).coefficientMul (v r).val) t =
      endpointPrimitive (fun r => (Ω r).coefficientMul (v r).val) t := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.1]
  intro r hr
  change (Ω' r).coefficientMul (v r).val = (Ω r).coefficientMul (v r).val
  rw [hΩ ⟨hr.1, hr.2.trans ht.2⟩]

set_option maxHeartbeats 4800000 in
/-- Smooth coefficients and forcing give a jointly smooth integrated
solution on the exact normalized closed interval. -/
theorem exists_paperA1_smoothSolution {K Ω : ℝ → K½} {src : ℝ → V½}
    {κ μ K₀ K₁ Ω₀ Ω₁ : ℝ} (hκ : 0 < κ) (hμ : 0 < μ)
    (hK : EndpointCoefficientC1Bound K K₀ K₁) (hΩ : EndpointCoefficientC1Bound Ω Ω₀ Ω₁)
    (hPos : ∀ t ∈ I, ∀ a v, κ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (hEnergy : EndpointSobolevEnergyBound K Ω μ)
    (hsK : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (K z.1)) LSlab)
    (hsΩ : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (Ω z.1)) LSlab)
    (hsL : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (src z.1)) LSlab) :
    ∃ s : PaperMeanIntegratedSolution 1 K Ω src,
      ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity s.velocity)) LSlab := by
  have hper (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : ℝ → HalfHolder A E) (t : ℝ) :
      SpatiallyPeriodic (fun x => HalfHolder.eval (toUnitTorus x) (f t)) := by
    intro k x
    change HalfHolder.eval (toUnitTorus (x + latticeVector k)) (f t) = _
    rw [(toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩]
  obtain ⟨Jk⟩ := exists_endpointSlabHalfHolderJets zero_lt_one coordinateDirection _ hsK
    (fun t _ => hper _ K t)
  obtain ⟨Jω⟩ := exists_endpointSlabHalfHolderJets zero_lt_one coordinateDirection _ hsΩ
    (fun t _ => hper _ Ω t)
  obtain ⟨Jl⟩ := exists_endpointSlabHalfHolderJets zero_lt_one coordinateDirection _ hsL
    (fun t _ => hper _ src t)
  have hEq (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : ℝ → HalfHolder A E)
      (J : EndpointSlabHalfHolderJets 1 coordinateDirection
        (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (f z.1))) :
      EqOn (J.curve []) f I := by
    intro t ht
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact J.eval_lift [] t ht x
  have hKeq := hEq _ K Jk
  have hΩeq := hEq _ Ω Jω
  have hLeq := hEq _ src Jl
  obtain ⟨Kmix, hKa, hKd⟩ := exists_endpointMixedCoefficient_jets Jk
  obtain ⟨Ωmix, hΩa, hΩd⟩ := exists_endpointMixedCoefficient_jets Jω
  obtain ⟨Lmix, hLa, hLd⟩ := exists_endpointMixedSource_jets zero_le_one Jl
  have hKl := (appendixCoefficient_caps hK).2
  have hΩl := (appendixCoefficient_caps hΩ).2
  have hkL : 0 ≤ 2 * K₁ := mul_nonneg zero_le_two hK.2.1
  have hωL : 0 ≤ 2 * Ω₁ := mul_nonneg zero_le_two hΩ.2.1
  have hKlip t (ht : t ∈ I) a b :
      ‖HalfHolder.eval a (Jk.curve [] t) - HalfHolder.eval b (Jk.curve [] t)‖ ≤
        2 * K₁ * dist a b := by rw [hKeq ht]; exact hKl t ht a b
  have hΩlip t (ht : t ∈ I) a b :
      ‖HalfHolder.eval a (Jω.curve [] t) - HalfHolder.eval b (Jω.curve [] t)‖ ≤
        2 * Ω₁ * dist a b := by rw [hΩeq ht]; exact hΩl t ht a b
  have hKbound t (ht : t ∈ I) : ‖(Jk.curve [] t).val.1‖ ≤ K₀ + 2 * K₁ := by
    rw [hKeq ht]
    exact (norm_fst_le (K t).val).trans ((appendixCoefficient_caps hK).1 t ht)
  have hKpos t (ht : t ∈ I) a v :
      κ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (Jk.curve [] t) v, v⟫_ℝ := by
    rw [hKeq ht]
    exact hPos t ht a v
  have hLip := norm_endpointMixedPathCoefficient_sub_le zero_le_one (Kmix []) (Ωmix [])
    (norm_endpointMixedCoefficient_sub_le_of_timeSlices hkL (Kmix []) (Jk.curve [])
      hKlip (hKa []))
    (norm_endpointMixedCoefficient_sub_le_of_timeSlices hωL (Ωmix []) (Jω.curve [])
      hΩlip (hΩa []))
  have hA (kin : ℝ → K½) (c : KMix) (z : ℝ → K½)
      (hz : EqOn z kin I) (a : A) (v : Path)
      (hc : (fun t => HalfHolder.eval a c v t) =ᵐ[TM]
        fun t => HalfHolder.eval a (z t) (v t)) :
      (fun t => HalfHolder.eval a c v t) =ᵐ[TM]
        fun t => HalfHolder.eval a (kin t) (v t) := by
    filter_upwards [hc, ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr hmem
    change HalfHolder.eval a c v r = _ at hr ⊢
    rw [hr, hz (Ioc_subset_Icc_self hmem)]
  have hMixPos a v (hv : endpointIntegral 1 v = 0) :
      μ * ‖v‖ ^ 2 ≤
        ⟪HalfHolder.eval a (endpointMixedPathCoefficient zero_le_one (Kmix []) (Ωmix [])) v, v⟫_ℝ := by
    rw [endpointMixedPathCoefficient_inner_eq_sobolevEnergy K Ω _ _ a v hv
      (hA K _ _ hKeq a v (hKa [] a v)) (hA Ω _ _ hΩeq a v (hΩa [] a v))]
    exact hEnergy a v hv
  obtain ⟨g, c, hg, hJoint, hProj, _, hEnd⟩ :=
    exists_endpointJointVelocity_of_matchedSpatialData zero_lt_one Kmix Ωmix Lmix
      Jk.curve Jω.curve Jl.curve Jk.smooth Jω.smooth Jl.smooth
      (fun q => ae_of_all _ (hLa q)) (fun q => ae_of_all _ (hKa q))
      (fun q => ae_of_all _ (hΩa q)) hKd hΩd hLd
      hκ hkL hKlip hKpos hKbound hμ (add_nonneg hkL (mul_nonneg zero_le_one hωL)) hLip hMixPos
  refine ⟨⟨g, c, hg.continuousOn, hEnd, ?_⟩, hJoint⟩
  intro t ht
  specialize hProj t ht
  rw [hKeq ht, hLeq ht, integratedMomentAgreement hΩeq ht] at hProj
  simp only [paperMeanIntegratedMomentum, map_add, map_sub, hProj]
  abel

private theorem paperA1_smoothData_conclusions
    {K Ω : ℝ → K½} {src : ℝ → V½} (s : PaperMeanIntegratedSolution 1 K Ω src)
    (hΩc : ContinuousOn Ω I) (G : ℝ → V½) (hG : ∀ t ∈ I, paperMeanIntegratedMomentum K Ω src s.velocity t =
      (s.constant : V½) + G t)
    (hJoint : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity s.velocity)) LSlab)
    (hsK : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (K z.1)) LSlab)
    (hsΩ : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (Ω z.1)) LSlab)
    (hsL : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (src z.1)) LSlab) :
    ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity (endpointPrimitive s.velocity))) LSlab ∧
    ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) s.constant.val) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (G z.1)) LSlab := by
  let v := endpointPhysicalLabelVelocity s.velocity
  let omegaField (z : ℝ × Vec3) := HalfHolder.eval (toUnitTorus z.2) (Ω z.1)
  let ωv (t : ℝ) (x : Vec3) := omegaField (t, x) (v t x)
  have hωv : ContDiffOn ℝ ∞ (Function.uncurry ωv) LSlab := hsΩ.clm_apply hJoint
  have hPrim := contDiffOn_endpointPhysicalJointPrimitive zero_lt_one hJoint
  have hΩPrim := contDiffOn_endpointPhysicalJointPrimitive zero_lt_one hωv
  let r (z : ℝ × Vec3) := HalfHolder.eval (toUnitTorus z.2)
    (paperMeanIntegratedMomentum K Ω src s.velocity z.1)
  have hΩE (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x)
        (endpointPrimitive (fun r => (Ω r).coefficientMul (s.velocity r).val) t) =
        endpointPrimitive (fun r => ωv r x) t := by
    have hCont : ContinuousOn (fun r => (Ω r).coefficientMul (s.velocity r).val) I := by
      exact (HalfHolder.coefficientMulL.continuous.comp_continuousOn hΩc).clm_apply
        (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn s.continuous)
    have hi : IntervalIntegrable (fun r => (Ω r).coefficientMul (s.velocity r).val) volume 0 t :=
      (hCont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    simpa only [endpointPrimitive, HalfHolder.eval_coefficientMul, ωv, omegaField, v, endpointPhysicalLabelVelocity]
      using ((HalfHolder.eval (toUnitTorus x)).intervalIntegral_comp_comm hi).symm
  have hR : ContDiffOn ℝ ∞ r LSlab := by
    refine (((hsK.clm_apply hJoint).sub hΩPrim).add hsL).congr ?_
    intro z hz
    simp only [r, paperMeanIntegratedMomentum, map_add, map_sub, HalfHolder.eval_coefficientMul, hΩE _ hz.1]
    rfl
  have hc0 : P (paperMeanIntegratedMomentum K Ω src s.velocity 0) = s.constant :=
    s.projected 0 ⟨le_rfl, zero_le_one⟩
  have hcSlice : ContDiff ℝ ∞ (fun x => r (0, x)) :=
    contDiffOn_univ.mp (hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨⟨le_rfl, zero_le_one⟩, mem_univ x⟩))
  have hc : ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) s.constant.val) := by
    rw [← hc0]
    let f0 := paperMeanIntegratedMomentum K Ω src s.velocity 0
    change ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray f0))
    rw [← periodicLerayHolderLift_pullback f0]
    apply contDiff_infty.mpr
    intro n
    have hPer : SpatiallyPeriodic (fun x => r (0, x)) := by
      intro k x
      exact congrArg (fun a => HalfHolder.eval a (paperMeanIntegratedMomentum K Ω src s.velocity 0))
        ((toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩)
    exact (spatialHolderHalf_periodicLerayHolderLift hPer
      (spatialHolderHalf_of_contDiff_periodic hcSlice hPer n)).1.1
  refine ⟨?_, hc, ?_⟩
  · refine hPrim.congr ?_
    intro z hz
    let ev := (HalfHolder.eval (toUnitTorus z.2)).comp endpointHalfHolderSolenoidal.subtypeL
    let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
    have hi : IntervalIntegrable s.velocity volume 0 z.1 :=
      (s.continuous.mono (Icc_subset_Icc_right hz.1.2)).intervalIntegrable_of_Icc hz.1.1
    exact (ev.intervalIntegral_comp_comm hi).symm
  · refine (hR.sub (hc.comp contDiff_snd).contDiffOn).congr ?_
    intro z hz
    have h := congrArg (HalfHolder.eval (toUnitTorus z.2)) (hG z.1 hz.1)
    rw [map_add] at h
    dsimp only [r, Function.comp_apply]
    rw [h, add_sub_cancel_left]

end

end TorusEuler

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "Path" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "I" => Icc (0 : ℝ) 1
local notation "LSlab" => Set.prod (Icc (0 : ℝ) 1) (univ : Set Vec3)
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "V½" => HalfHolder A Vec3

local instance : NormedAddCommGroup endpointHalfHolderSolenoidal := inferInstance
local instance : NormedSpace ℝ endpointHalfHolderSolenoidal := inferInstance

set_option maxHeartbeats 5500000 in
/-- Theorem A.1. The integrated spatially solenoidal velocity on
`[0,1]` gives the displacement with both zero traces and a unique
time-independent solenoidal constant and pressure gradient. Smooth
data give jointly smooth conclusions on the same closed slab. -/
theorem paperTheoremA1 :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K Ω : ℝ → K½) (src : ℝ → V½) {κ μ K₀ K₁ Ω₀ Ω₁ : ℝ},
        0 < κ → 0 < μ →
        EndpointCoefficientC1Bound K K₀ K₁ → EndpointCoefficientC1Bound Ω Ω₀ Ω₁ →
        (∀ t ∈ I, ∀ a v, κ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ) →
        EndpointSobolevEnergyBound K Ω μ → ContinuousOn src I →
        ∃ (s : PaperMeanIntegratedSolution 1 K Ω src) (φ : Pressure) (G : ℝ → V½),
          ContDiffOn ℝ 1 (endpointPrimitive s.velocity) I ∧
          endpointPrimitive s.velocity 0 = 0 ∧
          (∀ t ∈ I, HasDerivWithinAt (endpointPrimitive s.velocity) (s.velocity t) I t) ∧
          endpointClosedTimeNorm 1 s.velocity ≤
            C * (2 + κ⁻¹ + μ⁻¹ + K₀ + K₁ + Ω₀ + Ω₁) ^ (291 : ℕ) * endpointClosedTimeNorm 1 src ∧
          ContinuousOn G I ∧
          (∀ t ∈ I, SpatiallyPeriodic (φ t) ∧ (∫ x in centeredCell, φ t x) = 0 ∧
            (∀ x, HasGradientAt (φ t) (HalfHolder.eval (toUnitTorus x) (G t)) x) ∧
            paperMeanIntegratedMomentum K Ω src s.velocity t = (s.constant : V½) + G t) ∧
          (∀ (other : PaperMeanIntegratedSolution 1 K Ω src) (G' : ℝ → V½),
            (∀ t ∈ I, paperMeanIntegratedMomentum K Ω src other.velocity t = (other.constant : V½) + G' t) →
            EqOn other.velocity s.velocity I ∧
            EqOn (endpointPrimitive other.velocity) (endpointPrimitive s.velocity) I ∧
            other.constant = s.constant ∧ EqOn G' G I) ∧
          (ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (K z.1)) LSlab →
            ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (Ω z.1)) LSlab →
            ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (src z.1)) LSlab →
            ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity (endpointPrimitive s.velocity))) LSlab ∧
            ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) s.constant.val) ∧
            ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (G z.1)) LSlab) := by
  obtain ⟨C, hC, hInv⟩ := paperMeanIntegratedInverse_of_coercivity
  refine ⟨C * (4 : ℝ) ^ (291 : ℕ), by positivity, ?_⟩
  intro K Ω src κ μ K₀ K₁ Ω₀ Ω₁ hκ hμ hK hΩ hPos hEnergy hL
  have hKc : ContinuousOn K I := hK.2.2.1
  have hΩc : ContinuousOn Ω I := hΩ.2.2.1
  obtain ⟨hKn, hKl⟩ := appendixCoefficient_caps hK
  obtain ⟨hΩn, hΩl⟩ := appendixCoefficient_caps hΩ
  have hK₀ := hK.1
  have hK₁ := hK.2.1
  have hΩ₀ := hΩ.1
  have hΩ₁ := hΩ.2.1
  have hKn₀ : 0 ≤ K₀ + 2 * K₁ := by positivity
  have hΩn₀ : 0 ≤ Ω₀ + 2 * Ω₁ := by positivity
  obtain ⟨Kmix, _, hKa⟩ := exists_endpointMixedCoefficient_of_timeCurve hKn₀ K hKc hKn
  obtain ⟨Ωmix, _, hΩa⟩ := exists_endpointMixedCoefficient_of_timeCurve hΩn₀ Ω hΩc hΩn
  have hmixed (a : A) (v : Path) (hv : endpointIntegral 1 v = 0) :
      μ * ‖v‖ ^ 2 ≤
        ⟪HalfHolder.eval a (endpointMixedPathCoefficient zero_le_one Kmix Ωmix) v, v⟫_ℝ := by
    rw [endpointMixedPathCoefficient_inner_eq_sobolevEnergy K Ω Kmix Ωmix a v hv (hKa a v) (hΩa a v)]
    exact hEnergy a v hv
  obtain ⟨_, hSolve⟩ := hInv (T := 1) zero_lt_one le_rfl hκ hμ hKn₀ hΩn₀
    (by positivity : 0 ≤ 2 * K₁) (by positivity : 0 ≤ 2 * Ω₁) K Ω Kmix Ωmix
    hKc hΩc hKn hΩn hKl hΩl hKa hΩa hPos hmixed
  obtain ⟨s, hDisplacement, hStart, hDeriv, hBound, hUnique⟩ := hSolve src hL
  obtain ⟨φ, G, hGcont, hG⟩ := s.exists_potential hKc hΩc hL
  have hScale : 4 + κ⁻¹ + μ⁻¹ + (K₀ + 2 * K₁) + (Ω₀ + 2 * Ω₁) + 2 * K₁ + 2 * Ω₁ ≤
      4 * (2 + κ⁻¹ + μ⁻¹ + K₀ + K₁ + Ω₀ + Ω₁) := by
    linarith only [hK₀, hK₁, hΩ₀, hΩ₁, inv_nonneg.mpr hκ.le, inv_nonneg.mpr hμ.le]
  have hSrcNorm : 0 ≤ endpointClosedTimeNorm 1 src := by
    have h0 := norm_le_endpointClosedTimeNorm hL ⟨le_rfl, zero_le_one⟩
    exact (norm_nonneg _).trans h0
  have hFinalNorm := hBound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hScale 291) hC) hSrcNorm)
  refine ⟨s, φ, G, hDisplacement, hStart, hDeriv, ?_, hGcont, hG, ?_, ?_⟩
  · simpa only [mul_pow, mul_assoc] using hFinalNorm
  · intro other G' hG'
    obtain ⟨hEq, hc⟩ := hUnique other
    refine ⟨hEq, ?_, hc, ?_⟩
    · intro t ht
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      exact fun r hr => hEq ⟨hr.1, hr.2.trans ht.2⟩
    · intro t ht
      have hEqM : paperMeanIntegratedMomentum K Ω src other.velocity t =
          paperMeanIntegratedMomentum K Ω src s.velocity t := by
        unfold paperMeanIntegratedMomentum
        rw [hEq ht]
        congr 2
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ht.1]
        intro r hr
        change (Ω r).coefficientMul (other.velocity r).val = (Ω r).coefficientMul (s.velocity r).val
        rw [hEq ⟨hr.1, hr.2.trans ht.2⟩]
      have h := (hG' t ht).symm.trans (hEqM.trans (hG t ht).2.2.2)
      rw [hc] at h
      exact add_left_cancel h
  · intro hsK hsΩ hsL
    obtain ⟨s', hs'⟩ := exists_paperA1_smoothSolution hκ hμ hK hΩ hPos hEnergy hsK hsΩ hsL
    have hEq := (hUnique s').1
    have hJoint : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity s.velocity)) LSlab := by
      exact hs'.congr fun z hz => by
        change HalfHolder.eval (toUnitTorus z.2) (s.velocity z.1).val =
          HalfHolder.eval (toUnitTorus z.2) (s'.velocity z.1).val
        rw [hEq hz.1]
    exact paperA1_smoothData_conclusions s hΩc G (fun t ht => (hG t ht).2.2.2) hJoint hsK hsΩ hsL

end

end TorusEuler

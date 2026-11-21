import TorusEuler.EndpointPhysicalTimeSolve
import TorusEuler.EndpointJointHaarRegularity
import TorusEuler.EndpointJointWordRegularity
import TorusEuler.EndpointPhysicalJetData
import TorusEuler.EndpointSmoothSlices
import TorusEuler.EulerLimitClosure
import TorusEuler.OscillatoryJointRegularity
import TorusEuler.Piola

/-! The physical mean momentum and endpoint constraints on the closed slab. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => (Set.prod (TimeSlab(T)) (univ : Set Vec3))

local instance physicalMeanSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance physicalMeanSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- The periodic velocity represented by the recovered spatial half-Hölder curve. -/
def endpointPhysicalLabelVelocity (g : ℝ → S) : Velocity :=
  fun t x => HalfHolder.eval (toUnitTorus x) (g t).val

private theorem endpointPhysicalLabelVelocity_periodic (g : ℝ → S) (t : ℝ) :
    SpatiallyPeriodic (endpointPhysicalLabelVelocity g t) := by
  intro n x
  unfold endpointPhysicalLabelVelocity
  rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]

/-- The actual label derivative of the recovered solenoidal field has zero trace. -/
theorem divergence_endpointPhysicalLabelVelocity {T : ℝ} (g : ℝ → S)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LiftSlab(T))
    {t : ℝ} (ht : t ∈ TimeSlab(T)) (x : Vec3) :
    divergence (endpointPhysicalLabelVelocity g t) x = 0 := by
  have hSlice : ContDiff ℝ ∞ (endpointPhysicalLabelVelocity g t) := by
    apply contDiffOn_univ.mp
    exact hg.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y _ => ⟨ht, mem_univ y⟩)
  exact ((endpointTorusGradientPairing_iff_divergence_free hSlice (fun _ => rfl)).mp
    ((mem_endpointHalfHolderSolenoidal (g t).val).mp (g t).property)) x

private theorem hasDerivWithinAt_endpointPhysicalLabelVelocity {T t : ℝ}
    {g : ℝ → S} {dg : S} (h : HasDerivWithinAt g dg TimeSlab(T) t) (x : Vec3) :
    HasDerivWithinAt (fun r => endpointPhysicalLabelVelocity g r x)
      (HalfHolder.eval (toUnitTorus x) dg.val) TimeSlab(T) t := by
  let L := (HalfHolder.eval (toUnitTorus x)).comp endpointHalfHolderSolenoidal.subtypeL
  exact L.hasFDerivAt.comp_hasDerivWithinAt t h

private theorem hasDerivWithinAt_time_slice_of_joint {T t : ℝ} {v : Velocity}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T))
    (ht : t ∈ TimeSlab(T)) (x : Vec3) :
    HasDerivWithinAt (fun r => v r x)
      (fderivWithin ℝ (Function.uncurry v) LiftSlab(T) (t, x) (1, 0)) TimeSlab(T) t := by
  have hline : HasDerivWithinAt (fun r : ℝ => (r, x)) (1, 0) TimeSlab(T) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have htx : (t, x) ∈ LiftSlab(T) := ⟨ht, mem_univ x⟩
  have h := (hv.differentiableOn (by simp) (t, x) htx).hasFDerivWithinAt
  have hmap : MapsTo (fun r : ℝ => (r, x)) TimeSlab(T) LiftSlab(T) := fun _ hr => ⟨hr, mem_univ x⟩
  exact h.comp_hasDerivWithinAt t hline hmap

private theorem contDiffOn_jointTimeDerivative {T : ℝ} (hT : 0 < T) {v : Velocity}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 =>
      fderivWithin ℝ (Function.uncurry v) LiftSlab(T) z (1, 0)) LiftSlab(T) :=
  (hv.fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) (by simp)).clm_apply contDiffOn_const

private def endpointMeanUnitIntegral : C(Icc (0 : ℝ) 1, Vec3) →L[ℝ] Vec3 := by
  let π := projIcc (0 : ℝ) 1 zero_le_one
  let L : C(Icc (0 : ℝ) 1, Vec3) →ₗ[ℝ] Vec3 :=
    { toFun := fun f => phaseMean (f ∘ π)
      map_add' := fun f g => phaseMean_add (f.continuous.comp continuous_projIcc)
        (g.continuous.comp continuous_projIcc)
      map_smul' := fun c f => phaseMean_const_smul c (f ∘ π) }
  exact LinearMap.mkContinuous L 1 fun f => by
    rw [one_mul]
    exact norm_phaseMean_le (f := f ∘ π) fun s _ => f.norm_coe_le_norm (π s)

set_option maxHeartbeats 800000 in
/-- A time primitive of a jointly smooth periodic lift is jointly smooth on
the same closed slab. The integration path stays inside the slab. -/
theorem contDiffOn_endpointPhysicalJointPrimitive {T : ℝ} (hT : 0 < T) {v : Velocity}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => endpointPrimitive (fun r => v r z.2) z.1) LiftSlab(T) := by
  let Fθ (s : ℝ) (z : ℝ × Vec3) := v (z.1 * s) z.2
  have hc : ContDiffOn ℝ ∞ (Function.uncurry Fθ) (Icc (0 : ℝ) 1 ×ˢ LiftSlab(T)) := by
    apply hv.comp ((contDiffOn_snd.fst.mul contDiffOn_fst).prodMk contDiffOn_snd.snd)
    intro z hz
    refine ⟨⟨mul_nonneg hz.2.1.1 hz.1.1, ?_⟩, mem_univ _⟩
    exact (mul_le_of_le_one_right hz.2.1.1 hz.1.2).trans hz.2.1.2
  have hCurry := contDiffOn_currySlabWithin zero_lt_one ((convex_Icc 0 T).prod convex_univ)
    ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) hc
  refine (contDiffOn_fst.smul (endpointMeanUnitIntegral.contDiff.comp_contDiffOn hCurry)).congr ?_
  intro z hz
  have hInt : endpointMeanUnitIntegral (currySlabWithin hc.continuousOn z) = phaseMean (fun s => Fθ s z) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro s hs
    change currySlabWithin hc.continuousOn z (projIcc 0 1 zero_le_one s) = Fθ s z
    rw [currySlabWithin_apply hc.continuousOn hz, projIcc_of_mem zero_le_one hs]
  change endpointPrimitive (fun r => v r z.2) z.1 =
    z.1 • endpointMeanUnitIntegral (currySlabWithin hc.continuousOn z)
  rw [hInt]
  simpa only [endpointPrimitive, phaseMean, Fθ, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (fun r => v r z.2) z.1).symm

private theorem endpointPhysicalPrimitive_eval {T : ℝ} {g : ℝ → S}
    (hg : ContinuousOn g TimeSlab(T)) {t : ℝ} (ht : t ∈ TimeSlab(T)) (x : Vec3) :
    endpointPrimitive (fun r => endpointPhysicalLabelVelocity g r x) t =
      HalfHolder.eval (toUnitTorus x) (endpointPrimitive g t).val := by
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  let L := (HalfHolder.eval (toUnitTorus x)).comp endpointHalfHolderSolenoidal.subtypeL
  have hInt := (hg.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1
  exact L.intervalIntegral_comp_comm hInt

/-- Smoothness up to both time endpoints follows by applying the half-open
normalization theorem in forward and reversed time. -/
theorem contDiffOn_closedSlab_pressure_of_joint_contDiff_gradient
    {T : ℝ} (hT : 0 < T) {p : Pressure} {g : Velocity}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hP : ∀ t ∈ Icc 0 T, ∀ x, HasGradientAt (p t) (g t x) x)
    (hMean : ∀ t ∈ Icc 0 T, (∫ x in centeredCell, p t x) = 0) :
    ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  let B : Set (ℝ × Vec3) := Icc 0 T ×ˢ univ
  let Bₗ : Set (ℝ × Vec3) := Ico 0 T ×ˢ univ
  let Bᵣ : Set (ℝ × Vec3) := Ioc 0 T ×ˢ univ
  let R (z : ℝ × Vec3) : ℝ × Vec3 := (T - z.1, z.2)
  let gR : Velocity := fun t => g (T - t)
  let pR : Pressure := fun t => p (T - t)
  have hRc : ContDiff ℝ ∞ R := (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hleft : ContDiffOn ℝ ∞ (Function.uncurry p) Bₗ :=
    contDiffOn_pressure_of_joint_contDiff_gradient (hg.mono (prod_mono_left Ico_subset_Icc_self))
      (fun t ht => hP t (Ico_subset_Icc_self ht)) (fun t ht => hMean t (Ico_subset_Icc_self ht))
  have hRclosed : ∀ t ∈ Ico (0 : ℝ) T, T - t ∈ Icc 0 T := by
    intro t ht
    exact ⟨sub_nonneg.mpr ht.2.le, sub_le_self _ ht.1⟩
  have hgR : ContDiffOn ℝ ∞ (Function.uncurry gR) Bₗ :=
    hg.comp hRc.contDiffOn (fun z hz => ⟨hRclosed z.1 hz.1, mem_univ _⟩)
  have hpR : ContDiffOn ℝ ∞ (Function.uncurry pR) Bₗ :=
    contDiffOn_pressure_of_joint_contDiff_gradient hgR (fun t ht => hP (T - t) (hRclosed t ht))
      (fun t ht => hMean (T - t) (hRclosed t ht))
  have hright : ContDiffOn ℝ ∞ (Function.uncurry p) Bᵣ := by
    refine (hpR.comp hRc.contDiffOn (fun z hz => ?_)).congr (fun z _ => ?_)
    · exact ⟨⟨sub_nonneg.mpr hz.1.2, sub_lt_self T hz.1.1⟩, mem_univ _⟩
    · change p z.1 z.2 = p (T - (T - z.1)) z.2
      rw [sub_sub_cancel]
  intro z hz
  by_cases hzt : z.1 < T
  · have hzL : z ∈ Bₗ := ⟨⟨hz.1.1, hzt⟩, mem_univ _⟩
    have hlt : (fun w : ℝ × Vec3 => w.1) ⁻¹' Iio T ∈ 𝓝 z :=
      continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hzt)
    have hnbh : Bₗ ∈ 𝓝[B] z := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlt] with w hw hwt
      exact ⟨⟨hw.1.1, hwt⟩, hw.2⟩
    exact (hleft z hzL).mono_of_mem_nhdsWithin hnbh
  · have hzT : z.1 = T := le_antisymm hz.1.2 (le_of_not_gt hzt)
    have hzpos : 0 < z.1 := by simpa only [hzT] using hT
    have hzR : z ∈ Bᵣ := ⟨⟨hzpos, hz.1.2⟩, mem_univ _⟩
    have hpos : (fun w : ℝ × Vec3 => w.1) ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 z :=
      continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hzpos)
    have hnbh : Bᵣ ∈ 𝓝[B] z := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hpos] with w hw hwpos
      exact ⟨⟨hwpos, hw.1.2⟩, hw.2⟩
    exact (hright z hzR).mono_of_mem_nhdsWithin hnbh

/-- Periodic mean-zero slice potentials of a jointly smooth gradient select
a jointly smooth periodic normalized pressure on the closed time slab. -/
theorem exists_closedSlab_jointContDiff_periodicPressure_of_gradients
    {T : ℝ} (hT : 0 < T) {g : Velocity}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hSlice : ∀ t ∈ Icc 0 T, ∃ p : Vec3 → ℝ,
      SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
        ∀ x, HasGradientAt p (g t x) x) :
    ∃ p : Pressure, ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t) ∧ (∫ x in centeredCell, p t x) = 0 ∧
        ∀ x, HasGradientAt (p t) (g t x) x := by
  classical
  have hP (t : ℝ) : ∃ p : Vec3 → ℝ, t ∈ Icc 0 T →
      SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
        ∀ x, HasGradientAt p (g t x) x := by
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨p, hp⟩ := hSlice t ht
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun h => (ht h).elim⟩
  choose p hp using hP
  exact ⟨p, contDiffOn_closedSlab_pressure_of_joint_contDiff_gradient hT hg
    (fun t ht => (hp t ht).2.2) (fun t ht => (hp t ht).2.1), hp⟩


set_option maxHeartbeats 3200000 in
/-- The jointly smooth recovered label velocity solves the forced mean
equation for the actual coframe and the jointly smooth normalized pressure.
The displacement is the zero-ended primitive of the label velocity. -/
theorem exists_endpointPhysicalMeanFromJointVelocity {T : ℝ} (hT : 0 < T)
    (F G M : ℝ × A → Coefficient) (force : Velocity)
    (hFc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hMc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hF : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => F (r, a)) ((M (t, a)).comp (F (t, a))) TimeSlab(T) t)
    (hGF : ∀ (a : A) t, t ∈ TimeSlab(T) → (G (t, a)).comp (F (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (hFG : ∀ (a : A) t, t ∈ TimeSlab(T) → (F (t, a)).comp (G (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (K Ω : ℝ → K½) (src : ℝ → C½) (g : ℝ → S) (c : S)
    (hK : ContDiffOn ℝ 1 K TimeSlab(T)) (hΩ : ContinuousOn Ω TimeSlab(T))
    (hSrc : ContDiffOn ℝ 1 src TimeSlab(T)) (hg : ContDiffOn ℝ 1 g TimeSlab(T))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LiftSlab(T))
    (hKrep : ∀ t ∈ TimeSlab(T), ∀ a, HalfHolder.eval a (K t) = kineticForm (F (t, a)))
    (hΩrep : ∀ t ∈ TimeSlab(T), ∀ a, HalfHolder.eval a (Ω t) = vorticityForm (F (t, a)) (M (t, a)))
    (hSrcDeriv : ∀ t ∈ TimeSlab(T), ∀ x,
      HalfHolder.eval (toUnitTorus x) (derivWithin src TimeSlab(T) t) =
        -(F (t, toUnitTorus x)).adjoint (force t x))
    (hEq : ∀ t ∈ TimeSlab(T), endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
      c + endpointStrongSpatialProjection
        (endpointPrimitive (fun r => (Ω r).coefficientMul (g r).val) t) -
      endpointStrongSpatialProjection (src t))
    (hStart : endpointPrimitive g 0 = 0) (hFinish : endpointPrimitive g T = 0) :
    ∃ (Z B : Velocity) (q : Pressure),
      ContDiffOn ℝ ∞ (Function.uncurry Z) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry B) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (Z t) ∧ SpatiallyPeriodic (B t) ∧
        SpatiallyPeriodic (q t) ∧ (∫ x in centeredCell, q t x) = 0) ∧
      Z 0 = 0 ∧ Z T = 0 ∧
      (∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (endpointPhysicalLabelVelocity g t x) ∧
        HasDerivWithinAt (fun r => Z r x) (endpointPhysicalLabelVelocity g t x) TimeSlab(T) t ∧
        divergence (endpointPhysicalLabelVelocity g t) x = 0 ∧
        derivWithin (fun r => B r x) TimeSlab(T) t + M (t, toUnitTorus x) (B t x) +
          (G (t, toUnitTorus x)).adjoint (gradient (q t) x) = force t x) := by
  let v := endpointPhysicalLabelVelocity g
  let Z (t : ℝ) (x : Vec3) := endpointPrimitive (fun r => v r x) t
  let B (t : ℝ) (x : Vec3) := F (t, toUnitTorus x) (v t x)
  let dv (t : ℝ) (x : Vec3) := fderivWithin ℝ (Function.uncurry v) LiftSlab(T) (t, x) (1, 0)
  let Q (t : ℝ) (x : Vec3) :=
    (F (t, toUnitTorus x)).adjoint (force t x) -
      (2 : ℝ) • (F (t, toUnitTorus x)).adjoint (M (t, toUnitTorus x) (B t x)) -
      kineticForm (F (t, toUnitTorus x)) (dv t x)
  have hZ := contDiffOn_endpointPhysicalJointPrimitive hT hV
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B) LiftSlab(T) := hFc.clm_apply hV
  have hdc : ContDiffOn ℝ ∞ (Function.uncurry dv) LiftSlab(T) :=
    contDiffOn_jointTimeDerivative hT hV
  let Adj : Coefficient ≃ₗᵢ[ℝ] Coefficient := ContinuousLinearMap.adjoint
  have hAdj : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (F (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hFc
  have hQc : ContDiffOn ℝ ∞ (Function.uncurry Q) LiftSlab(T) :=
    ((hAdj.clm_apply hforce).sub ((contDiffOn_const (c := (2 : ℝ))).smul (hAdj.clm_apply (hMc.clm_apply hB)))).sub
      ((hAdj.clm_comp hFc).clm_apply hdc)
  have hdv (t : ℝ) (ht : t ∈ TimeSlab(T)) (x : Vec3) :
      HasDerivWithinAt (fun r => v r x) (dv t x) TimeSlab(T) t :=
    hasDerivWithinAt_time_slice_of_joint hV ht x
  obtain ⟨q, hq, hqSlice⟩ :=
    exists_closedSlab_jointContDiff_periodicPressure_of_gradients hT hQc (by
      intro t ht
      have hdg := (hg.differentiableOn_one t ht).hasDerivWithinAt
      obtain ⟨p, hpPer, hpMean, hpGrad, hpMomentum⟩ :=
        exists_endpointPhysicalPulledBackMomentumPressure hT ht endpointStrongSpatialProjection c
          endpointStrongSpatialProjection_agrees_weak hK.continuousOn hΩ hSrc.continuousOn hg.continuousOn hEq
          (hK.differentiableOn_one t ht).hasDerivWithinAt hdg
          (hSrc.differentiableOn_one t ht).hasDerivWithinAt F M hKrep (hΩrep t ht) (fun a => hF a t ht)
      refine ⟨p, hpPer, hpMean, fun x => ?_⟩
      have hvel := ((hasDerivWithinAt_endpointPhysicalLabelVelocity hdg x).derivWithin
        (uniqueDiffOn_Icc hT t ht)).symm.trans ((hdv t ht x).derivWithin (uniqueDiffOn_Icc hT t ht))
      have hm := hpMomentum x
      dsimp only at hm
      rw [hvel, hSrcDeriv t ht x, neg_neg] at hm
      have hgrad : gradient p x = Q t x := by
        dsimp only [Q, B, v, endpointPhysicalLabelVelocity]
        rw [← hm]
        abel
      rw [← hgrad, (hpGrad x).gradient]
      exact hpGrad x)
  refine ⟨Z, B, q, hZ, hB, hq, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, ?_, (hqSlice t ht).1, (hqSlice t ht).2.1⟩
    · intro n x
      dsimp only [Z]
      congr 1
      funext r
      exact endpointPhysicalLabelVelocity_periodic g r n x
    · intro n x
      dsimp only [B, v]
      rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩, endpointPhysicalLabelVelocity_periodic g t n x]
  · funext x
    change endpointPrimitive (fun r => endpointPhysicalLabelVelocity g r x) 0 = 0
    exact (endpointPhysicalPrimitive_eval hg.continuousOn (left_mem_Icc.mpr hT.le) x).trans
      ((congrArg (fun z : S => HalfHolder.eval (toUnitTorus x) z.val) hStart).trans (map_zero _))
  · funext x
    change endpointPrimitive (fun r => endpointPhysicalLabelVelocity g r x) T = 0
    exact (endpointPhysicalPrimitive_eval hg.continuousOn (right_mem_Icc.mpr hT.le) x).trans
      ((congrArg (fun z : S => HalfHolder.eval (toUnitTorus x) z.val) hFinish).trans (map_zero _))
  · intro t ht x
    refine ⟨rfl, ?_, divergence_endpointPhysicalLabelVelocity g hV ht x, ?_⟩
    · apply hasDerivWithinAt_endpointPrimitive_of_continuousOn _ ht
      exact hV.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, mem_univ x⟩)
    let a := toUnitTorus x
    have hP : (F (t, a)).adjoint ((G (t, a)).adjoint (gradient (q t) x)) = gradient (q t) x := by
      change ((F (t, a)).adjoint.comp (G (t, a)).adjoint) (gradient (q t) x) = _
      rw [← ContinuousLinearMap.adjoint_comp, hGF a t ht, ContinuousLinearMap.adjoint_id,
        ContinuousLinearMap.id_apply]
    have hLabelMomentum : kineticForm (F (t, a)) (dv t x) +
        (F (t, a)).adjoint ((G (t, a)).adjoint (gradient (q t) x)) =
        (F (t, a)).adjoint (force t x) -
          (2 : ℝ) • (F (t, a)).adjoint (M (t, a) (F (t, a) (v t x))) := by
      rw [hP, ((hqSlice t ht).2.2 x).gradient]
      dsimp only [Q, B, a]
      abel
    obtain ⟨dB, hdB, hMomentum⟩ := eulerianMomentum_of_strongLabelMomentum
      (F := fun r => F (r, a)) (M := fun r => M (r, a))
      (v := fun r => v r x) (I := TimeSlab(T)) (t := t) (G := G (t, a))
      (dv := dv t x) (f := force t x) (gradq := (G (t, a)).adjoint (gradient (q t) x))
      (hFG a t ht) (hF a t ht) (hdv t ht x) hLabelMomentum
    have hD : HasDerivWithinAt (fun r => B r x) dB TimeSlab(T) t := hdB
    rw [hD.derivWithin (uniqueDiffOn_Icc hT t ht)]
    exact hMomentum

section JointRecovery

local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "Mixed(" T ")" => HalfHolder A (Path(T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (Path(T) →L[ℝ] Path(T))

private theorem endpointContinuousSpatialRepresentatives_eqOn {T : ℝ} (hT : 0 < T)
    (w : Mixed(T)) {f g : ℝ → C½}
    (hf : ContinuousOn f TimeSlab(T)) (hg : ContinuousOn g TimeSlab(T))
    (hrf : ∀ᵐ t ∂TimeMeasure(T), endpointHalfHolderToL2 (f t) =
      endpointSpatialSlice (endpointMixedToJoint T w) t)
    (hrg : ∀ᵐ t ∂TimeMeasure(T), endpointHalfHolderToL2 (g t) =
      endpointSpatialSlice (endpointMixedToJoint T w) t) :
    EqOn f g TimeSlab(T) := by
  have hE : EqOn (endpointPrimitive f) (endpointPrimitive g) TimeSlab(T) := by
    intro t ht
    exact (endpointMixedPrimitive_eq_of_spatialRepresentative hT.le w hf hrf ⟨t, ht⟩).symm.trans
      (endpointMixedPrimitive_eq_of_spatialRepresentative hT.le w hg hrg ⟨t, ht⟩)
  intro t ht
  have hdF := hasDerivWithinAt_endpointPrimitive_of_continuousOn hf ht
  have hdG := hasDerivWithinAt_endpointPrimitive_of_continuousOn hg ht
  have hc := hdF.congr (fun r hr => (hE hr).symm) (hE ht).symm
  exact (hc.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (hdG.derivWithin (uniqueDiffOn_Icc hT t ht))

/-- A finite family of exact derivatives of the same recovered label velocity. -/
structure EndpointMeanRecoveredWords {T : ℝ} (hT : 0 < T)
    (Kmix Ωmix : List (Fin 3) → MixedCoefficient(T)) (srcMix : List (Fin 3) → Mixed(T))
    (g : ℝ → S) (N : ℕ) where
  mixed : List (Fin 3) → Mixed(T)
  curve : List (Fin 3) → ℝ → S
  base_eq : EqOn (curve []) g TimeSlab(T)
  smooth : ∀ q, q.length ≤ N → ContDiffOn ℝ ∞ (curve q) TimeSlab(T)
  spatial_derivative : ∀ q, q.length < N → ∀ i t, t ∈ TimeSlab(T) →
    endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (curve q t).val (curve (i :: q) t).val
  represents : ∀ q, q.length ≤ N → EndpointMixedRepresents (mixed q) (fun r => (curve q r).val)
  fixed : ∀ q, q.length ≤ N → endpointStrongMixedLeray T (mixed q) = mixed q
  projected_equation : ∀ q, q.length ≤ N → endpointStrongMixedLeray T
    (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (mixed q) + srcMix q +
      endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT.le (Kmix r) (Ωmix r)) mixed q) = 0

set_option maxHeartbeats 5600000 in
/-- Exact coefficient and source word jets recover a single jointly smooth
velocity. Every finite word family represents the same zeroth mixed solution. -/
theorem exists_endpointJointVelocity_of_matchedSpatialData_withWords {T μ L M μmix Lmix : ℝ}
    (hT : 0 < T)
    (Kmix Ωmix : List (Fin 3) → MixedCoefficient(T)) (srcMix : List (Fin 3) → Mixed(T))
    (K Ω : List (Fin 3) → ℝ → K½) (src : List (Fin 3) → ℝ → C½)
    (hK : ∀ q, ContDiffOn ℝ ∞ (K q) TimeSlab(T))
    (hΩ : ∀ q, ContDiffOn ℝ ∞ (Ω q) TimeSlab(T))
    (hSrc : ∀ q, ContDiffOn ℝ ∞ (src q) TimeSlab(T))
    (hSrcMix : ∀ q, EndpointMixedRepresents (srcMix q) (src q))
    (hKmix : ∀ q, ∀ᵐ a ∂unitTorusMeasure, ∀ f : Path(T),
      (fun r => HalfHolder.eval a (Kmix q) f r) =ᵐ[TimeMeasure(T)]
        fun r => HalfHolder.eval a (K q r) (f r))
    (hΩmix : ∀ q, ∀ᵐ a ∂unitTorusMeasure, ∀ f : Path(T),
      (fun r => HalfHolder.eval a (Ωmix q) f r) =ᵐ[TimeMeasure(T)]
        fun r => HalfHolder.eval a (Ω q r) (f r))
    (hDK : ∀ i q, endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (Kmix q) (Kmix (i :: q)))
    (hDΩ : ∀ i q, endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (Ωmix q) (Ωmix (i :: q)))
    (hDSrc : ∀ i q, endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (srcMix q) (srcMix (i :: q)))
    (hμ : 0 < μ) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ TimeSlab(T), ∀ a b,
      ‖HalfHolder.eval a (K [] t) - HalfHolder.eval b (K [] t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ TimeSlab(T), ∀ a z, μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) z, z⟫_ℝ)
    (hSup : ∀ t ∈ TimeSlab(T), ‖(K [] t).val.1‖ ≤ M)
    (hμmix : 0 < μmix) (hLmix : 0 ≤ Lmix)
    (hMixLip : ∀ a b,
      ‖HalfHolder.eval a (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix [])) -
        HalfHolder.eval b (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix []))‖ ≤ Lmix * dist a b)
    (hMixPos : ∀ a (z : Path(T)), endpointIntegral T z = 0 → μmix * ‖z‖ ^ 2 ≤
      ⟪HalfHolder.eval a (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix [])) z, z⟫_ℝ) :
    ∃ (g : ℝ → S) (c : S), ContDiffOn ℝ ∞ g TimeSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), endpointStrongSpatialProjection ((K [] t).coefficientMul (g t).val) =
        c + endpointStrongSpatialProjection
          (endpointPrimitive (fun r => (Ω [] r).coefficientMul (g r).val) t) -
        endpointStrongSpatialProjection (src [] t)) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      ∀ N : ℕ, Nonempty (EndpointMeanRecoveredWords hT Kmix Ωmix srcMix g N) := by
  let B := endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix [])
  obtain ⟨_, _, hMixedSolve⟩ := exists_endpointStrongMixedSolve hT
  obtain ⟨w, hw, hStrong, _⟩ :=
    hMixedSolve B hμmix hLmix hMixLip hMixPos (srcMix [])
  have hProjected : endpointStrongMixedLeray T
      (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) w + srcMix []) = 0 := by
    rw [← endpointMixedPathCoefficient_coefficientMul hT.le (Kmix []) (Ωmix [])]
    exact hStrong
  obtain ⟨Csrc, hBound⟩ := isCompact_Icc.exists_bound_of_continuousOn (hSrc []).continuousOn
  obtain ⟨g, hg, hRecover, hRep, hZero, hEnd, _⟩ :=
    exists_endpointMixedTimeRecovery hT (Kmix []) (Ωmix []) w (srcMix []) (K []) (src [])
      hw hProjected hμ hL (contDiffOn_zero.mpr (hK []).continuousOn) hLip hPos hSup
      (hSrc []).continuousOn (by simpa only using hBound)
      (ae_endpointMixedCoefficient_spatialSlice_of_pathAction (K []) (Kmix [])
        (hK []).continuousOn (hKmix []) w)
      ((hSrcMix []).spatialSlice hT.le (hSrc []).continuousOn)
  obtain ⟨_, _, hInv⟩ := exists_endpointMixedLerayInverse hT
  obtain ⟨e, he, _⟩ := hInv B hμmix hLmix hMixLip hMixPos
  have hCoercive (z : freezingFixedSpace (endpointStrongMixedLeray T)) (a : A) :
      μmix * ‖HalfHolder.eval a z.val‖ ^ 2 ≤ ⟪HalfHolder.eval a B (HalfHolder.eval a z.val),
        HalfHolder.eval a z.val⟫_ℝ := by
    apply hMixPos
    have hz := (mem_freezingFixedSpace (endpointStrongMixedLeray T) z.val).mp z.property
    rw [← hz]
    exact endpointStrongMixedLeray_timeIntegral_eq_zero hT z.val a
  let u (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  have hFamilies (N : ℕ) : Nonempty (EndpointMeanRecoveredWords hT Kmix Ωmix srcMix g N) := by
    obtain ⟨wN, hwN, hNFixed, hNProj, hND, _⟩ :=
      exists_endpointMixedSolveSpatialJets hT Kmix Ωmix srcMix w u hw hProjected e he hμmix hCoercive N
        (fun i q _ => hDK i q) (fun i q _ => hDΩ i q) (fun i q _ => hDSrc i q)
    obtain ⟨gN, hgN, hSpace⟩ :=
      exists_endpointSpatialJetTimeRecovery (n := ⊤) (N := N) hT Kmix Ωmix wN srcMix u hND K Ω src
        (fun q _ => hK q) (fun q _ => hΩ q) (fun q _ => hSrc q) (fun q _ => hSrcMix q)
        (fun q _ => hKmix q) (fun q _ => hΩmix q) hNFixed hNProj hμ hL hLip hPos hSup
    have hBaseRep := (hgN [] (Nat.zero_le N)).2.1
    rw [hwN] at hBaseRep
    have hBaseEq := endpointContinuousSpatialRepresentatives_eqOn hT w
      (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn
        (hgN [] (Nat.zero_le N)).1.continuousOn)
      (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg) hBaseRep hRep
    refine ⟨⟨wN, gN, (fun t ht => Subtype.ext (hBaseEq ht)), (fun q hq => (hgN q hq).1),
      ?_, ?_, hNFixed, hNProj⟩⟩
    · intro q hq i t ht
      simpa only [iteratedDerivWithin_zero] using hSpace 0 (by simp) t ht i q hq
    · intro q hq
      exact EndpointMixedRepresents.of_spatialSlice hT.le
        (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn (hgN q hq).1.continuousOn)
        (hgN q hq).2.1
  have hJoint : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LiftSlab(T) := by
    change ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (g z.1).val) LiftSlab(T)
    apply contDiffOn_endpointLift_of_finite_spatialJets hT (f := fun t => (g t).val)
    intro n
    obtain ⟨w⟩ := hFamilies n
    exact ⟨fun q t => (w.curve q t).val, fun t ht => congrArg Subtype.val (w.base_eq ht),
      fun q hq => endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn (w.smooth q hq),
      w.spatial_derivative⟩
  obtain ⟨w₀⟩ := hFamilies 0
  have hSmooth : ContDiffOn ℝ ∞ g TimeSlab(T) :=
    (w₀.smooth [] (by simp)).congr fun t ht => (w₀.base_eq ht).symm
  let c := endpointStrongSpatialProjection
    (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩)
      (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) w + srcMix []))
  let Ωw := (Ωmix []).coefficientMul w
  let Ωg (t : ℝ) := (Ω [] t).coefficientMul (g t).val
  have hΩg : ContinuousOn Ωg TimeSlab(T) :=
    (HalfHolder.contDiffOn_coefficientMul (hΩ [])).continuousOn.clm_apply
      (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg)
  have hGRep := EndpointMixedRepresents.of_spatialSlice hT.le
    (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg) hRep
  have hΩRep : EndpointMixedRepresents Ωw Ωg := hGRep.coefficientMul (hΩmix [])
  refine ⟨g, c, hSmooth, hJoint, ?_, hZero, hEnd, hFamilies⟩
  intro t ht
  have h := hRecover ⟨t, ht⟩
  change endpointStrongSpatialProjection ((K [] t).coefficientMul (g t).val) =
    c + endpointStrongSpatialProjection (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Ωw) -
      endpointStrongSpatialProjection (src [] t) at h
  rw [endpointMixedPrimitive_eq_endpointPrimitive Ωw hΩg hΩRep ⟨t, ht⟩] at h
  exact h

set_option maxHeartbeats 1200000 in
/-- Exact coefficient and source word jets recover a single jointly smooth
velocity. Every finite word family represents the same zeroth mixed solution. -/
theorem exists_endpointJointVelocity_of_matchedSpatialData {T μ L M μmix Lmix : ℝ}
    (hT : 0 < T)
    (Kmix Ωmix : List (Fin 3) → MixedCoefficient(T)) (srcMix : List (Fin 3) → Mixed(T))
    (K Ω : List (Fin 3) → ℝ → K½) (src : List (Fin 3) → ℝ → C½)
    (hK : ∀ q, ContDiffOn ℝ ∞ (K q) TimeSlab(T))
    (hΩ : ∀ q, ContDiffOn ℝ ∞ (Ω q) TimeSlab(T))
    (hSrc : ∀ q, ContDiffOn ℝ ∞ (src q) TimeSlab(T))
    (hSrcMix : ∀ q, EndpointMixedRepresents (srcMix q) (src q))
    (hKmix : ∀ q, ∀ᵐ a ∂unitTorusMeasure, ∀ f : Path(T),
      (fun r => HalfHolder.eval a (Kmix q) f r) =ᵐ[TimeMeasure(T)]
        fun r => HalfHolder.eval a (K q r) (f r))
    (hΩmix : ∀ q, ∀ᵐ a ∂unitTorusMeasure, ∀ f : Path(T),
      (fun r => HalfHolder.eval a (Ωmix q) f r) =ᵐ[TimeMeasure(T)]
        fun r => HalfHolder.eval a (Ω q r) (f r))
    (hDK : ∀ i q, endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (Kmix q) (Kmix (i :: q)))
    (hDΩ : ∀ i q, endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (Ωmix q) (Ωmix (i :: q)))
    (hDSrc : ∀ i q, endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (srcMix q) (srcMix (i :: q)))
    (hμ : 0 < μ) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ TimeSlab(T), ∀ a b,
      ‖HalfHolder.eval a (K [] t) - HalfHolder.eval b (K [] t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ TimeSlab(T), ∀ a z, μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) z, z⟫_ℝ)
    (hSup : ∀ t ∈ TimeSlab(T), ‖(K [] t).val.1‖ ≤ M)
    (hμmix : 0 < μmix) (hLmix : 0 ≤ Lmix)
    (hMixLip : ∀ a b,
      ‖HalfHolder.eval a (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix [])) -
        HalfHolder.eval b (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix []))‖ ≤ Lmix * dist a b)
    (hMixPos : ∀ a (z : Path(T)), endpointIntegral T z = 0 → μmix * ‖z‖ ^ 2 ≤
      ⟪HalfHolder.eval a (endpointMixedPathCoefficient hT.le (Kmix []) (Ωmix [])) z, z⟫_ℝ) :
    ∃ (g : ℝ → S) (c : S), ContDiffOn ℝ ∞ g TimeSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), endpointStrongSpatialProjection ((K [] t).coefficientMul (g t).val) =
        c + endpointStrongSpatialProjection
          (endpointPrimitive (fun r => (Ω [] r).coefficientMul (g r).val) t) -
        endpointStrongSpatialProjection (src [] t)) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 := by
  obtain ⟨g, c, hg, hJoint, hEq, hStart, hFinish, _⟩ :=
    exists_endpointJointVelocity_of_matchedSpatialData_withWords
      (μ := μ) (L := L) (M := M) (μmix := μmix) (Lmix := Lmix)
      hT Kmix Ωmix srcMix K Ω src hK hΩ hSrc hSrcMix hKmix hΩmix hDK hDΩ hDSrc
      hμ hL hLip hPos hSup hμmix hLmix hMixLip hMixPos
  exact ⟨g, c, hg, hJoint, hEq, hStart, hFinish⟩

end JointRecovery

/-- The divergence trace of the coframe-transformed field depends only on
the divergence of the original label field. -/
theorem trace_piola_coframe {F : Vec3 → Vec3 →L[ℝ] Vec3} {v : Vec3 → Vec3}
    {DF : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3} {G Dv : Vec3 →L[ℝ] Vec3} {a : Vec3}
    (hF : HasFDerivAt F DF a) (hsym : ∀ w z : Vec3, DF w z = DF z w)
    (hGF : G.comp (F a) = ContinuousLinearMap.id ℝ Vec3)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (F b).toLinearMap = 1)
    (hv : HasFDerivAt v Dv a) :
    LinearMap.trace ℝ Vec3 (((fderiv ℝ (fun b => F b (v b)) a).comp G).toLinearMap) =
      divergence v a := by
  have hFv : HasFDerivAt (fun b => F b (v b)) ((F a).comp Dv + DF.flip (v a)) a :=
    hF.clm_apply hv
  have hflip : DF.flip (v a) = DF (v a) := ContinuousLinearMap.ext fun z => hsym z (v a)
  rw [divergence_eq_trace_fderiv, hFv.fderiv, hv.fderiv, hflip, ContinuousLinearMap.add_comp]
  change LinearMap.trace ℝ Vec3
    ((((F a).comp Dv).comp G).toLinearMap + ((DF (v a)).comp G).toLinearMap) = _
  rw [map_add, trace_deriv_comp_inverse_eq_zero hF hGF hdet, add_zero]
  change LinearMap.trace ℝ Vec3 (((F a).toLinearMap.comp Dv.toLinearMap).comp G.toLinearMap) = _
  rw [LinearMap.trace_comp_cycle']
  change LinearMap.trace ℝ Vec3 ((G.comp (F a)).toLinearMap.comp Dv.toLinearMap) = _
  rw [hGF]
  exact congrArg (LinearMap.trace ℝ Vec3) (LinearMap.id_comp _)

/-- A twice differentiable volume-preserving deformation gives the coframe
trace identity with any left inverse of its derivative at the label. -/
theorem trace_piola_coframe_of_contDiffAt {X v : Vec3 → Vec3} {G : Vec3 →L[ℝ] Vec3}
    {a : Vec3} (hX : ContDiffAt ℝ 2 X a)
    (hGF : G.comp (fderiv ℝ X a) = ContinuousLinearMap.id ℝ Vec3)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (fderiv ℝ X b).toLinearMap = 1)
    (hv : DifferentiableAt ℝ v a) :
    LinearMap.trace ℝ Vec3 (((fderiv ℝ (fun b => fderiv ℝ X b (v b)) a).comp G).toLinearMap) =
      divergence v a :=
  trace_piola_coframe ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt)
    (hX.isSymmSndFDerivAt (by simp)) hGF hdet hv.hasFDerivAt


/-- For a volume-preserving label map with the stated deformation gradient,
the strong mean solution has zero coframe divergence. -/
theorem trace_endpointPhysicalMean_eq_zero_of_volumePreserving
    {X v B : Vec3 → Vec3} {F : Vec3 → Coefficient} {G : Coefficient} {a : Vec3}
    (hX : ContDiffAt ℝ 2 X a) (hF : ∀ b, F b = fderiv ℝ X b)
    (hGF : G.comp (F a) = ContinuousLinearMap.id ℝ Vec3)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (F b).toLinearMap = 1)
    (hv : DifferentiableAt ℝ v a) (hdiv : divergence v a = 0)
    (hB : ∀ b, B b = F b (v b)) :
    LinearMap.trace ℝ Vec3 (((fderiv ℝ B a).comp G).toLinearMap) = 0 := by
  have hEq : B = fun b => fderiv ℝ X b (v b) := funext fun b => by rw [hB b, hF b]
  rw [hEq]
  rw [hF a] at hGF
  have hJ : ∀ᶠ b in 𝓝 a, LinearMap.det (fderiv ℝ X b).toLinearMap = 1 :=
    hdet.mono fun b hb => by simpa only [hF b] using hb
  exact (trace_piola_coframe_of_contDiffAt hX hGF hJ hv).trans hdiv

section ForcedMean

local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (Path(T) →L[ℝ] Path(T))

private theorem norm_mixedCoefficient_sub_le_of_aeAction {T L : ℝ}
    (K : ℝ → K½) (Kmix : MixedCoefficient(T)) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ TimeSlab(T), ∀ a b,
      ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ L * dist a b)
    (hAction : ∀ (a : A) (v : Path(T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
      fun t => HalfHolder.eval a (K t) (v t)) (a b : A) :
    ‖HalfHolder.eval a Kmix - HalfHolder.eval b Kmix‖ ≤ L * dist a b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL dist_nonneg)
  intro w
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hAction a w, hAction b w, ae_restrict_mem (μ := volume) measurableSet_Ioc,
    Lp.coeFn_sub (HalfHolder.eval a Kmix w) (HalfHolder.eval b Kmix w)] with t ha hb ht hsub
  change HalfHolder.eval a Kmix w t = _ at ha
  change HalfHolder.eval b Kmix w t = _ at hb
  rw [_root_.sub_apply, hsub, Pi.sub_apply, ha, hb, ← _root_.sub_apply]
  exact ((HalfHolder.eval a (K t) - HalfHolder.eval b (K t)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hLip t (Ioc_subset_Icc_self ht) a b) (norm_nonneg _))

private theorem eval_endpointSourceDerivative {T t : ℝ} (hT : 0 < T) (ht : t ∈ TimeSlab(T))
    (a : A) (src : ℝ → C½) (f : ℝ → Vec3)
    (hs : ContDiffOn ℝ 1 src TimeSlab(T)) (hf : ContinuousOn f TimeSlab(T))
    (hEval : ∀ r ∈ TimeSlab(T), HalfHolder.eval a (src r) = -endpointPrimitive f r) :
    HalfHolder.eval a (derivWithin src TimeSlab(T) t) = -f t := by
  have hd : HasDerivWithinAt (fun r => HalfHolder.eval a (src r))
      (HalfHolder.eval a (derivWithin src TimeSlab(T) t)) TimeSlab(T) t :=
    (HalfHolder.eval a).hasFDerivAt.comp_hasDerivWithinAt t
      ((hs.differentiableOn_one t ht).hasDerivWithinAt)
  have hd' := hd.congr (fun r hr => (hEval r hr).symm) (hEval t ht).symm
  have hInt := (hasDerivWithinAt_endpointPrimitive_of_continuousOn hf ht).neg
  exact (hd'.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (hInt.derivWithin (uniqueDiffOn_Icc hT t ht))

private theorem continuousOn_endpointForceSlice {T : ℝ} {v : Velocity}
    (hv : ContinuousOn (Function.uncurry v) LiftSlab(T)) (x : Vec3) :
    ContinuousOn (fun r => v r x) TimeSlab(T) := by
  have hφ : Continuous (fun r : ℝ => (r, x)) := continuous_id.prodMk continuous_const
  have hmaps : MapsTo (fun r : ℝ => (r, x)) TimeSlab(T) LiftSlab(T) :=
    fun _ h => ⟨h, mem_univ x⟩
  exact hv.comp hφ.continuousOn hmaps

set_option maxHeartbeats 7000000 in
private theorem recover_endpointPhysicalVelocityFromJetData {T D L : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (F G M Mt : ℝ × A → Coefficient) (R : ℝ × Vec3 → Vec3)
    (hFc : ContinuousOn (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hMc : ContinuousOn (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hF : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => F (r, a)) ((M (t, a)).comp (F (t, a))) TimeSlab(T) t)
    (hM : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) TimeSlab(T) t)
    (hMt : ∀ a, ContinuousOn (fun r => Mt (r, a)) TimeSlab(T))
    (hGF : ∀ (a : A) t, t ∈ TimeSlab(T) → (G (t, a)).comp (F (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ (a : A) t, t ∈ TimeSlab(T) → ‖G (t, a)‖ ≤ D)
    (hMbound : ∀ (a : A) t, t ∈ TimeSlab(T) → ‖M (t, a)‖ ≤ L)
    (hupper : ∀ (a : A) t, t ∈ TimeSlab(T) → ∀ x : Vec3,
      ⟪endpointHessian (M (t, a)) (Mt (t, a)) x, x⟫_ℝ ≤ ‖x‖ ^ 2)
    (jets : EndpointPhysicalJets T (fun i : Fin 3 => EuclideanSpace.single i 1)
      (fun z => F (z.1, toUnitTorus z.2)) (fun z => M (z.1, toUnitTorus z.2)) R) :
    let K := jets.kinetic.curve []
    let Ω := jets.vorticity.curve []
    let src := jets.source.curve []
    ∃ (g : ℝ → S) (c : S), ContDiffOn ℝ ∞ g TimeSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
        c + endpointStrongSpatialProjection
          (endpointPrimitive (fun r => (Ω r).coefficientMul (g r).val) t) -
        endpointStrongSpatialProjection (src t)) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      (∀ t ∈ TimeSlab(T), ∀ a, HalfHolder.eval a (K t) = kineticForm (F (t, a))) ∧
      (∀ t ∈ TimeSlab(T), ∀ a, HalfHolder.eval a (Ω t) = vorticityForm (F (t, a)) (M (t, a))) ∧
      (∀ t ∈ TimeSlab(T), ∀ a z, (D ^ 2)⁻¹ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) z, z⟫_ℝ) ∧
      (∀ a (w : Path(T)), endpointIntegral T w = 0 → (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * ‖w‖ ^ 2 ≤
        ⟪HalfHolder.eval a
          (endpointMixedPathCoefficient hT.le (jets.kineticMixed []) (jets.vorticityMixed [])) w, w⟫_ℝ) ∧
      (∀ N : ℕ, Nonempty (EndpointMeanRecoveredWords hT jets.kineticMixed jets.vorticityMixed jets.sourceMixed g N)) := by
  let K := jets.kinetic.curve
  let Ω := jets.vorticity.curve
  let src := jets.source.curve
  have hKrep (t : ℝ) (ht : t ∈ TimeSlab(T)) (a : A) :
      HalfHolder.eval a (K [] t) = kineticForm (F (t, a)) := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact jets.kinetic.eval_lift [] t ht x
  have hΩrep (t : ℝ) (ht : t ∈ TimeSlab(T)) (a : A) :
      HalfHolder.eval a (Ω [] t) = vorticityForm (F (t, a)) (M (t, a)) := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact jets.vorticity.eval_lift [] t ht x
  obtain ⟨LK, hLK, hKl⟩ := jets.kinetic_lipschitz
  obtain ⟨LΩ, hLΩ, hΩl⟩ := jets.vorticity_lipschitz
  obtain ⟨BK, _, hKsup⟩ := jets.kinetic.norm_bound []
  let μ := (D ^ 2)⁻¹
  let μmix := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hμ : 0 < μ := inv_pos.mpr (pow_pos hDpos _)
  have hμmix : 0 < μmix := by dsimp only [μmix]; positivity
  have hkpos (t : ℝ) (ht : t ∈ TimeSlab(T)) (a : A) (z : Vec3) :
      μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) z, z⟫_ℝ := by
    rw [hKrep t ht a]
    exact kineticForm_elliptic hDpos (hGF a t ht) (hGbound a t ht) z
  have hLmix : 0 ≤ LK + T * LΩ := by positivity
  have hLipMix := norm_endpointMixedPathCoefficient_sub_le hT.le (jets.kineticMixed []) (jets.vorticityMixed [])
    (norm_mixedCoefficient_sub_le_of_aeAction (K []) (jets.kineticMixed []) hLK hKl (jets.kinetic_action []))
    (norm_mixedCoefficient_sub_le_of_aeAction (Ω []) (jets.vorticityMixed []) hLΩ hΩl (jets.vorticity_action []))
  have hMixPos (a : A) (w : Path(T)) (hw : endpointIntegral T w = 0) :
      μmix * ‖w‖ ^ 2 ≤
        ⟪HalfHolder.eval a
          (endpointMixedPathCoefficient hT.le (jets.kineticMixed []) (jets.vorticityMixed [])) w, w⟫_ℝ := by
    obtain ⟨x, hx⟩ := toUnitTorus_surjective a
    have hFa : ContinuousOn (fun t => F (t, a)) TimeSlab(T) := by
      rw [← hx]
      exact hFc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, mem_univ x⟩)
    have hMa : ContinuousOn (fun t => M (t, a)) TimeSlab(T) := by
      rw [← hx]
      exact hMc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, mem_univ x⟩)
    have htime : ∀ᵐ t ∂TimeMeasure(T), t ∈ TimeSlab(T) :=
      (ae_restrict_mem (μ := volume) measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht
    have hKr : (fun t => HalfHolder.eval a (jets.kineticMixed []) w t) =ᵐ[TimeMeasure(T)]
        fun t => kineticForm (F (t, a)) (w t) := by
      filter_upwards [htime, jets.kinetic_action [] a w] with t ht ht'
      change HalfHolder.eval a (jets.kineticMixed []) w t = HalfHolder.eval a (K [] t) (w t) at ht'
      rw [hKrep t ht a] at ht'
      exact ht'
    have hΩr : (fun t => HalfHolder.eval a (jets.vorticityMixed []) w t) =ᵐ[TimeMeasure(T)]
        fun t => vorticityForm (F (t, a)) (M (t, a)) (w t) := by
      filter_upwards [htime, jets.vorticity_action [] a w] with t ht ht'
      change HalfHolder.eval a (jets.vorticityMixed []) w t = HalfHolder.eval a (Ω [] t) (w t) at ht'
      rw [hΩrep t ht a] at ht'
      exact ht'
    exact endpointMixedPathCoefficient_coercive hT hT₁ hD hL
      (jets.kineticMixed []) (jets.vorticityMixed []) a
      (fun t => F (t, a)) (fun t => G (t, a)) (fun t => M (t, a)) (fun t => Mt (t, a))
      hFa hMa (hF a) (hM a) (hMt a) (hGF a) (hGbound a) (hMbound a) (hupper a)
      w hw hKr hΩr
  obtain ⟨g, c, hg, hJoint, hEq, hStart, hFinish, hWords⟩ :=
    exists_endpointJointVelocity_of_matchedSpatialData_withWords
    (μ := μ) (L := LK) (M := BK) (μmix := μmix) (Lmix := LK + T * LΩ) hT
    jets.kineticMixed jets.vorticityMixed jets.sourceMixed K Ω src
    jets.kinetic.smooth jets.vorticity.smooth jets.source.smooth
    (fun q => ae_of_all _ (jets.source_action q))
    (fun q => ae_of_all _ (jets.kinetic_action q))
    (fun q => ae_of_all _ (jets.vorticity_action q))
    jets.kinetic_mixed_derivative jets.vorticity_mixed_derivative jets.source_mixed_derivative
    hμ hLK hKl hkpos (fun t ht => (norm_fst_le (K [] t).val).trans (hKsup t ht))
    hμmix hLmix hLipMix hMixPos
  exact ⟨g, c, hg, hJoint, hEq, hStart, hFinish, hKrep, hΩrep, hkpos, hMixPos, hWords⟩

/-- The negative primitive of the force pulled back by the deformation adjoint. -/
def endpointPhysicalForcePrimitive (F : ℝ × A → Coefficient) (force : Velocity) :
    ℝ × Vec3 → Vec3 :=
  fun z => -endpointPrimitive (fun r => (F (r, toUnitTorus z.2)).adjoint (force r z.2)) z.1

/-- The exact spatial words and coercivity of the velocity underlying a
physical forced mean solution. -/
structure EndpointPhysicalMeanRecovery {T : ℝ} (hT : 0 < T) (D L : ℝ)
    (F M : ℝ × A → Coefficient) (force v : Velocity) where
  curve : ℝ → S
  jets : EndpointPhysicalJets T coordinateDirection
    (fun z => F (z.1, toUnitTorus z.2)) (fun z => M (z.1, toUnitTorus z.2))
    (endpointPhysicalForcePrimitive F force)
  lift_eq : v = endpointPhysicalLabelVelocity curve
  words : ∀ N : ℕ, Nonempty
    (EndpointMeanRecoveredWords hT jets.kineticMixed jets.vorticityMixed jets.sourceMixed curve N)
  projected_integrated : ∃ c : S, ∀ t ∈ TimeSlab(T),
    endpointStrongSpatialProjection ((jets.kinetic.curve [] t).coefficientMul (curve t).val) =
      c + endpointStrongSpatialProjection
        (endpointPrimitive (fun r => (jets.vorticity.curve [] r).coefficientMul (curve r).val) t) -
      endpointStrongSpatialProjection (jets.source.curve [] t)
  kinetic_coercive : ∀ t ∈ TimeSlab(T), ∀ a z,
    (D ^ 2)⁻¹ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (jets.kinetic.curve [] t) z, z⟫_ℝ
  mixed_coercive : ∀ a (w : Path(T)), endpointIntegral T w = 0 →
    (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * ‖w‖ ^ 2 ≤
      ⟪HalfHolder.eval a
        (endpointMixedPathCoefficient hT.le (jets.kineticMixed []) (jets.vorticityMixed [])) w, w⟫_ℝ

set_option maxHeartbeats 3600000 in
/-- The jointly smooth periodic forced mean solution with zero endpoint
displacements, for the physical ODE and Hessian assumptions of Theorem 4.2.
The source of the projected inverse is the actual negative primitive of the
pulled-back forcing. -/
theorem exists_endpointPhysicalForcedMean_withRecovery {T D L : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (F G M Mt : ℝ × A → Coefficient) (force : Velocity)
    (hFc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hMc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hforcePer : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (force t))
    (hF : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => F (r, a)) ((M (t, a)).comp (F (t, a))) TimeSlab(T) t)
    (hM : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) TimeSlab(T) t)
    (hMt : ∀ a, ContinuousOn (fun r => Mt (r, a)) TimeSlab(T))
    (hGF : ∀ (a : A) t, t ∈ TimeSlab(T) → (G (t, a)).comp (F (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (hFG : ∀ (a : A) t, t ∈ TimeSlab(T) → (F (t, a)).comp (G (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ (a : A) t, t ∈ TimeSlab(T) → ‖G (t, a)‖ ≤ D)
    (hMbound : ∀ (a : A) t, t ∈ TimeSlab(T) → ‖M (t, a)‖ ≤ L)
    (hupper : ∀ (a : A) t, t ∈ TimeSlab(T) → ∀ x : Vec3,
      ⟪endpointHessian (M (t, a)) (Mt (t, a)) x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ∃ (v Z B : Velocity) (q : Pressure),
      ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry Z) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry B) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (v t) ∧ SpatiallyPeriodic (Z t) ∧
        SpatiallyPeriodic (B t) ∧ SpatiallyPeriodic (q t) ∧ (∫ x in centeredCell, q t x) = 0) ∧
      Z 0 = 0 ∧ Z T = 0 ∧
      (∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (v t x) ∧
        HasDerivWithinAt (fun r => Z r x) (v t x) TimeSlab(T) t ∧
        divergence (v t) x = 0 ∧
        derivWithin (fun r => B r x) TimeSlab(T) t + M (t, toUnitTorus x) (B t x) +
          (G (t, toUnitTorus x)).adjoint (gradient (q t) x) = force t x) ∧
      Nonempty (EndpointPhysicalMeanRecovery hT D L F M force v) := by
  let Fℓ (z : ℝ × Vec3) := F (z.1, toUnitTorus z.2)
  let Mℓ (z : ℝ × Vec3) := M (z.1, toUnitTorus z.2)
  let pullForce (t : ℝ) (x : Vec3) := (Fℓ (t, x)).adjoint (force t x)
  let integratedForce := endpointPhysicalForcePrimitive F force
  let u (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  let Adj : Coefficient ≃ₗᵢ[ℝ] Coefficient := ContinuousLinearMap.adjoint
  have hAdj : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (Fℓ z).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hFc
  have hPull : ContDiffOn ℝ ∞ (Function.uncurry pullForce) LiftSlab(T) := hAdj.clm_apply hforce
  have hInt : ContDiffOn ℝ ∞ integratedForce LiftSlab(T) :=
    (contDiffOn_endpointPhysicalJointPrimitive hT hPull).neg
  have hPer (n : Fin 3 → ℤ) (x : Vec3) : toUnitTorus (x + latticeVector n) = toUnitTorus x :=
    (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩
  have hFper (t : ℝ) (_ht : t ∈ TimeSlab(T)) : SpatiallyPeriodic (fun x => Fℓ (t, x)) :=
    fun n x => congrArg (fun a => F (t, a)) (hPer n x)
  have hMper (t : ℝ) (_ht : t ∈ TimeSlab(T)) : SpatiallyPeriodic (fun x => Mℓ (t, x)) :=
    fun n x => congrArg (fun a => M (t, a)) (hPer n x)
  have hIntPer (t : ℝ) (ht : t ∈ TimeSlab(T)) : SpatiallyPeriodic (fun x => integratedForce (t, x)) := by
    intro n x
    dsimp only [integratedForce, endpointPhysicalForcePrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1]
    intro r hr
    dsimp only [pullForce, Fℓ]
    rw [hPer n x, hforcePer r ⟨hr.1, hr.2.trans ht.2⟩ n x]
  obtain ⟨jets⟩ := exists_endpointPhysicalJetData hT u Fℓ Mℓ integratedForce hFc hMc hInt hFper hMper hIntPer
  let K := jets.kinetic.curve
  let Ω := jets.vorticity.curve
  let src := jets.source.curve
  obtain ⟨g, c, hg, hJoint, hEq, hStart, hFinish, hKrep, hΩrep, hKpos, hMixedPos, hWords⟩ :=
    recover_endpointPhysicalVelocityFromJetData hT hT₁ hD hL F G M Mt integratedForce
      hFc.continuousOn hMc.continuousOn hF hM hMt hGF hGbound hMbound hupper jets
  have hSourceEval (t : ℝ) (ht : t ∈ TimeSlab(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (src [] t) = integratedForce (t, x) :=
    jets.source.eval_lift [] t ht x
  have hSourceDeriv (t : ℝ) (ht : t ∈ TimeSlab(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (derivWithin (src []) TimeSlab(T) t) =
        -(F (t, toUnitTorus x)).adjoint (force t x) := by
    have hcv := continuousOn_endpointForceSlice hPull.continuousOn x
    have hs : ContDiffOn ℝ 1 (src []) TimeSlab(T) := (jets.source.smooth []).of_le (by simp)
    exact eval_endpointSourceDerivative hT ht (toUnitTorus x) (src []) (fun r => pullForce r x)
      hs hcv (fun r hr => hSourceEval r hr x)
  obtain ⟨Z, B, q, hZ, hB, hq, hPerMean, hZ0, hZT, hMom⟩ :=
    exists_endpointPhysicalMeanFromJointVelocity hT F G M force hFc hMc hforce hF hGF hFG
      (K []) (Ω []) (src []) g c ((jets.kinetic.smooth []).of_le (by simp))
      (jets.vorticity.smooth []).continuousOn ((jets.source.smooth []).of_le (by simp))
      (hg.of_le (by simp)) hJoint hKrep hΩrep hSourceDeriv hEq hStart hFinish
  exact ⟨endpointPhysicalLabelVelocity g, Z, B, q, hJoint, hZ, hB, hq,
    (fun t ht => ⟨endpointPhysicalLabelVelocity_periodic g t, hPerMean t ht⟩), hZ0, hZT, hMom,
    ⟨⟨g, jets, rfl, hWords, ⟨c, hEq⟩, hKpos, hMixedPos⟩⟩⟩

set_option maxHeartbeats 1200000 in
/-- The jointly smooth periodic forced mean solution with zero endpoint
displacements, for the physical ODE and Hessian assumptions of Theorem 4.2.
The source of the projected inverse is the actual negative primitive of the
pulled-back forcing. -/
theorem exists_endpointPhysicalForcedMean {T D L : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (F G M Mt : ℝ × A → Coefficient) (force : Velocity)
    (hFc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hMc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hforcePer : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (force t))
    (hF : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => F (r, a)) ((M (t, a)).comp (F (t, a))) TimeSlab(T) t)
    (hM : ∀ (a : A) t, t ∈ TimeSlab(T) →
      HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) TimeSlab(T) t)
    (hMt : ∀ a, ContinuousOn (fun r => Mt (r, a)) TimeSlab(T))
    (hGF : ∀ (a : A) t, t ∈ TimeSlab(T) → (G (t, a)).comp (F (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (hFG : ∀ (a : A) t, t ∈ TimeSlab(T) → (F (t, a)).comp (G (t, a)) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ (a : A) t, t ∈ TimeSlab(T) → ‖G (t, a)‖ ≤ D)
    (hMbound : ∀ (a : A) t, t ∈ TimeSlab(T) → ‖M (t, a)‖ ≤ L)
    (hupper : ∀ (a : A) t, t ∈ TimeSlab(T) → ∀ x : Vec3,
      ⟪endpointHessian (M (t, a)) (Mt (t, a)) x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ∃ (v Z B : Velocity) (q : Pressure),
      ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry Z) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry B) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (v t) ∧ SpatiallyPeriodic (Z t) ∧
        SpatiallyPeriodic (B t) ∧ SpatiallyPeriodic (q t) ∧ (∫ x in centeredCell, q t x) = 0) ∧
      Z 0 = 0 ∧ Z T = 0 ∧
      (∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (v t x) ∧
        HasDerivWithinAt (fun r => Z r x) (v t x) TimeSlab(T) t ∧
        divergence (v t) x = 0 ∧
        derivWithin (fun r => B r x) TimeSlab(T) t + M (t, toUnitTorus x) (B t x) +
          (G (t, toUnitTorus x)).adjoint (gradient (q t) x) = force t x) := by
  obtain ⟨v, Z, B, q, hv, hZ, hB, hq, hPerMean, hStart, hFinish, hMom, _⟩ :=
    exists_endpointPhysicalForcedMean_withRecovery hT hT₁ hD hL F G M Mt force hFc hMc hforce
      hforcePer hF hM hMt hGF hFG hGbound hMbound hupper
  exact ⟨v, Z, B, q, hv, hZ, hB, hq, hPerMean, hStart, hFinish, hMom⟩

end ForcedMean

end

end TorusEuler

import TorusEuler.PeriodicEulerMomentumJets
import TorusEuler.InductiveLimitAssembly
import TorusEuler.EulerLimitClosure
import TorusEuler.TruncatedParentProjectedMomentum
import TorusEuler.EndpointPressureRecovery

/-! Passage from the approximate periodic projected momentum equations to the
jointly smooth preterminal Euler evolution. -/

open BoundedContinuousFunction ContinuousLinearMap Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local instance (m : ℕ) : NormedAddCommGroup (BoundedSpatialJet Vec3 Vec3 m) :=
  inferInstanceAs (NormedAddCommGroup
    (Vec3 →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) Vec3))
local instance (m : ℕ) : NormedSpace ℝ (BoundedSpatialJet Vec3 Vec3 m) :=
  inferInstanceAs (NormedSpace ℝ
    (Vec3 →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) Vec3))
local instance (m : ℕ) : NormedAddCommGroup (SpatialJetTuple Vec3 Vec3 m) :=
  inferInstanceAs (NormedAddCommGroup (∀ i : Fin (m + 1), BoundedSpatialJet Vec3 Vec3 i))
local instance (m : ℕ) : NormedSpace ℝ (SpatialJetTuple Vec3 Vec3 m) :=
  inferInstanceAs (NormedSpace ℝ (∀ i : Fin (m + 1), BoundedSpatialJet Vec3 Vec3 i))

/-- Uniform convergence of the evaluated components gives uniform convergence in the jet norm. -/
theorem tendstoUniformlyOn_spatialJetTuple_of_apply
    {E F ι τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {I : Set τ} {m : ℕ}
    {U : ι → τ → SpatialJetTuple E F m} {v : τ → SpatialJetTuple E F m}
    (h : ∀ i : Fin (m + 1), TendstoUniformlyOn
      (fun n (q : τ × E) => U n q.1 i q.2) (fun q : τ × E => v q.1 i q.2) l
      (I ×ˢ (univ : Set E))) : TendstoUniformlyOn U v l I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  have hcomp : ∀ᶠ n in l, ∀ i : Fin (m + 1), ∀ q ∈ I ×ˢ (univ : Set E),
      dist (v q.1 i q.2) (U n q.1 i q.2) < ε / 2 := by
    rw [Filter.eventually_all]
    intro i
    exact Metric.tendstoUniformlyOn_iff.mp (h i) (ε / 2) hδ
  filter_upwards [hcomp] with n hn t ht
  apply (dist_pi_lt_iff hε).mpr
  intro i
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le hδ.le).mpr ?_) (half_lt_self hε)
  intro x
  exact (hn i (t, x) ⟨ht, mem_univ x⟩).le

/-- Uniform convergence of the actual spatial jets through order `m` yields uniform
convergence of the compatible periodic tuples in their completed jet space. -/
theorem tendstoUniformlyOn_periodicVelocityJets_of_iteratedFDeriv
    {ι τ : Type*} {l : Filter ι} {I : Set τ} (m : ℕ)
    {U : ι → τ → smoothPeriodicVelocity} {v : τ → smoothPeriodicVelocity}
    (h : ∀ k ≤ m, TendstoUniformlyOn
      (fun n (q : τ × Vec3) => iteratedFDeriv ℝ k (U n q.1 : Vec3 → Vec3) q.2)
      (fun q : τ × Vec3 => iteratedFDeriv ℝ k (v q.1 : Vec3 → Vec3) q.2) l
      (I ×ˢ (univ : Set Vec3))) :
    TendstoUniformlyOn (fun n t => periodicVelocityJets m (U n t))
      (fun t => periodicVelocityJets m (v t)) l I := by
  let Uj (n : ι) (t : τ) : SpatialJetTuple Vec3 Vec3 m := periodicVelocityJets m (U n t)
  let vj (t : τ) : SpatialJetTuple Vec3 Vec3 m := periodicVelocityJets m (v t)
  have hc : TendstoUniformlyOn Uj vj l I := by
    apply tendstoUniformlyOn_spatialJetTuple_of_apply
    intro i
    simpa only [Uj, vj, periodicVelocityJets_apply] using h (i : ℕ) (Nat.le_of_lt_succ i.isLt)
  rw [Metric.tendstoUniformlyOn_iff] at hc ⊢
  exact hc


private def evalPeriodicMomentumJetZero (x : Vec3) : PeriodicVelocityJetSpace 0 →L[ℝ] Vec3 :=
  (continuousMultilinearCurryFin0 ℝ Vec3 Vec3).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((evalCLM ℝ x).comp ((ContinuousLinearMap.proj (0 : Fin 1)).comp
      (PeriodicVelocityJetSpace 0).subtypeL))

private theorem evalPeriodicMomentumJetZero_apply (u v : smoothPeriodicVelocity) (x : Vec3) :
    evalPeriodicMomentumJetZero x (periodicProjectedMomentumJets 0 (periodicVelocityJets 2 u)
      (periodicVelocityJets 2 v)) = periodicProjectedMomentum u v x := by
  let C := continuousMultilinearCurryFin0 ℝ Vec3 Vec3
  let V := periodicProjectedMomentumJets 0 (periodicVelocityJets 2 u) (periodicVelocityJets 2 v)
  change C ((V : SpatialJetTuple Vec3 Vec3 0) 0 x) = _
  rw [periodicProjectedMomentumJets_apply]
  change C (iteratedFDeriv ℝ 0 (periodicProjectedMomentum u v) x) = _
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, C.apply_symm_apply]

private theorem continuousOn_periodicProjectedMomentum {S : ℝ}
    (u : ℝ → smoothPeriodicVelocity)
    (h : ContinuousOn (fun t => periodicVelocityJets 2 (u t)) (Icc 0 S)) (x : Vec3) :
    ContinuousOn (fun t => periodicProjectedMomentum (u t) (u t) x) (Icc 0 S) := by
  have hW := ((periodicProjectedMomentumJets 0).continuous.comp_continuousOn h).clm_apply h
  exact ((evalPeriodicMomentumJetZero x).continuous.comp_continuousOn hW).congr
    (fun t _ => (evalPeriodicMomentumJetZero_apply (u t) (u t) x).symm)

private theorem tendstoUniformlyOn_bilinear_diagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : ℝ}
    (B : E →L[ℝ] E →L[ℝ] F) {U : ℕ → ℝ → E} {u : ℝ → E}
    (h : TendstoUniformlyOn U u atTop (Icc 0 S)) (hc : ContinuousOn u (Icc 0 S)) :
    TendstoUniformlyOn (fun j t => B (U j t) (U j t)) (fun t => B (u t) (u t))
      atTop (Icc 0 S) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hBA := B.uniformContinuous.comp_tendstoUniformlyOn h
  have hbound (t : ℝ) (ht : t ∈ Icc 0 S) : ‖B (u t)‖ ≤ ‖B‖ * max M 0 :=
    (B.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hM t ht).trans (le_max_left _ _)) (norm_nonneg _))
  have hM' (t : ℝ) (ht : t ∈ Icc 0 S) : ‖u t‖ ≤ max M 0 := (hM t ht).trans (le_max_left _ _)
  exact tendstoUniformlyOn_clm_apply_of_bounded hBA h (C := ‖B‖ * max M 0) (M := max M 0)
    (mul_nonneg (norm_nonneg B) (le_max_right M 0)) (le_max_right M 0) hbound hM'

set_option synthInstance.maxHeartbeats 125000 in
/-- Uniform convergence in two compatible spatial jet orders passes through the
actual signed projected quadratic momentum, at each fixed spatial point. -/
theorem tendstoUniformlyOn_periodicProjectedMomentum_of_jetTuples {S : ℝ}
    {U : ℕ → ℝ → smoothPeriodicVelocity} {u : ℝ → smoothPeriodicVelocity}
    (h : TendstoUniformlyOn (fun j t => periodicVelocityJets 2 (U j t))
      (fun t => periodicVelocityJets 2 (u t)) atTop (Icc 0 S))
    (hc : ContinuousOn (fun t => periodicVelocityJets 2 (u t)) (Icc 0 S)) (x : Vec3) :
    TendstoUniformlyOn (fun j t => periodicProjectedMomentum (U j t) (U j t) x)
      (fun t => periodicProjectedMomentum (u t) (u t) x) atTop (Icc 0 S) := by
  have hN := tendstoUniformlyOn_bilinear_diagonal (periodicProjectedMomentumJets 0) h hc
  simpa only [Function.comp_def, evalPeriodicMomentumJetZero_apply] using
    (evalPeriodicMomentumJetZero x).uniformContinuous.comp_tendstoUniformlyOn hN

private theorem integrated_periodicProjectedMomentum_of_uniformLimits
    {S : ℝ} (hS : 0 < S) {U : ℕ → ℝ → smoothPeriodicVelocity} {u : ℝ → smoothPeriodicVelocity}
    {R : ℕ → Velocity} (x : Vec3)
    (hU : TendstoUniformlyOn (fun j t => (U j t : Vec3 → Vec3) x)
      (fun t => (u t : Vec3 → Vec3) x) atTop (Icc 0 S))
    (hJ : TendstoUniformlyOn (fun j t => periodicVelocityJets 2 (U j t))
      (fun t => periodicVelocityJets 2 (u t)) atTop (Icc 0 S))
    (hUc : ∀ j, ContinuousOn (fun t => (U j t : Vec3 → Vec3) x) (Icc 0 S))
    (hJc : ∀ j, ContinuousOn (fun t => periodicVelocityJets 2 (U j t)) (Icc 0 S))
    (huc : ContinuousOn (fun t => periodicVelocityJets 2 (u t)) (Icc 0 S))
    (hR : TendstoUniformlyOn (fun j t => R j t x) (fun _ => 0) atTop (Icc 0 S))
    (hRc : ∀ j, ContinuousOn (fun t => R j t x) (Icc 0 S))
    (hStage : ∀ j t, t ∈ Icc 0 S → HasDerivWithinAt (fun r => (U j r : Vec3 → Vec3) x)
      (periodicProjectedMomentum (U j t) (U j t) x + R j t x) (Icc 0 S) t) :
    (∀ t ∈ Icc 0 S, (u t : Vec3 → Vec3) x = (u 0 : Vec3 → Vec3) x +
      endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) ∧
    (∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => (u r : Vec3 → Vec3) x)
      (periodicProjectedMomentum (u t) (u t) x) (Icc 0 S) t) := by
  let N j t := periodicProjectedMomentum (U j t) (U j t) x
  let n t := periodicProjectedMomentum (u t) (u t) x
  have hN : TendstoUniformlyOn N n atTop (Icc 0 S) :=
    tendstoUniformlyOn_periodicProjectedMomentum_of_jetTuples hJ huc x
  have hNc (j : ℕ) : ContinuousOn (N j) (Icc 0 S) :=
    continuousOn_periodicProjectedMomentum (U j) (hJc j) x
  have hInt (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 S) :
      (U j t : Vec3 → Vec3) x = (U j 0 : Vec3 → Vec3) x -
        (∫ s in (0 : ℝ)..t, -N j s) + ∫ s in (0 : ℝ)..t, R j s x := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc_right ht.2
    have hNint := ((hNc j).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hRint := ((hRc j).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 ((hUc j).mono hsub)
      (fun r hr => (hStage j r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
        (mem_of_superset (Ioo_mem_nhds hr.1 (hr.2.trans_le ht.2)) Ioo_subset_Icc_self))
      (hNint.add hRint)
    change (∫ r in (0 : ℝ)..t, N j r + R j r x) =
      (U j t : Vec3 → Vec3) x - (U j 0 : Vec3 → Vec3) x at hFTC
    rw [intervalIntegral.integral_add hNint hRint] at hFTC
    rw [intervalIntegral.integral_neg, sub_neg_eq_add, add_assoc, hFTC]
    abel
  have hLim := integratedLimit_of_uniformConvergence hS.le hU hN.neg hR
    (fun j => (hNc j).neg) hRc hInt
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · change (u t : Vec3 → Vec3) x = (u 0 : Vec3 → Vec3) x + ∫ s in (0 : ℝ)..t, n s
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg, sub_neg_eq_add] using hLim.1 t ht
  · simpa only [Pi.neg_apply, neg_neg] using hLim.2 t ht


/-- On a compact prefix, the periodic stage equations with a uniformly vanishing
residual give both the actual limiting projected equation and joint smoothness. -/
theorem periodicProjectedEuler_of_stage_limits {S : ℝ} (hS : 0 < S)
    {U R : ℕ → Velocity} {u : Velocity}
    (hStageSmooth : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (U j))
      (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hStagePeriodic : ∀ j t, t ∈ Icc 0 S → SpatiallyPeriodic (U j t))
    (huSmooth : ∀ t ∈ Icc 0 S, ContDiff ℝ ∞ (u t))
    (hU : TendstoUniformlyOn (fun j => Function.uncurry (U j)) (Function.uncurry u)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hJets : ∀ m, TendstoUniformlyOn
      (fun j (p : ℝ × Vec3) => iteratedFDeriv ℝ m (U j p.1) p.2)
      (fun p : ℝ × Vec3 => iteratedFDeriv ℝ m (u p.1) p.2) atTop (Icc 0 S ×ˢ univ))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (R j)) (fun _ => 0)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hStage : ∀ j t, t ∈ Icc 0 S → ∀ x,
      HasDerivWithinAt (fun r => U j r x)
        (periodicProjectedMomentum (U j t) (U j t) x + R j t x) (Icc 0 S) t) :
    (∀ t ∈ Icc 0 S, ∀ x,
      u t x = u 0 x + endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) ∧
    (∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x) (periodicProjectedMomentum (u t) (u t) x) (Icc 0 S) t) ∧
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ (univ : Set Vec3)) := by
  classical
  let I := Icc (0 : ℝ) S
  have hStageJets (j : ℕ) := stage_spatial_jets_of_joint_smoothness hS (hStageSmooth j)
  have hPeriodic (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (u t) := by
    intro n x
    have h₁ := hU.tendsto_at (x := (t, x + latticeVector n)) ⟨ht, mem_univ _⟩
    have h₂ := hU.tendsto_at (x := (t, x)) ⟨ht, mem_univ _⟩
    exact tendsto_nhds_unique_of_eventuallyEq h₁ h₂
      (Eventually.of_forall fun j => hStagePeriodic j t ht n x)
  have hJetCont (m : ℕ) := (hJets m).continuousOn
    (Frequently.of_forall fun j => (hStageJets j).2 m)
  let Uₛ (j : ℕ) (t : ℝ) : smoothPeriodicVelocity :=
    if ht : t ∈ I then ⟨U j t, (hStageJets j).1 t ht, hStagePeriodic j t ht⟩ else 0
  let uₛ (t : ℝ) : smoothPeriodicVelocity :=
    if ht : t ∈ I then ⟨u t, huSmooth t ht, hPeriodic t ht⟩ else 0
  have hUs (j : ℕ) (t : ℝ) (ht : t ∈ I) : (Uₛ j t : Vec3 → Vec3) = U j t := by
    simp only [Uₛ, dite_eq_left ht]
  have hus (t : ℝ) (ht : t ∈ I) : (uₛ t : Vec3 → Vec3) = u t := by
    simp only [uₛ, dite_eq_left ht]
  have hJetLimit : TendstoUniformlyOn (fun j t => periodicVelocityJets 2 (Uₛ j t))
      (fun t => periodicVelocityJets 2 (uₛ t)) atTop I := by
    apply tendstoUniformlyOn_periodicVelocityJets_of_iteratedFDeriv
    intro m _
    exact ((hJets m).congr (Eventually.of_forall fun j p hp => by rw [hUs j p.1 hp.1])).congr_right
      (fun p hp => by rw [hus p.1 hp.1])
  have hCStage (j : ℕ) := continuousOn_periodicVelocityJets_of_joint_spatialJets (Uₛ j)
    (fun m => ((hStageJets j).2 m).congr fun p hp => by rw [hUs j p.1 hp.1]) 2
  have hCu := continuousOn_periodicVelocityJets_of_joint_spatialJets uₛ
    (fun m => (hJetCont m).congr fun p hp => by rw [hus p.1 hp.1]) 2
  have hDynamics (x : Vec3) :
      (∀ t ∈ I, u t x = u 0 x + endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) ∧
      (∀ t ∈ I, HasDerivWithinAt (fun r => u r x) (periodicProjectedMomentum (u t) (u t) x) I t) := by
    have hmaps : I ⊆ (fun r => (r, x)) ⁻¹' (I ×ˢ (univ : Set Vec3)) :=
      fun r hr => ⟨hr, mem_univ x⟩
    have hU' := (((hU.comp (fun t => (t, x))).mono hmaps).congr
      (Eventually.of_forall fun j t ht => congrFun (hUs j t ht).symm x)).congr_right
      (fun t ht => congrFun (hus t ht).symm x)
    have hUc (j : ℕ) : ContinuousOn (fun t => (Uₛ j t : Vec3 → Vec3) x) I :=
      (((hStageSmooth j).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn) hmaps).congr
        (fun t ht => congrFun (hUs j t ht) x)
    have hRc (j : ℕ) : ContinuousOn (fun t => R j t x) I := by
      have hTime : ContinuousOn (fun t => derivWithin (fun r => U j r x) I t) I :=
        (contDiffOn_sliceTimeDerivWithin_Icc hS (hStageSmooth j)).continuousOn.comp
          (continuous_id.prodMk continuous_const).continuousOn hmaps
      have hMom : ContinuousOn (fun t => periodicProjectedMomentum (U j t) (U j t) x) I :=
        (continuousOn_periodicProjectedMomentum (Uₛ j) (hCStage j) x).congr
          (fun t ht => by
            change periodicProjectedMomentum (U j t) (U j t) x =
              periodicProjectedMomentum (Uₛ j t) (Uₛ j t) x
            rw [hUs j t ht])
      refine (hTime.sub hMom).congr fun t ht => ?_
      change R j t x = derivWithin (fun r => U j r x) (Icc 0 S) t -
        periodicProjectedMomentum (U j t) (U j t) x
      rw [(hStage j t ht x).derivWithin (uniqueDiffOn_Icc hS t ht)]
      abel
    have hStage' (j : ℕ) (t : ℝ) (ht : t ∈ I) :
        HasDerivWithinAt (fun r => (Uₛ j r : Vec3 → Vec3) x)
          (periodicProjectedMomentum (Uₛ j t) (Uₛ j t) x + R j t x) I t := by
      rw [hUs j t ht]
      exact (hStage j t ht x).congr_of_mem (fun r hr => congrFun (hUs j r hr) x) ht
    have hL := integrated_periodicProjectedMomentum_of_uniformLimits hS x hU' hJetLimit
      hUc hCStage hCu ((hR.comp (fun t => (t, x))).mono hmaps) hRc hStage'
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have hintegral : endpointPrimitive (fun s => periodicProjectedMomentum (uₛ s) (uₛ s) x) t =
          endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t := by
        apply endpointPrimitive_congr_ae _ ht
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := S))]
          with s hs
        rw [hus s (Ioc_subset_Icc_self hs)]
      simpa only [hus t ht, hus 0 ⟨le_rfl, hS.le⟩, hintegral] using hL.1 t ht
    · have hd := hL.2 t ht
      rw [hus t ht] at hd
      exact hd.congr_of_mem (fun r hr => congrFun (hus r hr).symm x) ht
  have hEq (t : ℝ) (ht : t ∈ I) (x : Vec3) := (hDynamics x).1 t ht
  exact ⟨hEq, fun t ht x => (hDynamics x).2 t ht,
    contDiffOn_periodicEulerVelocity_of_integrated_projected_momentum hS huSmooth hPeriodic hJetCont hEq⟩


private theorem projectedMomentum_contDiff_slice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (f t) := by
  have hp : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
  exact contDiffOn_univ.1 (hf.comp hp.contDiffOn fun x _ => ⟨ht, mem_univ x⟩)

private theorem projectedMomentum_hasDerivWithinAt {a b : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc a b ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc a b) (x : Vec3) :
    HasDerivWithinAt (fun r => u r x) (derivWithin (fun r => u r x) (Icc a b) t) (Icc a b) t := by
  have hj : ContDiff ℝ ∞ (fun s : ℝ => (s, x)) := contDiff_id.prodMk contDiff_const
  exact ((hu.comp hj.contDiffOn fun s hs => ⟨hs, mem_univ x⟩).differentiableOn (by simp) t ht).hasDerivWithinAt

/-- The within-slab time derivative of a smooth solenoidal field is fixed by the actual Leray projection. -/
theorem periodicLerayHolderLift_sliceTimeDerivWithin_eq_self
    {a b : ℝ} (hab : a < b) {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc a b ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc a b, SpatiallyPeriodic (u t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, divergence (u t) x = 0) {t : ℝ} (ht : t ∈ Icc a b) :
    periodicLerayHolderLift (fun x => derivWithin (fun r => u r x) (Icc a b) t) =
      fun x => derivWithin (fun r => u r x) (Icc a b) t := by
  let W : Velocity := fun r x => derivWithin (fun s => u s x) (Icc a b) r
  have hW : ContDiffOn ℝ ∞ (Function.uncurry W) (Icc a b ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hab hu
  have hWs : ContDiff ℝ ∞ (W t) := projectedMomentum_contDiff_slice hW ht
  have hWper : SpatiallyPeriodic (W t) := fun n x =>
    derivWithin_congr (fun r hr => hper r hr n x) (hper t ht n x)
  obtain ⟨v, hv, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hWper
    (spatialHolderHalf_of_contDiff_periodic hWs hWper 0)
  have hvSol : v ∈ endpointHalfHolderSolenoidal := by
    rw [mem_endpointHalfHolderSolenoidal]
    intro p
    let F (r : ℝ) (x : Vec3) := ⟪gradient p.lift x, u r x⟫_ℝ
    let D (r : ℝ) (x : Vec3) := ⟪gradient p.lift x, W r x⟫_ℝ
    have hPG : Continuous (gradient p.lift) :=
      (InnerProductSpace.toDual ℝ Vec3).symm.continuous.comp (p.smooth.continuous_fderiv (by simp))
    have hG : Continuous (fun q : ℝ × Vec3 => gradient p.lift q.2) := hPG.comp continuous_snd
    have hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ centeredCell) :=
      (hG.continuousOn.inner hu.continuousOn).mono (prod_mono_right (subset_univ _))
    have hD : ContinuousOn (Function.uncurry D) (Icc a b ×ˢ centeredCell) :=
      (hG.continuousOn.inner hW.continuousOn).mono (prod_mono_right (subset_univ _))
    have hder (r : ℝ) (hr : r ∈ Icc a b) (x : Vec3) (_ : x ∈ centeredCell) :
        HasDerivWithinAt (fun s => F s x) (D r x) (Icc a b) r :=
      (innerSL ℝ (gradient p.lift x)).hasFDerivAt.comp_hasDerivWithinAt r
        (projectedMomentum_hasDerivWithinAt hu hr x)
    have hInt := hasDerivWithinAt_integral_prod_Icc isCompact_centeredCell ht hF hD hder
    have hZero (r : ℝ) (hr : r ∈ Icc a b) : (0 : ℝ) = ∫ x in centeredCell, F r x := by
      have hSlice : ContDiff ℝ ∞ (u r) := projectedMomentum_contDiff_slice hu hr
      symm
      rw [show (∫ x in centeredCell, F r x) = ∫ x in centeredCell,
        ⟪gradient p.lift x, u r x⟫_ℝ from rfl,
        integral_gradient_pair_centeredCell (p.smooth.of_le (by simp)) (hSlice.of_le (by simp))
          p.periodic (hper r hr)]
      simp only [hdiv r hr, mul_zero, integral_zero, neg_zero]
    have hConst := (hInt.congr_of_mem hZero ht).derivWithin (uniqueDiffOn_Icc hab t ht)
    change derivWithin (Function.const ℝ (0 : ℝ)) (Icc a b) t = _ at hConst
    rw [derivWithin_const] at hConst
    rw [torusIntegral_eq_centeredCell]
    simp only [endpointPotentialGradient_toUnitTorus, hv]
    exact hConst.symm
  rw [show (fun x => derivWithin (fun r => u r x) (Icc a b) t) =
      fun x => HalfHolder.eval (toUnitTorus x) v from (funext hv).symm,
    periodicLerayHolderLift_pullback, (endpointStrongSpatialLeray_fixed_iff v).mpr hvSol]

/-- A projected momentum identity gives the pointwise evolution with the projected tensor divergence. -/
theorem hasDerivWithinAt_of_closedSlabLerayMomentum
    {a b : ℝ} (hab : a < b) {u R : Velocity}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc a b ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc a b, SpatiallyPeriodic (u t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, divergence (u t) x = 0)
    (hR : ∀ t ∈ Icc a b, closedSlabLerayMomentum a b u t = R t)
    {t : ℝ} (ht : t ∈ Icc a b) (x : Vec3) :
    HasDerivWithinAt (fun r => u r x)
      (R t x - periodicLerayHolderLift (momentumTensorDivergence ∘
        fderiv ℝ (fun y => momentumTensor (u t y) (u t y))) x) (Icc a b) t := by
  let W : Velocity := fun r y => derivWithin (fun s => u s y) (Icc a b) r
  let adv (y : Vec3) := fderiv ℝ (u t) y (u t y)
  have hW : ContDiffOn ℝ ∞ (Function.uncurry W) (Icc a b ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hab hu
  have hWs : ContDiff ℝ ∞ (W t) := projectedMomentum_contDiff_slice hW ht
  have hWper : SpatiallyPeriodic (W t) := fun n y =>
    derivWithin_congr (fun r hr => hper r hr n y) (hper t ht n y)
  have hUs : ContDiff ℝ ∞ (u t) := projectedMomentum_contDiff_slice hu ht
  have hAd : ContDiff ℝ ∞ adv := (hUs.fderiv_right (m := ∞) (by simp)).clm_apply hUs
  have hAdper : SpatiallyPeriodic adv := by
    intro n y
    change fderiv ℝ (u t) (y + latticeVector n) (u t (y + latticeVector n)) = fderiv ℝ (u t) y (u t y)
    rw [(hper t ht).fderiv (hUs.differentiable (by simp)) n y, hper t ht n y]
  have hCut := hR t ht
  change periodicLerayHolderLift (W t + adv) = R t at hCut
  rw [periodicLerayHolderLift_add hWper hAdper (spatialHolderHalf_of_contDiff_periodic hWs hWper 0)
    (spatialHolderHalf_of_contDiff_periodic hAd hAdper 0),
    periodicLerayHolderLift_sliceTimeDerivWithin_eq_self hab hu hper hdiv ht] at hCut
  have hA : momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (u t y) (u t y)) = adv :=
    momentumTensorDivergence_self_eq_advection (hUs.differentiable (by simp)) (hdiv t ht)
  rw [hA]
  exact (projectedMomentum_hasDerivWithinAt hu ht x).congr_deriv
    (eq_sub_of_add_eq (congrFun hCut x))

/-- The actual stage velocity is the initial slice plus the integral of the projected stage equation. -/
theorem eq_endpointPrimitive_of_closedSlabLerayMomentum
    {S : ℝ} (hS : 0 < S) {u R : Velocity}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 S, SpatiallyPeriodic (u t))
    (hdiv : ∀ t ∈ Icc 0 S, ∀ x, divergence (u t) x = 0)
    (hR : ∀ t ∈ Icc 0 S, closedSlabLerayMomentum 0 S u t = R t)
    {t : ℝ} (ht : t ∈ Icc 0 S) (x : Vec3) :
    u t x = u 0 x + endpointPrimitive (fun r =>
      R r x - periodicLerayHolderLift (momentumTensorDivergence ∘
        fderiv ℝ (fun y => momentumTensor (u r y) (u r y))) x) t := by
  let F (r : ℝ) := R r x - periodicLerayHolderLift (momentumTensorDivergence ∘
    fderiv ℝ (fun y => momentumTensor (u r y) (u r y))) x
  have hder (r : ℝ) (hr : r ∈ Icc 0 S) : HasDerivWithinAt (fun s => u s x) (F r) (Icc 0 S) r :=
    hasDerivWithinAt_of_closedSlabLerayMomentum hS hu hper hdiv hR hr x
  have hF : ContinuousOn F (Icc 0 S) := by
    have hW := contDiffOn_sliceTimeDerivWithin_Icc hS hu
    refine (hW.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ x⟩)).congr ?_
    intro r hr
    exact ((hder r hr).derivWithin (uniqueDiffOn_Icc hS r hr)).symm
  have hc : ContinuousOn (fun r => u r x) (Icc 0 S) :=
    hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ x⟩)
  have hInc : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc_right ht.2
  have hint : ∫ r in (0 : ℝ)..t, F r = u t x - u 0 x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hc.mono hInc) (fun r hr =>
      (hder r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))) ((hF.mono hInc).intervalIntegrable_of_Icc ht.1)
  change u t x = u 0 x + ∫ r in (0 : ℝ)..t, F r
  rw [hint]
  abel



/-- Proposition 8.1's projected evolution and joint preterminal velocity
regularity, from the inductive velocity bounds and actual projected residuals. -/
theorem exists_inductive_periodicEulerProjectedLimit
    {T : ℝ} {slab freq activation : ℕ → ℝ} {q : ℕ → ℕ} {U O R : ℕ → Velocity}
    (hT : 0 < T) (hslab : ∀ n, T ≤ slab n) (hinit : 2 ≤ freq 0)
    (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (hq : Tendsto q atTop atTop)
    (hactivation : Tendsto activation atTop (𝓝 T))
    (hUstage : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (U n))
      (Icc 0 (slab n) ×ˢ (univ : Set Vec3)))
    (hper : ∀ n t, t ∈ Icc 0 (slab n) → SpatiallyPeriodic (U n t))
    (hodd : ∀ n t, t ∈ Icc 0 (slab n) → Function.Odd (U n t))
    (hdiv : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, divergence (U n t) x = 0)
    (hOvanish : ∀ n ≥ 2, ∀ t ∈ Icc 0 (activation n), O n t = 0)
    (hO : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x,
      ‖O (n + 1) t x‖ ≤ (freq (n + 1))⁻¹)
    (hB : ∀ n m, m ≤ q (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)), ∀ x,
      ‖iteratedFDeriv ℝ m (U (n + 1) t - U n t - O (n + 1) t) x‖ ≤ (freq (n + 1))⁻¹)
    (hProj : ∀ n t, t ∈ Icc 0 (slab n) → closedSlabLerayMomentum 0 (slab n) (U n) t = R n t)
    (hResidual : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, ‖R n t x‖ ≤ ((freq (n + 1))⁻¹)^3) :
    ∃ u : Velocity,
      ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (U n)) (Function.uncurry u)
        atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3)) ∧
      (∀ t ∈ Ico 0 T, SpatiallyPeriodic (u t) ∧ Function.Odd (u t) ∧
        (∀ x, divergence (u t) x = 0) ∧
        ∀ x, timeDerivative T u t x = periodicProjectedMomentum (u t) (u t) x) ∧
      ∀ S, 0 < S → S < T → ∀ m, TendstoUniformlyOn
        (fun n (p : ℝ × Vec3) => iteratedFDeriv ℝ m (U n p.1) p.2)
        (fun p : ℝ × Vec3 => iteratedFDeriv ℝ m (u p.1) p.2)
        atTop (Icc 0 S ×ˢ (univ : Set Vec3)) := by
  obtain ⟨u, hu, hU, hLocal⟩ := exists_inductive_velocity_limit_and_spatial_jets hT hslab
    hinit hfreq hq hUstage hO hB
  have hPrefix (S : ℝ) (hST : S < T) :=
    hLocal (Icc 0 S) univ (Icc_subset_Icc_right hST.le) isOpen_univ
      (inductive_oscillations_eventually_zero_on_prefix hactivation hST hOvanish)
  have hDecay : Tendsto (fun n => ((freq (n + 1))⁻¹)^3) atTop (𝓝 0) := by
    simpa only [Nat.add_comm, zero_pow (by decide : 3 ≠ 0)] using
      (reciprocal_inductive_frequency_tail hinit hfreq 1).1.tendsto_atTop_zero.pow 3
  have hDynamics (S : ℝ) (hS : 0 < S) (hST : S < T) := by
    have hsub (n : ℕ) : Icc 0 S ⊆ Icc 0 (slab n) :=
      Icc_subset_Icc_right (hST.le.trans (hslab n))
    have hRlim : TendstoUniformlyOn (fun j => Function.uncurry (R j)) (fun _ => 0)
        atTop (Icc 0 S ×ˢ (univ : Set Vec3)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hDecay.eventually (Iio_mem_nhds hε)] with j hj p hp
      rw [dist_comm, dist_zero_right]
      exact (hResidual j p.1 (hsub j hp.1) p.2).trans_lt hj
    have hStage (j t) (ht : t ∈ Icc 0 S) (x : Vec3) :
        HasDerivWithinAt (fun r => U j r x)
          (periodicProjectedMomentum (U j t) (U j t) x + R j t x) (Icc 0 S) t := by
      have h := (hasDerivWithinAt_of_closedSlabLerayMomentum (hT.trans_le (hslab j))
        (hUstage j) (hper j) (hdiv j) (hProj j) (hsub j ht) x).mono (hsub j)
      simpa only [periodicProjectedMomentum, Pi.neg_apply, sub_eq_add_neg, add_comm] using h
    exact periodicProjectedEuler_of_stage_limits hS
      (fun j => (hUstage j).mono (prod_mono_left (hsub j)))
      (fun j t ht => hper j t (hsub j ht))
      (fun t ht => contDiffOn_univ.mp ((hPrefix S hST).1 t ht))
      (hU.mono (prod_mono_left (Icc_subset_Icc_right hST.le)))
      (fun m => ((hPrefix S hST).2 m).1) hRlim hStage
  have hdt : ∀ t ∈ Ico 0 T, ∀ x,
      timeDerivative T u t x = periodicProjectedMomentum (u t) (u t) x := by
    apply timeDerivative_eq_of_prefix_dynamics
    intro S hST t ht x
    obtain ⟨s, hs, hsT⟩ := exists_between (max_lt hST hT)
    have hs₀ : 0 < s := (le_max_right S 0).trans_lt hs
    have hSs : S ≤ s := (le_max_left S 0).trans hs.le
    exact (((hDynamics s hs₀ hsT).2.1 t ⟨ht.1, ht.2.trans hSs⟩ x).mono
      (Icc_subset_Icc_right hSs))
  refine ⟨u, hu, hU, contDiffOn_halfOpen_of_closedPrefixes (fun S hS hST =>
    (hDynamics S hS hST).2.2), ?_, fun S _ hST m => ((hPrefix S hST).2 m).1⟩
  intro t ht
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hmem : t ∈ Icc 0 S := ⟨ht.1, htS.le⟩
  have hmemT : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hmemStage (j : ℕ) : t ∈ Icc 0 (slab j) :=
    Icc_subset_Icc_right (hslab j) hmemT
  obtain ⟨huper, huodd⟩ := periodic_odd_of_pointwise_limit
    (fun x => hU.tendsto_at (x := (t, x)) ⟨hmemT, mem_univ _⟩)
    (fun j => hper j t (hmemStage j)) (fun j => hodd j t (hmemStage j))
  refine ⟨huper, huodd, ?_, hdt t ht⟩
  intro x
  exact divergence_eq_zero_of_tendsto_fderiv
    ((tendstoUniformlyOn_spatial_fderiv_of_first_jet ((hPrefix S hST).2 1).1).tendsto_at
      (x := (t, x)) ⟨hmem, mem_univ _⟩)
    (fun j => hdiv j t (hmemStage j) x)


/-- The negative Leray complement is the actual gradient of a normalized periodic potential. -/
theorem exists_periodicPressure_of_lerayComplement {f : Vec3 → Vec3}
    (hper : SpatiallyPeriodic f) (hf : SpatialHolderHalf 0 f) :
    ∃ p : Vec3 → ℝ, SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
      ∀ x, HasGradientAt p (periodicLerayHolderLift f x - f x) x := by
  obtain ⟨u, hu, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hper hf
  have hPu : periodicLerayHolderLift f =
      fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray u) := by
    rw [← funext hu, periodicLerayHolderLift_pullback]
  let c := endpointStrongSpatialProjection (-u)
  obtain ⟨p, hp, hm, hGrad⟩ := exists_endpointPressure_of_projected_equation (-u) c
    (endpointStrongSpatialProjection_agrees_weak (-u))
  have hc : (c : HalfHolder (UnitAddTorus (Fin 3)) Vec3) = -endpointStrongSpatialLeray u := by
    change endpointStrongSpatialLeray (-u) = _
    exact endpointStrongSpatialLeray.map_neg u
  refine ⟨p, hp, hm, fun x => ?_⟩
  have h := hGrad x
  rw [hc, map_sub, map_neg, map_neg, hu, ← congrFun hPu x, neg_sub_neg, sub_eq_add_neg] at h
  exact h

private theorem projectedPressure_slice {T : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (u t) := by
  have h := hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x (_ : x ∈ (univ : Set Vec3)) => mem_prod.mpr ⟨ht, mem_univ x⟩)
  exact contDiffOn_univ.mp h

/-- The actual projected Euler momentum equation yields a jointly smooth mean-zero pressure. -/
theorem exists_isEulerSolution_of_periodicProjectedMomentum {T : ℝ} {u : Velocity}
    (hT : 0 < T) (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Ico 0 T, SpatiallyPeriodic (u t))
    (hdiv : ∀ t ∈ Ico 0 T, ∀ x, divergence (u t) x = 0)
    (hdyn : ∀ t ∈ Ico 0 T, ∀ x,
      timeDerivative T u t x = periodicProjectedMomentum (u t) (u t) x) :
    ∃ p : Pressure, IsEulerSolution T u p ∧
      ∀ t ∈ Ico 0 T, ∀ x, HasGradientAt (p t)
        (-(timeDerivative T u t x + fderiv ℝ (u t) x (u t x))) x := by
  let I := Ico (0 : ℝ) T
  let A (t : ℝ) (x : Vec3) := fderiv ℝ (u t) x (u t x)
  let G (t : ℝ) (x : Vec3) := -(timeDerivative T u t x + A t x)
  have hAs (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (A t) := by
    have hUs := projectedPressure_slice hu ht
    exact (hUs.fderiv_right (m := ∞) (by simp)).clm_apply hUs
  have hAp (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (A t) := by
    intro n x
    have hUs := projectedPressure_slice hu ht
    change fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) = fderiv ℝ (u t) x (u t x)
    rw [(hper t ht).fderiv (hUs.differentiable (by simp)) n x, hper t ht n x]
  have hGeom (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      G t x = periodicLerayHolderLift (A t) x - A t x := by
    have huD := (projectedPressure_slice hu ht).differentiable (by simp)
    have hA : momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (u t y) (u t y)) = A t :=
      momentumTensorDivergence_self_eq_advection huD (hdiv t ht)
    have hD := hdyn t ht x
    rw [periodicProjectedMomentum, hA, Pi.neg_apply] at hD
    change -(timeDerivative T u t x + A t x) = _
    rw [hD]
    abel
  have hs (t : ℝ) : ∃ p : Vec3 → ℝ, t ∈ I → SpatiallyPeriodic p ∧
      (∫ x in centeredCell, p x) = 0 ∧ ∀ x, HasGradientAt p (G t x) x := by
    by_cases ht : t ∈ I
    · obtain ⟨p, hp, hm, hg⟩ := exists_periodicPressure_of_lerayComplement (hAp t ht)
        (spatialHolderHalf_of_contDiff_periodic (hAs t ht) (hAp t ht) 0)
      exact ⟨p, fun _ => ⟨hp, hm, fun x => (hGeom t ht x).symm ▸ hg x⟩⟩
    · exact ⟨fun _ => 0, fun ht' => (ht ht').elim⟩
  choose p hp using hs
  have hSpace : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) (I ×ˢ univ) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Ico 0 T) (by simpa using hu)
  have hTime : ContDiffOn ℝ ∞ (Function.uncurry (timeDerivative T u)) (I ×ˢ univ) :=
    contDiffOn_timeDerivative_of_joint_contDiff (by simpa using hu)
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) (I ×ˢ univ) := (hTime.add (hSpace.clm_apply hu)).neg
  have hP : ContDiffOn ℝ ∞ (Function.uncurry p) (I ×ˢ univ) :=
    contDiffOn_pressure_of_joint_contDiff_gradient hG (fun t ht => (hp t ht).2.2)
      (fun t ht => (hp t ht).2.1)
  refine ⟨p, ⟨hT, hu, hP, hper, (fun t ht => (hp t ht).1), (fun t ht => (hp t ht).2.1), ?_, hdiv⟩,
    fun t ht => (hp t ht).2.2⟩
  intro t ht x
  rw [((hp t ht).2.2 x).gradient]
  change timeDerivative T u t x + A t x + -(timeDerivative T u t x + A t x) = 0
  exact add_neg_cancel _


section HolderConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_nonneg_of_spatialHolderHalfConvergence {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) : 0 ≤ spatialHolderHalfNorm m f := by
  unfold spatialHolderHalfNorm
  apply Finset.sum_nonneg
  intro j hj
  obtain ⟨hSup, hHolder⟩ := hf.2 j (Finset.mem_range_succ_iff.mp hj)
  apply add_nonneg
  · exact (norm_nonneg _).trans (norm_le_spatialSupNorm hSup 0)
  · have h := le_ciSup hHolder ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) (0, 0) = 0 by
      simp [spatialHolderHalfQuotient]] at h
    exact h

/-- A common bound through the next spatial jet controls the half-Hölder norm of the difference. -/
theorem spatialHolderHalf_sub_le_of_uniform_jet_error {m : ℕ} {f g : Vec3 → E} {δ : ℝ}
    (hδ : 0 ≤ δ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : ∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x‖ ≤ δ) :
    SpatialHolderHalf m (f - g) ∧
      spatialHolderHalfNorm m (f - g) ≤ (3 * ((m : ℝ) + 1)) * δ := by
  have hJet (k : ℕ) (hk : k ≤ m + 1) (x : Vec3) : ‖iteratedFDeriv ℝ k (f - g) x‖ ≤ δ := by
    rw [iteratedFDeriv_sub (hf.of_le (by simp)) (hg.of_le (by simp)), Pi.sub_apply]
    exact h k hk x
  obtain ⟨hH, hN⟩ := spatialHolderHalf_of_bounded_jets (m := m) (hf.sub hg) (fun _ => δ) hJet
  have hs : √(2 * δ * δ) ≤ 2 * δ := by
    calc
      _ ≤ √((2 * δ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
      _ = _ := Real.sqrt_sq (mul_nonneg (by norm_num) hδ)
  refine ⟨hH, hN.trans ?_⟩
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), 3 * δ := Finset.sum_le_sum fun _ _ => by linarith
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- Uniform convergence through one additional spatial jet gives uniform convergence of the
spatial half-Hölder difference norm on the common time set. -/
theorem tendstoUniformlyOn_spatialHolderHalfNorm_sub_of_iteratedFDeriv
    {ι τ : Type*} {l : Filter ι} {I : Set τ} {U : ι → τ → Vec3 → E} {u : τ → Vec3 → E}
    (m : ℕ) (hU : ∀ n t, t ∈ I → ContDiff ℝ ∞ (U n t))
    (hu : ∀ t ∈ I, ContDiff ℝ ∞ (u t))
    (h : ∀ k ≤ m + 1, TendstoUniformlyOn
      (fun n (q : τ × Vec3) => iteratedFDeriv ℝ k (U n q.1) q.2)
      (fun q : τ × Vec3 => iteratedFDeriv ℝ k (u q.1) q.2) l
      (I ×ˢ (univ : Set Vec3))) :
    TendstoUniformlyOn (fun n t => spatialHolderHalfNorm m (U n t - u t)) (fun _ => 0) l I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let C : ℝ := 3 * ((m : ℝ) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / 2 / C
  have hδ : 0 < δ := div_pos (half_pos hε) hC
  have hComp : ∀ᶠ n in l, ∀ k : Fin (m + 2), ∀ q ∈ I ×ˢ (univ : Set Vec3),
      dist (iteratedFDeriv ℝ (k : ℕ) (u q.1) q.2)
        (iteratedFDeriv ℝ (k : ℕ) (U n q.1) q.2) < δ := by
    rw [Filter.eventually_all]
    intro k
    exact Metric.tendstoUniformlyOn_iff.mp (h k (Nat.le_of_lt_succ k.isLt)) δ hδ
  filter_upwards [hComp] with n hn t ht
  have hJet (k : ℕ) (hk : k ≤ m + 1) (x : Vec3) :
      ‖iteratedFDeriv ℝ k (U n t) x - iteratedFDeriv ℝ k (u t) x‖ ≤ δ := by
    have hh := hn ⟨k, Nat.lt_succ_of_le hk⟩ (t, x) ⟨ht, mem_univ x⟩
    rw [dist_comm, dist_eq_norm] at hh
    exact hh.le
  obtain ⟨hH, hN⟩ := spatialHolderHalf_sub_le_of_uniform_jet_error hδ.le (hU n t ht) (hu t ht) hJet
  change spatialHolderHalfNorm m (U n t - u t) ≤ C * δ at hN
  rw [dist_comm, dist_zero_right, Real.norm_of_nonneg (norm_nonneg_of_spatialHolderHalfConvergence hH)]
  refine hN.trans_lt ?_
  dsimp [δ]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hC.ne']
  exact half_lt_self hε


end HolderConvergence

/-- The inductive tower produces an actual preterminal Euler solution with
normalized pressure, together with the continuous terminal velocity and
convergence of all spatial jets on strict prefixes. -/
theorem exists_inductive_periodicEulerSolution
    {T : ℝ} {slab freq activation : ℕ → ℝ} {q : ℕ → ℕ} {U O R : ℕ → Velocity}
    (hT : 0 < T) (hslab : ∀ n, T ≤ slab n) (hinit : 2 ≤ freq 0)
    (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (hq : Tendsto q atTop atTop)
    (hactivation : Tendsto activation atTop (𝓝 T))
    (hUstage : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (U n))
      (Icc 0 (slab n) ×ˢ (univ : Set Vec3)))
    (hper : ∀ n t, t ∈ Icc 0 (slab n) → SpatiallyPeriodic (U n t))
    (hodd : ∀ n t, t ∈ Icc 0 (slab n) → Function.Odd (U n t))
    (hdiv : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, divergence (U n t) x = 0)
    (hOvanish : ∀ n ≥ 2, ∀ t ∈ Icc 0 (activation n), O n t = 0)
    (hO : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x,
      ‖O (n + 1) t x‖ ≤ (freq (n + 1))⁻¹)
    (hB : ∀ n m, m ≤ q (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)), ∀ x,
      ‖iteratedFDeriv ℝ m (U (n + 1) t - U n t - O (n + 1) t) x‖ ≤ (freq (n + 1))⁻¹)
    (hProj : ∀ n t, t ∈ Icc 0 (slab n) → closedSlabLerayMomentum 0 (slab n) (U n) t = R n t)
    (hResidual : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, ‖R n t x‖ ≤ ((freq (n + 1))⁻¹)^3) :
    ∃ (u : Velocity) (p : Pressure),
      IsEulerSolution T u p ∧ (∀ t ∈ Ico 0 T, Function.Odd (u t)) ∧
      ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (U n)) (Function.uncurry u)
        atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ S, 0 < S → S < T → ∀ m, TendstoUniformlyOn
        (fun n (x : ℝ × Vec3) => iteratedFDeriv ℝ m (U n x.1) x.2)
        (fun x : ℝ × Vec3 => iteratedFDeriv ℝ m (u x.1) x.2)
        atTop (Icc 0 S ×ˢ (univ : Set Vec3)) ∧
        TendstoUniformlyOn (fun n t => spatialHolderHalfNorm m (U n t - u t))
          (fun _ => 0) atTop (Icc 0 S) := by
  obtain ⟨u, hucont, hU, husmooth, hkin, hjets⟩ := exists_inductive_periodicEulerProjectedLimit
    hT hslab hinit hfreq hq hactivation hUstage hper hodd hdiv hOvanish hO hB hProj hResidual
  obtain ⟨p, hp, _⟩ := exists_isEulerSolution_of_periodicProjectedMomentum hT husmooth
    (fun t ht => (hkin t ht).1) (fun t ht => (hkin t ht).2.2.1) (fun t ht => (hkin t ht).2.2.2)
  refine ⟨u, p, hp, fun t ht => (hkin t ht).2.1, hucont, hU, fun S hS hST m => ⟨hjets S hS hST m, ?_⟩⟩
  exact tendstoUniformlyOn_spatialHolderHalfNorm_sub_of_iteratedFDeriv m
    (fun n t ht => (stage_spatial_jets_of_joint_smoothness (hT.trans_le (hslab n)) (hUstage n)).1 t
      (Icc_subset_Icc_right (hST.le.trans (hslab n)) ht))
    (fun t ht => hp.contDiff_velocity_slice ⟨ht.1, ht.2.trans_lt hST⟩)
    (fun k _ => hjets S hS hST k)

end

end TorusEuler

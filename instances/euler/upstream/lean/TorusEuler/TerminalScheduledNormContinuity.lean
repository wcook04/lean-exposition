import TorusEuler.TerminalScheduledStages
import TorusEuler.PeriodicEulerLimit

/-! Continuity in the spatial norms of the two auxiliary estimates. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

noncomputable section

/-- Continuity of a spatial field on the closed time slab in the specified
spatial norm, expressed through the spatial norm of differences. -/
def ContinuousOnSlabInSpatialNorm (T : ℝ) (norm : (Vec3 → Vec3) → ℝ)
    (f : Velocity) : Prop :=
  ∀ t ∈ Icc 0 T, Tendsto (fun r => norm (f r - f t)) (𝓝[Icc 0 T] t) (𝓝 0)

set_option maxHeartbeats 1200000 in
/-- One additional uniformly continuous spatial derivative controls the
half-Hölder difference of the fixed-point time jets on the whole torus. -/
theorem slabTimeJet_normContinuity {T : ℝ} (hT : 0 < T) {f : Velocity}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t)) (q m : ℕ) :
    ContinuousOnSlabInSpatialNorm T spatialSupNorm (slabTimeJet 0 T q f) ∧
      ContinuousOnSlabInSpatialNorm T (spatialHolderHalfNorm m) (slabTimeJet 0 T q f) := by
  classical
  let I : Set ℝ := Icc 0 T
  let F := slabTimeJet 0 T q f
  have hF (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (F t) :=
    slabTimeJet_slice_smooth hT hf q ht
  let v (t : ℝ) : smoothPeriodicVelocity :=
    if ht : t ∈ I then ⟨F t, hF t ht, slabTimeJet_periodic hper q ht⟩ else 0
  have hv (t : ℝ) (ht : t ∈ I) : (v t : Vec3 → Vec3) = F t := by
    simp only [v, dite_eq_left ht]
  let J t := periodicVelocityJets (m + 1) (v t)
  let J' (t : ℝ) := (J t : SpatialJetTuple Vec3 Vec3 (m + 1))
  have hJ : ContinuousOn J I :=
    continuousOn_periodicVelocityJets_of_joint_spatialJets v
      (fun k => ((stage_spatial_jets_of_joint_smoothness hT (slabTimeJet_smooth hT hf q)).2 k).congr
        fun p hp => by rw [hv p.1 hp.1]) (m + 1)
  have hDiff {t r : ℝ} (ht : t ∈ I) (hr : r ∈ I) (k : ℕ) (hk : k ≤ m + 1) (x : Vec3) :
      ‖iteratedFDeriv ℝ k (F r) x - iteratedFDeriv ℝ k (F t) x‖ ≤ dist (J r) (J t) := by
    let i : Fin (m + 1 + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    have hEval (s : ℝ) (hs : s ∈ I) : J' s i x = iteratedFDeriv ℝ k (F s) x := by
      calc
        J' s i x = iteratedFDeriv ℝ (i : ℕ) (v s : Vec3 → Vec3) x :=
          periodicVelocityJets_apply (m + 1) (v s) i x
        _ = _ := congrArg (fun g : Vec3 → Vec3 => iteratedFDeriv ℝ k g x) (hv s hs)
    change _ ≤ dist (J' r) (J' t)
    calc
      _ = dist (J' r i x) (J' t i x) := by
        rw [dist_eq_norm, hEval r hr, hEval t ht]
      _ ≤ _ := (BoundedContinuousFunction.dist_coe_le_dist x).trans (dist_le_pi_dist (J' r) (J' t) i)
  have hDist (t : ℝ) (ht : t ∈ I) :
      Tendsto (fun r => dist (J r) (J t)) (𝓝[I] t) (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℝ => J t) (𝓝[I] t) (𝓝 (J t)) := tendsto_const_nhds
    simpa only [dist_self] using (hJ t ht).dist hConst
  constructor
  · intro t ht
    have hb (r : ℝ) (hr : r ∈ I) (x : Vec3) : ‖(F r - F t) x‖ ≤ dist (J r) (J t) := by
      have h := hDiff ht hr 0 (Nat.zero_le _) x
      rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] at h
      exact h
    refine squeeze_zero' ?_ ?_ (hDist t ht)
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := I)] with r hr
      have hB : BddAbove (range fun x => ‖(F r - F t) x‖) := ⟨_, forall_mem_range.mpr (hb r hr)⟩
      exact (norm_nonneg _).trans (norm_le_spatialSupNorm hB 0)
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := I)] with r hr
      exact ciSup_le (hb r hr)
  · intro t ht
    have hb (r : ℝ) (hr : r ∈ I) := spatialHolderHalf_sub_le_of_uniform_jet_error (m := m)
      (dist_nonneg (x := J r) (y := J t)) (hF r hr) (hF t ht) (hDiff ht hr)
    have hLimit : Tendsto (fun r => (3 * ((m : ℝ) + 1)) * dist (J r) (J t))
        (𝓝[I] t) (𝓝 0) := by
      simpa only [mul_zero] using (hDist t ht).const_mul (3 * ((m : ℝ) + 1))
    refine squeeze_zero' ?_ ?_ hLimit
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := I)] with r hr
      exact (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hb r hr).1 (Nat.zero_le m) 0)
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := I)] with r hr
      exact (hb r hr).2

namespace ScheduledEulerConstruction

set_option maxHeartbeats 1800000 in
/-- The actual cutoff velocity and residual are continuous in the
supremum norm after each time derivative. The actual correction is
continuous in every spatial half-Hölder norm after each time derivative. -/
theorem selectedStep_slabTimeJet_normContinuity {P : InductiveEulerParameters}
    (c : ScheduledEulerConstruction P) (n q m : ℕ) :
    let s := c.construction.stages
    let T := s.slab (n + 2)
    ContinuousOnSlabInSpatialNorm T spatialSupNorm (slabTimeJet 0 T q (s.velocity (n + 2))) ∧
      ContinuousOnSlabInSpatialNorm T spatialSupNorm (slabTimeJet 0 T q (s.residual (n + 2))) ∧
      ContinuousOnSlabInSpatialNorm T (spatialHolderHalfNorm m) (slabTimeJet 0 T q
        (fun r x => s.velocity (n + 2) r x - s.velocity (n + 1) r x - s.oscillation (n + 2) r x)) := by
  let d := c.selectedStep n
  let b := d.selected.approximation
  let T := c.construction.stages.slab (n + 2)
  let I : Set ℝ := Icc 0 T
  let J := I ×ˢ (univ : Set Vec3)
  let s := d.stage.cutoff
  let G (r : ℝ) (x : Vec3) := b.meanCorrection r x + (s.velocity r x - b.velocity r x)
  have hT : 0 < T := d.selected.time_pos
  have hV : ContDiffOn ℝ ∞ (Function.uncurry s.velocity) J := s.smooth_velocity
  have hR : ContDiffOn ℝ ∞ (Function.uncurry s.residual) J := s.smooth_residual hT
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) J :=
    d.selected.properties.mean_smooth.add (hV.sub d.selected.properties.velocity_smooth)
  have hGper (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (G t) := by
    intro k x
    obtain ⟨hApprox, _, _, _, hMean⟩ := d.selected.properties.periodic t ht
    change SpatiallyPeriodic (b.velocity t) at hApprox
    change SpatiallyPeriodic (b.meanCorrection t) at hMean
    dsimp only [G]
    rw [hMean k x, hApprox k x, s.periodic_velocity t k x]
  dsimp only
  rw [c.selectedStep_increment_eq n, c.selectedStep_velocity_eq n, c.selectedStep_residual_eq n]
  exact ⟨(slabTimeJet_normContinuity hT hV (fun t _ => s.periodic_velocity t) q m).1,
    (slabTimeJet_normContinuity hT hR (fun _ ht => s.periodic_residual ht) q m).1,
    (slabTimeJet_normContinuity hT hG hGper q m).2⟩

/-- The selected oscillation itself is continuous in every spatial
half-Hölder norm after each Eulerian time derivative. -/
theorem selectedStep_oscillation_slabTimeJet_normContinuity {P : InductiveEulerParameters}
    (c : ScheduledEulerConstruction P) (n q m : ℕ) :
    let s := c.construction.stages
    let T := s.slab (n + 2)
    ContinuousOnSlabInSpatialNorm T (spatialHolderHalfNorm m)
      (slabTimeJet 0 T q (s.oscillation (n + 2))) := by
  dsimp only
  rw [c.stage_oscillation_eq n]
  let d := (c.selectedStep n).selected
  exact (slabTimeJet_normContinuity d.time_pos d.properties.oscillation_smooth
    (fun t ht => (d.properties.periodic t ht).2.2.2.1) q m).2

end ScheduledEulerConstruction

end

end TorusEuler

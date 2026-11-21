import TorusEuler.Theorem11FromInductiveStages
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Smoothness on the closed terminal slab from summable space-time increments. -/

open Filter Metric Set
open scoped ContDiff Topology

namespace TorusEuler

namespace InductiveEulerStages

/-- The mixed-derivative increment bound in the terminal smoothness note.
Time differentiation is at a fixed Eulerian spatial point and uses the
closed slab of the child stage. -/
def HasTerminalMixedIncrementBounds (s : InductiveEulerStages) : Prop :=
  ∀ q m : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (s.slab (n + 1)),
    let v (x : Vec3) := iteratedDerivWithin q
      (fun r => s.velocity (n + 1) r x - s.velocity n r x - s.oscillation (n + 1) r x)
      (Icc 0 (s.slab (n + 1))) t
    SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (s.frequency (n + 1))⁻¹

end InductiveEulerStages

section UniformDerivatives

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform limits of smooth functions and all their derivatives on the
closure of a convex open region are smooth up to the boundary. Here the
derivatives of the approximants are taken within the closed region. -/
theorem contDiffOn_closure_of_uniform_jets
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s)
    (hunique : UniqueDiffOn ℝ (closure s))
    {U : ℕ → E → F} {u : E → F} {p : E → FormalMultilinearSeries ℝ E F}
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) (closure s))
    (hu : TendstoUniformlyOn U u atTop (closure s))
    (hp : ∀ k : ℕ, TendstoUniformlyOn
      (fun j => iteratedFDerivWithin ℝ k (U j) (closure s)) (fun x => p x k) atTop (closure s)) :
    ContDiffOn ℝ ∞ u (closure s) ∧
      ∀ k : ℕ, EqOn (iteratedFDerivWithin ℝ k u (closure s)) (fun x => p x k) (closure s) := by
  have hTaylor (j : ℕ) :
      HasFTaylorSeriesUpToOn ∞ (U j) (ftaylorSeriesWithin ℝ (U j) (closure s)) (closure s) :=
    (hU j).ftaylorSeriesWithin hunique
  have hlt (k : ℕ) : (k : ℕ∞ω) < ∞ := by exact_mod_cast ENat.natCast_lt_top k
  have hpTaylor : HasFTaylorSeriesUpToOn ∞ u p (closure s) := by
    apply (hasFTaylorSeriesUpToOn_top_iff' (by rfl)).2
    constructor
    · intro x hx
      let evalZero := continuousMultilinearCurryFin0 (𝕜 := ℝ) (G := E) (G' := F)
      have hz := evalZero.continuous.continuousAt.tendsto.comp ((hp 0).tendsto_at hx)
      exact tendsto_nhds_unique_of_eventuallyEq hz (hu.tendsto_at hx)
        (Eventually.of_forall fun j => (hTaylor j).zero_eq x hx)
    · intro k x hx
      let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin k.succ => E) F
      have hD := curry.isometry.uniformContinuous.comp_tendstoUniformlyOn (hp k.succ)
      have hderiv (j : ℕ) (y : E) (hy : y ∈ s) :
          HasFDerivAt (iteratedFDerivWithin ℝ k (U j) (closure s))
            ((iteratedFDerivWithin ℝ k.succ (U j) (closure s) y).curryLeft) y :=
        ((hTaylor j).fderivWithin k (hlt k) y (subset_closure hy)).hasFDerivAt
          (mem_of_superset (hs.mem_nhds hy) subset_closure)
      have hOpen (y : E) (hy : y ∈ s) :
          HasFDerivAt (fun z => p z k) ((p y k.succ).curryLeft) y :=
        hasFDerivAt_of_uniform_spatial_limits hs ((hp k).mono subset_closure)
          (hD.mono subset_closure) hderiv hy
      have hc (i : ℕ) : ContinuousOn (fun z => p z i) (closure s) :=
        (hp i).continuousOn
          (Frequently.of_forall fun j => (hTaylor j).cont i (hlt i).le)
      have hct : ContinuousOn (fun z => (p z k.succ).curryLeft) (closure s) :=
        curry.continuous.comp_continuousOn (hc k.succ)
      refine hasFDerivWithinAt_closure_of_tendsto_fderiv
        (fun y hy => (hOpen y hy).differentiableAt.differentiableWithinAt)
        hconv hs (fun y hy => (hc k y hy).mono subset_closure) ?_
      apply ((hct x hx).mono subset_closure).tendsto.congr'
      exact eventually_nhdsWithin_of_forall fun y hy => (hOpen y hy).fderiv.symm
  exact ⟨hpTaylor.contDiffOn, fun k x hx =>
    (hpTaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn
      (hlt k).le hunique hx).symm⟩

/-- Summable consecutive differences at each derivative order give smoothness
on a closed convex slab. The given limit identifies the zero-order series. -/
theorem contDiffOn_closure_of_summable_jet_increments [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s)
    (hunique : UniqueDiffOn ℝ (closure s))
    {U : ℕ → E → F} {u : E → F}
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) (closure s))
    (hu : TendstoUniformlyOn U u atTop (closure s))
    (hinc : ∀ k : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ᶠ j in atTop, ∀ z ∈ closure s,
      dist (iteratedFDerivWithin ℝ k (U j) (closure s) z)
        (iteratedFDerivWithin ℝ k (U (j + 1)) (closure s) z) ≤ b j) :
    ContDiffOn ℝ ∞ u (closure s) ∧ ∀ k : ℕ, TendstoUniformlyOn
      (fun j => iteratedFDerivWithin ℝ k (U j) (closure s))
      (iteratedFDerivWithin ℝ k u (closure s)) atTop (closure s) := by
  have h (k : ℕ) : ∃ v : E → (E [×k]→L[ℝ] F), TendstoUniformlyOn
      (fun j => iteratedFDerivWithin ℝ k (U j) (closure s)) v atTop (closure s) := by
    obtain ⟨b, hb, hstep⟩ := hinc k
    obtain ⟨N, hN⟩ := eventually_atTop.1 hstep
    obtain ⟨v, hv, _⟩ := exists_uniformLimit_of_summable_increments N hb hN
    exact ⟨v, hv⟩
  choose v hv using h
  obtain ⟨hSmooth, hIdent⟩ := contDiffOn_closure_of_uniform_jets hs hconv hunique hU hu
    (p := fun x k => v k x) hv
  exact ⟨hSmooth, fun k => (hv k).congr_right (fun x hx => (hIdent k hx).symm)⟩

end UniformDerivatives

namespace InductiveEulerStages

/-- Near each point of the punctured lift, the mixed-derivative estimate
for the correction is eventually an estimate for the full increment.
The oscillation vanishes on the neighborhood throughout the child slab. -/
theorem eventually_mixed_increment_le_near_offOrigin (s : InductiveEulerStages)
    (hBounds : s.HasTerminalMixedIncrementBounds)
    (hRadius : Tendsto (fun n => (s.frequency n)⁻¹) atTop (𝓝 0))
    {c : Vec3} (hc : c ∈ offOrigin) :
    ∃ r > (0 : ℝ), ∀ q m : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (s.slab (n + 1)),
      ∀ x ∈ closedBall c r,
        ‖iteratedFDeriv ℝ m (fun y => iteratedDerivWithin q
          (fun v => s.velocity (n + 1) v y - s.velocity n v y)
          (Icc 0 (s.slab (n + 1))) t) x‖ ≤ (s.frequency (n + 1))⁻¹ := by
  obtain ⟨R, hR, _, _, _, _, hSep⟩ := exists_offOrigin_compact_neighborhood
    isCompact_singleton (singleton_subset_iff.mpr hc)
  refine ⟨R / 4, by positivity, fun q m => ?_⟩
  have hSmall : ∀ᶠ n in atTop, (s.frequency n)⁻¹ < R / 2 :=
    hRadius.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hSmall, hBounds q m] with n hn hB t ht x hx
  let I := Icc 0 (s.slab (n + 1))
  let U (r : ℝ) (y : Vec3) := s.velocity (n + 1) r y - s.velocity n r y
  let V (r : ℝ) (y : Vec3) := U r y - s.oscillation (n + 1) r y
  have hOsc (r : ℝ) (hr : r ∈ I) (y : Vec3) (hy : y ∈ ball c (R / 2)) :
      s.oscillation (n + 1) r y = 0 := by
    by_contra hne
    obtain ⟨z, hz⟩ := s.oscillation_support n r hr y hne
    have hdist := mem_ball.mp hy
    have htri := dist_triangle (latticeVector z) y c
    linarith [hSep c (mem_singleton c) z]
  have hSlices : EqOn (fun y => iteratedDerivWithin q (fun r => U r y) I t)
      (fun y => iteratedDerivWithin q (fun r => V r y) I t) (ball c (R / 2)) := by
    intro y hy
    apply iteratedDerivWithin_congr _ ht
    intro r hr
    change U r y = U r y - s.oscillation (n + 1) r y
    rw [hOsc r hr y hy, sub_zero]
  have hx' : x ∈ ball c (R / 2) :=
    mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by linarith))
  have hmEq : iteratedFDeriv ℝ m (fun y => iteratedDerivWithin q (fun r => U r y) I t) x =
      iteratedFDeriv ℝ m (fun y => iteratedDerivWithin q (fun r => V r y) I t) x := by
    rw [← iteratedFDerivWithin_of_isOpen m isOpen_ball hx',
      ← iteratedFDerivWithin_of_isOpen m isOpen_ball hx']
    exact iteratedFDerivWithin_congr hSlices hx' m
  change ‖iteratedFDeriv ℝ m (fun y => iteratedDerivWithin q (fun r => U r y) I t) x‖ ≤ _
  rw [hmEq]
  exact (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hB t ht).1 le_rfl x).trans (hB t ht).2

/-- On a closed space-time cylinder, summable bounds for the joint
derivatives of the increments yield the joint jets of the selected limit. -/
theorem terminal_joint_jets_of_increment_bounds (s : InductiveEulerStages)
    {T : ℝ} (hT : 0 < T) (hSlab : ∀ j, T ≤ s.slab j)
    (hSlabDecrease : ∀ j, s.slab (j + 1) ≤ s.slab j)
    {u : Velocity} (hLimit : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry u) atTop (Icc 0 T ×ˢ (univ : Set Vec3)))
    {c : Vec3} {r : ℝ} (hr : 0 < r)
    {weight : ℕ → ℕ → ℝ} (hSum : ∀ k, Summable (weight k))
    (hJoint : ∀ k : ℕ, ∀ᶠ j in atTop, ∀ z ∈ Icc 0 T ×ˢ closedBall c r,
      ‖iteratedFDerivWithin ℝ k
        (fun v : ℝ × Vec3 => s.velocity (j + 1) v.1 v.2 - s.velocity j v.1 v.2)
        (Icc 0 (s.slab (j + 1)) ×ˢ (univ : Set Vec3)) z‖ ≤ weight k j) :
    let S := Icc 0 T ×ˢ closedBall c r
    ContDiffOn ℝ ∞ (Function.uncurry u) S ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun j => iteratedFDerivWithin ℝ k (Function.uncurry (s.velocity j)) S)
        (iteratedFDerivWithin ℝ k (Function.uncurry u) S) atTop S := by
  intro S
  let V := Ioo (0 : ℝ) T ×ˢ ball c r
  have hClosure : closure V = S := by
    dsimp only [S, V]
    rw [closure_prod_eq, closure_Ioo hT.ne, closure_ball c hr.ne']
  have hUniqueBall : UniqueDiffOn ℝ (closedBall c r) := by
    apply uniqueDiffOn_convex (convex_closedBall c r)
    rw [interior_closedBall c hr.ne']
    exact ⟨c, mem_ball_self hr⟩
  have hUnique : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod hUniqueBall
  have hSub (j : ℕ) : S ⊆ Icc 0 (s.slab j) ×ˢ (univ : Set Vec3) :=
    prod_mono (Icc_subset_Icc_right (hSlab j)) (subset_univ _)
  have hStage (j : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (s.velocity j)) S :=
    (s.smooth j).mono (hSub j)
  have hLocal : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry u) atTop S :=
    hLimit.mono (prod_mono_right (subset_univ _))
  rw [← hClosure]
  apply contDiffOn_closure_of_summable_jet_increments (isOpen_Ioo.prod isOpen_ball)
    ((convex_Ioo _ _).prod (convex_ball _ _)) (hClosure ▸ hUnique)
    (fun j => hClosure ▸ hStage j) (hClosure ▸ hLocal)
  intro k
  refine ⟨weight k, hSum k, ?_⟩
  rw [hClosure]
  filter_upwards [hJoint k] with j hj z hz
  let G : (ℝ × Vec3) → Vec3 := fun v => s.velocity (j + 1) v.1 v.2 - s.velocity j v.1 v.2
  let A := Icc 0 (s.slab (j + 1)) ×ˢ (univ : Set Vec3)
  have hUniqueA : UniqueDiffOn ℝ A :=
    (uniqueDiffOn_Icc (hT.trans_le (hSlab (j + 1)))).prod uniqueDiffOn_univ
  have hG : ContDiffOn ℝ k G A :=
    ((s.smooth (j + 1)).sub ((s.smooth j).mono
      (prod_mono_left (Icc_subset_Icc_right (hSlabDecrease j))))).of_le (by simp)
  rw [dist_comm, dist_eq_norm, ← iteratedFDerivWithin_sub_apply
    (((hStage (j + 1)).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) z hz)
    (((hStage j).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) z hz) hUnique hz]
  change ‖iteratedFDerivWithin ℝ k G S z‖ ≤ _
  rw [iteratedFDerivWithin_subset (hSub (j + 1)) hUnique hUniqueA hG hz]
  exact hj z hz

end InductiveEulerStages

end TorusEuler

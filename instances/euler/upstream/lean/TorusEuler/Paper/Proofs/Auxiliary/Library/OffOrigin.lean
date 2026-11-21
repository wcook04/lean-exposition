import TorusEuler.TerminalMixedStageLimits
import TorusEuler.TerminalSeeleyExtension
import TorusEuler.InductiveLimitAssembly
import TorusEuler.SmoothPeriodicHolder
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # The summation off the origin (own content of Auxiliary Theorem 1.1)

Terminal_smoothness.tex:466-484 (proof of Theorem 1.1 of the note): the increments
`U_{j+1} - U_j` are summable with all mixed derivatives on `[0,T_∞] × K`, `K` compact off the
origin, so the sums converge there with all derivatives. This file proves the summation from
the mixed increment bounds only, without any convergence hypothesis on `[0,T] × ℝ³`: the
limit on `[0,T] × (ℝ³ ∖ lattice)` is produced from the summable increments (the library
lemma `InductiveEulerStages.terminal_contDiffOn_of_mixed_increment_bounds` (own content of Aux 1.1,
D16; adapted here as `local_limit_of_mixed_increment_bounds` and `exists_offOrigin_limit`) assumes a limit
`u` on the whole closed slab, which the auxiliary note does not provide near the origin).
The Seeley extension and its periodization are used from the library
(`exists_smoothExtensionOfClosedTimeSlab`, `exists_spatiallyPeriodic_contDiffOn_extension`).
-/

open Filter Metric Set
open scoped ContDiff Topology

namespace TorusEuler.Paper.Lib.Aux

open TorusEuler InductiveEulerStages

/-- Copy of `InductiveEulerStages.terminal_joint_jets_of_increment_bounds` with the uniform
convergence assumed only on the cylinder `[0,T] × closedBall c r` (the original uses it only
through its restriction to that cylinder). Own content of Theorem 1.1 of the note
(terminal_smoothness.tex:466-475). -/
theorem joint_jets_of_increment_bounds (s : InductiveEulerStages)
    {T : ℝ} (hT : 0 < T) (hSlab : ∀ j, T ≤ s.slab j)
    (hSlabDecrease : ∀ j, s.slab (j + 1) ≤ s.slab j)
    {u : Velocity} {c : Vec3} {r : ℝ} (hr : 0 < r)
    (hLocal : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry u) atTop (Icc 0 T ×ˢ closedBall c r))
    {weight : ℕ → ℕ → ℝ} (hSum : ∀ k, Summable (weight k))
    (hJoint : ∀ k : ℕ, ∀ᶠ j in atTop, ∀ z ∈ Icc 0 T ×ˢ closedBall c r,
      ‖iteratedFDerivWithin ℝ k
        (fun v : ℝ × Vec3 => s.velocity (j + 1) v.1 v.2 - s.velocity j v.1 v.2)
        (Icc 0 (s.slab (j + 1)) ×ˢ (univ : Set Vec3)) z‖ ≤ weight k j) :
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ closedBall c r) := by
  let S := Icc 0 T ×ˢ closedBall c r
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
  have hLocal' : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry u) atTop S := hLocal
  show ContDiffOn ℝ ∞ (Function.uncurry u) S
  rw [← hClosure]
  refine (contDiffOn_closure_of_summable_jet_increments (isOpen_Ioo.prod isOpen_ball)
    ((convex_Ioo _ _).prod (convex_ball _ _)) (hClosure ▸ hUnique)
    (fun j => hClosure ▸ hStage j) (hClosure ▸ hLocal') ?_).1
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


/-- Adapted copy of the body of `InductiveEulerStages.terminal_joint_jets_locally_of_mixed_increment_bounds`
(`hSquare` replaced by `s.frequency_square_gap hInit`; the limit is constructed instead of
assumed). Near each point `c` of the punctured lift, the sum of the increments converges uniformly
on `[0,T] × closedBall c r` to a field `v` that is smooth there (terminal_smoothness.tex:466-475:
"Only finitely many `O_j` meet a neighborhood of `K`" and the remaining increments are
summable in every mixed norm by the bound `λ_j⁻¹` and `∑ λ_j⁻¹ < ∞`). -/
theorem local_limit_of_mixed_increment_bounds (s : InductiveEulerStages)
    {T : ℝ} (hT : 0 < T) (hSlab : ∀ j, T ≤ s.slab j)
    (hSlabDecrease : ∀ j, s.slab (j + 1) ≤ s.slab j)
    (hInit : 2 ≤ s.frequency 0) (hBounds : s.HasTerminalMixedIncrementBounds)
    {c : Vec3} (hc : c ∈ offOrigin) :
    ∃ r > (0 : ℝ), ∃ v : Velocity,
      TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j)) (Function.uncurry v) atTop
        (Icc 0 T ×ˢ closedBall c r) ∧
      ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ closedBall c r) := by
  have hSquare := s.frequency_square_gap hInit
  have hRadius : Tendsto (fun j => (s.frequency j)⁻¹) atTop (𝓝 0) := by
    simpa only [zero_add] using
      (reciprocal_inductive_frequency_tail hInit hSquare 0).1.tendsto_atTop_zero
  have hFreq (j : ℕ) : 2 ≤ s.frequency j := by
    induction j with
    | zero => exact hInit
    | succ j ih => exact (by nlinarith : (2 : ℝ) ≤ s.frequency j ^ 2).trans (hSquare j)
  have hSum : Summable (fun j => (s.frequency (j + 1))⁻¹) := by
    simpa only [Nat.add_comm] using (reciprocal_inductive_frequency_tail hInit hSquare 1).1
  obtain ⟨r, hr, hMixed⟩ := s.eventually_mixed_increment_le_near_offOrigin hBounds hRadius hc
  let S := Icc 0 T ×ˢ closedBall c r
  let f (n : ℕ) (z : ℝ × Vec3) : Vec3 :=
    s.velocity (n + 1) z.1 z.2 - s.velocity n z.1 z.2
  have hf : ∀ᶠ n in atTop, ∀ z ∈ S, ‖f n z‖ ≤ (s.frequency (n + 1))⁻¹ := by
    filter_upwards [hMixed 0 0] with n hn z hz
    have h := hn z.1 (Icc_subset_Icc_right (hSlab (n + 1)) hz.1) z.2 hz.2
    simpa [f, iteratedDerivWithin_zero, norm_iteratedFDeriv_zero] using h
  have hTsum := tendstoUniformlyOn_tsum_nat_eventually hSum hf
  let v : Velocity := fun t x => s.velocity 0 t x + ∑' n, f n (t, x)
  have hLim : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry v) atTop S := by
    rw [Metric.tendstoUniformlyOn_iff] at hTsum ⊢
    intro ε hε
    filter_upwards [hTsum ε hε] with N hN z hz
    have hz' := hN z hz
    have hsum : ∑ n ∈ Finset.range N, f n z = s.velocity N z.1 z.2 - s.velocity 0 z.1 z.2 :=
      Finset.sum_range_sub (fun n => s.velocity n z.1 z.2) N
    show dist (Function.uncurry v z) (Function.uncurry (s.velocity N) z) < ε
    have hN' : Function.uncurry (s.velocity N) z =
        s.velocity 0 z.1 z.2 + ∑ n ∈ Finset.range N, f n z := by
      rw [hsum]; change s.velocity N z.1 z.2 = _; abel
    have hv : Function.uncurry v z = s.velocity 0 z.1 z.2 + ∑' n, f n z := rfl
    rw [hN', hv, dist_add_left]
    exact hz'
  refine ⟨r, hr, v, hLim, ?_⟩
  refine joint_jets_of_increment_bounds s hT hSlab hSlabDecrease hr hLim
    (weight := fun k j => (2 : ℝ) ^ k * (s.frequency (j + 1))⁻¹)
    (fun k => hSum.mul_left ((2 : ℝ) ^ k)) ?_
  intro k
  have hSimult : ∀ᶠ j in atTop, ∀ q m : Fin (k + 1), ∀ t ∈ Icc 0 (s.slab (j + 1)),
      ∀ x ∈ closedBall c r,
        ‖iteratedFDeriv ℝ m.val (fun y => iteratedDerivWithin q.val
          (fun v => s.velocity (j + 1) v y - s.velocity j v y)
          (Icc 0 (s.slab (j + 1))) t) x‖ ≤ (s.frequency (j + 1))⁻¹ :=
    Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun m => hMixed q.val m.val
  filter_upwards [hSimult] with j hj z hz
  let G (t : ℝ) (x : Vec3) := s.velocity (j + 1) t x - s.velocity j t x
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G)
      (Icc 0 (s.slab (j + 1)) ×ˢ (univ : Set Vec3)) :=
    (s.smooth (j + 1)).sub
      ((s.smooth j).mono (prod_mono_left (Icc_subset_Icc_right (hSlabDecrease j))))
  have ht : z.1 ∈ Icc 0 (s.slab (j + 1)) := Icc_subset_Icc_right (hSlab (j + 1)) hz.1
  apply norm_iteratedFDerivWithin_uncurry_le_of_mixed
    (hT.trans_le (hSlab (j + 1))) G hG (inv_nonneg.mpr (zero_le_two.trans (hFreq (j + 1)))) ht z.2
  intro q m hqm
  exact hj ⟨q, by omega⟩ ⟨m, by omega⟩ z.1 ht z.2 hz.2

/-- Adapted copy of `InductiveEulerStages.terminal_contDiffOn_of_mixed_increment_bounds` (the
limit is constructed, not assumed). The limit of the stages `U_j` on `[0,T] × (ℝ³ ∖ lattice)`: the pointwise limit exists, and it
is `C^∞` on `[0,T] × offOrigin` (terminal_smoothness.tex:466-477: "The sum therefore converges
with every mixed derivative up to `T_∞` away from zero"). -/
theorem exists_offOrigin_limit (s : InductiveEulerStages)
    {T : ℝ} (hT : 0 < T) (hSlab : ∀ j, T ≤ s.slab j)
    (hSlabDecrease : ∀ j, s.slab (j + 1) ≤ s.slab j)
    (hInit : 2 ≤ s.frequency 0) (hBounds : s.HasTerminalMixedIncrementBounds) :
    ∃ w : Velocity, ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ offOrigin) ∧
      ∀ t ∈ Icc 0 T, ∀ x ∈ offOrigin, Tendsto (fun j => s.velocity j t x) atTop (𝓝 (w t x)) := by
  let w : Velocity := fun t x => limUnder atTop (fun j => s.velocity j t x)
  have hloc (c : Vec3) (hc : c ∈ offOrigin) : ∃ r > (0 : ℝ), ∃ v : Velocity,
      (∀ z ∈ Icc 0 T ×ˢ closedBall c r, Tendsto (fun j => s.velocity j z.1 z.2) atTop (𝓝 (v z.1 z.2))) ∧
      ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ closedBall c r) := by
    obtain ⟨r, hr, v, hLim, hv⟩ :=
      local_limit_of_mixed_increment_bounds s hT hSlab hSlabDecrease hInit hBounds hc
    exact ⟨r, hr, v, fun z hz => hLim.tendsto_at hz, hv⟩
  have hTend (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (hx : x ∈ offOrigin) :
      Tendsto (fun j => s.velocity j t x) atTop (𝓝 (w t x)) := by
    obtain ⟨r, hr, v, hT', -⟩ := hloc x hx
    have := hT' (t, x) ⟨ht, mem_closedBall_self hr.le⟩
    show Tendsto _ _ (𝓝 (limUnder atTop (fun j => s.velocity j t x)))
    exact tendsto_nhds_limUnder ⟨_, this⟩
  refine ⟨w, ?_, hTend⟩
  intro z hz
  obtain ⟨r, hr, v, hT', hv⟩ := hloc z.2 hz.2
  have hOpen : univ ×ˢ ball z.2 r ∈ 𝓝 z :=
    (isOpen_univ.prod isOpen_ball).mem_nhds ⟨mem_univ _, mem_ball_self hr⟩
  have hz' : z ∈ Icc 0 T ×ˢ closedBall z.2 r := ⟨hz.1, mem_closedBall_self hr.le⟩
  have h1 : ContDiffWithinAt ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ offOrigin) z := by
    apply (hv z hz').mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hOpen] with y hy hyb
    exact ⟨hy.1, ball_subset_closedBall hyb.2⟩
  have hEq : Function.uncurry w =ᶠ[𝓝[Icc 0 T ×ˢ offOrigin] z] Function.uncurry v := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hOpen] with y hy hyb
    have hy' : y ∈ Icc 0 T ×ˢ closedBall z.2 r := ⟨hy.1, ball_subset_closedBall hyb.2⟩
    exact (hT' y hy').limUnder_eq
  exact h1.congr_of_eventuallyEq hEq ((hT' z hz').limUnder_eq)

end TorusEuler.Paper.Lib.Aux

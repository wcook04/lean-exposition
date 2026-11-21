import TorusEuler.TerminalMixedLimits
import TorusEuler.TerminalMixedJetBridge

/-! The selected Euler stages converge with all space-time jets away from the origin. -/

open Filter Metric Set
open scoped ContDiff Topology

namespace TorusEuler.InductiveEulerStages

/-- The sum of the actual increments converges with every joint derivative
on a closed cylinder about each point of the punctured lift. -/
theorem terminal_joint_jets_locally_of_mixed_increment_bounds (s : InductiveEulerStages)
    {T : ℝ} (hT : 0 < T) (hSlab : ∀ j, T ≤ s.slab j)
    (hSlabDecrease : ∀ j, s.slab (j + 1) ≤ s.slab j)
    (hInit : 2 ≤ s.frequency 0) (hSquare : ∀ j, s.frequency j ^ 2 ≤ s.frequency (j + 1))
    (hBounds : s.HasTerminalMixedIncrementBounds)
    {u : Velocity} (hLimit : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry u) atTop (Icc 0 T ×ˢ (univ : Set Vec3)))
    {c : Vec3} (hc : c ∈ offOrigin) :
    ∃ r > (0 : ℝ),
      let S := Icc 0 T ×ˢ closedBall c r
      ContDiffOn ℝ ∞ (Function.uncurry u) S ∧
        ∀ k : ℕ, TendstoUniformlyOn
          (fun j => iteratedFDerivWithin ℝ k (Function.uncurry (s.velocity j)) S)
          (iteratedFDerivWithin ℝ k (Function.uncurry u) S) atTop S := by
  have hRadius : Tendsto (fun j => (s.frequency j)⁻¹) atTop (𝓝 0) := by
    simpa only [zero_add] using (reciprocal_inductive_frequency_tail hInit hSquare 0).1.tendsto_atTop_zero
  obtain ⟨r, hr, hMixed⟩ := s.eventually_mixed_increment_le_near_offOrigin hBounds hRadius hc
  have hFreq (j : ℕ) : 2 ≤ s.frequency j := by
    induction j with
    | zero => exact hInit
    | succ j ih => exact (by nlinarith : (2 : ℝ) ≤ s.frequency j ^ 2).trans (hSquare j)
  have hSum : Summable (fun j => (s.frequency (j + 1))⁻¹) := by
    simpa only [Nat.add_comm] using (reciprocal_inductive_frequency_tail hInit hSquare 1).1
  refine ⟨r, hr, s.terminal_joint_jets_of_increment_bounds hT hSlab hSlabDecrease
    hLimit hr (fun k => hSum.mul_left ((2 : ℝ) ^ k)) ?_⟩
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

/-- The closed-slab velocity of the same Euler limit is jointly smooth
away from the singular lattice, including on the terminal slice. -/
theorem terminal_contDiffOn_of_mixed_increment_bounds (s : InductiveEulerStages)
    {T : ℝ} (hT : 0 < T) (hSlab : ∀ j, T ≤ s.slab j)
    (hSlabDecrease : ∀ j, s.slab (j + 1) ≤ s.slab j)
    (hInit : 2 ≤ s.frequency 0) (hSquare : ∀ j, s.frequency j ^ 2 ≤ s.frequency (j + 1))
    (hBounds : s.HasTerminalMixedIncrementBounds)
    {u : Velocity} (hLimit : TendstoUniformlyOn (fun j => Function.uncurry (s.velocity j))
      (Function.uncurry u) atTop (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ offOrigin) := by
  intro z hz
  obtain ⟨r, hr, hLocal, _⟩ := s.terminal_joint_jets_locally_of_mixed_increment_bounds
    hT hSlab hSlabDecrease hInit hSquare hBounds hLimit hz.2
  have hBall : z.2 ∈ closedBall z.2 r := mem_closedBall_self hr.le
  have hOpen : univ ×ˢ ball z.2 r ∈ 𝓝 z :=
    (isOpen_univ.prod isOpen_ball).mem_nhds ⟨mem_univ _, mem_ball_self hr⟩
  apply (hLocal z ⟨hz.1, hBall⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hOpen] with w hw hwBall
  exact ⟨hw.1, ball_subset_closedBall hwBall.2⟩

end TorusEuler.InductiveEulerStages

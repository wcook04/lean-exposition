import TorusEuler.Paper.Proofs.S678b.Library.Common
import TorusEuler.Theorem11FromInductiveStages
import TorusEuler.SmoothPeriodicHolder

/-! # The closed-slab limit `w` of the opening of Section 8

The opening of Section 8 (sections/09_limit.tex:2-5): on `[0,T_∞]`, (7.4) gives
`‖U_j - U_{j-1}‖_{C_tL^∞} ≤ 2λ_j^{-1}`, so the velocities converge uniformly to a continuous
field `w` on `[0,T_∞] × 𝕋³`. Proposition 8.1 identifies `w` with `u` before `T_∞`. Propositions
8.2 and 8.4 read `w` (09b:8-10, 09b:99-100).

* `closedSlab_velocity_limit` builds `w` exactly as the TeX does, from (7.4) at order zero
  alone; no bound on the orders `q_j` enters. Propositions 8.2 and 8.4 use it.
  It also returns the uniform convergence `U_j → w` on the closed slab, which Proposition 8.4
  passes to the off-origin trace lemma (there `q_j → ∞`, from Lemma 1.3, enters only at 09b:96).
* `limit_agreement`: any uniform limit of the `U_j` on the closed slab agrees with `u` before
  `T_∞`. -/

open Filter Set
open scoped Topology ContDiff

namespace TorusEuler.Paper.Lib.S678b

/-- (7.4) at order `m ≤ q_j` as a pointwise bound on the `m`-th derivative of the corrected
increment `U_j - U_{j-1} - O_j` (`j = n + 1`), from the increment clause of Theorem 7.1. -/
theorem increment_jet_bound {P : InductiveEulerParameters} {c : InductiveEulerConstruction P}
    {C T : ℝ} (h71 : Theorem71Conclusions c C T) (n m : ℕ) (hm : m ≤ P.order (n + 1))
    (t : ℝ) (ht : t ∈ Icc 0 (c.stages.slab (n + 1))) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (c.stages.velocity (n + 1) t - c.stages.velocity n t -
        c.stages.oscillation (n + 1) t) x‖ ≤ (P.frequency (n + 1))⁻¹ := by
  have h := (h71.increment (n + 1) (Nat.succ_pos n) t ht).2 m hm
  exact (norm_iteratedFDeriv_le_spatialHolderHalfNorm h.1 le_rfl x).trans h.2

/-- The velocity limit agrees with the solution of Proposition 8.1 before `T_∞` (09b:8-10): if
the `U_j` converge to `w` uniformly on `[0,T_∞] × ℝ³`, then `u(t) = w(t)` for `t < T_∞`, because
`U_j(t) → u(t)` in `C^{0,1/2}` (`h81.convergence` at `m = 0`). -/
theorem limit_agreement {P : InductiveEulerParameters} {c : InductiveEulerConstruction P}
    {C T : ℝ} {u : Velocity} {p : Pressure}
    (h71 : Theorem71Conclusions c C T) (h81 : Proposition81Conclusions c T u p) {w : Velocity}
    (hW : TendstoUniformlyOn (fun n => Function.uncurry (c.stages.velocity n))
      (Function.uncurry w) atTop (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ∀ t ∈ Ico 0 T, u t = w t := by
  obtain ⟨_, _, hSlab⟩ := h71.lifetime
  intro t ht
  funext x
  have h1 : Tendsto (fun j => c.stages.velocity j t x) atTop (𝓝 (w t x)) :=
    hW.tendsto_at (x := (t, x)) ⟨Ico_subset_Icc_self ht, mem_univ _⟩
  have hconv := (h81.convergence t ht.2 0).tendsto_at (x := t) ⟨ht.1, le_rfl⟩
  have hslice (j : ℕ) : ContDiff ℝ ∞ (c.stages.velocity j t) := by
    rw [← contDiffOn_univ]
    exact (h71.T1 j).1.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y _ => ⟨⟨ht.1, ht.2.le.trans (hSlab j).le⟩, mem_univ y⟩)
  have hbound (j : ℕ) :
      ‖c.stages.velocity j t x - u t x‖ ≤
        spatialHolderHalfNorm 0 (c.stages.velocity j t - u t) := by
    have hH := spatialHolderHalf_of_contDiff_periodic
      ((hslice j).sub (h81.euler.contDiff_velocity_slice ht))
      (fun n y => by
        show c.stages.velocity j t (y + _) - u t (y + _) = _
        rw [c.stages.periodic_velocity j t n y, h81.euler.periodic_velocity t ht n y]) 0
    have h := norm_iteratedFDeriv_le_spatialHolderHalfNorm hH le_rfl x
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  have h2 : Tendsto (fun j => c.stages.velocity j t x) atTop (𝓝 (u t x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hbound hconv
  exact tendsto_nhds_unique h2 h1

/-- The closed-slab limit `w` of the opening of Section 8 from (7.4) at order zero alone
(sections/09_limit.tex:2-5): by (7.4) at `m = 0` and the oscillation bound in it
(`h71.increment`), `‖U_j - U_{j-1}‖_{C_tL^∞} ≤ 2λ_j^{-1}` on `[0,T_∞]`; these bounds are
summable by the gap `λ_j^2 ≤ λ_{j+1}` of the schedule, so the `U_j` converge uniformly to a
continuous field `w` on `[0,T_∞] × ℝ³` (`exists_continuousOn_uniformLimit_of_summable_increments`).
Continuity of each `U_j` on the slab is (T1) (`h71.T1`), and `T_∞ < S_j` is `h71.lifetime`.
No bound on the orders `q_j` (Lemma 1.3) is used. Agreement with `u` before `T_∞`:
`limit_agreement`. -/
theorem closedSlab_velocity_limit {P : InductiveEulerParameters}
    {c : InductiveEulerConstruction P} {C T : ℝ} {u : Velocity} {p : Pressure}
    (h71 : Theorem71Conclusions c C T) (h81 : Proposition81Conclusions c T u p) :
    ∃ w : Velocity, ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (c.stages.velocity n)) (Function.uncurry w)
        atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Ico 0 T, u t = w t := by
  obtain ⟨_, _, hSlab⟩ := h71.lifetime
  have hinit := two_le_frequency_zero P
  have hb₁ : Summable (fun n => (P.frequency (n + 1))⁻¹) := by
    simpa only [Nat.add_comm] using
      (reciprocal_inductive_frequency_tail (freq := P.frequency) hinit
        (c.stages.frequency_square_gap hinit) 1).1
  have hstep (n : ℕ) (_ : n ≥ 0) (z : ℝ × Vec3) (hz : z ∈ Icc 0 T ×ˢ (univ : Set Vec3)) :
      dist (Function.uncurry (c.stages.velocity n) z)
        (Function.uncurry (c.stages.velocity (n + 1)) z) ≤ 2 * (P.frequency (n + 1))⁻¹ := by
    have ht : z.1 ∈ Icc 0 (c.stages.slab (n + 1)) :=
      ⟨hz.1.1, hz.1.2.trans (hSlab (n + 1)).le⟩
    have h0 := increment_jet_bound h71 n 0 (Nat.zero_le _) z.1 ht z.2
    rw [norm_iteratedFDeriv_zero] at h0
    have hO := (h71.increment (n + 1) (Nat.succ_pos n) z.1 ht).1 z.2
    rw [dist_comm, dist_eq_norm]
    change ‖c.stages.velocity (n + 1) z.1 z.2 - c.stages.velocity n z.1 z.2‖ ≤ _
    calc
      _ = ‖(c.stages.velocity (n + 1) z.1 - c.stages.velocity n z.1 -
            c.stages.oscillation (n + 1) z.1) z.2 + c.stages.oscillation (n + 1) z.1 z.2‖ := by
          simp only [Pi.sub_apply, sub_add_cancel]
      _ ≤ ‖(c.stages.velocity (n + 1) z.1 - c.stages.velocity n z.1 -
            c.stages.oscillation (n + 1) z.1) z.2‖ + ‖c.stages.oscillation (n + 1) z.1 z.2‖ :=
          norm_add_le _ _
      _ ≤ (P.frequency (n + 1))⁻¹ + (P.frequency (n + 1))⁻¹ := add_le_add h0 hO
      _ = 2 * (P.frequency (n + 1))⁻¹ := (two_mul _).symm
  have hcont (n : ℕ) : ContinuousOn (Function.uncurry (c.stages.velocity n))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (h71.T1 n).1.continuousOn.mono (prod_mono_left (Icc_subset_Icc_right (hSlab n).le))
  obtain ⟨v, hv, hV, -⟩ :=
    exists_continuousOn_uniformLimit_of_summable_increments 0 (hb₁.mul_left 2) hstep hcont
  let w (t : ℝ) (x : Vec3) := v (t, x)
  exact ⟨w, hv, hV, limit_agreement h71 h81 hV⟩

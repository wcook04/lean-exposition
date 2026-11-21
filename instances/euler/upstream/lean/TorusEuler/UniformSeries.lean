import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Set
open scoped Topology

namespace TorusEuler

/-- Summable uniform bounds on consecutive increments give uniform convergence
on the set and a pointwise tail bound, as used in §8. -/
theorem exists_uniformLimit_of_summable_increments
    {α E : Type*} [MetricSpace E] [CompleteSpace E] {s : Set α}
    {F : ℕ → α → E} {b : ℕ → ℝ} (N : ℕ) (hb : Summable b)
    (hstep : ∀ n ≥ N, ∀ x ∈ s, dist (F n x) (F (n + 1) x) ≤ b n) :
    ∃ f : α → E, TendstoUniformlyOn F f atTop s ∧
      ∀ n ≥ N, ∀ x ∈ s, dist (F n x) (f x) ≤ ∑' k, b (n + k) := by
  classical
  have hshift (n : ℕ) (hn : N ≤ n) (x : α) (hx : x ∈ s) :
      ∀ k : ℕ, dist (F (k + n) x) (F (k.succ + n) x) ≤ b (k + n) := by
    intro k
    rw [Nat.succ_add]
    exact hstep (k + n) (hn.trans (Nat.le_add_left n k)) x hx
  have hpoint (x : α) (hx : x ∈ s) : ∃ y, Tendsto (fun n => F n x) atTop (𝓝 y) := by
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable _ (hshift N le_rfl x hx) ((summable_nat_add_iff N).2 hb))
    exact ⟨y, (tendsto_add_atTop_iff_nat N).1 hy⟩
  let f (x : α) : E := if hx : x ∈ s then (hpoint x hx).choose else F 0 x
  have hf (x : α) (hx : x ∈ s) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    simpa only [f, dite_eq_left hx] using (hpoint x hx).choose_spec
  have htail (n : ℕ) (hn : N ≤ n) (x : α) (hx : x ∈ s) :
      dist (F n x) (f x) ≤ ∑' k, b (n + k) := by
    have hFn := (hf x hx).comp (tendsto_add_atTop_nat n)
    simpa only [zero_add, Nat.add_comm] using dist_le_tsum_of_dist_le_of_tendsto₀
      (fun k => b (k + n)) (hshift n hn x hx) ((summable_nat_add_iff n).2 hb) hFn
  refine ⟨f, Metric.tendstoUniformlyOn_iff.2 ?_, htail⟩
  intro ε hε
  have hbTail : Tendsto (fun n => ∑' k, b (n + k)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using (tendsto_sum_nat_add (f := b))
  filter_upwards [eventually_ge_atTop N, Metric.tendsto_nhds.mp hbTail ε hε] with n hn hεn x hx
  rw [Real.dist_eq, sub_zero] at hεn
  rw [dist_comm]
  exact ((htail n hn x hx).trans (le_abs_self _)).trans_lt hεn

/-- Continuity on a set passes to the uniform limit of the increment series. -/
theorem exists_continuousOn_uniformLimit_of_summable_increments
    {α E : Type*} [TopologicalSpace α] [MetricSpace E] [CompleteSpace E] {s : Set α}
    {F : ℕ → α → E} {b : ℕ → ℝ} (N : ℕ) (hb : Summable b)
    (hstep : ∀ n ≥ N, ∀ x ∈ s, dist (F n x) (F (n + 1) x) ≤ b n)
    (hF : ∀ n, ContinuousOn (F n) s) :
    ∃ f : α → E, ContinuousOn f s ∧ TendstoUniformlyOn F f atTop s ∧
      ∀ n ≥ N, ∀ x ∈ s, dist (F n x) (f x) ≤ ∑' k, b (n + k) := by
  obtain ⟨f, hf, htail⟩ := exists_uniformLimit_of_summable_increments N hb hstep
  exact ⟨f, hf.continuousOn (Frequently.of_forall hF), hf, htail⟩

/-- On a set where the oscillatory increments vanish after grade `N`, the
summable bounds for the remaining increments control the full limit. -/
theorem exists_uniformLimit_of_vanishing_oscillatory_increments
    {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {s : Set α}
    {F B O : ℕ → α → E} {b : ℕ → ℝ} (N : ℕ) (hb : Summable b)
    (hdecomp : ∀ n ≥ N, ∀ x ∈ s, F (n + 1) x - F n x = B n x + O n x)
    (hO : ∀ n ≥ N, ∀ x ∈ s, O n x = 0)
    (hB : ∀ n ≥ N, ∀ x ∈ s, ‖B n x‖ ≤ b n) :
    ∃ f : α → E, TendstoUniformlyOn F f atTop s ∧
      ∀ n ≥ N, ∀ x ∈ s, dist (F n x) (f x) ≤ ∑' k, b (n + k) := by
  apply exists_uniformLimit_of_summable_increments N hb
  intro n hn x hx
  rw [dist_comm, dist_eq_norm, hdecomp n hn x hx, hO n hn x hx, add_zero]
  exact hB n hn x hx

end TorusEuler

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

open Filter Set
open scoped BigOperators Topology

namespace TorusEuler

/-- The tail bound from (7.7) used to put every approximation on a common time interval. -/
theorem activationLifetime_tail {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j)
    (hquarter : ∀ j, 4 * τ (j + 1) ≤ τ j) (j : ℕ) :
    Summable (fun n => τ (j + n)) ∧ (∑' n : ℕ, τ (j + n)) ≤ (4 / 3 : ℝ) * τ j := by
  have hterm (n : ℕ) : τ (j + n) ≤ τ j * (1 / 4 : ℝ) ^ n := by
    induction n with
    | zero => simp
    | succ n hn =>
      calc
        τ (j + (n + 1)) ≤ τ (j + n) * (1 / 4 : ℝ) := by
          rw [← Nat.add_assoc]
          linarith only [hquarter (j + n)]
        _ ≤ (τ j * (1 / 4 : ℝ) ^ n) * (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hn (by norm_num)
        _ = _ := by rw [pow_succ, mul_assoc]
  have hg := summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hs : Summable (fun n => τ (j + n)) :=
    (hg.mul_left (τ j)).of_nonneg_of_le (fun n => hτ (j + n)) hterm
  refine ⟨hs, ?_⟩
  calc
    (∑' n : ℕ, τ (j + n)) ≤ ∑' n : ℕ, τ j * (1 / 4 : ℝ) ^ n :=
      hs.tsum_le_tsum hterm (hg.mul_left (τ j))
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

/-- The common closed time interval in Theorem 7.1. Index zero in this statement can stand
    for the first activation time. A strict later increase ensures each activation is before
    the limit, even when two initial activations coincide. -/
theorem activationTimes_converge {t τ : ℕ → ℝ} (ht0 : 0 ≤ t 0)
    (hτ : ∀ j, 0 < τ j) (hquarter : ∀ j, 4 * τ (j + 1) ≤ τ j)
    (hstep : ∀ j, 0 ≤ t (j + 1) - t j ∧ t (j + 1) - t j ≤ τ j)
    (hlater : ∀ j, ∃ k, t j < t k) :
    ∃ T : ℝ, 0 < T ∧ Tendsto t atTop (𝓝 T) ∧
      ∀ j, 0 < T - t j ∧ T - t j ≤ (4 / 3 : ℝ) * τ j ∧ T < t j + 2 * τ j := by
  let d := fun n => t (n + 1) - t n
  have hsτ := fun j => activationLifetime_tail (fun j => (hτ j).le) hquarter j
  have hd : Summable d := by
    refine (by simpa using (hsτ 0).1 : Summable τ).of_nonneg_of_le ?_ ?_
    · exact fun j => (hstep j).1
    · exact fun j => (hstep j).2
  let T := t 0 + ∑' n : ℕ, d n
  have htlim : Tendsto t atTop (𝓝 T) := by
    have ht := hd.hasSum.tendsto_sum_nat.const_add (t 0)
    have htel (n : ℕ) : (t 0 + ∑ i ∈ Finset.range n, d i) = t n := by
      change t 0 + (∑ i ∈ Finset.range n, (t (i + 1) - t i)) = t n
      rw [Finset.sum_range_sub]; ring
    exact ht.congr' (Eventually.of_forall htel)
  have htmono : Monotone t :=
    monotone_nat_of_le_succ fun n => sub_nonneg.mp (hstep n).1
  have hle (j : ℕ) : t j ≤ T := by
    exact ge_of_tendsto htlim (eventually_atTop.2 ⟨j, fun _ hi => htmono hi⟩)
  have hlt (j : ℕ) : t j < T := by
    obtain ⟨k, hk⟩ := hlater j
    exact hk.trans_le (hle k)
  refine ⟨T, ht0.trans_lt (hlt 0), htlim, fun j => ?_⟩
  have hTail : T - t j = ∑' n : ℕ, d (j + n) := by
    have hadd := hd.sum_add_tsum_nat_add j
    change (∑ i ∈ Finset.range j, (t (i + 1) - t i)) + (∑' i : ℕ, d (i + j)) = _ at hadd
    simp only [Finset.sum_range_sub, Nat.add_comm _ j] at hadd
    dsimp [T]
    linarith
  have hds : Summable (fun n => d (j + n)) :=
    (hsτ j).1.of_nonneg_of_le (fun n => (hstep (j + n)).1) (fun n => (hstep (j + n)).2)
  have hbound : T - t j ≤ (4 / 3 : ℝ) * τ j := by
    rw [hTail]
    exact (hds.tsum_le_tsum (fun n => (hstep (j + n)).2) (hsτ j).1).trans (hsτ j).2
  exact ⟨sub_pos.mpr (hlt j), hbound, by linarith only [hbound, hτ j]⟩

/-- A lower bound tending to infinity on successive activation intervals gives a full
    one-sided limit, as used after (8.2). -/
theorem tendsto_atTop_of_activationBounds {t : ℕ → ℝ} {T : ℝ} {b : ℕ → ℝ} {f : ℝ → ℝ}
    (htlim : Tendsto t atTop (𝓝 T)) (hbelow : ∀ j, t j < T)
    (hb : Tendsto b atTop atTop)
    (hf : ∀ᶠ j in atTop, ∀ r ∈ Ico (t j) (t (j + 1)), b j ≤ f r) :
    Tendsto f (𝓝[Iio T] T) atTop := by
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨j, hj⟩ := eventually_atTop.1 ((hb.eventually_ge_atTop B).and hf)
  have hnear : ∀ᶠ r in 𝓝 T, t j < r := Ioi_mem_nhds (hbelow j)
  filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with r hrT hrj
  obtain ⟨k, hk⟩ := eventually_atTop.1 (htlim.eventually_const_lt (show r < T from hrT))
  have hex : ∃ n : ℕ, r < t (j + n + 1) :=
    ⟨k, hk _ (by omega)⟩
  let n := Nat.find hex
  have hup : r < t (j + n + 1) := Nat.find_spec hex
  have hlow : t (j + n) ≤ r := by
    by_cases hn : n = 0
    · simpa [hn] using le_of_lt (show t j < r from hrj)
    · have hp : n - 1 < n := by omega
      have hnot := Nat.find_min hex hp
      have hi : j + (n - 1) + 1 = j + n := by omega
      rw [hi] at hnot
      exact le_of_not_gt hnot
  have h := hj (j + n) (by omega)
  exact h.1.trans (h.2 r ⟨hlow, hup⟩)

end TorusEuler

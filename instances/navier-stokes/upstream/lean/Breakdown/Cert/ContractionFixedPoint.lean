import Breakdown.Cert.Nodes

open scoped Topology
open Filter

noncomputable section

namespace Breakdown.Cert

theorem contractionFixedPointHolds_proof : ContractionFixedPointHolds := by
  intro E _ _ S D Ξ c θ hS hne hmaps hc hθ hlow htri hlsc hcontr
  obtain ⟨x₀, hx₀⟩ := hne
  set θ' := max θ 0 with hθ'
  have hθ'1 : θ' < 1 := max_lt hθ zero_lt_one
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hpos : 0 < 1 - θ' := by linarith
  have hD0 : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ D x y := fun x hx y hy =>
    le_trans (mul_nonneg hc.le (norm_nonneg _)) (hlow x hx y hy)
  have hcontr' : ∀ x ∈ S, ∀ y ∈ S, D (Ξ x) (Ξ y) ≤ θ' * D x y := fun x hx y hy =>
    (hcontr x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hD0 x hx y hy))
  set x : ℕ → E := fun n => Ξ^[n] x₀ with hx
  have hxs : ∀ n, x (n + 1) = Ξ (x n) := fun n => Function.iterate_succ_apply' Ξ n x₀
  have hxS : ∀ n, x n ∈ S := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [hxs]; exact hmaps ih
  set K := D (x 0) (x 1) with hK
  have hK0 : 0 ≤ K := hD0 _ (hxS 0) _ (hxS 1)
  have hstep : ∀ n, D (x n) (x (n + 1)) ≤ θ' ^ n * K := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul]
    | succ n ih =>
      calc D (x (n + 1)) (x (n + 1 + 1)) = D (Ξ (x n)) (Ξ (x (n + 1))) := by
            rw [hxs (n + 1), hxs n]
        _ ≤ θ' * D (x n) (x (n + 1)) := hcontr' _ (hxS n) _ (hxS (n + 1))
        _ ≤ θ' * (θ' ^ n * K) := mul_le_mul_of_nonneg_left ih hθ'0
        _ = θ' ^ (n + 1) * K := by ring
  set M := K / (1 - θ') with hM
  have hM0 : 0 ≤ M := div_nonneg hK0 hpos.le
  have hKM : (1 - θ') * M = K := by rw [hM]; field_simp
  have hKleM : K ≤ M := by nlinarith [mul_nonneg hθ'0 hM0]
  have hfar : ∀ j n, D (x n) (x (n + j + 1)) ≤ θ' ^ n * M := by
    intro j
    induction j with
    | zero => intro n; exact (hstep n).trans (mul_le_mul_of_nonneg_left hKleM (pow_nonneg hθ'0 n))
    | succ j ih =>
      intro n
      have h2 : n + (j + 1) + 1 = n + 1 + j + 1 := by omega
      rw [h2]
      calc D (x n) (x (n + 1 + j + 1))
          ≤ D (x n) (x (n + 1)) + D (x (n + 1)) (x (n + 1 + j + 1)) :=
            htri _ (hxS n) _ (hxS (n + 1)) _ (hxS _)
        _ ≤ θ' ^ n * K + θ' ^ (n + 1) * M := add_le_add (hstep n) (ih (n + 1))
        _ = θ' ^ n * M := by linear_combination (-θ' ^ n) * hKM
  have hdist : ∀ n, dist (x n) (x (n + 1)) ≤ (K / c) * θ' ^ n := by
    intro n
    rw [dist_eq_norm, div_mul_eq_mul_div, le_div_iff₀ hc]
    calc ‖x n - x (n + 1)‖ * c = c * ‖x n - x (n + 1)‖ := mul_comm _ _
      _ ≤ D (x n) (x (n + 1)) := hlow _ (hxS n) _ (hxS (n + 1))
      _ ≤ θ' ^ n * K := hstep n
      _ = K * θ' ^ n := mul_comm _ _
  have hfundamental : CauchySeq x := cauchySeq_of_le_geometric θ' (K / c) hθ'1 hdist
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hfundamental
  have haS : a ∈ S := hS.mem_of_tendsto ha (Eventually.of_forall hxS)
  have hxa : ∀ n, D (x n) a ≤ θ' ^ n * M := by
    intro n
    refine hlsc (x n) (hxS n) a haS x hxS ha _ ?_
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    obtain ⟨j, rfl⟩ : ∃ j, m = n + j + 1 := ⟨m - n - 1, by omega⟩
    exact hfar j n
  have hlim : Tendsto (fun n => x (n + 1)) atTop (𝓝 (Ξ a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n => θ' ^ (n + 1) * M / c) atTop (𝓝 (0 * M / c)) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hθ'0 hθ'1).comp
        (tendsto_add_atTop_nat 1)).mul_const M).div_const c
    rw [zero_mul, zero_div] at h1
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
    rw [le_div_iff₀ hc]
    calc ‖x (n + 1) - Ξ a‖ * c = c * ‖x (n + 1) - Ξ a‖ := mul_comm _ _
      _ ≤ D (x (n + 1)) (Ξ a) := hlow _ (hxS _) _ (hmaps haS)
      _ = D (Ξ (x n)) (Ξ a) := by rw [hxs n]
      _ ≤ θ' * D (x n) a := hcontr' _ (hxS n) _ haS
      _ ≤ θ' * (θ' ^ n * M) := mul_le_mul_of_nonneg_left (hxa n) hθ'0
      _ = θ' ^ (n + 1) * M := by ring
  have hlim2 : Tendsto (fun n => x (n + 1)) atTop (𝓝 a) := ha.comp (tendsto_add_atTop_nat 1)
  have hfix : Ξ a = a := tendsto_nhds_unique hlim hlim2
  refine ⟨a, haS, hfix, fun y hy hyf => ?_⟩
  have h1 : D y a ≤ θ' * D y a := by
    have h := hcontr' y hy a haS
    rwa [hyf, hfix] at h
  have h0 := hD0 y hy a haS
  have h2 : D y a ≤ 0 := by nlinarith
  have h3 := hlow y hy a haS
  have h4 : ‖y - a‖ ≤ 0 := by nlinarith [norm_nonneg (y - a)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h4)

end Breakdown.Cert

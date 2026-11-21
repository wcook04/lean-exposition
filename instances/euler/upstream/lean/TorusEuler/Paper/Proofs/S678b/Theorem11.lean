import TorusEuler.Paper.S678.Statements

/-! # Proof of Theorem 1.1 from Section 8 -/

open Set

namespace TorusEuler.Paper

/-- Proof of **Theorem 1.1** (`cc:target:unforced`), following
sections/09b_terminal_properties.tex:125-128: Propositions 8.1, 8.2, 8.4 and Corollary 8.3,
applied to the sequence of Theorem 7.1 fixed at the opening of Section 8
(sections/09_limit.tex:2), prove the theorem.

* `hText_section8_setting` (09_limit.tex:2, "On the common interval `[0,T_∞]` of
  Theorem 7.1") supplies the construction `c`, the constant `C` and `T = T_∞` with
  `Theorem71Conclusions c C T`.
* `h8_1` (Proposition 8.1) supplies `u`, `p`: `u_0 = u(0)` is smooth, odd and divergence free;
  `u` is a smooth odd Euler solution on `[0,T_∞)` (the first block of
  `EulerSingularityWitness` and the oddness clause); `maximal_agreement` identifies every
  maximal solution from `u_0` with `u` on `[0,T_∞)` (uniqueness conjunct).
* `h8_2` (Proposition 8.2) gives (1.3): bounded velocity and `|curl u(t,0)| → ∞`.
* `h8_3` (Corollary 8.3, applied with `h8_2`'s conclusions as its setting) gives maximality with
  `T_* = T_∞ ∈ (0,∞)`, both divergent integrals (1.2), and `T' = T_∞` for every maximal
  solution from `u_0` (uniqueness conjunct).
* `h8_4` (Proposition 8.4) gives the `C^m(K)` limits of `u(t)` and `∂_t u(t)`. -/
theorem Proof.theorem_1_1_of (h8_1 : Statement.proposition_8_1)
    (h8_2 : Statement.proposition_8_2) (h8_3 : Statement.corollary_8_3)
    (h8_4 : Statement.proposition_8_4) (hText_section8_setting : Statement.Text.section8_setting) :
    Statement.theorem_1_1 := by
  obtain ⟨P, c, C, T, h71⟩ := hText_section8_setting
  obtain ⟨u, p, hu⟩ := h8_1 P c C T h71
  have hv := h8_2 P c C T u p h71 hu
  have ht := h8_3 P c C T u p h71 hu hv
  have ho := h8_4 P c C T u p h71 hu
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, ht.time_pos⟩
  refine ⟨u 0, T, u, p, ⟨hu.initial_smooth, hu.euler.periodic_velocity 0 h0, hu.initial_odd,
    hu.initial_divergence_free, ht.maximal, rfl, hu.odd, ht.gradient_integral, ht.curl_integral,
    hv.bounded_velocity, hv.central_curl, ho.velocity, ho.time_derivative⟩, ?_⟩
  intro T' v q hmax hv0
  exact ⟨ht.maximal_time T' v q hmax hv0, (hu.maximal_agreement T' v q hmax hv0).2⟩

end TorusEuler.Paper

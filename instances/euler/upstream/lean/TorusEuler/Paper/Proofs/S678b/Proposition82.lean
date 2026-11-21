import TorusEuler.Paper.Proofs.S678b.Library.Proposition82

/-! # Proof of Proposition 8.2 (cites Lemmas 1.3, 2.2, 2.4 and B.1) -/

namespace TorusEuler.Paper

/-- Proof of **Proposition 8.2** (`cc:uf:terminal:velocity-curl`), following
sections/09b_terminal_properties.tex:7-66, for every construction `c` with the conclusions of
Theorem 7.1 (`h71`) and every limit `u` with the conclusions of Proposition 8.1 (`h81`).

* Bounded velocity (09b:8-10): the continuous closed-slab limit `w` of the opening of Section 8
  (09_limit.tex:2-5), built from (7.4) at order zero alone (`Lib.S678b.closedSlab_velocity_limit`;
  Lemma 1.3 does not enter this step), is bounded, and `h81` identifies it with `u` before
  `T_∞`.
* The decomposition at the origin (09b:12-20): (T4) at steps `j-1` and `j`, through the data
  of item 2 of the proof of Theorem 7.1 carried by the construction
  (`c.centralWaves.gradient_split`, `cutoff_complete`, `error_bound`; the fields `T4_gradient`
  and `T4_times` of `h71` state the same facts and are not used).
* The projection (8.1) (09b:21-34): by (2.3) and Lemma 2.4 (`h2_4`, its (2.10) and (2.11)), the
  `E_3` component of `κ_j/λ_j` is at least `1/2` and its length at most `C(1+τ^2)`
  (`Lib.S678b.wave_geometry_of_lemma24`). The TeX reads the bound `CL_{j+1}^4` on the normalized
  length of `[t_j,S_j]` from item 2 of the proof of Theorem 7.1 (09b:28-29): `h71.window_upper`.
  The hypotheses (2.7) of Lemma 2.4 for wave `j` are read from the same item 2 (08b:312-326):
  `h71.comparison`, for every constant `C₀` and all large `j`.
* The retained strength (09b:36-47): `σ_{j-1} ≥ cμ^{1/4}` at `t_j` by (7.3) (the frozen values
  `c.centralWaves.strength_at_crossing`); by the frame equation `(log σ)' = B_{33}` of (2.2)
  (`h2_2`), `|∂_t log σ_{j-1}| ≤ |∇U_{j-2}(t,0)| ≤ λ_{j-2}^9 ≤ μ^{1/32}` with (7.6) from
  Bernstein (B.1) (`hB_1`), over an interval of length at most `τ_j ≤ μ^{-1/16}` ((T4) through
  `c.stages.activation_step`, and (7.7) through `c.lifetime`); (1.15) (`h1_3`) gives
  `L_{j+1}^8 ≤ μ^{1/8}`.
* (8.2) for `U_j` and its passage to `u` (09b:48-63), with Proposition 8.1 (`h81`) for the
  convergence of the gradients before `T_∞`, exported as `curl_lower`; then
  `|curl u(t,0)| → ∞` (09b:64-66).

Equations: (1.15), (2.2), (2.3), (2.6), (2.7), (2.10), (2.11), (7.3), (7.4), (7.6),
(7.7), (8.1), (8.2).

`h1_3` is used for (1.15), `h2_2` for the log-strength equation of (2.2) in the retained-strength
step, `h2_4` for (2.10)-(2.11), `hB_1` for (7.6). -/
theorem Proof.proposition_8_2_of (h1_3 : Statement.lemma_1_3) (h2_2 : Statement.lemma_2_2)
    (h2_4 : Statement.lemma_2_4) (hB_1 : Statement.lemma_B_1) : Statement.proposition_8_2 :=
  fun _P _c _C _T _u _p h71 h81 =>
    Lib.S678b.proposition82_of_conclusions h1_3 h2_2 h2_4 hB_1 h71 h81

end TorusEuler.Paper

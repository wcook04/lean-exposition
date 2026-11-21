import TorusEuler.Paper.S678.Vocabulary
import TorusEuler.Paper.S678.StepData
import TorusEuler.InductiveScheduledConstruction

/-! # Statements of package S678

Faithful statements of Theorem 1.1, Lemma 1.3, Lemma 6.1, Theorem 7.1, Propositions 8.1, 8.2,
Corollary 8.3, Proposition 8.4 of the latest manuscript, and of the unnumbered opening of
Section 8 (`Text.section8_setting`). The statements of Sections 7 and 8 use the conclusion
predicates of `TorusEuler.Paper.S678.Vocabulary`; Theorem 7.1 also exports the step data of
`TorusEuler.Paper.S678.StepData`. -/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Topology

namespace TorusEuler.Paper

/-- **Theorem 1.1** (`cc:target:unforced`, sections/01_problem.tex:60).
There is an odd divergence-free `u₀ ∈ C^∞(𝕋³;ℝ³)` whose maximal classical solution `u` of the
Euler equations (1.1) is smooth and odd on `𝕋³ × [0,T_*)` for a finite `T_* > 0`, and satisfies
(1.2) `∫_0^{T_*} ‖∇u‖_∞ = ∫_0^{T_*} ‖curl u‖_∞ = ∞`, (1.3) `sup_{t<T_*} ‖u(t)‖_∞ < ∞` and
`|curl u(t,0)| → ∞` as `t ↑ T_*`; for every compact `K ⊂ 𝕋³ ∖ {0}` and every `m ≥ 0`, both
`u(t)` and `∂_t u(t)` converge in `C^m(K)` as `t ↑ T_*`.

The clauses are those of `EulerSingularityWitness u₀ T u p` (with `T = T_*`); the last conjunct
is "whose maximal classical solution": every maximal solution from `u₀` has maximal time `T_*`
and coincides with `u` on `[0,T_*)`.

Representation: `𝕋³` is the `ℤ³`-periodic lift to `ℝ³`; a classical solution is
`IsEulerSolution` (smooth on `[0,T) × ℝ³`, periodic, with mean-zero pressure); maximality is
`IsMaximalEulerSolution` (no smooth continuation past `T`); `‖·‖_∞` is `torusLInf` (essential
supremum over the unit cell); the pointwise norm of `∇u(t)` in (1.2) is the operator norm of
`fderiv ℝ (u t)` (all matrix norms are equivalent, so the divergence does not depend on this
choice); `∂_t u` is `timeDerivative T u`; convergence in `C^m(K)` is `HasOffOriginLimits`
(compact `K` avoiding the lattice). -/
def Statement.theorem_1_1 : Prop :=
  ∃ (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure),
    EulerSingularityWitness u₀ T u p ∧
      ∀ (T' : ℝ) (v : Velocity) (q : Pressure),
        IsMaximalEulerSolution T' v q → v 0 = u₀ → T' = T ∧ EqOn v u (Ico 0 T)

/-- **Lemma 1.3** (`cc:uf:tower:lem:slow-orders`, sections/01b_parameters.tex:54).
Let `b ≥ 1`, `K(s) = 320b(s+1)`, let `𝓑` be a function on the positive integers with the
floor (1.13) `log 𝓑(s) ≥ 4K(s+1)^3` (`s ≥ 1`), let `N ≥ 𝓑(1)`, and define `q_j`, `λ_j` by (1.14):
`q_1 = 1`, `K_j = K(q_j)`, `λ_0 = N`, `λ_j = λ_{j-1}^{K_j}` (`j ≥ 1`),
`q_{j+1} = max{1 ≤ s ≤ q_j + 1 : 𝓑(s) ≤ λ_{j-1}}` (`j ≥ 1`), `L_j = 4 log λ_{j+1}`. Then
`q_j ≤ q_{j+1} ≤ q_j + 1` (`j ≥ 1`), `q_j → ∞`, and (1.15) `L_{j+1} ≤ (log λ_{j-1})^2` (`j ≥ 1`).

Representation: `freq j = λ_j`, `B = 𝓑`; `K(s)` is `frequencyExponent b s`; the maximum in
(1.14) is `IsGreatest`; `𝓑(s) > 0` is stated with (1.13), which presupposes it. Generalization:
the two other conditions of Subsection 1.5 on `𝓑` (nondecreasing, and bounding the fixed-order
constants) are not hypotheses; the proof in Appendix C uses neither, and without them the
statement applies to the schedule of every `InductiveEulerParameters`, which does not record
monotonicity. The values `q_0`, `𝓑(0)` are unconstrained. -/
def Statement.lemma_1_3 : Prop :=
  ∀ (b : ℕ) (B : ℕ → ℝ) (N : ℝ) (q : ℕ → ℕ) (freq : ℕ → ℝ),
    1 ≤ b →
    (∀ s : ℕ, 1 ≤ s → 0 < B s ∧ 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) →
    B 1 ≤ N →
    q 1 = 1 →
    freq 0 = N →
    (∀ j : ℕ, 1 ≤ j → freq j = freq (j - 1) ^ frequencyExponent b (q j)) →
    (∀ j : ℕ, 1 ≤ j →
      IsGreatest {s : ℕ | 1 ≤ s ∧ s ≤ q j + 1 ∧ B s ≤ freq (j - 1)} (q (j + 1))) →
    (∀ j : ℕ, 1 ≤ j → q j ≤ q (j + 1) ∧ q (j + 1) ≤ q j + 1) ∧
      Tendsto q atTop atTop ∧
      ∀ j : ℕ, 1 ≤ j → Schedule.L freq (j + 1) ≤ Real.log (freq (j - 1)) ^ 2

/-- **Lemma 6.1** (`cc:uf:base:lem:first`, sections/03a_exact_base.tex:38).
For `0 < ρ ≤ 1`, the stationary shear (6.1) `U_0 = sin(2πx_2)(e_1 + ρe_3)` with gradient
`B_ρ = 2π(e_1 + ρe_3) ⊗ e_2` at the origin, a frequency `λ ≥ 1` and a final time `T > 0`: if
`T|B_ρ| ≤ 1/8`, the first wave (6.3) (wave vector `λe_1` at time zero, seed of (3.2) at the origin
with initial direction `e_2`, scaled so that `max_{[0,T]} |𝐚(t,0)| = λ^{-3/4}`) satisfies the two
conditions (5.5) for every `𝖣 ≥ 2`, and its strength at the origin at time zero lies between
`λ^{1/4}/2` and `λ^{1/4}` (`Lemma61Conclusions`).

The first conjunct records that the first wave of (6.3) exists (the text constructs it);
the second is the lemma, stated for every object satisfying the defining equations of (6.3).

Representation: the first wave is represented by its data at the origin, the structure
`FirstWaveOrigin ρ T λ` (the lemma concerns only these data); `|B_ρ|` is the operator norm
(equal to the Frobenius norm, `B_ρ` having rank one); `freq = λ`. -/
def Statement.lemma_6_1 : Prop :=
  ∀ ρ T freq : ℝ, 0 < ρ → ρ ≤ 1 → 1 ≤ freq → 0 < T →
    T * ‖stationaryShearGradient ρ‖ ≤ 1 / 8 →
      Nonempty (FirstWaveOrigin ρ T freq) ∧ ∀ w : FirstWaveOrigin ρ T freq, Lemma61Conclusions w

/-- **Theorem 7.1** (`cc:uf:tower:thm:finite`, sections/08b_induction.tex:142).
For every sufficiently large `N` there are fields `U_j`, `j ≥ 1`, and times
`0 = t_1 = t_2 < t_3 < ⋯` with (T1)–(T3) for `j ≥ 0` and (T4) (including (7.3)) for `j ≥ 1`, in
which `U_0` is the shear (6.1) at `ρ = ε_1`; the activation times converge to
`T_∞ ∈ (0,∞)` with `T_∞ < S_j` for every `j`; for `j ≥ 1` the oscillation `O_j` is supported in
the ball of radius `λ_{j-1}^{-1}` about the origin and satisfies (7.4); for `j ≥ 2`, `O_j`
vanishes on `[0,t_j]` (all in `Theorem71Conclusions c C T`, `C = 18e³`, `T = T_∞`).
Equations: (6.1), (7.1), (7.3), (7.4), (1.13), (1.14), (2.23); in the exported step data (7.2),
(5.46), (5.55).

Quantifiers. The cutoff symbol `ψ` of Appendix B comes first: it is fixed once
(sections/appB_cutoff.tex:2-5) and the constants of Lemma B.1 depend on it. The statement holds
for every admissible symbol (`S5.CutoffSymbol ψ`: radial, smooth, `0 ≤ ψ ≤ 1`, `ψ = 1` on
`|ζ| ≤ 1`, `supp ψ ⊆ {|ζ| ≤ 2}`), as `Statement.proposition_5_11` is;
`exists_appendixB_cutoffSymbol` supplies one. The constructions of Subsections 5.1 and 5.6
come next. Subsection 5.1 fixes the envelope radius `ℓ_* = 𝖣^{-a}` with an absolute exponent
`a`, "fixed sufficiently large". In the Lean statement this is `∀ a₀, ∃ a ≥ a₀`: the exponent
can be taken above any given floor.
Then come the integer `b ≥ 1` (fixed in Subsection 5.6) and the fixed-order constants (fixed by
the estimates of Sections 3, 5, 6 and 7 and of Lemma B.1). The constants are represented by a
majorant `F(s)` of the constants at orders and depths at most `7K(s)`. The absolute constant
`C ≥ 2` of (7.3), "for which (2.23) holds", is explicit: `C = 18e³`, the constant of (2.23) in
`Statement.proposition_2_8` (upper bound `18e³`, lower bound `e⁻¹/4 ≥ (18e³)⁻¹`). The function `𝓑`
of Subsection 1.5 is any function admitted there (`AdmissibleThreshold b F 𝓑`: nondecreasing,
bounding the fixed-order constants, with (1.13)). For it, "every sufficiently large `N`" is
`N ≥ N₁`, and the parameter record `P` is the schedule (1.14) built from `b`, `𝓑` and `λ_0 = N`.

Exports (ledger).
* The step data of the construction, in the vocabulary of Section 5, read by the auxiliary note
  (`Theorem71Steps c a ψ`): for every `j ≥ 1`, the parent `U_{j-1}` with its flow and pressure
  satisfies the hypotheses of Subsection 5.1 with `𝖣 = λ_{j-1}^9` and `λ = λ_j`; wave `j`
  (constant vector `k_*`, seed, cutoff `χ̃_j`) is launched at `t_j`, and its seed at the center
  is `𝐚_j`; the profiles are the expansion of Subsection 5.5 at depth `P = 6K_{j+1}` (7.2) with
  `ℓ_* = 𝖣^{-a}`; `V = U_{j-1} + W^♮` and `Π = π_{j-1} + 𝖯^♮` satisfy (5.46) of Lemma 5.8;
  `U_j = S_{Λ_j}V` is the truncation (5.55) with the symbol `ψ`, `Λ_j = λ_j^5`, and `π_j` is its
  zero-mean pressure; and
  `O_j = W_osc^♮` is the oscillation of Lemma 5.8. The
  envelope exponent `a ≥ a₀` and the symbol `ψ` are fixed before `𝓑`; the auxiliary note
  chooses `𝓑` above its own constants, which depend on them.
* `P.strengthConstant = C`: the parameter record carries the constant of (7.3).
* The construction carries the data of item 2 of the proof read by Section 8
  (`c.centralWaves`: the comparison windows of Subsection 6.2, the selected crossings and the
  comparison hypotheses (2.7) of each wave), the central wave equations and (5.5) of each wave
  (`InductiveEulerWave.center`), and the bounds (7.7) (`lifetime`).

Representation: as in `Theorem71Conclusions` (whose docstring lists which defining clauses of
the objects defined by reference are recorded there) and `Theorem71StepData`. Through
`Theorem71Steps`, `U_j`, `π_j` and `O_j` are the objects that Section 7 builds from Section 5,
but no time regularity of `O_j` is stated here. -/
def Statement.theorem_7_1 : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∀ a₀ : ℕ, ∃ (b a : ℕ) (F : ℕ → ℝ), 1 ≤ b ∧ a₀ ≤ a ∧
    ∀ B : ℕ → ℝ, AdmissibleThreshold b F B →
      ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
        ∃ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (T : ℝ),
          P.exponentParameter = b ∧ P.threshold = B ∧ P.frequency 0 = N ∧
            P.strengthConstant = 18 * Real.exp 3 ∧
            Theorem71Conclusions c (18 * Real.exp 3) T ∧ Theorem71Steps c a ψ

/-- **Section 8, opening** (unnumbered text, sections/09_limit.tex:2): "On the common interval
`[0,T_∞]` of Theorem 7.1": Section 8 fixes the sequence `U_j`, the times `t_j`, `S_j` and the
limit `T_∞` of Theorem 7.1 (for a large initial frequency `N`). The statement records that such a
sequence exists: a construction `c` with an absolute constant `C` and a time `T = T_∞`
satisfying the conclusions of Theorem 7.1.

Representation: as in `Theorem71Conclusions`. -/
def Statement.Text.section8_setting : Prop :=
  ∃ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (C T : ℝ),
    Theorem71Conclusions c C T

/-- **Proposition 8.1** (`cc:uf:terminal:agreement`, sections/09_limit.tex:11).
For the sequence of Theorem 7.1: the data `U_j(0)` converge in every `C^{m,1/2}` to an odd
divergence-free field `u_0`, and `u_0 ∈ C^∞`. The maximal smooth solution `u` from `u_0`, with
maximal time `T_* > 0`, has `T_* ≥ T_∞`; for every `T < T_∞` and `m ≥ 0`, `U_j → u` in
`C([0,T];C^{m,1/2})`; `u` is smooth and odd on `[0,T_∞) × 𝕋³`.

Setting (ledger): stated for every construction `c` satisfying the conclusions of Theorem 7.1
(`Theorem71Conclusions c C T`, `T = T_∞`); the conclusions are `Proposition81Conclusions c T u p`.

Representation: as in `Proposition81Conclusions` (the solution on `[0,T_∞)` is asserted to
exist, and every maximal solution from `u_0` extends it). -/
def Statement.proposition_8_1 : Prop :=
  ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (C T : ℝ),
    Theorem71Conclusions c C T →
      ∃ (u : Velocity) (p : Pressure), Proposition81Conclusions c T u p

/-- **Proposition 8.2** (`cc:uf:terminal:velocity-curl`, sections/09b_terminal_properties.tex:3).
The solution has bounded velocity on `[0,T_∞)`, and `|curl u(t,0)| → ∞` as `t ↑ T_∞`.

Setting (ledger): for every construction `c` with `Theorem71Conclusions c C T` and every `u`, `p`
with `Proposition81Conclusions c T u p` (`T = T_∞`).

Exports (ledger): the curl lower bound (8.2) of the proof, passed to the limit `u`
(`Proposition82Conclusions.curl_lower`), which Corollary 8.3 uses in place of the
Beale–Kato–Majda criterion.

Representation: as in `Proposition82Conclusions`; `‖u(t)‖_{L^∞}` is `torusLInf (u t)`. -/
def Statement.proposition_8_2 : Prop :=
  ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (C T : ℝ) (u : Velocity)
    (p : Pressure),
    Theorem71Conclusions c C T → Proposition81Conclusions c T u p →
      Proposition82Conclusions c T u

/-- **Corollary 8.3** (`cc:uf:terminal:time`, sections/09b_terminal_properties.tex:69).
The maximal existence time is `T_* = T_∞ ∈ (0,∞)`, and both integrals in (1.2),
`∫_0^{T_*} ‖∇u‖_∞` and `∫_0^{T_*} ‖curl u‖_∞`, diverge.

Setting (ledger): for every construction `c` with `Theorem71Conclusions c C T`, and `u`, `p` with
`Proposition81Conclusions c T u p` and `Proposition82Conclusions c T u` (`T = T_∞`).

Representation: as in `Corollary83Conclusions`: `T_* = T_∞` is the maximality of `u` on
`[0,T_∞)` together with `T_* = T_∞` for every maximal solution from `u(0)`; the integrals are
lower Lebesgue integrals of `torusLInf` over `[0,T_∞)`; the pointwise norm of `∇u(t)` is the
operator norm of `fderiv ℝ (u t)`. -/
def Statement.corollary_8_3 : Prop :=
  ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (C T : ℝ) (u : Velocity)
    (p : Pressure),
    Theorem71Conclusions c C T → Proposition81Conclusions c T u p →
      Proposition82Conclusions c T u → Corollary83Conclusions T u p

/-- **Proposition 8.4** (`cc:uf:terminal:off-origin`, sections/09b_terminal_properties.tex:88).
For every compact `K ⊂ 𝕋³ ∖ {0}` and every integer `m ≥ 0`, both `u(t)` and `∂_t u(t)` converge
in `C^m(K)` as `t ↑ T_∞`.

Setting (ledger): for every construction `c` with `Theorem71Conclusions c C T` and every `u`, `p`
with `Proposition81Conclusions c T u p` (`T = T_∞`).

Representation: as in `Proposition84Conclusions` (`HasOffOriginLimits` on the lift; `∂_t u` is
`timeDerivative T u`). -/
def Statement.proposition_8_4 : Prop :=
  ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (C T : ℝ) (u : Velocity)
    (p : Pressure),
    Theorem71Conclusions c C T → Proposition81Conclusions c T u p →
      Proposition84Conclusions T u

end TorusEuler.Paper

import TorusEuler.Paper.S678.StepData
import TorusEuler.TerminalTimeJet
import TorusEuler.TerminalScheduledNormContinuity

/-! # Vocabulary for the statements of package Auxiliary

Notation of the auxiliary note "Smooth terminal regularity away from the origin"
(`paper/craik_criminale_rewrite/auxiliary/terminal_smoothness.tex`) and of Remark 1.2 of the
latest manuscript (`sections/01_problem.tex:80`). References with prefix M are to the main
manuscript, as in the note; numbers of the note are those of its compiled `.aux` file.

* `Paper.SmoothTerminalExtension T u`: the restriction of `u` to `[0,T) × (𝕋³ ∖ {0})` extends
  to a smooth field on an open space-time neighbourhood of `{T} × (𝕋³ ∖ {0})` (the conclusion
  of Theorem 1.1 of the note and of Remark 1.2).
* `Paper.Aux.TimeDerivativeThreshold b G 𝓑`: the additional condition of the note on the
  function `𝓑` of Subsection M.1.5 (terminal_smoothness.tex:56-68).
* `Paper.Aux.MixedIncrementBound c m q j`: the bound (1.2) of the note at the step `j` of a
  construction `c`.
* `Paper.Aux.TimeBounds c q ψq j`: the bounds (1.3) of the note at the step `j`, for all time
  orders `i ≤ q`.

Index conventions are those of `TorusEuler.Paper.S678.Vocabulary`: `c.stages.velocity j = U_j`,
`c.stages.residual j = R_j`, `c.stages.oscillation j = O_j` (`j ≥ 1`), `c.stages.slab j = S_j`,
`P.frequency j = λ_j`, `P.order j = q_j`. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler.Paper

noncomputable section

/-- **Smooth extension through the terminal time away from the origin.** The restriction of the
field `u` to `[0,T) × (𝕋³ ∖ {0})` extends to a smooth field on an open space-time neighbourhood
of `{T} × (𝕋³ ∖ {0})`: Theorem 1.1 of the auxiliary note (`aux:terminal:smooth`,
auxiliary/terminal_smoothness.tex:47-51), and Remark 1.2 of the main manuscript
(sections/01_problem.tex:81-82: "extends smoothly in space and time through `T_*` away from the
origin"). No equation is imposed on the extension (terminal_smoothness.tex:53: "The Euler
equations are imposed only for `0 ≤ t < T_*`").

Representation: `𝕋³` is the `ℤ³`-periodic lift to `ℝ³` and `𝕋³ ∖ {0}` is `offOrigin`, the
complement of the lattice; the neighbourhood is an open set `O ⊆ ℝ × ℝ³` containing
`{T} × offOrigin`; the extended field is a spatially periodic field `g` that equals `u` on
`[0,T) × offOrigin` and is `C^∞` on `([0,T) × offOrigin) ∪ O`, the union of the domain of the
restriction and the neighbourhood. Periodicity of `g` makes `O` lattice invariant without loss
of generality (`O` may be replaced by the union of its lattice translates). -/
def SmoothTerminalExtension (T : ℝ) (u : Velocity) : Prop :=
  ∃ (O : Set (ℝ × Vec3)) (g : Velocity), IsOpen O ∧ ({T} : Set ℝ) ×ˢ offOrigin ⊆ O ∧
    ContDiffOn ℝ ∞ (Function.uncurry g) (Ico 0 T ×ˢ offOrigin ∪ O) ∧
    (∀ t : ℝ, SpatiallyPeriodic (g t)) ∧
    EqOn (Function.uncurry g) (Function.uncurry u) (Ico 0 T ×ˢ offOrigin)

namespace Aux

/-- **The choice of `𝓑` in the auxiliary note** (auxiliary/terminal_smoothness.tex:56-68).
Subsection M.1.5 admits any nondecreasing function `𝓑` with the floor (M.1.13) that, for every
integer `s ≥ 1`, bounds the fixed-order constants of the main paper at orders and depths at most
`7K(s)` (`AdmissibleThreshold`). The note chooses one for which `𝓑(s)` also bounds the constants
in its time-derivative estimates with all derivative orders and the depth at most `7K(s)`,
`K(s) = 320b(s+1)`. These constants depend only on the orders and the depth (:63-65: the
estimates display the dependence on the previous frequency parameter as fixed powers and contain
no constant depending on the constructed solution).

This predicate is the additional condition: `G(7K(s)) ≤ 𝓑(s)` for every `s ≥ 1`.

Representation: the constants are represented by a majorant `G`, and `K(s)` is
`frequencyExponent b s`. `G n` bounds every constant that the note's proof bounds by `𝓑` at
derivative orders and depth at most `n`: the constants of its time-derivative estimates and,
since the statements of Lemmas 1.2 and 1.3 of the note do not assume `AdmissibleThreshold`,
also the fixed-order constants of the main paper that the proof uses at those orders and that
depth (for example the constant of (M.B.2) at the order `P`, terminal_smoothness.tex:413-414).
In the text `𝓑(s)` bounds both kinds (the second by Subsection M.1.5), so the text's choice of
`𝓑` satisfies this condition. The statements of Lemmas 1.2 and 1.3 and Theorem 1.1 of the
note quantify `G` existentially, after the cutoff symbol `ψ` of Appendix M.B and the envelope
exponent `a` of Subsection M.5.1, on which the constants depend, and before `b`. -/
def TimeDerivativeThreshold (b : ℕ) (G B : ℕ → ℝ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → G (7 * frequencyExponent b s) ≤ B s

/-- **The bound (1.2) of the auxiliary note at step `j`** (`aux:terminal:increment-mixed`,
auxiliary/terminal_smoothness.tex:83-86), for the construction `c`, the Hölder order `m` and the
time order `q`: `‖∂_t^q(U_j - U_{j-1} - O_j)‖_{C([0,S_j];C^{m,1/2})} ≤ λ_j^{-1}`, the time
derivatives being taken at a fixed spatial point (:87).

Representation: `∂_t^q` at a fixed spatial point is `slabTimeJet 0 S_j q`, the iterated derivative
within `[0,S_j]` (one-sided at the endpoints) of `t ↦ f(t,x)`. The norm of
`C([0,S_j];C^{m,1/2})` is the supremum over `t ∈ [0,S_j]` (a bound at every time), and membership
in this space is the continuity of `t ↦ ∂_t^q(⋯)(t)` in `C^{m,1/2}`
(`ContinuousOnSlabInSpatialNorm`).

`C^{m,1/2}` is `SpatialHolderHalf m` with the norm `spatialHolderHalfNorm m` on the periodic lift:
the sum over orders `k ≤ m` of the supremum and the 1/2-Hölder seminorm of the `k`-th Fréchet
derivative (operator norm), in place of the multi-index partials `∂^β` of the paper's norms (the
convention of `Statement.lemma_B_1`). The two norms are equivalent with constants depending only
on `m`. The proof of (1.2) absorbs these constants: it adds the two bounds
`C_qμ^{a_q}λ_j^{-5/2} ≤ ½λ_j^{-1}` and `μλ_j^{-3P+5m+2+ψ'_q} ≤ ½λ_j^{-1}`, each with powers of
`λ_j` to spare for `j` large (:381-385, :417-421). For `q = 0` the bound is (M.7.4), which
`Theorem71Conclusions.increment` states with the same norm. -/
def MixedIncrementBound {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (m q j : ℕ) : Prop :=
  let S := c.stages.slab j
  let w : Velocity := slabTimeJet 0 S q
    (fun r x => c.stages.velocity j r x - c.stages.velocity (j - 1) r x -
      c.stages.oscillation j r x)
  (∀ t ∈ Icc 0 S, SpatialHolderHalf m (w t) ∧ spatialHolderHalfNorm m (w t) ≤ (P.frequency j)⁻¹) ∧
    ContinuousOnSlabInSpatialNorm S (spatialHolderHalfNorm m) w

/-- **The bounds (1.3) of the auxiliary note at step `j`** (`aux:terminal:time-bounds`,
auxiliary/terminal_smoothness.tex:101-104), for the construction `c`, the time order `q` and the
exponent `ψq` (the `ψ_q` of the note, not the cutoff symbol of Appendix M.B): for `0 ≤ i ≤ q`,
`‖∂_t^iU_j‖_{C([0,S_j];L^∞)} ≤ λ_j^{ψ_q}` and `‖∂_t^iR_j‖_{C([0,S_j];L^∞)} ≤ λ_{j+1}^{-5/2}`,
where `R_j` is the residual of `U_j` (:77-78).

Representation: as in `MixedIncrementBound`; the `L^∞` norm of these continuous fields is the
pointwise supremum (a bound at every `x`), and membership in `C([0,S_j];L^∞)` is continuity in
the supremum norm (`ContinuousOnSlabInSpatialNorm … spatialSupNorm`); `R_j` is the momentum
residual of `U_j` and its pressure `π_j` on `[0,S_j]` (`c.stages.residual j`); the exponent `ψ_q`
is a natural number (`λ_j ≥ 1`, so this is no restriction). -/
def TimeBounds {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (q ψq j : ℕ) : Prop :=
  let S := c.stages.slab j
  ∀ i : ℕ, i ≤ q →
    (∀ t ∈ Icc 0 S, ∀ x : Vec3,
      ‖slabTimeJet 0 S i (c.stages.velocity j) t x‖ ≤ P.frequency j ^ ψq ∧
        ‖slabTimeJet 0 S i (c.stages.residual j) t x‖ ≤ P.frequency (j + 1) ^ (-(5 / 2) : ℝ)) ∧
      ContinuousOnSlabInSpatialNorm S spatialSupNorm (slabTimeJet 0 S i (c.stages.velocity j)) ∧
      ContinuousOnSlabInSpatialNorm S spatialSupNorm (slabTimeJet 0 S i (c.stages.residual j))

end Aux

end

end TorusEuler.Paper

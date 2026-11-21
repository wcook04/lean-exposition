import TorusEuler.Paper.Auxiliary.Vocabulary
import TorusEuler.Paper.S678.Statements

/-! # Statements of package Auxiliary

Faithful statements (kept for reference after decision D28: they are not ledger rows, are
not proved, and lie outside the spine) of Theorem 1.1, Lemma 1.2 and Lemma 1.3 of the auxiliary note "Smooth
terminal regularity away from the origin" (`paper/craik_criminale_rewrite/auxiliary/
terminal_smoothness.tex`; numbers from its compiled `.aux` file), in namespace
`TorusEuler.Paper.Aux`, and of Remark 1.2 of the latest manuscript
(`sections/01_problem.tex:80`), which the note proves. References with prefix M are to the main
manuscript. The vocabulary is that of `TorusEuler.Paper.Auxiliary.Vocabulary`,
`TorusEuler.Paper.S678.Vocabulary` and `TorusEuler.Paper.S678.StepData`.

The lemmas concern "the fields `U_j` of this construction" (terminal_smoothness.tex:75): the
construction of Theorem M.7.1 obtained with a function `𝓑` chosen as in the note. They are
stated in predicate form, for every construction satisfying the conclusions of Theorem M.7.1
(`Theorem71Conclusions`) and its exported step data (`Theorem71Steps`) whose threshold satisfies
the additional condition of the note (`Aux.TimeDerivativeThreshold`). -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler.Paper

namespace Aux

/-- **Lemma 1.3** of the auxiliary note (`aux:terminal:time`, auxiliary/terminal_smoothness.tex:97).
For every integer `q ≥ 0` there are an exponent `ψ_q` and an index `j_q`, depending only on `q` and
the fixed construction, such that for `j ≥ j_q` and `0 ≤ i ≤ q`, (1.3)
`‖∂_t^iU_j‖_{C([0,S_j];L^∞)} ≤ λ_j^{ψ_q}` and `‖∂_t^iR_j‖_{C([0,S_j];L^∞)} ≤ λ_{j+1}^{-5/2}`
(`Aux.TimeBounds c q ψ_q j`).
Equations: (1.3) of the note; in the setting, (M.1.13), (M.1.14) (the parameters `P`); (M.6.1),
(M.7.1), (M.7.3), (M.7.4) (`Theorem71Conclusions`) and (M.2.23) (its constant `C = 18e³`);
(M.7.2), (M.5.46), (M.5.55) (`Theorem71Steps`); (M.7.5) (the stage type of `c`).

Setting (:56-79). "The additional estimates concern the fields `U_j` of this construction" (:75):
the construction of Theorem M.7.1 obtained with a function `𝓑` of Subsection M.1.5 that also
bounds the constants of the time-derivative estimates of the note (:56-62), for an initial
frequency `N` chosen after `𝓑` (:66-68) and sufficiently large, as Theorem M.7.1 requires.
Predicate form: the lemma holds for every construction `c` with the conclusions (not the
hypotheses on `𝓑`) of `Statement.theorem_7_1` (`P.strengthConstant = 18e³`,
`Theorem71Conclusions c (18e³) T` with `T = T_∞`, and the step data `Theorem71Steps c a ψ`, the
ledger export of Theorem 7.1: the Section M.5 data of every step, with `O_j` the oscillation of
step `j`, :77-78) whose parameters `P` (the schedule (M.1.14) with `𝓑 = P.threshold` and
`λ_0 = P.frequency 0`) satisfy `Aux.TimeDerivativeThreshold P.exponentParameter G P.threshold`.
As in the note, there is no condition on the initial frequency `N = λ_0` beyond those that `P`
records ((M.1.13) and `λ_0 ≥ 𝓑(1)`): the lemma covers the construction for every `N` that
Theorem M.7.1 admits, and its proof raises only the starting index, never `N` (:133-135).

Quantifiers. The cutoff symbol `ψ` of Appendix M.B comes first (any `S5.CutoffSymbol`, as in
`Statement.theorem_7_1`), then the envelope exponent `a` of `ℓ_* = 𝖣^{-a}` (Subsection M.5.1
fixes it "sufficiently large": `∃ a₀, ∀ a ≥ a₀`), then the majorant `G` of the constants of the
time-derivative estimates (and of the main-paper constants named under "Generalization" below),
which depends only on the orders, the depth (:63-65) and these fixed
choices, and on no quantity of the constructed solution. The exponent `ψ_q` and the index
`j_q` come after the construction ("depending only on `q` and the fixed construction").

Representation: as in `Aux.TimeBounds` (time derivatives at a fixed spatial point within
`[0,S_j]`; `C([0,S_j];L^∞)` as a bound at every point and time together with continuity in the
supremum norm; `ψ_q ∈ ℕ`) and `Aux.TimeDerivativeThreshold`.

Generalization. The construction is any construction with these properties (the text's
construction is one). The conditions of Subsection M.1.5 on `𝓑` that `AdmissibleThreshold`
records (nondecreasing, and `𝓑(s)` bounds the fixed-order constants of the main paper at orders
and depths at most `7K(s)`) and the choice of `b` in Subsection M.5.6 are not hypotheses:
`P.exponentParameter` is any `b ≥ 1`, and `P` records only the floor (M.1.13) and the schedule
(M.1.14). The note's proof bounds by `𝓑(q_{j+1})` both the constants of its time-derivative
estimates and fixed-order constants of the main paper used at orders and depth at most
`7K(q_{j+1})` (:143-148), for example the constant of the tail bound (M.B.2) at the order `P`
(:413-414). In this statement the majorant `G` covers both kinds (`Aux.TimeDerivativeThreshold`).
The fixed-order constants depend only on the orders, the depth and the fixed profiles
(sections/01b_parameters.tex:13-17); in `Statement.theorem_5_6`, `Statement.lemma_5_7`,
`Statement.proposition_5_11` and `Statement.lemma_B_1` they come after `ψ` and `a` and before
`b`, so `G` can be chosen before `b`, as here. -/
def Statement.lemma_1_3 : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ G : ℕ → ℝ,
    ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (T : ℝ),
      TimeDerivativeThreshold P.exponentParameter G P.threshold →
      P.strengthConstant = 18 * Real.exp 3 → Theorem71Conclusions c (18 * Real.exp 3) T →
      Theorem71Steps c a ψ →
        ∀ q : ℕ, ∃ ψq jq : ℕ, ∀ j : ℕ, jq ≤ j → TimeBounds c q ψq j

/-- **Lemma 1.2** of the auxiliary note (`aux:terminal:mixed`, auxiliary/terminal_smoothness.tex:81).
For all integers `m, q ≥ 0` and all sufficiently large `j`, (1.2)
`‖∂_t^q(U_j - U_{j-1} - O_j)‖_{C([0,S_j];C^{m,1/2})} ≤ λ_j^{-1}`; the time derivatives are taken
at a fixed spatial point, and the starting index may depend on `(m,q)`
(`Aux.MixedIncrementBound c m q j`).
Equations: (1.2) of the note; in the setting, as in `Aux.Statement.lemma_1_3`: (M.1.13),
(M.1.14); (M.6.1), (M.7.1), (M.7.3), (M.7.4), (M.2.23); (M.7.2), (M.5.46), (M.5.55); (M.7.5).

Setting, predicate form and quantifiers: as in `Aux.Statement.lemma_1_3` (every construction
with the conclusions, not the hypotheses on `𝓑`, of `Statement.theorem_7_1`:
`P.strengthConstant = 18e³`, `Theorem71Conclusions c (18e³) T` and `Theorem71Steps c a ψ`,
whose threshold satisfies `Aux.TimeDerivativeThreshold` for the majorant `G`, with no condition
on the initial frequency beyond those of `P`; `ψ`, then `a ≥ a₀`, then `G`). "All sufficiently
large `j`", with a starting index depending on `(m,q)`, is `∀ m q, ∀ᶠ j in atTop`.

Representation: as in `Aux.MixedIncrementBound` (time derivatives at a fixed spatial point within
`[0,S_j]`; `C([0,S_j];C^{m,1/2})` as a bound at every time together with continuity in
`C^{m,1/2}`; `O_j = c.stages.oscillation j`). Generalization: as in `Aux.Statement.lemma_1_3`
(any such construction; no `AdmissibleThreshold` hypothesis and no condition on `b`, so `G` also
covers the fixed-order constants of the main paper that the proof bounds by `𝓑(q_{j+1})`). -/
def Statement.lemma_1_2 : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ G : ℕ → ℝ,
    ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (T : ℝ),
      TimeDerivativeThreshold P.exponentParameter G P.threshold →
      P.strengthConstant = 18 * Real.exp 3 → Theorem71Conclusions c (18 * Real.exp 3) T →
      Theorem71Steps c a ψ →
        ∀ m q : ℕ, ∀ᶠ j in atTop, MixedIncrementBound c m q j

/-- **Theorem 1.1** of the auxiliary note (`aux:terminal:smooth`,
auxiliary/terminal_smoothness.tex:46). The function `𝓑` of Subsection M.1.5 may be chosen so that
the restriction of the solution in Theorem M.1.1 to `[0,T_*) × (𝕋³ ∖ {0})` extends to a smooth
field on an open space-time neighbourhood of `{T_*} × (𝕋³ ∖ {0})`. All other conclusions of that
theorem remain unchanged. The Euler equations are imposed only for `0 ≤ t < T_*`.
Equations: the Euler equations (M.1.1) (through `EulerSingularityWitness`, the uniqueness
conjunct over `IsMaximalEulerSolution` and `Proposition81Conclusions`), (M.1.2), (M.1.3)
(through `EulerSingularityWitness`), (M.1.13), (M.1.14); through `Theorem71Conclusions` and its
constant `C = 18e³`, (M.6.1), (M.7.1), (M.7.3), (M.7.4), (M.2.23); through `Theorem71Steps`,
(M.7.2), (M.5.46), (M.5.55); through the stage type of `c`, (M.7.5).

Quantifiers, as in `Statement.theorem_7_1`: the cutoff symbol `ψ` of Appendix M.B, a floor `a₀`
for the envelope exponent, then `b ≥ 1`, the envelope exponent `a ≥ a₀`, the majorant `F` of the
fixed-order constants of the main paper and the majorant `G` of the constants of the
time-derivative estimates of the note (`G` may also majorize fixed-order constants of the main
paper, as in the lemmas; here they are bounded through `AdmissibleThreshold` as well).
"`𝓑` may be chosen so that …" is: functions `𝓑` admitted
by Subsection M.1.5 (`AdmissibleThreshold b F 𝓑`) that satisfy the additional condition of the
note (`Aux.TimeDerivativeThreshold b G 𝓑`, the choice at :56-62) exist (first conjunct), and
every such `𝓑` has the property (the proof applies to each of them).

"The solution in Theorem M.1.1" is the solution obtained with `𝓑` ("the construction and the main
theorem are obtained with it", :69-70; `𝓑` is chosen before `N`, :66-68): for every sufficiently
large `N` there are the construction `c` of Theorem M.7.1 with `λ_0 = N` (with its conclusions,
`C = 18e³`, and its step data) and fields `u`, `p` with the conclusions of Proposition M.8.1 for
`c` (so the `U_j` converge to `u`, and `u` is the restriction to `[0,T_∞)` of every maximal
solution from `u(0)`). For them all conclusions of Theorem M.1.1 hold, as in
`Statement.theorem_1_1` (`EulerSingularityWitness (u 0) T u p` and the uniqueness of the maximal
solution, with `T = T_* = T_∞`), and `u` extends smoothly through `T_*` away from the origin
(`SmoothTerminalExtension T u`). The extension is not required to solve the Euler equations.
The conjuncts on `P`, `Theorem71Conclusions`, `Theorem71Steps` and `Proposition81Conclusions`
are this rendering of the subject "the solution in Theorem M.1.1" obtained with `𝓑` (the
conclusion of `Statement.theorem_7_1` for `𝓑` and `N`, and that of Proposition M.8.1 for its
sequence), not additional conclusions; the theorem asserts nothing new about them.

Representation: as in `Statement.theorem_7_1`, `Statement.theorem_1_1`,
`Proposition81Conclusions` and `SmoothTerminalExtension`. -/
def Statement.theorem_1_1 : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∀ a₀ : ℕ, ∃ (b a : ℕ) (F G : ℕ → ℝ), 1 ≤ b ∧ a₀ ≤ a ∧
    (∃ B : ℕ → ℝ, AdmissibleThreshold b F B ∧ TimeDerivativeThreshold b G B) ∧
    ∀ B : ℕ → ℝ, AdmissibleThreshold b F B → TimeDerivativeThreshold b G B →
      ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
        ∃ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (T : ℝ)
          (u : Velocity) (p : Pressure),
          P.exponentParameter = b ∧ P.threshold = B ∧ P.frequency 0 = N ∧
            P.strengthConstant = 18 * Real.exp 3 ∧
            Theorem71Conclusions c (18 * Real.exp 3) T ∧ Theorem71Steps c a ψ ∧
            Proposition81Conclusions c T u p ∧
            EulerSingularityWitness (u 0) T u p ∧
            (∀ (T' : ℝ) (v : Velocity) (q : Pressure),
              IsMaximalEulerSolution T' v q → v 0 = u 0 → T' = T ∧ EqOn v u (Ico 0 T)) ∧
            SmoothTerminalExtension T u

end Aux

/-- **Remark 1.2** (unlabelled, sections/01_problem.tex:80). The solution in Theorem 1.1 may be
chosen so that it extends smoothly in space and time through `T_*` away from the origin; a proof
is given in the auxiliary note (its Theorem 1.1, `Aux.Statement.theorem_1_1`). In the spine the
remark is proved from the library theorem `auxiliaryTerminalSmoothness` (decision D28), not from
`Aux.Statement.theorem_1_1`.

Statement: there is a solution with all conclusions of Theorem 1.1, as in
`Statement.theorem_1_1` (`EulerSingularityWitness u₀ T u p`, `T = T_*`, and the uniqueness of the
maximal solution from `u₀`), whose restriction to `[0,T_*) × (𝕋³ ∖ {0})` extends to a smooth field
on an open space-time neighbourhood of `{T_*} × (𝕋³ ∖ {0})`, the extension of Theorem 1.1 of the
note (`SmoothTerminalExtension T u`).
Equations: the Euler equations (1.1), (1.2) and (1.3), through `EulerSingularityWitness` and the
uniqueness conjunct over `IsMaximalEulerSolution`, as in `Statement.theorem_1_1`.

Representation: as in `Statement.theorem_1_1` and `SmoothTerminalExtension`. -/
def Statement.remark_1_2 : Prop :=
  ∃ (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure),
    EulerSingularityWitness u₀ T u p ∧
      (∀ (T' : ℝ) (v : Velocity) (q : Pressure),
        IsMaximalEulerSolution T' v q → v 0 = u₀ → T' = T ∧ EqOn v u (Ico 0 T)) ∧
      SmoothTerminalExtension T u

end TorusEuler.Paper

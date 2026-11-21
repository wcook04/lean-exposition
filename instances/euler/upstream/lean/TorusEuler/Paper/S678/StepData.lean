import TorusEuler.Paper.S678.Vocabulary
import TorusEuler.Paper.S5.Vocabulary

/-! # The step data of the construction of Theorem 7.1

Vocabulary for the ledger export of Theorem 7.1 (`cc:uf:tower:thm:finite`,
sections/08b_induction.tex:142) that records how each field of the sequence is built:
`Paper.Theorem71StepData` (the defining clauses of step `j`, in the vocabulary of Section 5,
`TorusEuler.Paper.S5`) and `Paper.Theorem71Steps` (every step `j ≥ 1` has such data, for one
cutoff symbol `ψ` of Appendix B), and the glue lemma `Paper.exists_appendixB_cutoffSymbol`
(a symbol exists).

Step `j` is described in sections/08b_induction.tex:94-139 and 199-227: "At step `j` we choose
the wave over `U_{j-1}` as in Section 6 and apply Proposition 5.11 to obtain `U_j`", with
`U = U_{j-1}`, `λ = λ_j`, activation time `t_j`, final time `S_j`, `𝖣 = λ_{j-1}^9`, depth
`P = 6K_{j+1}` (7.2) and final Fourier cutoff `Λ_j = λ_j^5`; items 4 and 5 of the proof
(:376-461) take the expansion of Subsection 5.5, `V = U_{j-1} + W^♮`, `U_j = S_{Λ_j}V` and
`O_j = W_osc^♮`. The auxiliary note (auxiliary/terminal_smoothness.tex:75-79, 115-462) reads
these data: the parent `U = U_{j-1}` with its flow `X`, `M = (∇U)∘X`, `R_U = R_{j-1}`, `T = S_j`,
`𝖣 = λ_{j-1}^9`, the depth `P`, the norms at `ℓ_*` and `h`, the mean and transverse solutions,
`A₁`, `V₁ = χ̃A₁`, `R_χ̃`, the cutoff of Subsection 6.2, the weight `γ` on `[t_j, t_j + 1/r]`
(through (6.8)), `V` and its residual `R_V` (5.46), `v_Λ = (S_{Λ_j} - Id)V`, `U_j = S_{Λ_j}V`,
`U_j - U_{j-1} - O_j = W̄^♮ + v_Λ` and `R_j` (through (5.58)).

Index conventions are those of `TorusEuler.Paper.S678.Vocabulary`: `c.stages.velocity j = U_j`,
`(c.stage j).flow = X_j`, `(c.stage j).pressure = π_j`, `c.stages.activation j = t_j`,
`c.stages.slab j = S_j`, `c.centralWaves.{waveVector, amplitude, cutoff} j = κ_j(·,0), 𝐚_j(·,0),
χ̃_j`, `c.stages.oscillation j = O_j`, `P.frequency j = λ_j`, `P.order j = q_j`. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

open HierarchyTwistedProfile

noncomputable section

/-- **The data of step `j` of the construction of Theorem 7.1** (`cc:uf:tower:thm:finite`,
sections/08b_induction.tex:94-139, 199-227, 376-461), for `j ≥ 1`, in the vocabulary of
Section 5 (`TorusEuler.Paper.S5`). The step applies Section 5 with the parent `U = U_{j-1}`
(flow `X = X_{j-1}`, pressure `p_U = π_{j-1}`), `𝖣 = λ_{j-1}^9`, `λ = λ_j`, activation time
`t₀ = t_j` and final time `T = S_j` (sections/08b_induction.tex:221-227). The arguments are the
constant wave vector `k = k_*`, the seed at the origin `center = 𝐚(·,0)`, the seed `amp = 𝐚` at
all labels, the parent coefficient profiles `d` of `U`, `X`, `k_*`, the cutoff `χ = χ̃_j`, the
pulled-back residual `R = R_U∘X`, the activation term `S = χ̃'A₁` and the profiles `u` of the
expansion; `a` is the envelope exponent (`ℓ_* = 𝖣^{-a}`) and `ψ` the cutoff symbol of
Appendix B.

* `parent`: the standing hypotheses of Subsection 5.1 on `U_{j-1}` on `[0,S_j]`
  (sections/08a_parent_step.tex:9-33, 99-104: (5.1), (5.2), (5.6)), which item 1 of the proof
  establishes (sections/08b_induction.tex:269-282, with (7.6)).
* `launch`: `k_* ≠ 0`, `t_j ∈ [0,S_j)` and `|κ(t_j,0)| = λ_j` (sections/08a_parent_step.tex:35-40),
  for `κ = (D_aX)^{-T}k_*`.
* `origin`: the seed at the origin solves (3.2), is perpendicular to `κ(·,0)` and satisfies the
  two conditions (5.5) with `𝖣 = λ_{j-1}^9` (sections/08a_parent_step.tex:47-53, 78-94; item 2,
  sections/08b_induction.tex:284-328).
* `amplitude`: the seed of wave `j` at the center is `𝐚_j = 𝐚(·,0)` on `[t_j,S_j]`
  (sections/08b_induction.tex:108-116). The auxiliary note reads it for the weight
  `γ = λ_j^{3/4}|𝐚(·,0)| ≤ Ce^{-L_j}` on `[t_j, t_j + 1/r]` by (6.8)
  (auxiliary/terminal_smoothness.tex:403-407): for `j ≥ 2`, (6.8) for `𝐚_j` is
  `(c.centralWaves.crossing (j-2)).early_gain` with the peak `λ_j^{-3/4}`, through
  `c.centralWaves.current_amplitude (j-2)`.
* `seed`: the seed at every label solves (3.2) on `[t_j,S_j]` from (5.4)
  (sections/08a_parent_step.tex:63-69).
* `cutoff`: `χ` is the time cutoff `χ̃_j` of wave `j` (sections/08b_induction.tex:118; `χ̃_1 ≡ 1`
  by (6.3); for `j ≥ 2` the display of Subsection 6.2, sections/08b_induction.tex:68-73), which
  `Theorem71Conclusions.first_cutoff` and `later_cutoff` fix.
* `expansion`: the profiles of Subsection 5.5 (sections/06c_finite_hierarchy.tex:222-302:
  (3.7), (3.8), (5.11), (5.15), (5.25)–(5.28)) at depth `P = 6K_{j+1}` (7.2), with envelope radius
  `ℓ_* = 𝖣^{-a}` (sections/08a_parent_step.tex:105-110), width `h = λ_j^{-1/2}`
  (sections/08a_parent_step.tex:46-47), `R = R_{j-1}∘X_{j-1}` and `S = χ̃_j'A₁`; item 4,
  sections/08b_induction.tex:376-381.
* `approximate`: Lemma 5.8 for this expansion (sections/08_exact_wave.tex:82-88): `V = U_{j-1} + W^♮`
  is smooth, periodic, odd and divergence free, `Π = π_{j-1} + 𝖯^♮` is smooth and periodic, and
  (5.46) `V_t + V·∇V + ∇Π = R_V = R_P^♮ + R_χ̃^♮` on `[0,S_j]`, with `R_χ̃ = S + C[S]` (3.8). These
  are the first three conjunct groups of `Statement.lemma_5_8` at the data of step `j`. The
  auxiliary note reads `V`, `R_V` (auxiliary/terminal_smoothness.tex:387-389) and cites the
  identity (5.58) for `R_j` (:428-440), a display in the proof of Proposition 5.11
  (sections/08_exact_wave.tex:408-416) whose premises are (5.46) and the truncation (5.55); this
  field and `truncation` are these premises at step `j`.
* `truncation`: `U_j = S_{Λ_j}V` (5.55) with `Λ_j = λ_j^5` and `V = U_{j-1} + W^♮`,
  `W = ∑_{p=1}^P (V_p + C_{p+1} + B_p)` (item 5, sections/08b_induction.tex:414-415;
  sections/08b_induction.tex:105-107, 227), and `π_j` is the zero-mean pressure of `U_j` with
  `Δπ_j = -tr((∇U_j)²)` (sections/08_exact_wave.tex:386-387). The residual `R_j` of `U_j` with
  `π_j` is then fixed by the type (`c.stages.residual j`).
* `oscillation`: `O_j = W_osc^♮`, the Eulerian oscillation `(W - ⟨W⟩)^♮` of Lemma 5.8
  (sections/08b_induction.tex:118-120; (3.1)), on `[0,S_j]`.

Representation: the objects of Section 5 enter in the predicate form of
`TorusEuler.Paper.S5` (`S5.Parent`, `S5.Launch`, `S5.Origin`, `S5.IsSeed`, `S5.IsExpansion`,
`S5.IsTruncation`), with their documented representation changes (periodic lift; operator norms;
the label flow `X s t`; `f^♮ = graphRead (fun t => X t 0) f`; `S_Λ` the real Fourier multiplier
`realVectorFourierCutoff ψ Λ`; profiles as lattice-twisted profiles on the closed slab; the
divergence corrections in the latest indexing `C₁ = 0`, `C_{p+1} = C[V_p]`); (5.46) is written
as in `Statement.lemma_5_8` (`momentumResidual` on the closed slab, joint smoothness on
`[0,S_j] × ℝ³`); `K_{j+1} = K(q_{j+1})` is
`frequencyExponent P.exponentParameter (P.order (j + 1))`; the identifications with the fields
of `c` are stated on `[0,S_j]` (cutoff, oscillation) and on `[t_j,S_j]` (central seed), the sets
on which the text uses them.

Not recorded, because no later proof reads them: the central wave vector `κ_j` of the step
(the type and `Theorem71Conclusions` record the wave vector `c.centralWaves.waveVector j`, but it
is not identified with `κ(·,0)` of `k`), the normalization `max |𝐚_j(t,0)| = λ_j^{-3/4}` (for
`j ≥ 2` it is `(c.centralWaves.crossing (j-2)).peak`; `S5.Origin` records `γ ≤ 1`), and the
data (6.3) of the first wave. -/
structure Theorem71StepData {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (a : ℕ) (ψ : Vec3 → ℝ) (j : ℕ) (k : Vec3) (center : ℝ → Vec3) (amp : ℝ → Vec3 → Vec3)
    {hT : 0 < c.stages.slab j}
    (d : ParentGeometry hT (c.stages.velocity (j - 1)) (c.stage (j - 1)).flow k)
    (χ : PaperWaveCutoff (c.stages.activation j) (c.stages.slab j))
    (R S : HierarchyTwistedProfile (c.stages.slab j) k Vec3)
    (u : HierarchyProfiles (HierarchyTwistedProfile (c.stages.slab j) k Vec3)
      (HierarchyTwistedProfile (c.stages.slab j) k ℝ)) : Prop where
  parent : S5.Parent (c.stages.slab j) (c.stages.velocity (j - 1)) (c.stage (j - 1)).flow
    (c.stage (j - 1)).pressure (P.frequency (j - 1) ^ 9) (P.frequency j)
  launch : S5.Launch (c.stages.slab j) (c.stage (j - 1)).flow k (P.frequency j)
    (c.stages.activation j)
  origin : S5.Origin (c.stages.slab j) (c.stages.velocity (j - 1)) (c.stage (j - 1)).flow k
    (P.frequency (j - 1) ^ 9) (P.frequency j) (c.stages.activation j) center
  amplitude : ∀ t ∈ Icc (c.stages.activation j) (c.stages.slab j),
    center t = c.centralWaves.amplitude j t
  seed : S5.IsSeed (c.stages.velocity (j - 1)) (c.stage (j - 1)).flow k (c.stages.activation j)
    (c.stages.slab j) center amp
  cutoff : ∀ t ∈ Icc 0 (c.stages.slab j), χ.value t = c.centralWaves.cutoff j t
  expansion : S5.IsExpansion d (c.stage (j - 1)).pressure χ (S5.radius (P.frequency (j - 1) ^ 9) a)
    (S5.width (P.frequency j)) amp (6 * frequencyExponent P.exponentParameter (P.order (j + 1)))
    R S u
  approximate :
    let Y : Velocity := fun t => (c.stage (j - 1)).flow t 0
    let depth := 6 * frequencyExponent P.exponentParameter (P.order (j + 1))
    let V : Velocity := c.stages.velocity (j - 1) + graphRead Y (S5.expansion u depth)
    let Pres : Pressure := (c.stage (j - 1)).pressure + graphRead Y (S5.expansionPressure u depth)
    let RV : Velocity :=
      graphRead Y (S5.remainder (S5.ops d) u depth + (S + S5.curlCorrection d S))
    (ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 (c.stages.slab j) ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 (c.stages.slab j), SpatiallyPeriodic (V t) ∧ Function.Odd (V t) ∧
        ∀ x, divergence (V t) x = 0) ∧
    (ContDiffOn ℝ ∞ (Function.uncurry Pres) (Icc 0 (c.stages.slab j) ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 (c.stages.slab j), SpatiallyPeriodic (Pres t)) ∧
    ∀ t ∈ Icc 0 (c.stages.slab j), ∀ x,
      momentumResidual (Icc 0 (c.stages.slab j)) V Pres t x = RV t x
  truncation : S5.IsTruncation (c.stages.slab j) ψ (P.frequency j ^ 5)
    (c.stages.velocity (j - 1) + graphRead (fun t => (c.stage (j - 1)).flow t 0)
      (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (j + 1)))))
    (c.stages.velocity j) (c.stage j).pressure
  oscillation : ∀ t ∈ Icc 0 (c.stages.slab j),
    c.stages.oscillation j t =
      graphRead (fun t => (c.stage (j - 1)).flow t 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (j + 1))) -
          (S5.ops d).average
            (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (j + 1))))) t

/-- **The step data of the construction of Theorem 7.1** (`cc:uf:tower:thm:finite`,
sections/08b_induction.tex:142), exported by `Statement.theorem_7_1` for the auxiliary note
(ledger `exports` of row 7.1). Every step `j ≥ 1`
of the construction `c` has data in the sense of `Theorem71StepData c a ψ j`, for the envelope
exponent `a` and the cutoff symbol `ψ` of Appendix B: the parent `U_{j-1}`, the wave `j` with its
seed at the center and its cutoff, the expansion of Subsection 5.5 at depth `P = 6K_{j+1}` (7.2),
the approximate solution `V` with (5.46) of Lemma 5.8, the truncation `U_j = S_{Λ_j}V` (5.55),
`Λ_j = λ_j^5`, and the oscillation `O_j = W_osc^♮` of Lemma 5.8. The auxiliary note says that
its estimates concern "the fields $U_j$ of this construction"
(auxiliary/terminal_smoothness.tex:75), with `O_j` the oscillation of step `j` and `R_j` the
residual of `U_j` (:77-78); its proof (:115-462) reads the step data listed in
`Theorem71StepData`.

Representation: as in `Theorem71StepData`. The symbol `ψ` is a parameter: Appendix B fixes it
once (sections/appB_cutoff.tex:2-5), before every constant that depends on it, and
`Statement.theorem_7_1` quantifies it first, as `Statement.proposition_5_11` does. -/
def Theorem71Steps {P : InductiveEulerParameters} (c : InductiveEulerConstruction P) (a : ℕ)
    (ψ : Vec3 → ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    ∃ (hT : 0 < c.stages.slab j) (k : Vec3) (center : ℝ → Vec3) (amp : ℝ → Vec3 → Vec3)
      (d : ParentGeometry hT (c.stages.velocity (j - 1)) (c.stage (j - 1)).flow k)
      (χ : PaperWaveCutoff (c.stages.activation j) (c.stages.slab j))
      (R S : HierarchyTwistedProfile (c.stages.slab j) k Vec3)
      (u : HierarchyProfiles (HierarchyTwistedProfile (c.stages.slab j) k Vec3)
        (HierarchyTwistedProfile (c.stages.slab j) k ℝ)),
      Theorem71StepData c a ψ j k center amp d χ R S u

/-- A cutoff symbol of Appendix B exists (sections/appB_cutoff.tex:2-3, "Fix a radial
`ψ ∈ C_c^∞(ℝ³)` with `0 ≤ ψ ≤ 1`, `ψ = 1` on `|ζ| ≤ 1` and `supp ψ ⊆ {|ζ| ≤ 2}`"): the radial
bump `ψ(ζ) = σ(2 - |ζ|)` of Mathlib's `ContDiffBumpBase.ofInnerProductSpace` at radius `2`, with
`σ` the smooth transition. Glue for applying `Statement.theorem_7_1`, which is stated for every
such symbol; it is not the content of a numbered result. -/
theorem exists_appendixB_cutoffSymbol : ∃ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ := by
  let B := ContDiffBumpBase.ofInnerProductSpace Vec3
  refine ⟨fun ξ => B.toFun 2 ξ, ?_⟩
  have hval (ξ : Vec3) : B.toFun 2 ξ = Real.smoothTransition ((2 - ‖ξ‖) / (2 - 1)) := rfl
  refine ⟨fun ξ η h => by simp only [hval, h], ?_, fun ξ => B.mem_Icc 2 ξ,
    fun ξ hξ => B.eq_one 2 (by norm_num) ξ hξ, fun ξ hξ => ?_⟩
  · have h := B.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun (x : Vec3) (_ : x ∈ (univ : Set Vec3)) =>
        (show ((2 : ℝ), x) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set Vec3) from ⟨by norm_num, mem_univ x⟩))
    exact contDiffOn_univ.mp h
  · rw [hval]
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by norm_num))

end

end TorusEuler.Paper

import TorusEuler.InductiveStageConstruction
import TorusEuler.Paper.S2.Vocabulary

/-! # Vocabulary for the statements of package S678

Notation of Subsection 1.5, Sections 6–8 and Theorem 1.1 of the latest manuscript
(`paper/craik_criminale_rewrite`), and the conclusion predicates that the statements of
Sections 7 and 8 use as their setting.

* `Paper.Schedule.L`, `Paper.Schedule.ε`, `Paper.Schedule.τ`: the gain `L_j`, the coupling
  ratio `ε_j` of (1.14) and the half length `τ_j` of Section 7.
* `Paper.Lemma61Conclusions`: the conclusions of Lemma 6.1 for the first wave (6.3).
* `Paper.AdmissibleThreshold`: the conditions that Subsection 1.5 imposes on the function `𝓑`.
* `Paper.Theorem71Conclusions`: the conclusions of Theorem 7.1 for a construction.
* `Paper.Proposition81Conclusions`, `Paper.Proposition82Conclusions`,
  `Paper.Corollary83Conclusions`, `Paper.Proposition84Conclusions`: the conclusions of
  Section 8 for the limit of a construction satisfying `Theorem71Conclusions`.

Index conventions. Lean indices are the manuscript's indices: `P.frequency j = λ_j`,
`P.order j = q_j`, `c.stages.velocity j = U_j`, `c.stages.activation j = t_j` (`j ≥ 1`;
the value at `0` is an unused `0`), `c.stages.slab j = S_j`, and the central data
`c.centralWaves.waveVector j = κ_j`, `amplitude j = 𝐚_j`, `cutoff j = χ̃_j`,
`error j = E_{c,j}`, `c.stages.oscillation j = O_j` for `j ≥ 1`. Clauses about a
positive index carry an explicit hypothesis `1 ≤ j` (or `2 ≤ j`), and `j - 1` is the
manuscript's `j-1` under that hypothesis. -/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Topology

namespace TorusEuler.Paper

open MovingWaveVector (frame entry)

noncomputable section

namespace Schedule

/-- The prescribed logarithmic gain `L_j = 4 log λ_{j+1}` of (1.14), for the frequency
sequence `freq j = λ_j`. -/
def L (freq : ℕ → ℝ) (j : ℕ) : ℝ := 4 * Real.log (freq (j + 1))

/-- The prescribed coupling ratio `ε_j = L_{j+1}^{-2}` of (1.14) (written there as
`ε_{j-1} = L_j^{-2}` for `j ≥ 2`); used for `j ≥ 1`. -/
def ε (freq : ℕ → ℝ) (j : ℕ) : ℝ := couplingRatioOfGain (L freq (j + 1))

/-- The half length `τ_j = λ_{j-1}^{-1/8} L_{j+1}^3` of the endpoint interval
`[t_j, S_j]`, `S_j = t_j + 2τ_j` (Section 7, display before (7.2)); used for `j ≥ 1`. -/
def τ (freq : ℕ → ℝ) (j : ℕ) : ℝ := freq (j - 1) ^ (-1 / 8 : ℝ) * L freq (j + 1) ^ 3

end Schedule

/-- The conclusions of Lemma 6.1 (`cc:uf:base:lem:first`) for the first wave (6.3) at the
origin over the stationary shear (6.1) with parameter `ρ`, on `[0,T]`, at frequency
`freq = λ`.

* `propagation`: the first condition (5.5): for every `𝖣 ≥ 2`, every solution `𝐛` of the
  seed equation (3.2) at the origin (where `M = ∇U_0(t,0) = B_ρ`) that is perpendicular to
  `κ(·,0)`, and all `0 ≤ t' ≤ t ≤ T`, `|𝐛(t)|/γ(t) ≤ 𝖣 |𝐛(t')|/γ(t')` with
  `γ(t) = λ^{3/4} |𝐚(t,0)|`.
* `coupling`: the second condition (5.5): `ν(t,0) ≥ 𝖣^{-1}` on `[0,T]`, where `ν(t,0)` is
  the coupling `E_1 · B_ρ E_2` in the frame `(κ/|κ|, 𝐚/|𝐚|, ·)` of the pair at the origin.
* `initial_strength`: `λ^{1/4}/2 ≤ |𝐚(0,0)| |κ(0,0)| ≤ λ^{1/4}`.

Representation: the first wave is the structure `FirstWaveOrigin ρ T λ` (its data at the
origin: `κ(0,0) = λe_1`, `𝐚(0,0)` a positive multiple of `e_2`, the equations (2.1) and
(3.2) over the constant gradient `B_ρ`, transversality, and `max_{[0,T]} |𝐚(t,0)| = λ^{-3/4}`);
the matrix norm is the operator norm. -/
structure Lemma61Conclusions {ρ T freq : ℝ} (w : FirstWaveOrigin ρ T freq) : Prop where
  propagation : ∀ D : ℝ, 2 ≤ D → ∀ b : ℝ → Vec3,
    (∀ t ∈ Icc 0 T, HasDerivWithinAt b
      (affineWaveAmplitudeOperator (stationaryShearGradient ρ) (w.covector t) (b t)) (Icc 0 T) t) →
    (∀ t ∈ Icc 0 T, ⟪w.covector t, b t⟫_ℝ = 0) →
    ∀ t' t : ℝ, t' ∈ Icc 0 T → t ∈ Icc 0 T → t' ≤ t →
      ‖b t‖ / (freq ^ (3 / 4 : ℝ) * ‖w.amplitude t‖) ≤
        D * (‖b t'‖ / (freq ^ (3 / 4 : ℝ) * ‖w.amplitude t'‖))
  coupling : ∀ D : ℝ, 2 ≤ D → ∀ t ∈ Icc 0 T,
    D⁻¹ ≤ entry (frame w.covector w.amplitude t) (stationaryShearGradient ρ) 0 1
  initial_strength :
    freq ^ (1 / 4 : ℝ) / 2 ≤ ‖w.amplitude 0‖ * ‖w.covector 0‖ ∧
      ‖w.amplitude 0‖ * ‖w.covector 0‖ ≤ freq ^ (1 / 4 : ℝ)

/-- The conditions of Subsection 1.5 on the function `𝓑` (here `B`): it is nondecreasing on
the positive integers, `B(s)` bounds the fixed-order constants at orders and depths at most
`7K(s)` (represented by a majorant `F(s)` of those constants, `F(s) ≤ B(s)`), and the floor
(1.13) `log B(s) ≥ 4K(s+1)^3` holds for `s ≥ 1`, where `K(s) = 320b(s+1)`
(`frequencyExponent b s`). The field `pos` records `B(s) > 0`, which (1.13) presupposes. -/
structure AdmissibleThreshold (b : ℕ) (F B : ℕ → ℝ) : Prop where
  nondecreasing : ∀ s t : ℕ, 1 ≤ s → s ≤ t → B s ≤ B t
  bounds_constants : ∀ s : ℕ, 1 ≤ s → F s ≤ B s
  pos : ∀ s : ℕ, 1 ≤ s → 0 < B s
  floor : ∀ s : ℕ, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)

/-- The conclusions of Theorem 7.1 (`cc:uf:tower:thm:finite`) for a construction `c`, the
absolute constant `C` of (7.3) and the limit `T = T_∞` of the activation times.

The schedule (1.14) (`b`, `𝓑`, `q_j`, `λ_j`) is part of the parameters `P`. The fields:
* `shear`: `U_0` is the stationary shear (6.1) at `ρ = ε_1`.
* `first_times`, `times_increase`: `0 = t_1 = t_2 < t_3 < ⋯`.
* `final_times`: `S_0 = 1` and `S_j = t_j + 2τ_j` for `j ≥ 1`.
* `T1`: (T1) for `j ≥ 0`: `U_j` is smooth on `[0,S_j] × 𝕋³`, odd, divergence free and
  supported on frequencies at most `2Λ_j = 2λ_j^5`.
* `T2`: (T2) for `j ≥ 0`: `|U_j| ≤ λ_j`; the flow `X_j` of `U_j` from time zero satisfies
  `sup |(D_aX_j)^{±1}| ≤ λ_j`; `|R_j| ≤ λ_{j+1}^{-3}`.
* `T3`: (T3) for `j ≥ 0`: `D²π_j ≤ (∑_{i=1}^j λ_{i-1}^{-1}) Id` on `[0,S_j] × 𝕋³`.
* `T4_gradient`, `T4_times`, `T4_late_values`: (T4) for `j ≥ 1`: on `[t_j,S_j]`,
  `∇U_j(t,0) = ∇U_{j-1}(t,0) + χ̃_j 𝐚_j ⊗ κ_j + E_{c,j}` with `|E_{c,j}| ≤ λ_j^{-1/4}`;
  `0 ≤ t_{j+1} - t_j ≤ τ_j` and `χ̃_j = 1` on `[t_{j+1},S_j]`; at `t_{j+1}` the values (7.3)
  `η_j/ν_j = ε_j`, `π ≤ ν_j ≤ 4π`, `C^{-1}λ_j^{1/4} ≤ σ_j ≤ Cλ_j^{1/4}L_{j+1}^2`, with
  `ν_j, η_j` the couplings (7.1) of `∇U_{j-1}(t,0)` in the frame of `(κ_j, 𝐚_j)` and
  `σ_j = |𝐚_j||κ_j|`; `strength_constant`: `C ≥ 2`. The predicate records only `C ≥ 2`, not the
  TeX qualifier "for which (2.23) holds"; `Statement.theorem_7_1` makes the identification by
  taking the explicit constant `C = 18e³` of (2.23) in `Statement.proposition_2_8`.
* `first_cutoff`, `later_cutoff`: the time cutoffs are those of the text: `χ̃_1 ≡ 1` (6.3),
  and for `j ≥ 2`, `χ̃_j(t) = 1 - χ(1 + r(t - t_j))` for `t ≥ t_j` and `0` for `t < t_j`
  (Subsection 6.2), with `r = (2σν)^{1/2}` for the strength `σ` and first coupling `ν` of
  the preceding pair `(κ_{j-1}, 𝐚_{j-1})` over `∇U_{j-2}(t_j,0)`, frozen at `t_j`.
* `lifetime`: `t_j → T_∞ ∈ (0,∞)` and `T_∞ < S_j` for every `j`.
* `oscillation_support`: for `j ≥ 1`, `O_j(t)` is supported in the closed ball of radius
  `λ_{j-1}^{-1}` about the origin (about the lattice `ℤ³` in the lift), `t ∈ [0,S_j]`.
* `increment`: (7.4) for `j ≥ 1`: `‖O_j‖_{C([0,S_j];L^∞)} ≤ λ_j^{-1}` and
  `‖U_j - U_{j-1} - O_j‖_{C([0,S_j];C^{m,1/2})} ≤ λ_j^{-1}` for `0 ≤ m ≤ q_j`.
* `oscillation_vanishes`: for `j ≥ 2`, `O_j = 0` on `[0,t_j]`.

Representation: `𝕋³` is the `ℤ³`-periodic lift to `ℝ³`; matrix norms are operator norms;
`λ_{j+1}^{-3}` is written `(λ_{j+1}^{-1})^3`; the sum in (T3) is reindexed
`∑_{i<j} λ_i^{-1}`; the function `χ` of Subsection 5.1 is `envelopeCutoff`.

Objects defined by reference. The statement uses objects that the text defines in Sections 6
and 7. Here they are fields of `c`, and only the following of their defining clauses are
recorded.
* Fixed by the type of `c` (`InductiveEulerStage`): the flow `X_j` (`X_j(t) = (c.stage j).flow 0 t`,
  the label flow of `U_j`), the pressure `π_j` (smooth, periodic, zero mean,
  `Δπ_j = -tr((∇U_j)²)`) and the residual `R_j` (the momentum residual of `U_j` and `π_j`).
  `E_{c,j}` is the remainder in `T4_gradient` and is fixed once `χ̃_j, 𝐚_j, κ_j` are.
* The central pair `(κ_j, 𝐚_j)` is not fixed. The type records only the central wave equations
  over `∇U_{j-1}(t,0)` on `[t_j,S_j]`, transversality and (5.5) with `𝖣 = λ_{j-1}^9`
  (`InductiveEulerWave.center`). For `j ≥ 2` it also records, through the selected crossing
  `c.centralWaves.crossing (j-2)` (`current_vector`, `current_amplitude`), the initial data of
  Subsection 6.2: `κ_j(t_j,0) = λ_j E_3(t_j)`, `𝐚_j(t_j,0)` a positive multiple of
  `-E_1(t_j)/S + E_2(t_j)`, and `max_{[t_j,S_j]} |𝐚_j(t,0)| = λ_j^{-3/4}`. For `j = 1` the data
  of (6.3) are not recorded: `κ_1(0,0) = λ_1 e_1`, the initial direction `e_2` and the
  normalization `max |𝐚_1(t,0)| = λ_1^{-3/4}`. Only the coupling `ν_1(0) = 2π` of (6.4) is
  recorded (`InductiveEulerBase.initial_coupling`). `Statement.theorem_7_1` adds, through
  `Theorem71Steps` (field `amplitude`), that `𝐚_j` is the seed at the origin of the wave of
  step `j` on `[t_j,S_j]`; it records neither the data (6.3) nor an identification of `κ_j`.
* The cutoffs `χ̃_j` are fixed only by the fields `first_cutoff` and `later_cutoff`, not by the
  type.
* The oscillation `O_j` is not identified with `W_osc^♮` of Lemma 5.8, and no time regularity
  of it is stated. It enters only through `oscillation_support`, `increment` and
  `oscillation_vanishes`, so (7.4) is an existential decomposition
  `U_j - U_{j-1} = O_j + (small)` with `O_j` small and localized. `Statement.theorem_7_1` adds
  the identification through `Theorem71Steps` (`TorusEuler.Paper.S678.StepData`).

Section 8 uses only the listed properties. `c` also carries the data of item 2 of the proof
of Theorem 7.1 that Section 8 reads (`c.centralWaves`: the comparison windows of Subsection 6.2
and the selected crossings) and the bounds (7.7) (`c.lifetime`). -/
structure Theorem71Conclusions {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (C T : ℝ) : Prop where
  shear : ∀ t : ℝ, c.stages.velocity 0 t = stationaryShear (Schedule.ε P.frequency 1)
  first_times : c.stages.activation 1 = 0 ∧ c.stages.activation 2 = 0
  times_increase : ∀ j : ℕ, 2 ≤ j → c.stages.activation j < c.stages.activation (j + 1)
  final_times : c.stages.slab 0 = 1 ∧
    ∀ j : ℕ, 1 ≤ j → c.stages.slab j = c.stages.activation j + 2 * Schedule.τ P.frequency j
  T1 : ∀ j : ℕ,
    ContDiffOn ℝ ∞ (Function.uncurry (c.stages.velocity j))
        (Icc 0 (c.stages.slab j) ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 (c.stages.slab j), SpatiallyPeriodic (c.stages.velocity j t) ∧
        Function.Odd (c.stages.velocity j t) ∧ (∀ x, divergence (c.stages.velocity j t) x = 0) ∧
        RealTorusFourierBand (2 * P.frequency j ^ 5) (c.stages.torusVelocity j t)
  T2 : ∀ j : ℕ,
    (∀ t ∈ Icc 0 (c.stages.slab j), ∀ x, ‖c.stages.velocity j t x‖ ≤ P.frequency j) ∧
      ChildFlow.DeformationOn (c.stages.velocity j) (c.stage j).flow (c.stages.slab j)
        (P.frequency j) ∧
      ∀ t ∈ Icc 0 (c.stages.slab j), ∀ x, ‖c.stages.residual j t x‖ ≤ (P.frequency (j + 1))⁻¹ ^ 3
  T3 : ∀ j : ℕ, ∀ t ∈ Icc 0 (c.stages.slab j), ∀ x v : Vec3,
    ⟪v, fderiv ℝ (gradient ((c.stage j).pressure t)) x v⟫_ℝ ≤
      (∑ i ∈ Finset.range j, (P.frequency i)⁻¹) * ‖v‖ ^ 2
  T4_gradient : ∀ j : ℕ, 1 ≤ j → ∀ t ∈ Icc (c.stages.activation j) (c.stages.slab j),
    fderiv ℝ (c.stages.velocity j t) 0 =
        fderiv ℝ (c.stages.velocity (j - 1) t) 0 +
          c.centralWaves.cutoff j t •
            (innerSL ℝ (c.centralWaves.waveVector j t)).smulRight (c.centralWaves.amplitude j t) +
          c.centralWaves.error j t ∧
      ‖c.centralWaves.error j t‖ ≤ P.frequency j ^ (-1 / 4 : ℝ)
  T4_times : ∀ j : ℕ, 1 ≤ j →
    0 ≤ c.stages.activation (j + 1) - c.stages.activation j ∧
      c.stages.activation (j + 1) - c.stages.activation j ≤ Schedule.τ P.frequency j ∧
      ∀ t ∈ Icc (c.stages.activation (j + 1)) (c.stages.slab j), c.centralWaves.cutoff j t = 1
  strength_constant : 2 ≤ C
  T4_late_values : ∀ j : ℕ, 1 ≤ j →
    let t := c.stages.activation (j + 1)
    let E := frame (c.centralWaves.waveVector j) (c.centralWaves.amplitude j) t
    let M := fderiv ℝ (c.stages.velocity (j - 1) t) 0
    let ν := entry E M 0 1
    let η := entry E M 2 1
    let σ := ‖c.centralWaves.amplitude j t‖ * ‖c.centralWaves.waveVector j t‖
    η / ν = Schedule.ε P.frequency j ∧ Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi ∧
      C⁻¹ * P.frequency j ^ (1 / 4 : ℝ) ≤ σ ∧
      σ ≤ C * P.frequency j ^ (1 / 4 : ℝ) * Schedule.L P.frequency (j + 1) ^ 2
  first_cutoff : ∀ t : ℝ, c.centralWaves.cutoff 1 t = 1
  later_cutoff : ∀ j : ℕ, 2 ≤ j → ∀ t : ℝ,
    let t₀ := c.stages.activation j
    let σ := ‖c.centralWaves.amplitude (j - 1) t₀‖ * ‖c.centralWaves.waveVector (j - 1) t₀‖
    let ν := entry (frame (c.centralWaves.waveVector (j - 1)) (c.centralWaves.amplitude (j - 1)) t₀)
      (fderiv ℝ (c.stages.velocity (j - 2) t₀) 0) 0 1
    let r := Real.sqrt (2 * σ * ν)
    c.centralWaves.cutoff j t = if t < t₀ then 0 else 1 - envelopeCutoff (1 + r * (t - t₀))
  lifetime : 0 < T ∧ Tendsto c.stages.activation atTop (𝓝 T) ∧ ∀ j : ℕ, T < c.stages.slab j
  oscillation_support : ∀ j : ℕ, 1 ≤ j → ∀ t ∈ Icc 0 (c.stages.slab j), ∀ x : Vec3,
    c.stages.oscillation j t x ≠ 0 →
      ∃ n : Fin 3 → ℤ, dist (latticeVector n) x ≤ (P.frequency (j - 1))⁻¹
  increment : ∀ j : ℕ, 1 ≤ j → ∀ t ∈ Icc 0 (c.stages.slab j),
    (∀ x, ‖c.stages.oscillation j t x‖ ≤ (P.frequency j)⁻¹) ∧
      ∀ m : ℕ, m ≤ P.order j →
        SpatialHolderHalf m
            (c.stages.velocity j t - c.stages.velocity (j - 1) t - c.stages.oscillation j t) ∧
          spatialHolderHalfNorm m
            (c.stages.velocity j t - c.stages.velocity (j - 1) t - c.stages.oscillation j t) ≤
            (P.frequency j)⁻¹
  oscillation_vanishes : ∀ j : ℕ, 2 ≤ j → ∀ t ∈ Icc 0 (c.stages.activation j),
    c.stages.oscillation j t = 0
  /-- The comparison hypotheses (2.7) of the central wave `j + 2` on its window, checked in
  item 2 of the proof of Theorem 7.1 (sections/08b_induction.tex:312-326), for every constant
  `C₀` and all large `j`. The proof of Proposition 8.2 reads them to apply Lemma 2.4 to wave
  `j + 2`. -/
  comparison : ∀ C₀ : ℕ, ∀ᶠ j in atTop,
    FiniteSmallness (c.centralWaves.physical j) (c.centralWaves.window j) C₀
  /-- The normalized length of the window of the central wave `j + 2` is at most a constant
  times `L_{j+3}^4` (item 2 of the proof of Theorem 7.1, sections/08b_induction.tex:306-310;
  read by the proof of Proposition 8.2, sections/09b_terminal_properties.tex:28). -/
  window_upper : ∃ K : ℝ, ∀ j : ℕ,
    c.centralWaves.window j ≤ K * Schedule.L P.frequency (j + 3) ^ 4

/-- The conclusions of Proposition 8.1 (`cc:uf:terminal:agreement`) for the sequence `U_j` of a
construction `c` with `T = T_∞`, a velocity `u` and a pressure `p`.

* `initial_convergence`, `initial_odd`, `initial_divergence_free`, `initial_smooth`: the data
  `U_j(0)` converge in every `C^{m,1/2}` to the odd divergence-free field `u_0 = u(0)`, and
  `u_0 ∈ C^∞`.
* `euler`, `odd`: `u` is a smooth Euler solution (with mean-zero pressure `p`) on
  `[0,T_∞) × 𝕋³`, odd at every time.
* `maximal_agreement`: every maximal smooth solution from `u_0` (maximal time `T_*`) has
  `T_* ≥ T_∞` and coincides with `u` on `[0,T_∞)`.
* `convergence`: for every `T < T_∞` and `m ≥ 0`, `U_j → u` in `C([0,T];C^{m,1/2})`.

Representation: the maximal solution `u` "supplied by Section 1" is represented by its
restriction to `[0,T_∞)`, whose existence is part of the conclusion (local well-posedness is not
assumed); `maximal_agreement` says that every maximal solution from `u_0` extends it, which is
`T_* ≥ T_∞` together with the identification of the two fields. The norms are finite because
`U_j(t)` and `u(t)` are smooth and periodic. -/
structure Proposition81Conclusions {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (T : ℝ) (u : Velocity) (p : Pressure) : Prop where
  initial_convergence : ∀ m : ℕ,
    Tendsto (fun j => spatialHolderHalfNorm m (c.stages.velocity j 0 - u 0)) atTop (𝓝 0)
  initial_odd : Function.Odd (u 0)
  initial_divergence_free : ∀ x, divergence (u 0) x = 0
  initial_smooth : ContDiff ℝ ∞ (u 0)
  euler : IsEulerSolution T u p
  maximal_agreement : ∀ (T₁ : ℝ) (v : Velocity) (q : Pressure),
    IsMaximalEulerSolution T₁ v q → v 0 = u 0 → T ≤ T₁ ∧ EqOn v u (Ico 0 T)
  convergence : ∀ S < T, ∀ m : ℕ,
    TendstoUniformlyOn (fun j t => spatialHolderHalfNorm m (c.stages.velocity j t - u t))
      (fun _ => 0) atTop (Icc 0 S)
  odd : ∀ t ∈ Ico 0 T, Function.Odd (u t)

/-- The conclusions of Proposition 8.2 (`cc:uf:terminal:velocity-curl`) for the solution `u` on
`[0,T)`, `T = T_∞`, of a construction `c`.

* `bounded_velocity`: `sup_{0 ≤ t < T_∞} ‖u(t)‖_{L^∞} < ∞`.
* `central_curl`: `|curl u(t,0)| → ∞` as `t ↑ T_∞`.
* `curl_lower` (exported from the proof, ledger `exports`): the curl lower bound (8.2) passed to
  the limit: there are `c₁ > 0` and `C₁` such that for all large `j` and `t ∈ [t_j,t_{j+1})`,
  `|curl u(t,0)| ≥ c₁ λ_{j-1}^{1/8} - C₁ λ_{j-1}^{1/32} - C₁`. The middle term bounds the older
  gradient `C λ_{j-2}^9 ≤ C λ_{j-1}^{1/32}` as in the proof; Corollary 8.3 uses this bound in
  place of the Beale–Kato–Majda criterion. -/
structure Proposition82Conclusions {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (T : ℝ) (u : Velocity) : Prop where
  bounded_velocity : ∃ M : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal M
  central_curl : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop
  curl_lower : ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ ∀ᶠ j : ℕ in atTop,
    ∀ t ∈ Ico (c.stages.activation j) (c.stages.activation (j + 1)),
      c₁ * P.frequency (j - 1) ^ (1 / 8 : ℝ) - C₁ * P.frequency (j - 1) ^ (1 / 32 : ℝ) - C₁ ≤
        ‖curl (u t) 0‖

/-- The conclusions of Corollary 8.3 (`cc:uf:terminal:time`) for the solution `u`, `p` on
`[0,T)`, `T = T_∞`: the maximal existence time is `T_* = T_∞ ∈ (0,∞)` (`u` admits no smooth
continuation, and every maximal solution from `u(0)` has maximal time `T_∞`), and both
integrals in (1.2) diverge.

Representation: the integrals are lower Lebesgue integrals over `[0,T_∞)` of `torusLInf`
(essential supremum over the unit cell); the pointwise norm of `∇u(t)` is the operator norm
of `fderiv ℝ (u t)` (all matrix norms are equivalent, so the divergence does not depend on
this choice). -/
structure Corollary83Conclusions (T : ℝ) (u : Velocity) (p : Pressure) : Prop where
  maximal : IsMaximalEulerSolution T u p
  maximal_time : ∀ (T₁ : ℝ) (v : Velocity) (q : Pressure),
    IsMaximalEulerSolution T₁ v q → v 0 = u 0 → T₁ = T
  time_pos : 0 < T
  gradient_integral : (∫⁻ t in Ico 0 T, torusLInf (fderiv ℝ (u t))) = ⊤
  curl_integral : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤

/-- The conclusions of Proposition 8.4 (`cc:uf:terminal:off-origin`) for the solution `u` on
`[0,T)`, `T = T_∞`: for every compact `K ⊂ 𝕋³ ∖ {0}` and every `m ≥ 0`, both `u(t)` and
`∂_t u(t)` converge in `C^m(K)` as `t ↑ T_∞`. Representation: `HasOffOriginLimits` on the lift
(compact `K` avoiding the lattice; the limit is `C^m` on an open neighborhood of `K`). -/
structure Proposition84Conclusions (T : ℝ) (u : Velocity) : Prop where
  velocity : HasOffOriginLimits T u
  time_derivative : HasOffOriginLimits T (timeDerivative T u)

end

end TorusEuler.Paper

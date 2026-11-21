import TorusEuler.Paper.Auxiliary.Statements
import TorusEuler.Paper.Proofs.Auxiliary.Library.OffOrigin

/-! # Proof of Theorem 1.1 of the auxiliary note

Conditional proof `Paper.Aux.Proof.theorem_1_1_of` of `Paper.Aux.Statement.theorem_1_1`
(auxiliary/terminal_smoothness.tex:46-54), following its proof (terminal_smoothness.tex:466-484)
and the setup (:56-79). The glue of this file chooses `𝓑` (the threshold satisfying both
conditions of the note, :56-62), assembles the conclusions of Theorem M.1.1 from Section 8 and
proves the extension (own content of the row).
-/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler.Paper

namespace Lib.Aux

/-- **Glue** (terminal_smoothness.tex:56-62). For any majorants `F`, `G` there is a threshold
`𝓑` admitted by Subsection M.1.5 (`AdmissibleThreshold b F 𝓑`) that also bounds the constants of
the time-derivative estimates (`Aux.TimeDerivativeThreshold b G 𝓑`): `𝓑(s) = exp(4K(s+1)^3) +
∑_{t ≤ s} (|F t| + |G(7K t)|)`. -/
theorem exists_threshold (b : ℕ) (F G : ℕ → ℝ) :
    ∃ B : ℕ → ℝ, AdmissibleThreshold b F B ∧ Paper.Aux.TimeDerivativeThreshold b G B := by
  let e : ℕ → ℝ := fun s => Real.exp (4 * (frequencyExponent b (s + 1) : ℝ) ^ 3)
  let w : ℕ → ℝ := fun t => |F t| + |G (7 * frequencyExponent b t)|
  let B : ℕ → ℝ := fun s => e s + ∑ t ∈ Finset.range (s + 1), w t
  have hw (t : ℕ) : 0 ≤ w t := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum (s : ℕ) : 0 ≤ ∑ t ∈ Finset.range (s + 1), w t := Finset.sum_nonneg fun t _ => hw t
  have hterm (s : ℕ) : w s ≤ ∑ t ∈ Finset.range (s + 1), w t :=
    Finset.single_le_sum (f := w) (fun t _ => hw t) (Finset.self_mem_range_succ s)
  have hK {s t : ℕ} (h : s ≤ t) : frequencyExponent b (s + 1) ≤ frequencyExponent b (t + 1) := by
    unfold frequencyExponent; exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨B, ⟨fun s t _ hst => ?_, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_⟩, fun s _ => ?_⟩
  · refine add_le_add ?_ ?_
    · refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hK hst) 3
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : s + 1 ≤ t + 1))
        (fun t _ _ => hw t)
  · calc F s ≤ |F s| := le_abs_self _
      _ ≤ w s := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ _ := hterm s
      _ ≤ B s := le_add_of_nonneg_left (Real.exp_pos _).le
  · exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (hsum s)
  · calc 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 = Real.log (e s) := (Real.log_exp _).symm
      _ ≤ Real.log (B s) :=
        Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_right (hsum s))
  · calc G (7 * frequencyExponent b s) ≤ |G (7 * frequencyExponent b s)| := le_abs_self _
      _ ≤ w s := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ _ := hterm s
      _ ≤ B s := le_add_of_nonneg_left (Real.exp_pos _).le

/-- **Glue.** A smooth periodic-lift extension through `T` away from the origin gives the
extension of the statement (`SmoothTerminalExtension`), with the neighbourhood `O = ℝ × offOrigin`. -/
theorem smoothTerminalExtension_of_hasSmoothOffOriginExtension {T : ℝ} {u : Velocity}
    (h : HasSmoothOffOriginExtension T u) : SmoothTerminalExtension T u := by
  obtain ⟨g, hg, hper, heq⟩ := h
  refine ⟨univ ×ˢ offOrigin, g, isOpen_univ.prod isOpen_offOrigin,
    prod_mono (subset_univ _) le_rfl, ?_, hper, heq⟩
  exact hg.mono (union_subset (prod_mono (subset_univ _) le_rfl) le_rfl)

/-- **Glue** (terminal_smoothness.tex:52, "All other conclusions of that theorem remain
unchanged"): the conclusions of Theorem M.1.1 and the uniqueness of the maximal solution from
the four Section 8 predicates. Proposition 8.1 supplies the solution, 8.2 the bounded velocity
and the central curl, 8.3 the maximality and the divergent integrals, 8.4 the off-origin limits. -/
theorem witness_of_section8 {P : InductiveEulerParameters} {c : InductiveEulerConstruction P}
    {T : ℝ} {u : Velocity} {p : Pressure}
    (h81 : Proposition81Conclusions c T u p) (h82 : Proposition82Conclusions c T u)
    (h83 : Corollary83Conclusions T u p) (h84 : Proposition84Conclusions T u) :
    EulerSingularityWitness (u 0) T u p ∧
      ∀ (T' : ℝ) (v : Velocity) (q : Pressure),
        IsMaximalEulerSolution T' v q → v 0 = u 0 → T' = T ∧ EqOn v u (Ico 0 T) := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, h83.time_pos⟩
  exact ⟨⟨h81.initial_smooth, h81.euler.periodic_velocity 0 h0, h81.initial_odd,
    h81.initial_divergence_free, h83.maximal, rfl, h81.odd, h83.gradient_integral,
    h83.curl_integral, h82.bounded_velocity, h82.central_curl, h84.velocity,
    h84.time_derivative⟩, fun T' v q hv hv0 => ⟨h83.maximal_time T' v q hv hv0,
    (h81.maximal_agreement T' v q hv hv0).2⟩⟩

/-- **Own content** (terminal_smoothness.tex:466-484, proof of Theorem 1.1). The mixed increment
bounds of Lemma 1.2 of the note (`hMixed`, for every `(m,q)` at all large steps) give the smooth
extension of the limit `u` through `T = T_∞` away from the origin. Steps: the increments are
summable with all mixed derivatives on `[0,T] × K` (`exists_offOrigin_limit`, using
the clause `oscillation_support` of the stage type of the construction `c` that `h7_1` supplies (the
same clause as `Theorem71Conclusions.oscillation_support`): "Only finitely many `O_j` meet a
neighborhood of `K`", and the smoothness `s.smooth` of the earlier terms, again from that stage
type: "the finitely many earlier terms are smooth because `S_j > T_∞`"); the sum equals `u`
before `T_∞` by Proposition 8.1 (`convergence`, :478); Seeley's extension theorem extends it
smoothly through `T_∞` (:480-483); it is periodized. -/
theorem smoothTerminalExtension_of_mixed {P : InductiveEulerParameters}
    {c : InductiveEulerConstruction P} {C T : ℝ} {u : Velocity} {p : Pressure}
    (h71 : Theorem71Conclusions c C T) (h81 : Proposition81Conclusions c T u p)
    (hMixed : ∀ m q : ℕ, ∀ᶠ j in atTop, Paper.Aux.MixedIncrementBound c m q j) :
    SmoothTerminalExtension T u := by
  obtain ⟨hTpos, -, hlife⟩ := h71.lifetime
  have hSlab : ∀ j, T ≤ c.stages.slab j := fun j => (hlife j).le
  have hSlabDec : ∀ j, c.stages.slab (j + 1) ≤ c.stages.slab j := fun j => (c.slab_succ_lt j).le
  have hInit : 2 ≤ c.stages.frequency 0 := by
    have hpos := P.threshold_pos 1 le_rfl
    have hfl := P.threshold_floor 1 le_rfl
    have hK : (1 : ℝ) ≤ (frequencyExponent P.exponentParameter (1 + 1) : ℝ) := by
      have hb := P.exponentParameter_ge
      have : 1 ≤ frequencyExponent P.exponentParameter (1 + 1) := by
        unfold frequencyExponent
        exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
      exact_mod_cast this
    have h3 : (1 : ℝ) ≤ (frequencyExponent P.exponentParameter (1 + 1) : ℝ) ^ 3 := one_le_pow₀ hK
    have h4 : 4 ≤ Real.log (P.threshold 1) := by linarith
    have h2 : 2 ≤ P.threshold 1 := by
      by_contra h
      have := Real.log_lt_log hpos (not_le.mp h)
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
    exact h2.trans P.initial_threshold
  have hBounds : c.stages.HasTerminalMixedIncrementBounds := by
    intro q m
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (hMixed m q)] with n hn t ht
    obtain ⟨h1, -⟩ := hn
    exact h1 t ht
  obtain ⟨w, hw, hwlim⟩ :=
    exists_offOrigin_limit c.stages hTpos hSlab hSlabDec hInit hBounds
  -- the limit equals `u` before `T` (Proposition 8.1)
  have hEq : ∀ t ∈ Ico 0 T, ∀ x, x ∈ offOrigin → w t x = u t x := by
    intro t ht x hx
    have htI : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    have hconv := (h81.convergence t ht.2 0).tendsto_at (show t ∈ Icc 0 t from ⟨ht.1, le_rfl⟩)
    have hu : Tendsto (fun j => c.stages.velocity j t x) atTop (𝓝 (u t x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hconv
      have hjt : t ∈ Icc 0 (c.stages.slab j) := ⟨ht.1, ht.2.le.trans (hSlab j)⟩
      have hsm : ContDiff ℝ ∞ (c.stages.velocity j t - u t) :=
        (contDiff_slice_on_closedSlab (h71.T1 j).1 hjt).sub
          (h81.euler.contDiff_velocity_slice ht)
      have hpe : SpatiallyPeriodic (c.stages.velocity j t - u t) := fun n y => by
        simp only [Pi.sub_apply]
        rw [((h71.T1 j).2 t hjt).1 n y, h81.euler.periodic_velocity t ht n y]
      have hs : SpatialHolderHalf 0 (c.stages.velocity j t - u t) :=
        spatialHolderHalf_of_contDiff_periodic hsm hpe 0
      have := norm_iteratedFDeriv_le_spatialHolderHalfNorm hs le_rfl x
      rw [norm_iteratedFDeriv_zero] at this
      simpa using this
    exact tendsto_nhds_unique (hwlim t htI x hx) hu
  obtain ⟨g, hg, hgEq⟩ := exists_smoothExtensionOfClosedTimeSlab hTpos isOpen_offOrigin hw
  have hgu : EqOn g (Function.uncurry u) (Ico 0 T ×ˢ offOrigin) := fun z hz =>
    (hgEq ⟨Ico_subset_Icc_self hz.1, hz.2⟩).trans (hEq z.1 hz.1 z.2 hz.2)
  obtain ⟨G, hG, hGEq, hPer⟩ := exists_spatiallyPeriodic_contDiffOn_extension isOpen_univ hg hgu
    h81.euler.periodic_velocity
  exact smoothTerminalExtension_of_hasSmoothOffOriginExtension ⟨Function.curry G, hG, hPer, hGEq⟩

end Lib.Aux

namespace Aux

/-- **Proof of Theorem 1.1 of the auxiliary note** (`aux:terminal:smooth`,
auxiliary/terminal_smoothness.tex:46), following the setup (:56-79) and the proof (:466-484).

* The fixed choices `ψ`, `a₀` and the exponents `b`, `a` and the majorant `F` come from
  `h7_1` (Theorem 7.1: the construction `c` and the sequence `U_j` of the main paper, for every
  admissible `𝓑` and large `N`); the floor `a ≥ a₀` of Lemma 1.2 is merged with that of 7.1.
* The choice of `𝓑` (:56-62) is `Lib.Aux.exists_threshold` (both conditions);
  `hAux_1_2` (Lemma 1.2: the majorant `G` and the mixed increment bounds (1.2)) gives
  `G` and, for the construction of `h7_1` with `P.threshold = 𝓑`, the bounds
  `MixedIncrementBound c m q j` for all large `j`.
* `h8_1` (Proposition 8.1) gives the limit `u`, `p` of the `U_j` and the identification with
  the maximal solution (:478, "equals `u` before `T_∞`"); `h8_2`, `h8_3`, `h8_4` give the other
  conclusions of Theorem M.1.1 (":52, all other conclusions remain unchanged"): bounded velocity
  and central curl (8.2), `T_* = T_∞` and the divergent integrals (8.3), the off-origin limits
  (8.4), through `Lib.Aux.witness_of_section8`.
* The extension is `Lib.Aux.smoothTerminalExtension_of_mixed` (Seeley, :480-483).

Conditional and unused since decision D28: it assumes the unproved `Aux.Statement.lemma_1_2`;
the auxiliary note has no spine rows. -/
theorem Proof.theorem_1_1_of (h7_1 : Statement.theorem_7_1) (h8_1 : Statement.proposition_8_1)
    (h8_2 : Statement.proposition_8_2) (h8_3 : Statement.corollary_8_3)
    (h8_4 : Statement.proposition_8_4) (hAux_1_2 : Aux.Statement.lemma_1_2) :
    Aux.Statement.theorem_1_1 := by
  intro ψ hψ a₀
  obtain ⟨a₁, h12⟩ := hAux_1_2 ψ hψ
  obtain ⟨b, a, F, hb, ha, h7⟩ := h7_1 ψ hψ (max a₀ a₁)
  obtain ⟨G, h12a⟩ := h12 a (le_of_max_le_right ha)
  refine ⟨b, a, F, G, hb, le_of_max_le_left ha, Lib.Aux.exists_threshold b F G,
    fun B hF hG => ?_⟩
  obtain ⟨N₁, hN⟩ := h7 B hF
  refine ⟨N₁, fun N hN₁ => ?_⟩
  obtain ⟨P, c, T, hPb, hPB, hPN, hPC, h71, hSteps⟩ := hN N hN₁
  obtain ⟨u, p, h81⟩ := h8_1 P c _ T h71
  have h82 := h8_2 P c _ T u p h71 h81
  have h83 := h8_3 P c _ T u p h71 h81 h82
  have h84 := h8_4 P c _ T u p h71 h81
  have hTD : TimeDerivativeThreshold P.exponentParameter G P.threshold := by
    rw [hPb, hPB]; exact hG
  have hMixed := h12a P c T hTD hPC h71 hSteps
  obtain ⟨hW, hU⟩ := Lib.Aux.witness_of_section8 h81 h82 h83 h84
  exact ⟨P, c, T, u, p, hPb, hPB, hPN, hPC, h71, hSteps, h81, hW, hU,
    Lib.Aux.smoothTerminalExtension_of_mixed h71 h81 hMixed⟩

end Aux

end TorusEuler.Paper

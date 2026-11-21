import TorusEuler.Paper.Proofs.S678a.Library.Base
import TorusEuler.Paper.Proofs.S678a.Library.StepBuild
import TorusEuler.Paper.Proofs.S678a.Library.LaterWaveTip
import TorusEuler.Paper.Proofs.S678a.Library.Budget
import TorusEuler.Paper.Proofs.S678a.Library.Conclusions
import TorusEuler.Paper.Proofs.S678a.Library.Bernstein
import TorusEuler.Paper.Proofs.S678a.Library.StageParent
import TorusEuler.Paper.Proofs.S678a.Library.StepInput

/-! # Theorem 7.1

Proof of `Statement.theorem_7_1` (sections/08b_induction.tex:142-179, with the proof :250-488; the remark and the figure :186-197 are not part of it)
from the statements it cites: Lemma 1.3 ((1.15) for the schedule (1.14), the lifetime (7.7)), Lemma 2.2, Lemma 2.5
(the reference solution of (2.12) and its turning time) and Lemmas 2.6, 2.7 and Proposition 2.8 (item 2, the later waves), Proposition 5.4, Lemmas 5.8-5.10 and
Proposition 5.11 (items 4-6, the expansion, the truncation and the pressure of each step), Lemma 6.1 (the
first wave, item 2) and Lemma B.1 (Bernstein bounds, the cutoff tails, the parent hypotheses).
The proof fixes the symbol `ψ`, the exponent `a` and the cost table `Γ, K, C, ...` of the
instances of 5.4-5.11, then `b` and the majorant `F`; for any admissible `B` and large `N` the
parameters are built (`exists_parameters_of_threshold`), the numerical budget of every step
follows from the threshold (`stepNumericalBudget_of_threshold_le`), the base and every step carry
the local data of Section 5 (`exists_base_of_section5`, `exists_step_of_section5`), and the
quantitative clauses come from the fields of the construction (`conclusions_of_construction`). -/

open Set Filter
open scoped Topology

namespace TorusEuler.Paper

open TorusEuler TorusEuler.InductiveEulerParameters Lib.S678a

noncomputable section

set_option maxHeartbeats 6400000 in
/-- **Theorem 7.1** (sections/08b_induction.tex:142), conditional on the results it cites. Where
each hypothesis enters: `h1_3` the schedule and lifetime (7.7) (`exists_parameters_of_threshold`,
`lemma13_schedule`) and (1.15) in the later-wave, switch and comparison steps (`LaterWaveTip`,
`TipThresholds`, `Conclusions`); `h2_2`, `h2_5` (the reference solution of (2.12) and its turning time), `h2_6`, `h2_7`, `h2_8` the later wave over the actual parent
(`LaterWaveTip`, `WaveSelection`) (`h2_2`, with `h1_3` and `hB_1`, also enters `conclusions_of_construction` for the comparison and
window clauses of the exported conclusions); `h5_4` the seed, expansion, vanishing and support of each
step (`StepBuild`, `Base`); `h5_8`-`h5_11` the bounds, flow and residual of the cutoff child (`h5_9`: (5.50) for (T4) at the center;
`h5_11`: the C^2 bound of (5.56) for the deformation of `V + v_Λ`, the e-clause of (5.56) for the residual
and (5.57) for the pressure increment of (T3)) (`StepChild`, `StepInput`, `StepObjects`) and the (T1) facts of the truncation (`CutoffChild`); `h6_1` the first wave and the two
conditions (5.5) (`Base`); `hB_1` the Bernstein jets, the cutoff tails, the parent hypotheses of
Subsection 5.1 and the older central gradient (`Bernstein`, `StepInput`, `StageParent`,
`TipThresholds`). -/
theorem Proof.theorem_7_1_of (h1_3 : Statement.lemma_1_3) (h2_2 : Statement.lemma_2_2)
    (h2_5 : Statement.lemma_2_5) (h2_6 : Statement.lemma_2_6) (h2_7 : Statement.lemma_2_7) (h2_8 : Statement.proposition_2_8)
    (h5_4 : Statement.proposition_5_4) (h5_8 : Statement.lemma_5_8) (h5_9 : Statement.lemma_5_9)
    (h5_10 : Statement.lemma_5_10) (h5_11 : Statement.proposition_5_11)
    (h6_1 : Statement.lemma_6_1) (hB_1 : Statement.lemma_B_1) : Statement.theorem_7_1 := by
  classical
  intro ψ hψ a₀
  obtain ⟨a4, h4⟩ := split54 h5_4
  obtain ⟨a8, h8⟩ := split58 h5_8
  obtain ⟨a9, h9⟩ := split59 h5_9
  obtain ⟨a10, h10⟩ := split510 h5_10
  obtain ⟨a11, h11⟩ := split511 h5_11 ψ hψ
  let a : ℕ := max (max (max a4 a8) (max a9 a10)) (max a11 (max a₀ 3))
  have ha4 : a4 ≤ a := by omega
  have ha8 : a8 ≤ a := by omega
  have ha9 : a9 ≤ a := by omega
  have ha10 : a10 ≤ a := by omega
  have ha11 : a11 ≤ a := by omega
  have ha₀ : a₀ ≤ a := by omega
  have ha3 : 3 ≤ a := by omega
  obtain ⟨b8, Γ8, K58, hB8⟩ := h8 a ha8
  obtain ⟨b9, Γ9, hB9⟩ := h9 a ha9
  obtain ⟨b10, Γ10, hB10⟩ := h10 a ha10
  obtain ⟨b11, Γ11, C11, K11, hB11⟩ := h11 a ha11
  let Cc : ℝ := max C11 0
  have hC11 : C11 ≤ Cc := le_max_left _ _
  have hCc : 0 ≤ Cc := le_max_right _ _
  let Γ : ℕ → ℝ := fun p => max (max 1 (max (Γ8 p) (Γ9 p))) (max (max (Γ10 p) (Γ11 p)) (K58 0 p))
  obtain ⟨Ct, hCt0, hCt⟩ := tails_of_lemma_B_1 hB_1 hψ
  have hTail : TailBounds ψ Ct := hCt
  obtain ⟨Cj, hCj0, hJets⟩ := exists_velocity_jets hB_1
  obtain ⟨Npar, hNpar4, hParentAll⟩ := stage_parent hB_1
  let cost : StepCosts Unit :=
    { analytic := fun _ _ p => 3 * ((p : ℝ) + 1) * Cj p
      cutoffTail := fun p => max (Ct p) |K11 p|
      step := Γ
      mean := fun m p => |K58 m p| }
  have hΓ1 : ∀ q, 1 ≤ cost.step q := fun q => (le_max_left _ _).trans' (le_max_left _ _)
  let b : ℕ := max (max (max b8 b9) (max b10 b11)) (max (stepExponentFloor a 0 0 0) 1)
  refine ⟨b, a, fixedOrderThreshold b cost.table, le_max_right _ _ |>.trans' (le_max_right _ _),
    ha₀, ?_⟩
  intro B hB
  have hC : (2 : ℝ) ≤ 18 * Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  obtain ⟨C₀, Nw, hC₀, hNw, hWave⟩ :=
    exists_inductiveEulerTip_laterWaveV_threshold hB_1 h1_3 h2_2 h2_5 h2_6 h2_7 h2_8 _ hC
  obtain ⟨Ns, hNs, hSw⟩ :=
    exists_inductiveEulerTip_scheduled_switch_bound_of_lemma13 h1_3 (18 * Real.exp 3) hC
  let Nfloor : ℝ := max (max (max (Real.exp 4) ((64 * Real.pi) ^ (16 : ℕ))) (max (Real.exp 1) Nw))
    (max (max Npar Ns) (max (max 2 ((2 * Cc) ^ (2 : ℕ))) ((4 : ℝ) ^ (16 : ℕ))))
  have hb1 : 1 ≤ b := le_max_right _ _ |>.trans' (le_max_right _ _)
  obtain ⟨N₁, hN₁⟩ := exists_parameters_of_threshold h1_3 b C₀ (18 * Real.exp 3) Nfloor B hb1 hC₀ hC
    hB.pos hB.floor
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨P, hPb, hPC₀, hPstr, hPth, hPfreq, hPfloor, hLife⟩ := hN₁ N hN
  refine ⟨P, ?_⟩
  -- the floors
  obtain ⟨hA1, hA2⟩ := max_le_iff.mp hPfloor
  obtain ⟨hA11, hA12⟩ := max_le_iff.mp hA1
  obtain ⟨hF1, hF2⟩ := max_le_iff.mp hA11
  obtain ⟨hF3, hF4⟩ := max_le_iff.mp hA12
  obtain ⟨hA21, hA22⟩ := max_le_iff.mp hA2
  obtain ⟨hF5, hF6⟩ := max_le_iff.mp hA21
  obtain ⟨hA221, hF9⟩ := max_le_iff.mp hA22
  obtain ⟨hF7, hF8⟩ := max_le_iff.mp hA221
  have hexp4 : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hZero : max 2 ((2 * Cc) ^ (2 : ℕ)) ≤ P.frequency 0 := max_le hF7 hF8
  have hb8 : b8 ≤ P.exponentParameter := by rw [hPb]; omega
  have hb9 : b9 ≤ P.exponentParameter := by rw [hPb]; omega
  have hb10 : b10 ≤ P.exponentParameter := by rw [hPb]; omega
  have hb11 : b11 ≤ P.exponentParameter := by rw [hPb]; omega
  have hbfloor : stepExponentFloor a 0 0 0 ≤ P.exponentParameter := by rw [hPb]; omega
  have hΓ1' : ∀ q, 1 ≤ cost.step q := fun q => le_max_of_le_left (le_max_left _ _)
  have h54' : Body54 a := h4 a ha4
  have h58' : Body58 a P.exponentParameter Γ K58 :=
    hB8 P.exponentParameter hb8 Γ (fun p => le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))
  have h59' : Body59 a P.exponentParameter Γ :=
    hB9 P.exponentParameter hb9 Γ (fun p => le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))
  have h510' : Body510 a P.exponentParameter Γ :=
    hB10 P.exponentParameter hb10 Γ (fun p => le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
  have h511' : Body511 ψ a P.exponentParameter Γ C11 K11 :=
    hB11 P.exponentParameter hb11 Γ (fun p => le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))
  have hTh : ∀ s, 1 ≤ s → fixedOrderThreshold P.exponentParameter cost.table s ≤ P.threshold s := by
    rw [hPb, hPth]
    exact fun s hs => hB.bounds_constants s hs
  have num : ∀ i, P.StepNumericalBudget i a 0 0 0 Cc cost := fun i =>
    stepNumericalBudget_of_threshold_le P cost Cc hTh hbfloor hZero hΓ1' i
  have nums : ∀ i, StepNumbers P i Γ K58 Cc K11 Ct (Cj (P.stepDepth i))
      (Γ (P.stepDepth i) * ((P.frequency i ^ 9) ^ P.exponentParameter)) (P.frequency i) :=
    fun i => stepNumbers_of_budget (num i) (fun _ => rfl) hΓ1' (fun _ _ => le_abs_self _)
      (fun q => le_max_of_le_right (le_max_right _ _)) (fun q => le_max_left _ _)
      (fun q => (le_abs_self _).trans (le_max_right _ _)) hCt0 (fun q => le_rfl) hCj0 hCc
  have hParent : ∀ {m : ℕ} {act T : ℝ} (s : InductiveEulerStage P m act), 0 < T →
      T ≤ P.slab m act → T ≤ 1 →
      S5.Parent T s.velocity s.flow s.pressure (P.frequency m ^ 9) (P.frequency (m + 1)) :=
    fun s h1 h2 h3 => hParentAll P hF5 s h1 h2 h3
  have hConst : 18 * Real.exp 3 ≤ P.strengthConstant := le_of_eq hPstr.symm
  -- every step
  have hStep : ∀ (n : ℕ) (tip : InductiveEulerTip P n), InductiveEulerPrefix P hLife n tip →
      ∃ step : InductiveEulerStep tip, LocalStep tip.parent step.child step.wave a ψ ∧
        step.wave.cutoff = waveSwitch tip.nextActivation step.physical.rate := by
    intro n tip pre
    obtain ⟨w, ⟨d⟩⟩ := hWave tip hLife hF4 hPstr hPC₀
    have hSwitch : ∀ t, |deriv (waveSwitch tip.nextActivation w.physical.rate) t| *
        |S5.weight (P.frequency (n + 1 + 1)) d.crossing.amplitude t| ≤
          P.frequency (n + 1) * P.frequency (n + 1 + 2) ^ (-4 : ℝ) :=
      hSw tip hF6 hPstr w d
    have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
      P.exponentParameter_ge (by linarith : (1 : ℝ) ≤ P.frequency 0) P.frequency_step
    have hf1 : 1 ≤ P.frequency (n + 1) :=
      (by linarith : (1 : ℝ) ≤ P.frequency 0).trans (hMono (Nat.zero_le _))
    exact exists_step_of_section5 pre w d h54' h58' h59' h510' h511' hTail hParent ha3 hF1
      hConst hC11 (nums (n + 1))
      (fun t ht => hJets tip.parent hf1 _ t ⟨ht.1, ht.2.trans (tip.next_slab_lt hLife).le⟩) hSwitch
  -- the base
  obtain ⟨bse, hbl, hbv, hbc⟩ := exists_base_of_section5 hLife h6_1 h54' h58' h59' h510' h511'
    hTail hParent (fun s hf N t ht => hJets s hf N t ht) ha3 hF2 hF3 hC11 (nums 0)
  obtain ⟨c, hcb, hsteps, hcut⟩ := exists_construction_of_local hLife a ψ bse hbl hStep
  have hvel : c.base.stationary.velocity =
      fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3))) := by
    rw [hcb]; exact hbv
  have hfirst : ∀ t : ℝ, c.centralWaves.cutoff 1 t = 1 := by
    intro t
    have : c.centralWaves.cutoff 1 = c.base.wave.cutoff := rfl
    rw [this, hcb, hbc]
  obtain ⟨T, hTc⟩ := conclusions_of_construction h1_3 h2_2 hB_1 c hF9 hvel hfirst hcut
  have hstr : c.centralWaves.strengthConstant = 18 * Real.exp 3 := hPstr
  rw [hstr] at hTc
  exact ⟨c, T, hPb, hPth, hPfreq, hPstr, hTc, hsteps⟩

end

end TorusEuler.Paper

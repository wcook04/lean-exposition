import TorusEuler.TerminalAuxiliaryAssembly
import TorusEuler.TerminalTimeCutoffBounds
import TorusEuler.TerminalTimeVelocityCutoff

/-! Close the auxiliary time induction with the cutoff of the selected approximation. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

open InductiveEulerParameters

namespace ScheduledEulerConstruction

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P)

/-- The uncut velocity and residual estimates through a common time order. -/
def ApproximationTimeBounds (q e n : ℕ) : Prop :=
  let b := (c.selectedStep n).selected.approximation
  let T := c.construction.stages.slab (n + 2)
  ∀ i ≤ q, ∀ t ∈ Icc 0 T,
    (∀ m ≤ (P.stepDepth (n + 1)), spatialHolderHalfNorm m (slabTimeJet 0 T i b.velocity t) ≤
      (P.frequency (n + 2)) ^ (2 * ((m : ℝ) + 1) + (e : ℝ))) ∧
    spatialHolderHalfNorm 1 (slabTimeJet 0 T i b.residual t) ≤
      (P.frequency (n + 2)) ^ (e : ℝ) * (P.frequency (n + 3)) ^ (-4 : ℝ)

/-- The mean portion of the uncut correction contributes half the allowed
mixed increment at the requested time and spatial orders. -/
def MeanTimeBound (q m n : ℕ) : Prop :=
  let b := (c.selectedStep n).selected.approximation
  let T := c.construction.stages.slab (n + 2)
  ∀ t ∈ Icc 0 T,
    let jet := slabTimeJet 0 T q b.meanCorrection t
    SpatialHolderHalf m jet ∧ spatialHolderHalfNorm m jet ≤ (1 / 2 : ℝ) * (P.frequency (n + 2))⁻¹

/-- Time estimates for the graph before truncation, on the chosen later
steps of the same physical sequence. -/
structure TerminalGraphStep : Prop where
  approximate : ∀ q A : ℕ, ∃ e : ℕ, ∀ᶠ n in atTop,
    c.construction.stages.StageTimeBounds q A (n + 1) → c.ApproximationTimeBounds (q + 1) e n
  mean : ∀ q m A : ℕ, ∀ᶠ n in atTop,
    c.construction.stages.StageTimeBounds q A (n + 1) → c.MeanTimeBound (q + 1) m n

private theorem eventual_childFrequency_ge (P : InductiveEulerParameters) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ (P.frequency (n + 2)) :=
  (P.terminal_frequency_tendsto_atTop.comp (tendsto_add_atTop_nat 2)).eventually_ge_atTop C

private theorem eventual_nextExponent_ge (P : InductiveEulerParameters) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, C ≤ (frequencyExponent P.exponentParameter (P.order (n + 3))) :=
  (P.terminal_frequencyExponent_tendsto_atTop.comp (tendsto_add_atTop_nat 2)).eventually_ge_atTop C

set_option maxHeartbeats 2000000 in
/-- The fixed cutoff costs can be chosen before the schedule. The cutoff
estimates then apply to the same fields as the selected graph bounds. -/
theorem exists_terminalCutoffCosts :
    ∃ cutoffCost : Bool → ℕ → ℕ → ℕ → ℝ,
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (reserve : ℕ → ℕ → ℕ),
      TerminalCostBounds P cutoffCost reserve → c.TerminalGraphStep →
      c.construction.stages.TerminalTimeStep := by
  obtain ⟨Cr, Ct, hCr, _, hCutoff⟩ := exists_terminalTimeCutoffResidualBudget
  let cutoffCost : Bool → ℕ → ℕ → ℕ → ℝ := fun isStress q _ depth =>
    if isStress then Ct q depth else terminalCutoffTailCost depth
  refine ⟨cutoffCost, ?_⟩
  intro P c reserve hCosts hGraph
  have hCost (n j : ℕ) (row : Bool) (hj : j ≤ 7 * (frequencyExponent P.exponentParameter (P.order (n + 3)))) :
      cutoffCost row j 0 (P.stepDepth (n + 1)) ≤ (P.frequency (n + 2)) := by
    have hd : (P.stepDepth (n + 1)) ≤ 7 * (frequencyExponent P.exponentParameter (P.order (n + 3))) := by
      change 6 * frequencyExponent P.exponentParameter (P.order (n + 3)) ≤ _
      omega
    exact (le_abs_self _).trans ((hCosts (n + 1) row j 0 (P.stepDepth (n + 1)) hj (Nat.zero_le _) hd).trans
      (P.terminal_frequency_mono (by omega)))
  apply c.terminalTimeStep_of_selectedCutoffs
  · intro q ψ
    obtain ⟨e, hApprox⟩ := hGraph.approximate q ψ
    refine ⟨e + 3, ?_⟩
    filter_upwards [hApprox,
      eventual_childFrequency_ge P (max 2 (max Cr (1 + terminalCutoffTailCost 0))),
      eventual_nextExponent_ge P (max (q + 1) (16 + 2 * e))] with n hApprox hF hK
    intro hParent
    let d := c.selectedStep n
    let b := d.selected.approximation
    let T := c.construction.stages.slab (n + 2)
    let freq := (P.frequency (n + 2))
    let depth := (P.stepDepth (n + 1))
    let K := (frequencyExponent P.exponentParameter (P.order (n + 3)))
    let prop := d.selected.properties
    have hT : 0 < T := d.selected.time_pos
    have hf : 2 ≤ freq := (le_max_left _ _).trans hF
    have hCrF : Cr ≤ freq := (le_max_left _ _).trans ((le_max_right _ _).trans hF)
    have hTailF : 1 + terminalCutoffTailCost 0 ≤ freq :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hF)
    have hqK : q + 1 ≤ K := (le_max_left _ _).trans hK
    have hLarge : 16 + 2 * e ≤ K := (le_max_right _ _).trans hK
    have hK' : (16 : ℝ) + 2 * (e : ℝ) ≤ (K : ℝ) := by exact_mod_cast hLarge
    have hCtF : Ct (q + 1) depth ≤ freq := by
      exact hCost n (q + 1) true (by change q + 1 ≤ 7 * K; omega)
    have hDepth : 2 ≤ depth := by
      change 2 ≤ 6 * K
      omega
    have hBounds := hApprox hParent
    obtain ⟨s, hsV, hsR⟩ := c.exists_selectedDyadicCutoff n
    dsimp only
    intro i hi t ht x
    rw [← hsV, ← hsR]
    have hVper (r : ℝ) (hr : r ∈ Icc 0 T) : SpatiallyPeriodic (b.velocity r) :=
      (prop.periodic r hr).1
    have hRper (r : ℝ) (hr : r ∈ Icc 0 T) : SpatiallyPeriodic (b.residual r) :=
      (prop.periodic r hr).2.2.1
    have hV := s.slabTimeJet_cutoffVelocity_rate (i := i) (exponent := (e : ℝ)) hT prop.velocity_smooth hVper ht hf hTailF
      (by simpa using (hBounds i hi t ht).1 0 (Nat.zero_le depth)) x
    have hVpow : freq ^ ((e : ℝ) + 3) = freq ^ (e + 3) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using (Real.rpow_natCast freq (e + 3))
    refine ⟨hV.trans_eq hVpow, ?_⟩
    have hR := hCutoff s hT (pow_pos (zero_lt_two.trans_le hf) (5 : ℕ))
      prop.velocity_smooth prop.residual_smooth hVper hRper (q + 1) i depth hi hDepth t ht
      (freq ^ (2 * ((depth : ℝ) + 1) + (e : ℝ)))
      (fun j hj => (hBounds j (hj.trans hi) t ht).1 depth le_rfl)
    simpa only [neg_div] using slabTimeJet_cutoffResidual_rate hf (Nat.cast_nonneg e)
      (P.frequency_step (n + 2)) hK' hCr hCrF hCtF (hBounds i hi t ht).2 hR x
  · intro q m ψ
    obtain ⟨e, hApprox⟩ := hGraph.approximate q ψ
    filter_upwards [hApprox, hGraph.mean q m ψ, eventual_childFrequency_ge P 2,
      eventual_nextExponent_ge P (m + e + 5)] with n hApprox hMean hf hK
    intro hParent t ht
    let d := c.selectedStep n
    let b := d.selected.approximation
    let T := c.construction.stages.slab (n + 2)
    let freq := (P.frequency (n + 2))
    let depth := (P.stepDepth (n + 1))
    let K := (frequencyExponent P.exponentParameter (P.order (n + 3)))
    let prop := d.selected.properties
    have hT : 0 < T := d.selected.time_pos
    have hK' : ((m : ℝ) + (e : ℝ) + 5) ≤ (K : ℝ) := by exact_mod_cast hK
    have hDepth : depth = 6 * K := rfl
    have hm : m ≤ depth := by omega
    have hDepthRate : 5 * (m : ℝ) + 5 + (e : ℝ) ≤ 3 * depth := by
      rw [hDepth, Nat.cast_mul, Nat.cast_ofNat]
      linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) e]
    have hTailF : terminalCutoffTailCost depth ≤ freq :=
      hCost n 0 false (Nat.zero_le _)
    have hBounds := hApprox hParent
    have hM := hMean hParent t ht
    obtain ⟨s, hsV, _⟩ := c.exists_selectedDyadicCutoff n
    have hSplit (r : ℝ) (_ : r ∈ Icc 0 T) :
        b.velocity r =
          (c.construction.tip n).parent.velocity r + b.oscillation r + b.meanCorrection r :=
      congrFun b.velocity_eq_parent_add_oscillation_add_mean r
    have hRate := s.slabTimeJet_increment_rate hT prop.velocity_smooth
      (fun r hr => (prop.periodic r hr).1) prop.mean_smooth hSplit hm ht hf hDepthRate hTailF
      ((hBounds (q + 1) le_rfl t ht).1 depth le_rfl) hM
    have hIncrement :
        (fun r x => s.velocity r x - (c.construction.tip n).parent.velocity r x - b.oscillation r x) =
          (fun r x => b.meanCorrection r x + (d.stage.cutoff.velocity r x - b.velocity r x)) := by
      rw [hsV]
      funext r x
      have hV := congrFun (congrFun b.velocity_eq_parent_add_oscillation_add_mean r) x
      change b.velocity r x =
        (c.construction.tip n).parent.velocity r x + b.oscillation r x + b.meanCorrection r x at hV
      rw [hV]
      abel
    rw [hIncrement] at hRate
    exact hRate

end ScheduledEulerConstruction

end TorusEuler

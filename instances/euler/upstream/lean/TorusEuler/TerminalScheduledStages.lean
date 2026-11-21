import TorusEuler.InductiveScheduledConstruction
import TorusEuler.TerminalStageTimeBounds

/-! The time estimates are attached to the cutoffs that generated the common sequence. -/

open Filter Set
open scoped Topology

namespace TorusEuler.ScheduledEulerConstruction

noncomputable section

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P)

local notation "tower" => c.construction.stages

theorem selectedStep_velocity_eq (n : ℕ) :
    (tower).velocity (n + 2) = (c.selectedStep n).stage.cutoff.velocity :=
  c.stage_velocity_eq n

theorem selectedStep_residual_eq (n : ℕ) :
    (tower).residual (n + 2) = (c.selectedStep n).stage.cutoff.residual :=
  c.stage_residual_eq n

/-- The correction whose mixed derivatives enter the limit is exactly the
uncut mean plus the cutoff tail from the same step. -/
theorem selectedStep_increment_eq (n : ℕ) :
    (fun t x => (tower).velocity (n + 2) t x - (tower).velocity (n + 1) t x -
      (tower).oscillation (n + 2) t x) =
      (fun t x => (c.selectedStep n).selected.approximation.meanCorrection t x +
        ((c.selectedStep n).stage.cutoff.velocity t x - (c.selectedStep n).selected.approximation.velocity t x)) := by
  rw [c.selectedStep_velocity_eq n, c.stage_oscillation_eq n]
  funext t x
  have h := congrFun (congrFun
    (c.selectedStep n).selected.approximation.velocity_eq_parent_add_oscillation_add_mean t) x
  change (c.selectedStep n).selected.approximation.velocity t x =
    (tower).velocity (n + 1) t x + (c.selectedStep n).selected.approximation.oscillation t x +
      (c.selectedStep n).selected.approximation.meanCorrection t x at h
  rw [h]
  abel

/-- The cutoff of a selected step has the exact symbol and scale used in
the mixed-time cutoff estimates. -/
theorem exists_selectedDyadicCutoff (n : ℕ) :
    let d := c.selectedStep n
    ∃ s : TruncatedChildStage ((tower).slab (n + 2)) (P.frequency (n + 2) ^ 5) dyadicMultiplierCutoff
      d.selected.approximation.velocity d.selected.approximation.residual,
      s.velocity = d.stage.cutoff.velocity ∧ s.residual = d.stage.cutoff.residual := by
  intro d
  let R := (P.frequency (n + 1) ^ frequencyExponent P.exponentParameter (P.order (n + 2))) ^ (5 : ℕ)
  have h (Λ : ℝ) (ψ : Vec3 → ℝ) (hΛ : R = Λ) (hψ : d.stage.symbol = ψ) :
      ∃ s : TruncatedChildStage ((tower).slab (n + 2)) Λ ψ
        d.selected.approximation.velocity d.selected.approximation.residual,
        s.velocity = d.stage.cutoff.velocity ∧ s.residual = d.stage.cutoff.residual := by
    subst Λ
    subst ψ
    exact ⟨d.stage.cutoff, rfl, rfl⟩
  exact h _ _ (congrArg (fun x : ℝ => x ^ (5 : ℕ)) (P.frequency_step (n + 1)).symm) d.cutoff_symbol

private theorem eventually_of_succ {p : ℕ → Prop} (h : ∀ᶠ n in atTop, p (n + 1)) :
    ∀ᶠ n in atTop, p n := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨n₀ + 1, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n => exact hn₀ n (by omega)

/-- A fixed-order auxiliary estimate for the later physical steps gives
the time-order induction on the sequence of actual cutoffs. -/
theorem terminalTimeStep_of_selectedCutoffs
    (time : ∀ q ψ, ∃ Ψ : ℕ, ∀ᶠ n in atTop, (tower).StageTimeBounds q ψ (n + 1) →
      let s := (c.selectedStep n).stage.cutoff
      ∀ i ≤ q + 1, ∀ t ∈ Icc 0 ((tower).slab (n + 2)), ∀ x,
        ‖slabTimeJet 0 ((tower).slab (n + 2)) i s.velocity t x‖ ≤ P.frequency (n + 2) ^ Ψ ∧
        ‖slabTimeJet 0 ((tower).slab (n + 2)) i s.residual t x‖ ≤
          P.frequency (n + 3) ^ (-(5 / 2) : ℝ))
    (increment : ∀ q m ψ, ∀ᶠ n in atTop, (tower).StageTimeBounds q ψ (n + 1) →
      ∀ t ∈ Icc 0 ((tower).slab (n + 2)),
        let d := c.selectedStep n
        let v := slabTimeJet 0 ((tower).slab (n + 2)) (q + 1)
          (fun r x => d.selected.approximation.meanCorrection r x +
            (d.stage.cutoff.velocity r x - d.selected.approximation.velocity r x)) t
        SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency (n + 2))⁻¹) :
    (tower).TerminalTimeStep := by
  constructor
  · intro q ψ
    obtain ⟨Ψ, h⟩ := time q ψ
    refine ⟨Ψ, eventually_of_succ (h.mono fun n hn hp => ?_)⟩
    intro i hi t ht x
    rw [c.selectedStep_velocity_eq n, c.selectedStep_residual_eq n]
    exact hn hp i hi t ht x
  · intro q m ψ
    refine eventually_of_succ ((increment q m ψ).mono fun n hn hp t ht => ?_)
    rw [c.selectedStep_increment_eq n]
    exact hn hp t ht

end

end TorusEuler.ScheduledEulerConstruction

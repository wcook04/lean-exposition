import TorusEuler.TerminalTimeJet
import TorusEuler.TerminalMixedLimits

/-! Time-order induction on one common sequence of physical stages. -/

open Filter Set
open scoped Topology

namespace TorusEuler.InductiveEulerStages

variable (s : InductiveEulerStages)

/-- The velocity and residual estimates at a stage, up to a common
time order, in the auxiliary note's fixed-spatial-point derivatives. -/
def StageTimeBounds (q ψ n : ℕ) : Prop :=
  ∀ i ≤ q, ∀ t ∈ Icc 0 (s.slab n), ∀ x,
    ‖slabTimeJet 0 (s.slab n) i (s.velocity n) t x‖ ≤ s.frequency n ^ ψ ∧
      ‖slabTimeJet 0 (s.slab n) i (s.residual n) t x‖ ≤ s.frequency (n + 1) ^ (-(5 / 2) : ℝ)

theorem stageTimeBounds_zero (hfreq : ∀ n, 1 ≤ s.frequency n) (n : ℕ) :
    s.StageTimeBounds 0 1 n := by
  intro i hi t ht x
  obtain rfl := Nat.eq_zero_of_le_zero hi
  simp only [pow_one]
  refine ⟨((s.torusVelocity n t).norm_coe_le_norm _).trans (s.velocity_bound n t ht), ?_⟩
  refine (s.residual_bound n t ht x).trans ?_
  have hf := hfreq (n + 1)
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (zero_le_one.trans hf)]
  exact Real.rpow_le_rpow_of_exponent_le hf (by norm_num)

/-- The exact mixed increment of the same physical stage. -/
def StageMixedIncrementBound (q m n : ℕ) : Prop :=
  ∀ t ∈ Icc 0 (s.slab (n + 1)),
    let v := slabTimeJet 0 (s.slab (n + 1)) q
      (fun r x => s.velocity (n + 1) r x - s.velocity n r x - s.oscillation (n + 1) r x) t
    SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (s.frequency (n + 1))⁻¹

theorem stageMixedIncrementBound_zero {m n : ℕ} (hm : m ≤ s.order (n + 1)) :
    s.StageMixedIncrementBound 0 m n := by
  intro t ht
  let v := s.velocity (n + 1) t - s.velocity n t - s.oscillation (n + 1) t
  have h : SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (s.frequency (n + 1))⁻¹ :=
    s.correction_bound n m hm t ht
  have hv : v = fun x => s.velocity (n + 1) t x - s.velocity n t x - s.oscillation (n + 1) t x := by
    funext x
    simp only [v, Pi.sub_apply]
  rw [hv] at h
  exact h

/-- A local time step may use all velocity and residual jets through
the preceding time order at the parent. -/
structure TerminalTimeStep : Prop where
  time : ∀ q ψ, ∃ Ψ : ℕ, ∀ᶠ n in atTop,
    s.StageTimeBounds q ψ n → s.StageTimeBounds (q + 1) Ψ (n + 1)
  increment : ∀ q m ψ, ∀ᶠ n in atTop,
    s.StageTimeBounds q ψ n → s.StageMixedIncrementBound (q + 1) m n

/-- Successive estimates on a fixed sequence give the two quantified
auxiliary lemmas, with a starting index for each requested pair of orders. -/
theorem terminalTimeBounds_of_step (hfreq : ∀ n, 1 ≤ s.frequency n)
    (horder : Tendsto s.order atTop atTop) (step : s.TerminalTimeStep) :
    (∀ q, ∃ ψ : ℕ, ∀ᶠ n in atTop, s.StageTimeBounds q ψ n) ∧
      s.HasTerminalMixedIncrementBounds := by
  have hTime (q : ℕ) : ∃ ψ : ℕ, ∀ᶠ n in atTop, s.StageTimeBounds q ψ n := by
    induction q with
    | zero =>
      exact ⟨1, Eventually.of_forall (s.stageTimeBounds_zero hfreq)⟩
    | succ q ih =>
      obtain ⟨ψ, hψ⟩ := ih
      obtain ⟨Ψ, hΨ⟩ := step.time q ψ
      have hnext : ∀ᶠ n in atTop, s.StageTimeBounds (q + 1) Ψ (n + 1) :=
        (hΨ.and hψ).mono fun _ h => h.1 h.2
      obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hnext
      refine ⟨Ψ, eventually_atTop.2 ⟨n₀ + 1, ?_⟩⟩
      intro n hn
      cases n with
      | zero => omega
      | succ j => exact hn₀ j (by omega)
  refine ⟨hTime, ?_⟩
  intro q m
  change ∀ᶠ n in atTop, s.StageMixedIncrementBound q m n
  cases q with
  | zero =>
    have h : ∀ᶠ n in atTop, m ≤ s.order (n + 1) :=
      (horder.comp (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop m)
    exact h.mono fun _ hn => s.stageMixedIncrementBound_zero hn
  | succ q =>
    obtain ⟨ψ, hψ⟩ := hTime q
    exact ((step.increment q m ψ).and hψ).mono fun _ h => h.1 h.2

end TorusEuler.InductiveEulerStages

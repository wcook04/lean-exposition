module

public import QuarticQuery.Amplification.Geometry
public import QuarticQuery.Amplification.Average

/-!
# The amplification procedure as explicit data

A `Proc` is a finite tree of classical mixtures, restarts, circuits and success
measurements. It is a value of a plain inductive type: no Hilbert space, no `A`,
and no `p` appears in it. `amplify γ η` is computed from `γ` and `η` alone, and
`Proc.expect` runs any tree on any `Preparation`. This is the corrected order of
quantifiers of Lemma 3.1: one procedure, black-box in `A`, for all `A`.

`Proc.expect A h P φ` is the expectation over all branches of the payoff `h`,
read at the normalised output state, with `none` marking failure. Branch states
stay unnormalised and carry their probability as a squared norm. Quantifying over
`h` determines the whole law of the output states, so this is a state-level
semantics, stronger than a classical distribution on measured outcomes.

The law of `attempts M n` is computed as an explicit finite sum in
`expect_attempts_eq_sum`.
-/

@[expose] public section

namespace QuarticQuery.Amplification

open Finset

/-- Ledger: def-grover-trial. Finite classical control over circuits and success
measurements. `restart` discards every register and returns to `|0⟩`. -/
inductive Proc where
  | fail
  | success
  | restart (next : Proc)
  | run (c : Circuit) (next : Proc)
  | measure (yes no : Proc)
  | mix (n : ℕ) (weight : Fin n → ℝ) (branch : Fin n → Proc)

/-- Ledger: lem-3.1. The call cap is syntactic: it bounds every branch. -/
def Proc.callCap : Proc → ℕ
  | .fail => 0
  | .success => 0
  | .restart next => next.callCap
  | .run c next => c.calls + next.callCap
  | .measure yes no => max yes.callCap no.callCap
  | .mix _ _ branch => Finset.univ.sup fun j => (branch j).callCap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Ledger: lem-3.1. Expected payoff over branches. Mass enters as the squared norm
of the branch state; `restart` keeps the branch mass and resets the vector. -/
noncomputable def Proc.expect (A : Preparation H) (h : Option H → ℝ) : Proc → H → ℝ
  | .fail, φ => ‖φ‖ ^ 2 * h none
  | .success, φ => ‖φ‖ ^ 2 * h (some (normalised φ))
  | .restart next, φ => next.expect A h (((‖φ‖ : ℝ) : ℂ) • A.zero)
  | .run c next, φ => next.expect A h (Circuit.run A c φ)
  | .measure yes no, φ =>
      yes.expect A h (A.good φ) + no.expect A h (φ - A.good φ)
  | .mix _ weight branch, φ => ∑ j, weight j * (branch j).expect A h φ

/-- Ledger: def-grover-trial. The law of `ℓ`: probability `1/2` on `ℓ = 0`, and
probability `1/2` uniform on `ℓ < M`. -/
noncomputable def trialWeight (M ℓ : ℕ) : ℝ :=
  (if ℓ = 0 then 1 / 2 else 0) + 1 / (2 * M)

/-- Ledger: def-grover-trial. Up to `n` independent trials, stopping at the first
success. -/
noncomputable def attempts (M : ℕ) : ℕ → Proc
  | 0 => .fail
  | n + 1 => .mix M (fun ℓ => trialWeight M ℓ) fun ℓ =>
      .restart (.run (groverCircuit ℓ) (.measure .success (attempts M n)))

/-- Ledger: def-grover-trial. `M = ⌈10/√γ⌉`. -/
noncomputable def iterationBound (γ : ℝ) : ℕ := ⌈10 / Real.sqrt γ⌉₊

/-- Ledger: def-grover-trial. `⌈log(1/η)/log(40/31)⌉` trials. -/
noncomputable def trialCount (η : ℝ) : ℕ := ⌈Real.log (1 / η) / Real.log (40 / 31)⌉₊

/-- Ledger: lem-3.1. The procedure. Its parameters depend on `γ` and `η` only. -/
noncomputable def amplify (γ η : ℝ) : Proc := attempts (iterationBound γ) (trialCount η)

/-! ## Calls -/

/-- Ledger: lem-3.1. A trial uses at most `2M + 1` calls, on every branch. -/
theorem callCap_attempts (M n : ℕ) : (attempts M n).callCap ≤ n * (2 * M + 1) := by
  induction n with
  | zero => simp [attempts, Proc.callCap]
  | succ n ih =>
    simp only [attempts, Proc.callCap]
    refine Finset.sup_le fun ℓ _ => ?_
    rw [calls_groverCircuit, max_eq_right (Nat.zero_le _)]
    have h1 : (n + 1) * (2 * M + 1) = n * (2 * M + 1) + (2 * M + 1) := by ring
    have := ℓ.isLt
    omega

/-! ## Gates are linear -/

theorem Gate.eval_smul (A : Preparation H) (g : Gate) (c : ℂ) (v : H) :
    g.eval A (c • v) = c • g.eval A v := by
  cases g with
  | prepare => simp [Gate.eval]
  | unprepare => simp [Gate.eval]
  | flipZero =>
    simp only [Gate.eval, Preparation.flipZero, inner_smul_right]
    module
  | flipGood =>
    simp only [Gate.eval, Preparation.flipGood, map_smul]
    module
  | negate => simp [Gate.eval]

theorem Circuit.run_smul (A : Preparation H) (c : Circuit) (a : ℂ) (v : H) :
    Circuit.run A c (a • v) = a • Circuit.run A c v := by
  induction c generalizing v with
  | nil => rfl
  | cons g c ih =>
    simp only [Circuit.run, List.foldl_cons] at ih ⊢
    rw [Gate.eval_smul, ih]

theorem normalised_smul {r : ℝ} (hr : 0 < r) (v : H) :
    normalised ((r : ℂ) • v) = normalised v := by
  by_cases hv : v = 0
  · simp [hv, normalised]
  have hn : ‖(r : ℂ) • v‖ = r * ‖v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [normalised, normalised, hn, smul_smul]
  congr 1
  push_cast
  have h1 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2 : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv'
  field_simp

/-! ## One trial -/

namespace Preparation

variable (A : Preparation H)

/-- The success mass after `ℓ` iterations. -/
noncomputable def mass (ℓ : ℕ) : ℝ := Real.sin ((2 * ℓ + 1) * A.angle) ^ 2

theorem mass_eq (ℓ : ℕ) : A.mass ℓ = ‖A.good (A.iterate ℓ)‖ ^ 2 :=
  (A.norm_good_iterate_sq ℓ).symm

/-- Ledger: def-grover-trial. The failure probability of one trial. -/
noncomputable def trialFail (M : ℕ) : ℝ :=
  ∑ ℓ : Fin M, trialWeight M ℓ * (1 - A.mass ℓ)

/-- Ledger: def-grover-trial. The success-side payoff of one trial. -/
noncomputable def trialGain (M : ℕ) (h : Option H → ℝ) : ℝ :=
  ∑ ℓ : Fin M, trialWeight M ℓ * A.mass ℓ * h (some (normalised (A.good (A.iterate ℓ))))

/-- The payoff of up to `n` trials from a unit branch. -/
noncomputable def attemptValue (M : ℕ) (h : Option H → ℝ) : ℕ → ℝ
  | 0 => h none
  | n + 1 => A.trialGain M h + A.trialFail M * attemptValue M h n

end Preparation

/-- Ledger: def-grover-trial. Payoff of `attempts` from a branch of any mass. -/
theorem expect_attempts (A : Preparation H) (h : Option H → ℝ) (M n : ℕ) (φ : H) :
    (attempts M n).expect A h φ = ‖φ‖ ^ 2 * A.attemptValue M h n := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    obtain ⟨r, hr⟩ : ∃ r, r = ‖φ‖ := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := hr ▸ norm_nonneg φ
    have hterm : ∀ ℓ : Fin M,
        Proc.expect A h (.restart (.run (groverCircuit ℓ)
            (.measure .success (attempts M n)))) φ =
          r ^ 2 * (A.mass ℓ * h (some (normalised (A.good (A.iterate ℓ)))) +
            (1 - A.mass ℓ) * A.attemptValue M h n) := by
      intro ℓ
      have hrun : Circuit.run A (groverCircuit ℓ) ((r : ℂ) • A.zero) =
          (r : ℂ) • A.iterate ℓ := Circuit.run_smul A _ _ _
      simp only [Proc.expect, ← hr, hrun, map_smul, ← smul_sub, ih]
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        mul_pow, mul_pow, A.norm_bad_iterate_sq, ← A.mass_eq]
      rcases hr0.eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · rw [normalised_smul hpos]
        simp only [Preparation.mass]
        ring
    change ∑ ℓ : Fin M, trialWeight M ℓ * Proc.expect A h (.restart (.run (groverCircuit ℓ)
        (.measure .success (attempts M n)))) φ = _
    simp_rw [hterm]
    rw [Preparation.attemptValue, Preparation.trialGain, Preparation.trialFail, ← hr,
      Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    ring

/-- Ledger: def-grover-trial. The law of first success as a finite sum: success at
trial `t` after a choice of `ℓ` has mass `fᵗ w(ℓ) sin²((2ℓ+1)θ)`, and failure has
mass `fⁿ`. -/
theorem attemptValue_eq_sum (A : Preparation H) (h : Option H → ℝ) (M n : ℕ) :
    A.attemptValue M h n =
      (∑ t ∈ range n, A.trialFail M ^ t * A.trialGain M h) + A.trialFail M ^ n * h none := by
  induction n with
  | zero => simp [Preparation.attemptValue]
  | succ n ih =>
    rw [Preparation.attemptValue, ih, Finset.sum_range_succ', mul_add, Finset.mul_sum,
      pow_succ']
    simp only [pow_succ', pow_zero, one_mul, mul_assoc]
    ring

/-- Ledger: def-grover-trial. `attempts` from `|0⟩`: the explicit outcome law. -/
theorem expect_attempts_eq_sum (A : Preparation H) (h : Option H → ℝ) (M n : ℕ) :
    (attempts M n).expect A h A.zero =
      (∑ t ∈ range n, ∑ ℓ : Fin M,
        A.trialFail M ^ t * (trialWeight M ℓ * A.mass ℓ) *
          h (some (normalised (A.good (A.iterate ℓ))))) +
      A.trialFail M ^ n * h none := by
  rw [expect_attempts, A.norm_zero, one_pow, one_mul, attemptValue_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Preparation.trialGain, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  ring

/-! ## The success probability of one trial -/

theorem trialWeight_nonneg (M ℓ : ℕ) : 0 ≤ trialWeight M ℓ := by
  rw [trialWeight]; split_ifs <;> positivity

theorem sum_trialWeight {M : ℕ} (hM : M ≠ 0) : ∑ ℓ : Fin M, trialWeight M ℓ = 1 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  rw [← Finset.sum_range (fun ℓ => trialWeight M ℓ)]
  simp only [trialWeight]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (by simpa using Nat.pos_of_ne_zero hM),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  norm_num

namespace Preparation

variable (A : Preparation H)

theorem mass_nonneg (ℓ : ℕ) : 0 ≤ A.mass ℓ := sq_nonneg _

theorem mass_le_one (ℓ : ℕ) : A.mass ℓ ≤ 1 := Real.sin_sq_le_one _

theorem mass_zero : A.mass 0 = A.prob := by
  simp [mass, sin_angle_sq]

theorem trialFail_nonneg (M : ℕ) : 0 ≤ A.trialFail M :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (trialWeight_nonneg _ _) (sub_nonneg.mpr (A.mass_le_one _))

theorem trialFail_eq {M : ℕ} (hM : M ≠ 0) :
    A.trialFail M = 1 - ∑ ℓ : Fin M, trialWeight M ℓ * A.mass ℓ := by
  simp only [trialFail, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sum_trialWeight hM]

/-- Ledger: def-grover-trial. Success of one trial, as the two halves of the mixture. -/
theorem one_sub_trialFail {M : ℕ} (hM : M ≠ 0) :
    1 - A.trialFail M =
      A.prob / 2 + (1 / 2) * ((1 / (M : ℝ)) * ∑ ℓ ∈ range M, A.mass ℓ) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  rw [A.trialFail_eq hM, sub_sub_cancel, ← Finset.sum_range (fun ℓ => trialWeight M ℓ * A.mass ℓ)]
  have hterm : ∀ ℓ ∈ range M, trialWeight M ℓ * A.mass ℓ =
      (if ℓ = 0 then A.prob / 2 else 0) + 1 / (2 * (M : ℝ)) * A.mass ℓ := by
    intro ℓ _
    by_cases h0 : ℓ = 0
    · subst h0
      simp only [trialWeight, ite_true, add_mul, A.mass_zero]
      ring
    · simp only [trialWeight, ite_eq_right h0]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (by simpa using Nat.pos_of_ne_zero hM), ← Finset.mul_sum]
  field_simp

end Preparation

end QuarticQuery.Amplification

module

public import QuarticQuery.Amplification.Procedure

/-!
# Lemma 3.1: bounded amplification

`bounded_amplification` is the abstract lemma in its corrected form: `amplify γ η`
is fixed from `γ` and `η`, then the claims hold for every `Preparation` on every
inner product space. The output is the state `|g⟩` up to phase, stated on the law
of output states, so any measurement of the output is covered. Finite dimension
is never used.

`index_law_of_amplified` is the fact Proposition 3.2 consumes: from a uniform
superposition over indices, the index measured on success has law `w i / ∑ w`,
exactly, and exactly as before amplification.

Not yet done here: `amplify` is not an `AdaptiveProgram`. The embedding needs fresh
registers in place of `Proc.restart`, the classical mixture in `Proc.mix` as a
purified or decision-tree randomness (`AdaptiveProgram` has no coin), and `A`,
`A⁻¹` compiled to bit-oracle queries with their own query counts.
-/

@[expose] public section

namespace QuarticQuery.Amplification

open Finset

universe u

/-! ## Numerics -/

/-- Ledger: lem-3.1. `(31/40)^n ≤ η`. -/
theorem pow_trialCount_le {η : ℝ} (h0 : 0 < η) : (31 / 40 : ℝ) ^ trialCount η ≤ η := by
  have hl : 0 < Real.log (40 / 31) := Real.log_pos (by norm_num)
  have hn : Real.log (1 / η) / Real.log (40 / 31) ≤ trialCount η := Nat.le_ceil _
  rw [div_le_iff₀ hl] at hn
  have h1 : Real.log (31 / 40) = -Real.log (40 / 31) := by
    rw [← Real.log_inv]; norm_num
  have h2 : Real.log (1 / η) = -Real.log η := by
    rw [one_div, Real.log_inv]
  have h3 : Real.log ((31 / 40 : ℝ) ^ trialCount η) ≤ Real.log η := by
    rw [Real.log_pow, h1]
    rw [h2] at hn
    linarith
  exact (Real.log_le_log_iff (by positivity) h0).mp h3

theorem iterationBound_ne_zero {γ : ℝ} (hγ : 0 < γ) : iterationBound γ ≠ 0 := by
  have hr := Real.sqrt_pos.mpr hγ
  have : 0 < iterationBound γ := Nat.ceil_pos.mpr (by positivity)
  omega

theorem trialCount_pos {η : ℝ} (h0 : 0 < η) (h1 : η < 1 / 2) : 0 < trialCount η := by
  have hl : 0 < Real.log (40 / 31) := Real.log_pos (by norm_num)
  have hL : 0 < Real.log (1 / η) := Real.log_pos (by
    rw [lt_div_iff₀ h0]; linarith)
  exact Nat.ceil_pos.mpr (div_pos hL hl)

theorem quarter_le_log : (1 / 4 : ℝ) ≤ Real.log (40 / 31) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpos := Real.exp_pos (1 / 4 : ℝ)
  by_contra hlt
  have hlt' : (40 / 31 : ℝ) < Real.exp (1 / 4) := not_le.mp hlt
  have : (40 / 31 : ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 :=
    pow_lt_pow_left₀ hlt' (by norm_num) (by norm_num)
  rw [h4] at this
  norm_num at this he
  linarith

/-- Ledger: lem-3.1. `O(γ^{-1/2} log(1/η))` with an explicit constant. -/
theorem callCap_amplify_le {γ η : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2) (h0 : 0 < η)
    (h1 : η < 1 / 2) :
    ((amplify γ η).callCap : ℝ) ≤ 138 * (Real.sqrt γ)⁻¹ * Real.log (1 / η) := by
  have hr : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hr1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have ha : 1 ≤ (Real.sqrt γ)⁻¹ := (one_le_inv₀ hr).mpr hr1
  obtain ⟨a, haa⟩ : ∃ a, a = (Real.sqrt γ)⁻¹ := ⟨_, rfl⟩
  rw [← haa] at ha ⊢
  obtain ⟨L, hLL⟩ : ∃ L, L = Real.log (1 / η) := ⟨_, rfl⟩
  rw [← hLL]
  have hL2 : Real.log 2 ≤ L := by
    rw [hLL]
    exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h0]; linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hL : 1 / 2 ≤ L := hlog2.trans hL2
  have hq := quarter_le_log
  have hlpos : 0 < Real.log (40 / 31) := by linarith
  have hn : (trialCount η : ℝ) ≤ 6 * L := by
    have hle : (trialCount η : ℝ) < L / Real.log (40 / 31) + 1 := by
      rw [trialCount, ← hLL]
      exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hlpos.le)
    have hdiv : L / Real.log (40 / 31) ≤ 4 * L := by
      rw [div_le_iff₀ hlpos]
      nlinarith
    linarith
  have hM : (iterationBound γ : ℝ) ≤ 10 * a + 1 := by
    have hle : (iterationBound γ : ℝ) < 10 / Real.sqrt γ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    rw [div_eq_mul_inv, ← haa] at hle
    linarith
  have hcast : ((amplify γ η).callCap : ℝ) ≤
      (trialCount η : ℝ) * (2 * (iterationBound γ : ℝ) + 1) := by
    exact_mod_cast callCap_attempts (iterationBound γ) (trialCount η)
  have hfac : 2 * (iterationBound γ : ℝ) + 1 ≤ 23 * a := by linarith
  calc ((amplify γ η).callCap : ℝ)
      ≤ (trialCount η : ℝ) * (2 * (iterationBound γ : ℝ) + 1) := hcast
    _ ≤ (6 * L) * (23 * a) :=
        mul_le_mul hn hfac (by positivity) (by linarith)
    _ = 138 * a * L := by ring

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Failure -/

namespace Preparation

variable (A : Preparation H)

/-- Ledger: lem-3.1. A trial succeeds with probability at least `9/40` if `p ≥ γ`. -/
theorem nine_fortieths_le {γ : ℝ} (hγ : 0 < γ) (hp : γ ≤ A.prob) :
    (9 / 40 : ℝ) ≤ 1 - A.trialFail (iterationBound γ) := by
  have hM : 10 / Real.sqrt γ ≤ (iterationBound γ : ℝ) := Nat.le_ceil _
  rw [A.one_sub_trialFail (iterationBound_ne_zero hγ)]
  obtain ⟨X, hX⟩ : ∃ X, X = (1 / ((iterationBound γ : ℕ) : ℝ)) *
      ∑ ℓ ∈ range (iterationBound γ), A.mass ℓ := ⟨_, rfl⟩
  rw [← hX]
  by_cases hhalf : 1 / 2 ≤ A.prob
  · have : 0 ≤ X := by
      rw [hX]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun ℓ _ => A.mass_nonneg ℓ)
    linarith
  · have hhalf' : A.prob ≤ 1 / 2 := by linarith
    have hs : Real.sqrt γ ≤ Real.sin (2 * A.angle) := by
      rw [sin_two_angle, Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (mul_nonneg A.prob_nonneg (by linarith))]
      nlinarith [A.prob_nonneg]
    have h : (9 / 20 : ℝ) ≤ X := by
      rw [hX]
      exact average_sin_sq_ge_nine_twentieths hγ hM hs
    linarith [A.prob_nonneg]

theorem trialFail_le {γ : ℝ} (hγ : 0 < γ) (hp : γ ≤ A.prob) :
    A.trialFail (iterationBound γ) ≤ 31 / 40 := by
  have := A.nine_fortieths_le hγ hp
  linarith

/-- Ledger: lem-3.1. `p = 0`: every trial fails. -/
theorem trialFail_of_prob_zero (h : A.prob = 0) {M : ℕ} (hM : M ≠ 0) : A.trialFail M = 1 := by
  rw [← sum_trialWeight hM, trialFail]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [A.mass_eq, A.good_iterate_of_prob_zero h]
  simp

end Preparation

/-! ## The law of the output -/

/-- A payoff that cannot see a global phase of the output. -/
def PhaseInvariant (h : Option H → ℝ) : Prop :=
  ∀ c : ℂ, ‖c‖ = 1 → ∀ v, h (some (c • v)) = h (some v)

/-- Extend a payoff on states by zero on failure. -/
def onSuccess (k : H → ℝ) : Option H → ℝ := fun o => o.elim 0 k

/-- Ledger: lem-3.1. The probability that a procedure succeeds. -/
noncomputable def Proc.successProb (P : Proc) (A : Preparation H) : ℝ :=
  P.expect A (fun o => if o.isSome then 1 else 0) A.zero

/-- Ledger: lem-3.1. The probability that a procedure reports failure. -/
noncomputable def Proc.failProb (P : Proc) (A : Preparation H) : ℝ :=
  P.expect A (fun o => if o.isNone then 1 else 0) A.zero

/-- Ledger: lem-3.1. Expected payoff of the output state, conditional on success. -/
noncomputable def Proc.conditional (P : Proc) (A : Preparation H) (k : H → ℝ) : ℝ :=
  P.expect A (onSuccess k) A.zero / P.successProb A

theorem Preparation.trialGain_of_phase (A : Preparation H) {M : ℕ} (hM : M ≠ 0)
    {h : Option H → ℝ} (hh : PhaseInvariant h) :
    A.trialGain M h = (1 - A.trialFail M) * h (some A.goodState) := by
  have hfail : 1 - A.trialFail M = ∑ ℓ : Fin M, trialWeight M ℓ * A.mass ℓ := by
    rw [A.trialFail_eq hM, sub_sub_cancel]
  rw [hfail, Finset.sum_mul, Preparation.trialGain]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hs : Real.sin ((2 * (ℓ : ℕ) + 1) * A.angle) = 0
  · have : A.mass ℓ = 0 := by simp [Preparation.mass, hs]
    simp [this]
  · obtain ⟨c, hc, e⟩ := A.phaseEq_normalised_good_iterate hs
    rw [e, hh c hc]

/-- Ledger: lem-3.1. All successful branches are `|g⟩` up to phase: on phase-blind
payoffs the output is one state, whatever `ℓ` and the stopping trial were. -/
theorem expect_attempts_of_phase (A : Preparation H) {M : ℕ} (hM : M ≠ 0) (n : ℕ)
    {h : Option H → ℝ} (hh : PhaseInvariant h) :
    (attempts M n).expect A h A.zero =
      (1 - A.trialFail M ^ n) * h (some A.goodState) + A.trialFail M ^ n * h none := by
  rw [expect_attempts, A.norm_zero, one_pow, one_mul]
  induction n with
  | zero => simp [Preparation.attemptValue]
  | succ n ih =>
    rw [Preparation.attemptValue, ih, A.trialGain_of_phase hM hh, pow_succ']
    ring

theorem failProb_attempts (A : Preparation H) {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    (attempts M n).failProb A = A.trialFail M ^ n := by
  have := expect_attempts_of_phase A hM n
    (h := fun o => if o.isNone then 1 else 0) (fun _ _ _ => by simp)
  simpa [Proc.failProb] using this

theorem successProb_attempts (A : Preparation H) {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    (attempts M n).successProb A = 1 - A.trialFail M ^ n := by
  have := expect_attempts_of_phase A hM n
    (h := fun o => if o.isSome then 1 else 0) (fun _ _ _ => by simp)
  simpa [Proc.successProb] using this

theorem phaseEq_smul_iff {c : ℂ} (hc : ‖c‖ = 1) (v g : H) :
    PhaseEq (c • v) g ↔ PhaseEq v g := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  constructor
  · rintro ⟨d, hd, e⟩
    refine ⟨c⁻¹ * d, by rw [norm_mul, norm_inv, hc, hd]; simp, ?_⟩
    rw [← smul_smul, ← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rintro ⟨d, hd, e⟩
    exact ⟨c * d, by rw [norm_mul, hc, hd, one_mul], by rw [e, smul_smul]⟩

open Classical in
/-- The mass of successful outputs that differ from `|g⟩` by more than a phase. -/
noncomputable def Proc.wrongStateMass (P : Proc) (A : Preparation H) : ℝ :=
  P.expect A (onSuccess fun v => if PhaseEq v A.goodState then 0 else 1) A.zero

/-- Ledger: lem-3.1. Lemma 3.1, corrected: one procedure from `γ` and `η`, black-box
in `A`, for all `A`. The call bounds hold on every branch for every `p`. Successful
outputs are `|g⟩` up to phase as a statement about states. `p ≥ γ` gives failure at
most `η`, and `p = 0` gives certain failure. -/
theorem bounded_amplification {γ η : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hη : 0 < η)
    (hη1 : η < 1 / 2) :
    (amplify γ η).callCap ≤ trialCount η * (2 * iterationBound γ + 1) ∧
    ((amplify γ η).callCap : ℝ) ≤ 138 * (Real.sqrt γ)⁻¹ * Real.log (1 / η) ∧
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : Preparation H),
      (amplify γ η).successProb A + (amplify γ η).failProb A = 1 ∧
      (∀ h : Option H → ℝ, PhaseInvariant h →
        (amplify γ η).expect A h A.zero =
          (amplify γ η).successProb A * h (some A.goodState) +
          (amplify γ η).failProb A * h none) ∧
      (∀ k : H → ℝ, (∀ c : ℂ, ‖c‖ = 1 → ∀ v, k (c • v) = k v) →
        (amplify γ η).successProb A ≠ 0 →
        (amplify γ η).conditional A k = k A.goodState) ∧
      (amplify γ η).wrongStateMass A = 0 ∧
      (γ ≤ A.prob → (amplify γ η).failProb A ≤ η) ∧
      (A.prob = 0 → (amplify γ η).failProb A = 1) := by
  refine ⟨callCap_attempts _ _, callCap_amplify_le hγ hγ1 hη hη1, ?_⟩
  intro H _ _ A
  have hM := iterationBound_ne_zero hγ
  have hf := failProb_attempts A hM (trialCount η)
  have hs := successProb_attempts A hM (trialCount η)
  have hlaw : ∀ h : Option H → ℝ, PhaseInvariant h →
      (amplify γ η).expect A h A.zero =
        (amplify γ η).successProb A * h (some A.goodState) +
        (amplify γ η).failProb A * h none := by
    intro h hh
    rw [amplify, hf, hs]
    exact expect_attempts_of_phase A hM _ hh
  have hcond : ∀ k : H → ℝ, (∀ c : ℂ, ‖c‖ = 1 → ∀ v, k (c • v) = k v) →
      (amplify γ η).expect A (onSuccess k) A.zero =
        (amplify γ η).successProb A * k A.goodState := by
    intro k hk
    have := hlaw (onSuccess k) (fun c hc v => hk c hc v)
    simpa [onSuccess] using this
  refine ⟨?_, hlaw, ?_, ?_, ?_, ?_⟩
  · rw [amplify, hf, hs]; ring
  · intro k hk hne
    rw [Proc.conditional, hcond k hk, mul_div_cancel_left₀ _ hne]
  · classical
    rw [Proc.wrongStateMass, hcond]
    · have : PhaseEq A.goodState A.goodState := ⟨1, by simp, by simp⟩
      simp [this]
    · intro c hc v
      simp only [phaseEq_smul_iff hc]
  · intro hp
    rw [amplify, hf]
    calc A.trialFail (iterationBound γ) ^ trialCount η
        ≤ (31 / 40 : ℝ) ^ trialCount η :=
          pow_le_pow_left₀ (A.trialFail_nonneg _) (A.trialFail_le hγ hp) _
      _ ≤ η := pow_trialCount_le hη
  · intro hp
    rw [amplify, hf, A.trialFail_of_prob_zero hp hM, one_pow]

/-! ## The sampler consequence -/

/-- Ledger: lem-3.1. An index register holding the uniform superposition
`(1/√m) ∑ᵢ |i⟩|φᵢ⟩`. `branch i` is `|i⟩|φᵢ⟩`; `read i` projects onto index `i`
and commutes with the success projection. -/
structure IndexRegister (A : Preparation H) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  read : ι → H →ₗ[ℂ] H
  read_good : ∀ i v, read i (A.good v) = A.good (read i v)
  read_complete : ∀ v, ∑ i, ‖read i v‖ ^ 2 = ‖v‖ ^ 2
  branch : ι → H
  state_eq : A.state =
    (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ) • ∑ i, branch i
  read_branch : ∀ i j, read i (branch j) = if i = j then branch j else 0

namespace IndexRegister

variable {A : Preparation H} {ι : Type*} [Fintype ι] [DecidableEq ι] (R : IndexRegister A ι)

/-- The success probability `wᵢ` of index `i`. -/
noncomputable def weight (i : ι) : ℝ := ‖A.good (R.branch i)‖ ^ 2

theorem read_goodPart (i : ι) :
    R.read i A.goodPart =
      (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ) • A.good (R.branch i) := by
  rw [Preparation.goodPart, R.read_good]
  conv_lhs => rw [R.state_eq]
  rw [map_smul, map_sum, map_smul]
  simp [R.read_branch]

theorem norm_read_goodPart_sq (i : ι) :
    ‖R.read i A.goodPart‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ * R.weight i := by
  rw [R.read_goodPart, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), weight]

theorem prob_eq : A.prob = (Fintype.card ι : ℝ)⁻¹ * ∑ i, R.weight i := by
  have h := R.read_complete A.goodPart
  rw [Finset.mul_sum, ← Finset.sum_congr rfl fun i _ => R.norm_read_goodPart_sq i, h]
  rfl

/-- Ledger: lem-3.1. In the normalised successful state, index `i` has probability
`wᵢ / ∑ w`, exactly. -/
theorem norm_read_goodState_sq (hS : 0 < ∑ i, R.weight i) (i : ι) :
    ‖R.read i A.goodState‖ ^ 2 = R.weight i / ∑ j, R.weight j := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    intro h0
    have h0' : Fintype.card ι = 0 := by exact_mod_cast h0
    have := Fintype.card_eq_zero_iff.mp h0'
    simp at hS
  have hg : ‖A.goodPart‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ * ∑ i, R.weight i := R.prob_eq
  rw [Preparation.goodState, normalised, map_smul, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, inv_pow, hg, R.norm_read_goodPart_sq]
  field_simp

/-- Ledger: lem-3.1. Still exact after any number of Grover iterations. -/
theorem norm_read_normalised_iterate_sq (hS : 0 < ∑ i, R.weight i) {ℓ : ℕ}
    (hs : Real.sin ((2 * ℓ + 1) * A.angle) ≠ 0) (i : ι) :
    ‖R.read i (normalised (A.good (A.iterate ℓ)))‖ ^ 2 = R.weight i / ∑ j, R.weight j := by
  obtain ⟨c, hc, e⟩ := A.phaseEq_normalised_good_iterate hs
  rw [e, map_smul, norm_smul, hc, one_mul, R.norm_read_goodState_sq hS]

/-- Ledger: lem-3.1. The fact Proposition 3.2 consumes. Conditional on the amplified
procedure succeeding, measuring the index gives `i` with probability `wᵢ / ∑ w`,
exactly. -/
theorem index_law_of_amplified {γ η : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hη : 0 < η)
    (hη1 : η < 1 / 2) (hS : 0 < ∑ i, R.weight i) (i : ι)
    (hne : (amplify γ η).successProb A ≠ 0) :
    (amplify γ η).conditional A (fun v => ‖R.read i v‖ ^ 2) =
      R.weight i / ∑ j, R.weight j := by
  rw [(bounded_amplification hγ hγ1 hη hη1).2.2 A |>.2.2.1 _ _ hne,
    R.norm_read_goodState_sq hS]
  intro c hc v
  rw [map_smul, norm_smul, hc, one_mul]

end IndexRegister

end QuarticQuery.Amplification

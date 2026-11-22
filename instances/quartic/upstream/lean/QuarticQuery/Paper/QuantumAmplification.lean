module

public import QuarticQuery.Upper.Amplify

/-!
# Section 3.1 and the coherent-access interface

Compiled as part of the `QuarticQuery` library target.
It does not change the status of its imported declarations.


The geometry is the two-dimensional calculation of Brassard, Hoyer, Mosca and
Tapp, Section 2, Lemma 1 and equation (8), arXiv:quant-ph/0005055v1, pp. 5-7.
The exact trigonometric average is also Boyer, Brassard, Hoyer and Tapp,
Section 4, Lemma 2, arXiv:quant-ph/9605034v1, p. 3.

The full-state theorem `Amplification.bounded_amplification` is abstract.
The query implementation `Upper.Samples.amplify` measures a label and resets a
known basis state. Its exact label law is sufficient for the tournament. No
statement here identifies those two output interfaces.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Amplification QuarticQuery.Upper

/-! ## The exact statements used by the amplification argument -/

section Geometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Ledger: claim-grover-state. The complete state decomposition, normalized
good and bad vectors, angle range, and successful-state conclusion. The last
clause applies only when the successful component is nonzero. -/
theorem quantum_grover_state (A : Preparation H) (h0 : 0 < A.prob) (h1 : A.prob < 1) :
    (0 < A.angle ∧ A.angle < Real.pi / 2) ∧
    ‖A.goodState‖ = 1 ∧ ‖A.badState‖ = 1 ∧
    A.good A.goodState = A.goodState ∧ A.good A.badState = 0 ∧
    inner ℂ A.goodState A.badState = 0 ∧
    A.state = ((Real.sin A.angle : ℝ) : ℂ) • A.goodState +
      ((Real.cos A.angle : ℝ) : ℂ) • A.badState ∧
    ∀ ℓ : ℕ,
      A.iterate ℓ =
        ((Real.sin ((2 * ℓ + 1) * A.angle) : ℝ) : ℂ) • A.goodState +
        ((Real.cos ((2 * ℓ + 1) * A.angle) : ℝ) : ℂ) • A.badState ∧
      (A.good (A.iterate ℓ) ≠ 0 →
        PhaseEq (normalised (A.good (A.iterate ℓ))) A.goodState) := by
  have hbad : A.badPart ≠ 0 := by
    intro hb
    have hn := A.norm_badPart_sq
    rw [hb, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
    linarith
  have hbadnorm : ‖A.badState‖ = 1 := by
    exact norm_normalised hbad
  have horth : inner ℂ A.goodState A.badState = 0 := by
    rw [← A.good_goodState, A.good_symm, A.good_badState, inner_zero_right]
  refine ⟨A.angle_mem (h0 := h0) (h1 := h1), A.norm_goodState h0, hbadnorm,
    A.good_goodState, A.good_badState, horth, A.state_eq, ?_⟩
  intro ℓ
  refine ⟨A.iterate_eq ℓ, ?_⟩
  intro hgood
  have hs : Real.sin ((2 * ℓ + 1) * A.angle) ≠ 0 := by
    intro hs
    apply hgood
    rw [A.good_iterate, hs]
    simp
  exact A.phaseEq_normalised_good_iterate hs

/-- Ledger: claim-grover-state. The zero-success case has no successful output
at any iteration; it does not require a conditional state at probability zero. -/
theorem quantum_grover_zero (A : Preparation H) (h : A.prob = 0) (ℓ : ℕ) :
    A.good (A.iterate ℓ) = 0 :=
  A.good_iterate_of_prob_zero h ℓ

/-- Ledger: claim-sin2theta. The equality and the lower bound occur together
under the paper's hypotheses. The lower bound is extracted from the proof of
`Preparation.nine_fortieths_le`. -/
theorem quantum_sin_two_angle (A : Preparation H) {γ : ℝ}
    (hp : γ ≤ A.prob) (hhalf : A.prob ≤ 1 / 2) :
    Real.sin (2 * A.angle) = 2 * Real.sqrt (A.prob * (1 - A.prob)) ∧
    Real.sqrt γ ≤ Real.sin (2 * A.angle) := by
  refine ⟨A.sin_two_angle, ?_⟩
  rw [A.sin_two_angle, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (mul_nonneg A.prob_nonneg (by linarith))]
  nlinarith [A.prob_nonneg]

/-- Ledger: eq-9. Both links of the displayed inequality, with exactly the
paper's `M = ceil(10 / sqrt gamma)` and `gamma <= p <= 1/2` hypotheses. -/
theorem quantum_eq_9 (A : Preparation H) {γ : ℝ} (hγ : 0 < γ)
    (hp : γ ≤ A.prob) (hhalf : A.prob ≤ 1 / 2) :
    let M := iterationBound γ
    (1 / 2 - 1 / (2 * (M : ℝ) * |Real.sin (2 * A.angle)|) ≤
      (1 / (M : ℝ)) * ∑ ℓ ∈ Finset.range M,
        Real.sin ((2 * ℓ + 1) * A.angle) ^ 2) ∧
    (9 / 20 : ℝ) ≤ 1 / 2 - 1 / (2 * (M : ℝ) * |Real.sin (2 * A.angle)|) := by
  intro M
  have hr : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hs : Real.sqrt γ ≤ Real.sin (2 * A.angle) :=
    (quantum_sin_two_angle A hp hhalf).2
  have hspos : 0 < Real.sin (2 * A.angle) := hr.trans_le hs
  have hM : 10 / Real.sqrt γ ≤ (M : ℝ) := Nat.le_ceil _
  have hMpos : (0 : ℝ) < M := (div_pos (by norm_num) hr).trans_le hM
  have hM0 : M ≠ 0 := iterationBound_ne_zero hγ
  refine ⟨average_sin_sq_ge hM0 hspos.ne', ?_⟩
  have h10 : 10 ≤ (M : ℝ) * Real.sqrt γ := by
    rwa [div_le_iff₀ hr] at hM
  have hprod : 10 ≤ (M : ℝ) * Real.sin (2 * A.angle) :=
    h10.trans (mul_le_mul_of_nonneg_left hs hMpos.le)
  rw [abs_of_pos hspos]
  have hsmall : 1 / (2 * (M : ℝ) * Real.sin (2 * A.angle)) ≤ 1 / 20 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  linarith

end Geometry

/-! ## The finite trial loop and its parameter-only budget -/

/-- Ledger: def-grover-trial. The three choices in the construction agree by
definition with the paper. `amplify` is fixed before the preparation is given. -/
theorem quantum_grover_parameters (γ η : ℝ) :
    iterationBound γ = ⌈10 / Real.sqrt γ⌉₊ ∧
    trialCount η = ⌈Real.log (1 / η) / Real.log (40 / 31)⌉₊ ∧
    amplify γ η = attempts (iterationBound γ) (trialCount η) :=
  ⟨rfl, rfl, rfl⟩

/-- Ledger: def-grover-trial. The random iteration count is the half point
mass, half uniform mixture, which has total mass one for `M > 0`. -/
theorem quantum_grover_trial_distribution {M : ℕ} (hM : M ≠ 0) :
    (∀ ℓ : Fin M, trialWeight M ℓ =
      (if (ℓ : ℕ) = 0 then 1 / 2 else 0) + 1 / (2 * (M : ℝ))) ∧
    (∀ ℓ : Fin M, 0 ≤ trialWeight M ℓ) ∧
    (∑ ℓ : Fin M, trialWeight M ℓ) = 1 :=
  ⟨fun _ => rfl, fun _ => trialWeight_nonneg _ _, sum_trialWeight hM⟩

/-- Ledger: def-grover-trial. The recursion uses a fresh start for each trial
and terminates at the first successful projection. -/
theorem quantum_grover_trial_recursion (M n : ℕ) :
    attempts M (n + 1) =
      .mix M (fun ℓ => trialWeight M ℓ) (fun ℓ =>
        .restart (.run (groverCircuit ℓ) (.measure .success (attempts M n)))) := rfl

/-- Ledger: def-grover-trial. Every branch is capped even when the actual
success probability is below the promised threshold or is zero. -/
theorem quantum_grover_call_cap (γ η : ℝ) :
    (amplify γ η).callCap ≤ trialCount η * (2 * iterationBound γ + 1) :=
  callCap_attempts _ _

/-- Ledger: lem-3.1. The padded budget itself is bounded, not merely the cap of
the abstract `Proc`. This numerical statement is needed by `stageCost` and
`searchCost`, whose definitions charge the whole padded product. -/
theorem amplification_budget_le {γ η : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hη : 0 < η) (hη1 : η < 1 / 2) :
    (trialCount η : ℝ) * (2 * (iterationBound γ : ℝ) + 1) ≤
      138 * (Real.sqrt γ)⁻¹ * Real.log (1 / η) := by
  have hr : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hr1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have ha : 1 ≤ (Real.sqrt γ)⁻¹ := (one_le_inv₀ hr).mpr hr1
  obtain ⟨a, haa⟩ : ∃ a, a = (Real.sqrt γ)⁻¹ := ⟨_, rfl⟩
  rw [← haa] at ha ⊢
  obtain ⟨L, hLL⟩ : ∃ L, L = Real.log (1 / η) := ⟨_, rfl⟩
  rw [← hLL]
  have hL2 : Real.log 2 ≤ L := by
    rw [hLL]
    exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hη]; linarith)
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
  have hfac : 2 * (iterationBound γ : ℝ) + 1 ≤ 23 * a := by linarith
  calc
    (trialCount η : ℝ) * (2 * (iterationBound γ : ℝ) + 1)
        ≤ (6 * L) * (23 * a) :=
      mul_le_mul hn hfac (by positivity) (by linarith)
    _ = 138 * a * L := by ring

/-! ## The measured implementation used by the theorem -/

/-- Ledger: lem-3.1. The implementation in the bit-query model has the exact
successful-label law and an input-independent cap on every branch. It is the
measured counterpart used by the tournament, not a returned-state theorem. -/
theorem quantum_amplified_label_law {ι β : Type} [Fintype ι] [Inhabited ι] [Fintype β]
    {n : ℕ} {L : BitInput ι → Option β → ℝ} (h : Samples n L)
    {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃ f : BitInput ι → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, γ ≤ ∑ b, L x (some b) → f x ≤ η) ∧
      (∀ x, ∑ b, L x (some b) = 0 → f x = 1) ∧
      Runs (trialCount η * (2 * ((2 * iterationBound γ + 1) * n)))
        (fun x => ampLaw (f x) (fun b => L x (some b))) :=
  h.amplify hγ hη

/-- Ledger: lem-3.1. Nonnegative weights of positive total mass and a failure
probability in `[0,1)` give a probability law with positive successful mass.
Conditioning on that event preserves the normalized original label law. -/
theorem quantum_amplified_conditional {β : Type} [Fintype β] (q : β → ℝ)
    (hq0 : ∀ b, 0 ≤ q b) (hq : 0 < ∑ c, q c) {f : ℝ}
    (hf0 : 0 ≤ f) (hf1 : f < 1) :
    (∀ o : Option β, 0 ≤ ampLaw f q o) ∧
    (∑ o : Option β, ampLaw f q o) = 1 ∧
    0 < ∑ c, ampLaw f q (some c) ∧
    ∀ b, ampLaw f q (some b) / (∑ c, ampLaw f q (some c)) =
      q b / ∑ c, q c := by
  have hfpos : 0 < 1 - f := sub_pos.mpr hf1
  have hsum : (∑ c, ampLaw f q (some c)) = 1 - f := by
    simp only [ampLaw, ← Finset.mul_sum, ← Finset.sum_div]
    rw [div_self hq.ne', mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o
    cases o with
    | none => exact hf0
    | some b => exact mul_nonneg hfpos.le (div_nonneg (hq0 b) hq.le)
  · rw [Fintype.sum_option]
    change f + (∑ c, ampLaw f q (some c)) = 1
    rw [hsum]
    ring
  · rw [hsum]
    exact hfpos
  · intro b
    rw [hsum]
    change ((1 - f) * (q b / ∑ c, q c)) / (1 - f) = _
    exact mul_div_cancel_left₀ _ hfpos.ne'

/-! ## Retaining fresh registers through all trials -/

section CoherentTrials

variable {ι β : Type} [Fintype ι] [Inhabited ι] [Fintype β]

/-- Ledger: lem-3.1. The finite trial loop as a coherent sampler. Every classical choice
is retained in an orthogonal register; successful branches leave subsequent
trials dormant. The cap counts abstract reads. The proof transports the
source `Samples.attempts` induction from `Runs.bind` to `Samples.bind`. -/
theorem quantum_attempts_samples {n : ℕ} {L : BitInput ι → Option β → ℝ} (h : Samples n L) {M : ℕ}
    (hM : M ≠ 0) : ∃ f₀ : BitInput ι → ℝ,
      (∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ 1) ∧
      (∀ x γ, 0 < γ → M = iterationBound γ → γ ≤ ∑ b, L x (some b) → f₀ x ≤ 31 / 40) ∧
      (∀ x, ∑ b, L x (some b) = 0 → f₀ x = 1) ∧
      ∀ t, Samples (t * ((2 * M + 1) * n)) fun x => ampLaw (f₀ x ^ t) fun b => L x (some b) := by
  classical
  obtain ⟨Z, _, o, out, F, hF, hL⟩ := h
  let A : BitInput ι → Preparation (Reg Z) := fun x => prepOf (F x) o (isGood out)
  have hprob : ∀ x, (A x).prob = ∑ b, L x (some b) := fun x => by
    simp only [hL]
    exact prob_eq_sum (F x) o out
  have hfail1 : ∀ x, (A x).trialFail M ≤ 1 := fun x => by
    rw [(A x).trialFail_eq hM]
    have : 0 ≤ ∑ ℓ : Fin M, trialWeight M ℓ * (A x).mass ℓ :=
      Finset.sum_nonneg fun ℓ _ => mul_nonneg (trialWeight_nonneg _ _) ((A x).mass_nonneg _)
    linarith
  refine ⟨fun x => (A x).trialFail M, fun x => ⟨(A x).trialFail_nonneg M, hfail1 x⟩,
    fun x γ hγ hM' hp => ?_, fun x h0 => ?_, fun t => ?_⟩
  · subst hM'
    exact (A x).trialFail_le hγ (by rw [hprob]; exact hp)
  · exact (A x).trialFail_of_prob_zero (by rw [hprob, h0]) hM
  · -- one trial of length `ℓ`
    have htrial : ∀ ℓ : Fin M, Samples ((2 * M + 1) * n) fun x o' =>
        lawOf ((A x).iterate ℓ) out o' := fun ℓ => by
      have hc := isCirc_circU hF o (isGood out) (groverCircuit ℓ)
      rw [calls_groverCircuit] at hc
      have hs : Samples ((2 * (ℓ : ℕ) + 1) * n) fun x o' => lawOf ((A x).iterate ℓ) out o' :=
        ⟨Z, inferInstance, o, out, _, hc, fun x b => by rw [circU_apply]; rfl⟩
      refine hs.mono (Nat.mul_le_mul_right n ?_)
      have := ℓ.isLt
      omega
    have hweights : Samples (ι := ι) 0 fun _ (ℓ : Fin M) => trialWeight M ℓ :=
      Samples.gate (fun ℓ => trialWeight_nonneg _ _) (sum_trialWeight hM)
    induction t with
    | zero =>
      refine (Samples.pure (ι := ι) (none : Option β)).mono (by omega) |>.congr fun x o' => ?_
      cases o' with
      | none => simp [ampLaw, pt_self]
      | some b => simp [ampLaw, pt_of_ne]
    | succ t ih =>
      let K : Option β → BitInput ι → Option β → ℝ := fun o₁ x o' =>
        match o₁ with
        | none => ampLaw ((A x).trialFail M ^ t) (fun b => L x (some b)) o'
        | some b => pt (some b) o'
      have hK : ∀ o₁, Samples (t * ((2 * M + 1) * n)) (K o₁) := fun o₁ => by
        cases o₁ with
        | none => exact ih
        | some b => exact (Samples.pure (ι := ι) (some b)).mono (by omega)
      have hstep := fun ℓ : Fin M => (htrial ℓ).bind hK
      have hall := hweights.bind hstep
      refine (hall.mono (by
        generalize (2 * M + 1) * n = Y
        have e : (t + 1) * Y = t * Y + Y := by ring
        omega)).congr fun x o' => ?_
      -- the value of one trial
      obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ampLaw 0 (fun b => L x (some b)) o' := ⟨_, rfl⟩
      obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ampLaw ((A x).trialFail M ^ t) (fun b => L x (some b)) o' :=
        ⟨_, rfl⟩
      have hterm : ∀ ℓ : Fin M, ∑ o₁, lawOf ((A x).iterate ℓ) out o₁ * K o₁ x o' =
          (1 - (A x).mass ℓ) * V + (A x).mass ℓ * Q := by
        intro ℓ
        rw [Fintype.sum_option]
        simp only [K]
        rw [← hV]
        congr 1
        · rw [show lawOf ((A x).iterate ℓ) out none = 1 - (A x).mass ℓ from
            lawOf_iterate_none (F x) o out ℓ]
        · simp only [show ∀ b, lawOf ((A x).iterate ℓ) out (some b) = _ from
            lawOf_iterate_some (F x) o out ℓ, ← hL, hQ]
          cases o' with
          | none => simp [ampLaw, pt_of_ne]
          | some b =>
            have : ∀ c : β, pt (some c) (some b) = pt c b := fun c => by
              by_cases h : c = b
              · subst h; simp [pt_self]
              · rw [pt_of_ne h, pt_of_ne (by simpa using h)]
            simp only [this, ampLaw, sub_zero, one_mul]
            rw [Finset.sum_congr rfl fun c _ => mul_assoc _ _ _, ← Finset.mul_sum]
            rw [sum_mul_pt]
      simp only [hterm]
      have hsum : ∑ ℓ : Fin M, trialWeight M ℓ * ((1 - (A x).mass ℓ) * V + (A x).mass ℓ * Q) =
          (A x).trialFail M * V + (1 - (A x).trialFail M) * Q := by
        have h1 : 1 - (A x).trialFail M = ∑ ℓ : Fin M, trialWeight M ℓ * (A x).mass ℓ := by
          rw [(A x).trialFail_eq hM]; ring
        rw [h1, Preparation.trialFail, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ℓ _ => by ring
      rw [hsum, hV, hQ]
      cases o' with
      | none =>
        simp only [ampLaw]
        rw [pow_succ']
        ring
      | some b =>
        simp only [ampLaw]
        rw [pow_succ']
        ring

/-- Ledger: lem-3.1. The coherent trial loop at the parameters of Lemma 3.1.
This preserves the successful label law while retaining all workspace. Apply
`Samples.runs` afterwards to charge two bit queries per abstract read. -/
theorem quantum_amplify_samples {n : ℕ} {L : BitInput ι → Option β → ℝ} (h : Samples n L) {γ η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) : ∃ f : BitInput ι → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, γ ≤ ∑ b, L x (some b) → f x ≤ η) ∧
      (∀ x, ∑ b, L x (some b) = 0 → f x = 1) ∧
      Samples (trialCount η * ((2 * iterationBound γ + 1) * n))
        fun x => ampLaw (f x) fun b => L x (some b) := by
  obtain ⟨f₀, h01, hfail, hzero, hrun⟩ := quantum_attempts_samples h (iterationBound_ne_zero hγ)
  refine ⟨fun x => f₀ x ^ trialCount η, fun x => ⟨pow_nonneg (h01 x).1 _,
    pow_le_one₀ (h01 x).1 (h01 x).2⟩, fun x hp => ?_, fun x h0 => ?_, hrun _⟩
  · calc f₀ x ^ trialCount η ≤ (31 / 40 : ℝ) ^ trialCount η :=
        pow_le_pow_left₀ (h01 x).1 (hfail x γ hγ rfl hp) _
      _ ≤ η := pow_trialCount_le hη
  · simp [hzero x h0]


end CoherentTrials

/-! ## Coherent access and reversal in the ordinary bit-query model -/

/-- Ledger: claim-coherent-access. Reversing a retained-workspace circuit costs
the same number of abstract reads. -/
theorem quantum_inverse_reads {ι Z : Type} [Fintype Z] {n : ℕ}
    {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F) :
    IsCirc n (fun x => (F x).symm) := hF.symm

/-- Ledger: claim-coherent-access. A family indexed by a superposed classical
register is a single coherent circuit with the common read count. -/
theorem quantum_controlled_reads {ι Γ : Type} [Fintype Γ] {Z : Γ → Type}
    [∀ c, Fintype (Z c)] {n : ℕ}
    {F : ∀ c, BitInput ι → Reg (Z c) ≃ₗᵢ[ℂ] Reg (Z c)}
    (hF : ∀ c, IsCirc n (F c)) :
    IsCirc n (fun x => sigmaOp (fun c => F c x)) := IsCirc.sigma hF

/-- Ledger: claim-coherent-access. Loading an addressed input bit, using it,
and unloading it uses exactly two ordinary bit queries. The embedding holds
for arbitrary superpositions of addresses. -/
theorem quantum_controlled_bit_query {ι Z : Type} [Fintype ι] [Inhabited ι]
    [Fintype Z] {w : ℕ} (e : Z ↪ Fin (w + 1)) (R : ReadSpec ι Z) :
    ∃ P : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (P next).queryCap = 2 + next.queryCap ∧
      ∀ x ψ b, (P next).outputMass x (clEmb e ψ) b =
        next.outputMass x (clEmb e (R.op x ψ)) b :=
  compile_read e R

/-- Ledger: claim-coherent-access. An `n`-read coherent circuit compiles to at
most `2n` ordinary bit queries, independently of its input and continuation. -/
theorem quantum_compile_circuit {ι Z : Type} [Fintype ι] [Inhabited ι]
    [Fintype Z] {w n : ℕ} (e : Z ↪ Fin (w + 1))
    {F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z} (hF : IsCirc n F) :
    ∃ P : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (P next).queryCap ≤ 2 * n + next.queryCap ∧
      ∀ x ψ b, (P next).outputMass x (clEmb e ψ) b =
        next.outputMass x (clEmb e (F x ψ)) b :=
  compile_circ e hF

/-- Ledger: claim-coherent-access. Every adaptive classical query tree has a
coherent sampler at the same abstract-read depth, retaining all queried bits. -/
theorem quantum_coherent_tree {ι : Type} [Nonempty ι] (T : QueryTree ι) :
    Samples T.depth (fun (x : BitInput ι) b => pt (T.eval x) b) :=
  Samples.tree T

end QuarticQuery.Paper

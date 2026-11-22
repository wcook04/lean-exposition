module

public import QuarticQuery.Upper.SuccessGateBridge
public import QuarticQuery.Upper.TrialStatistics
public import QuarticQuery.Amplification.Bounded

/-! Scalar consequences of the actual marked-and-routed success norm. -/

public section
namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {N : ℕ} {Z : Type} [Fintype Z]

/-- Identical normalized trials have exact success mass one minus the N-th
power of their single-trial failure mass. This is independent of the later
factorization and also covers success probability zero. -/
theorem assembledSuccess_norm_iid (o : Z) (S : Z → Bool)
    (v : Reg Z) (hv : ‖v‖ = 1) :
    ‖assembledSuccess o S (fun _ : Fin N => v)‖ ^ 2 =
      1 - (lawOf v S false) ^ N := by
  classical
  rw [assembledSuccess_norm_product]
  have ht : (∑ z, ‖v.ofLp z‖ ^ 2) = (1 : ℝ) := by
    rw [← reg_norm_sq, hv]
    norm_num
  have hb : (∑ z, if S z = false then ‖v.ofLp z‖ ^ 2 else 0) =
      lawOf v S false := by simp [lawOf]
  simp only [ht, hb, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, one_pow]

/-- The complement of the trial's good law is exactly the analytic failure
number. No positive-probability premise is needed. -/
theorem opaqueTrialVector_bad_mass {M : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) [DecidablePred S]
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M)
    (hV : V (rket a₀) = choiceState M) :
    lawOf (opaqueTrialVector U o S V a₀)
      (fun p => decide (S p.2)) false =
      (prepOf U o S).trialFail M := by
  have hn := opaqueTrialVector_norm U o S V a₀
  have hg := opaqueTrialVector_good_mass hM U o S V a₀ hV
  have hs := sum_lawOf (opaqueTrialVector U o S V a₀)
    (fun p => decide (S p.2))
  rw [Fintype.sum_bool, hn, hg] at hs
  nlinarith

/-- Exact success norm of N independent opaque trials, including p=0. -/
theorem assembledSuccess_opaque_norm {M : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) [DecidablePred S]
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M)
    (hV : V (rket a₀) = choiceState M) (N : ℕ) :
    ‖assembledSuccess (⟨a₀, o⟩ : Σ _ : Fin M, Z)
      (fun p => decide (S p.2))
      (fun _ : Fin N => opaqueTrialVector U o S V a₀)‖ ^ 2 =
      1 - (prepOf U o S).trialFail M ^ N := by
  rw [assembledSuccess_norm_iid _ _ _ (opaqueTrialVector_norm U o S V a₀)]
  rw [opaqueTrialVector_bad_mass hM U o S V a₀ hV]

/-- The forced zero-iterate half of a trial contributes at least half the
initial good probability, uniformly in the later iteration schedule. -/
theorem trialFail_gain_ge_half {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : Preparation H) {M : ℕ}
    (hM : 0 < M) : A.prob / 2 ≤ 1 - A.trialFail M := by
  rw [A.one_sub_trialFail (Nat.ne_of_gt hM)]
  have hsum : 0 ≤ ∑ ℓ ∈ Finset.range M, A.mass ℓ := by
    exact Finset.sum_nonneg fun ℓ _ => A.mass_nonneg ℓ
  have hinv : 0 ≤ (1 / (M : ℝ)) := by positivity
  nlinarith [mul_nonneg hinv hsum]

/-- At least one independent trial retains that half-probability lower
bound. This avoids any conditioning on a nonzero success event. -/
theorem trialFail_pow_gain_ge_half {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : Preparation H) {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) :
    A.prob / 2 ≤ 1 - A.trialFail M ^ N := by
  have h0 : 0 ≤ A.trialFail M := A.trialFail_nonneg M
  have h1 : A.trialFail M ≤ 1 := by
    have hp := trialFail_gain_ge_half A hM
    have hprob := A.prob_nonneg
    linarith
  have hpow : ∀ n : ℕ, A.trialFail M ^ (n + 1) ≤ A.trialFail M := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        calc
          A.trialFail M ^ (n + 1) * A.trialFail M ≤
              A.trialFail M * A.trialFail M :=
            mul_le_mul_of_nonneg_right ih h0
          _ ≤ A.trialFail M := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hp := trialFail_gain_ge_half A hM
  linarith [hpow n]

/-- The established analytic schedule bounds the same exact physical norm. -/
theorem trialFail_pow_le_error {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : Preparation H)
    {γ η : ℝ} (hγ : 0 < γ) (hp : γ ≤ A.prob) (hη : 0 < η) :
    A.trialFail (iterationBound γ) ^ trialCount η ≤ η := by
  calc
    A.trialFail (iterationBound γ) ^ trialCount η ≤
        (31 / 40 : ℝ) ^ trialCount η :=
      pow_le_pow_left₀ (A.trialFail_nonneg _) (A.trialFail_le hγ hp) _
    _ ≤ η := pow_trialCount_le hη

/-- A positive number of routed opaque trials retains at least half the
original good probability, with no branch conditioning. -/
theorem assembledSuccess_opaque_gain {M : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) [DecidablePred S]
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M)
    (hV : V (rket a₀) = choiceState M) {N : ℕ} (hN : 0 < N) :
    (prepOf U o S).prob / 2 ≤
      ‖assembledSuccess (⟨a₀, o⟩ : Σ _ : Fin M, Z)
        (fun p => decide (S p.2))
        (fun _ : Fin N => opaqueTrialVector U o S V a₀)‖ ^ 2 := by
  rw [assembledSuccess_opaque_norm hM U o S V a₀ hV N]
  exact trialFail_pow_gain_ge_half (prepOf U o S) hM hN

/-- Zero original good mass produces zero routed success mass. -/
theorem assembledSuccess_opaque_zero {M : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) [DecidablePred S]
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M)
    (hV : V (rket a₀) = choiceState M) (N : ℕ)
    (hzero : (prepOf U o S).prob = 0) :
    ‖assembledSuccess (⟨a₀, o⟩ : Σ _ : Fin M, Z)
      (fun p => decide (S p.2))
      (fun _ : Fin N => opaqueTrialVector U o S V a₀)‖ ^ 2 = 0 := by
  rw [assembledSuccess_opaque_norm hM U o S V a₀ hV N,
    (prepOf U o S).trialFail_of_prob_zero hzero (Nat.ne_of_gt hM)]
  simp

/-- Published bounded schedule: all-input cap is handled by the circuit;
this lemma supplies the exact retained success mass lower bound. -/
theorem assembledSuccess_opaque_error
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) [DecidablePred S]
    {γ η : ℝ} (hγ : 0 < γ) (hp : γ ≤ (prepOf U o S).prob)
    (hη : 0 < η)
    (V : Reg (Fin (iterationBound γ)) ≃ₗᵢ[ℂ]
      Reg (Fin (iterationBound γ)))
    (a₀ : Fin (iterationBound γ))
    (hV : V (rket a₀) = choiceState (iterationBound γ)) :
    1 - η ≤
      ‖assembledSuccess (⟨a₀, o⟩ : Σ _ : Fin (iterationBound γ), Z)
        (fun p => decide (S p.2))
        (fun _ : Fin (trialCount η) => opaqueTrialVector U o S V a₀)‖ ^ 2 := by
  have hM : 0 < iterationBound γ := Nat.pos_of_ne_zero (iterationBound_ne_zero hγ)
  rw [assembledSuccess_opaque_norm hM U o S V a₀ hV (trialCount η)]
  linarith [trialFail_pow_le_error (prepOf U o S) hγ hp hη]

end QuarticQuery.Upper
end

module

public import QuarticQuery.Upper.OneTrialFactor

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {Z : Type} [Fintype Z]

/-- A coordinate good-label law is exactly the squared norm of its projector. -/
theorem lawOf_bool_good (ψ : Reg Z) (S : Z → Prop) [DecidablePred S] :
    lawOf ψ (fun z => decide (S z)) true = ‖coordProj S ψ‖ ^ 2 := by
  classical
  rw [reg_norm_sq]
  simp only [lawOf]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : S z
  · simp [coordProj_apply, hz]
  · simp [coordProj_apply, hz]

/-- The opaque trial vector has norm one for every fixed oracle, including
zero initial good probability. -/
theorem opaqueTrialVector_norm {M : ℕ}
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M) :
    ‖opaqueTrialVector U o S V a₀‖ = 1 := by
  simp [opaqueTrialVector, norm_rket]

/-- The fixed prepared selector gives precisely the analytic one-trial
success mass, without dividing by the initial success probability. -/
theorem opaqueTrialVector_good_mass {M : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) [DecidablePred S]
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M)
    (hV : V (rket a₀) = choiceState M) :
    lawOf (opaqueTrialVector U o S V a₀)
      (fun p => decide (S p.2)) true =
      1 - (prepOf U o S).trialFail M := by
  classical
  rw [lawOf_sigma]
  have hs : ∀ a : Fin M,
      slice a (opaqueTrialVector U o S V a₀) =
        (V (rket a₀)).ofLp a • (prepOf U o S).iterate a.val := by
    intro a
    have h := slice_opaquePrefix_full U o S hM
      (leftOp V (rket ⟨a₀, o⟩)) a
    simpa [opaqueTrialVector, slice_leftOp_rket, circU_apply,
      Preparation.iterate, prepOf] using h
  have hw : ∀ a : Fin M,
      ‖(V (rket a₀)).ofLp a‖ ^ 2 = trialWeight M a.val := by
    intro a
    rw [hV]
    simp [choiceState, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (trialWeight_nonneg M a.val)]
  have hsum :
      (∑ a : Fin M, lawOf (slice a (opaqueTrialVector U o S V a₀))
        (fun z => decide (S z)) true) =
      ∑ a : Fin M, trialWeight M a.val * (prepOf U o S).mass a.val := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hs a, lawOf_smul, hw, lawOf_bool_good]
    change trialWeight M a.val *
      ‖(prepOf U o S).good ((prepOf U o S).iterate a.val)‖ ^ 2 = _
    rw [← (prepOf U o S).mass_eq a.val]
  rw [hsum]
  rw [(prepOf U o S).trialFail_eq (Nat.ne_of_gt hM)]
  ring

end QuarticQuery.Upper

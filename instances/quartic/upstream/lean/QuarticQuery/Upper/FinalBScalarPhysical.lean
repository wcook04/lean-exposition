module

public import QuarticQuery.Upper.FinalB
public import QuarticQuery.Upper.ScalarBounds
public import QuarticQuery.Upper.PhysicalContinuation

/-! Scalar success laws and physical continuation for the same final amplifier. -/

public section
namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {Z : Type} [Fintype Z]

/-- The success projection of the actual initialized final circuit has the
exact independent-trial success probability. -/
theorem finalB_success_exact {M N : ℕ} (hM : 0 < M)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool)
    (hV : V (rket a₀) = choiceState M) :
    ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z))
      (finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o)))‖ ^ 2 =
      1 - (prepOf U o (fun z => S z = true)).trialFail M ^ N := by
  rw [finalB_success_eq, LinearIsometryEquiv.norm_map]
  exact assembledSuccess_opaque_norm hM U o (fun z => S z = true)
    V a₀ hV N

/-- A positive number of trials retains at least half the initial good mass. -/
theorem finalB_success_gain {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool)
    (hV : V (rket a₀) = choiceState M) :
    (prepOf U o (fun z => S z = true)).prob / 2 ≤
      ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z))
        (finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o)))‖ ^ 2 := by
  rw [finalB_success_exact hM V U a₀ o S hV]
  exact trialFail_pow_gain_ge_half (prepOf U o (fun z => S z = true)) hM hN

/-- If the original good mass is zero, the actual circuit never succeeds. -/
theorem finalB_success_zero {M N : ℕ} (hM : 0 < M)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool)
    (hV : V (rket a₀) = choiceState M)
    (hzero : (prepOf U o (fun z => S z = true)).prob = 0) :
    ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z))
      (finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o)))‖ ^ 2 = 0 := by
  rw [finalB_success_exact hM V U a₀ o S hV,
    (prepOf U o (fun z => S z = true)).trialFail_of_prob_zero hzero
      (Nat.ne_of_gt hM)]
  simp

/-- The published schedule gives the target error for the actual circuit. -/
theorem finalB_success_error
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Bool)
    {γ η : ℝ} (hγ : 0 < γ)
    (hp : γ ≤ (prepOf U o (fun z => S z = true)).prob)
    (hη : 0 < η)
    (V : Reg (Fin (iterationBound γ)) ≃ₗᵢ[ℂ]
      Reg (Fin (iterationBound γ)))
    (a₀ : Fin (iterationBound γ))
    (hV : V (rket a₀) = choiceState (iterationBound γ)) :
    1 - η ≤
      ‖coordProj (finalSuccess (M := iterationBound γ) (N := trialCount η) (Z := Z))
        (finalB (N := trialCount η) V U o S
          (rket (finalOrigin (N := trialCount η) a₀ o)))‖ ^ 2 := by
  have hM : 0 < iterationBound γ :=
    Nat.pos_of_ne_zero (iterationBound_ne_zero hγ)
  rw [finalB_success_exact hM V U a₀ o S hV]
  linarith [trialFail_pow_le_error (prepOf U o (fun z => S z = true)) hγ hp hη]

/-- One physical oracle per logical read, with the same initialized circuit
and arbitrary future continuation. -/
theorem finalB_physical_on_embedding {ι : Type} [Fintype ι] [Inhabited ι]
    {M N n w : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z) (hF : IsCirc n F)
    (o : Z) (S : Z → Bool)
    (e : FinalBasis N M Z ↪ Fin (w + 1)) :
    ∃ K : AdaptiveProgram ι w → AdaptiveProgram ι w,
      ∀ next, (K next).queryCap ≤ N * ((2 * (M - 1) + 1) * n) + next.queryCap ∧
        ∀ x ψ b, (K next).outputMass x (clEmb e ψ) b =
          next.outputMass x
            (clEmb e (finalB (N := N) V (F x) o S ψ)) b := by
  exact physicalContinuation_on_embedding (finalB_isCirc V F hF o S) e

end QuarticQuery.Upper
end

module

public import QuarticQuery.Upper.FinalBScalarPhysical

/-! Authored direct agreement target for round-four return 04's uniform
opaque amplifier. It imports the circuit and state definitions but not the
proof module. The intentional `sorry` is not a proof. This shares the
maintained vocabulary and is not an independent semantic review. -/

@[expose] public section
namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {Z : Type} [Fintype Z]

theorem uniformOpaqueAmplifier
    (o : Z) (S : Z → Bool) {γ η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    let M := iterationBound γ
    let N := trialCount η
    let a₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (iterationBound_ne_zero hγ)⟩
    ∃ V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M),
      V (rket a₀) = choiceState M ∧
      (∀ (ι : Type) [Nonempty ι] (n : ℕ)
          (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z),
          IsCirc n F →
          IsCirc (N * ((2 * (M - 1) + 1) * n))
            (fun x => finalB (N := N) V (F x) o S)) ∧
      ∀ U : Reg Z ≃ₗᵢ[ℂ] Reg Z,
        let A := prepOf U o (fun z => S z = true)
        let ψ := finalB (N := N) V U o S
          (rket (finalOrigin (N := N) a₀ o))
        let ξ := assembledOriginalAux (N := N) (⟨a₀, o⟩ : AmpTrial M Z) S
          (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)
          (fun _ => trialSelectorGood A V a₀)
        coordProj (finalSuccess (M := M) (N := N) (Z := Z)) ψ =
            retainedProduct ξ A.goodState ∧
        ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z)) ψ‖ ^ 2 =
            1 - A.trialFail M ^ N ∧
        (A.prob = 0 →
          coordProj (finalSuccess (M := M) (N := N) (Z := Z)) ψ = 0) ∧
        (0 < A.prob → A.prob / 2 ≤
          ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z)) ψ‖ ^ 2) ∧
        (0 < A.prob → ‖ξ‖ ^ 2 =
          ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z)) ψ‖ ^ 2) ∧
        (γ ≤ A.prob → 1 - η ≤
          ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z)) ψ‖ ^ 2) ∧
        (∀ (b : Fin N → Bool) (a : Fin M) (y : Fin N → AmpTrial M Z),
          firstSuccess b = none → ξ.ofLp (b, (a, y)) = 0) ∧
        coordProj (fun p : FinalAux N M Z =>
          (firstSuccess p.1).isSome = true) ξ = ξ := by
  sorry

end QuarticQuery.Upper
end

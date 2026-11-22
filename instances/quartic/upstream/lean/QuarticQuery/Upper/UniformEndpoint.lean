module

public import QuarticQuery.Upper.FinalBScalarPhysical

/-! A single choice of the selector gate precedes the quantification over
oracle inputs. Every clause below concerns the same fixed final circuit. -/

@[expose] public section
namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {Z : Type} [Fintype Z]

/-- The bounded coherent amplifier, with a fixed choice gate and a literal
original `Z` subsystem. Its success vector is factored even at zero good
mass; the scalar statements and circuit certificate concern the same `B`. -/
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
  classical
  dsimp only
  let M := iterationBound γ
  let N := trialCount η
  have hM : 0 < M := Nat.pos_of_ne_zero (iterationBound_ne_zero hγ)
  have hN : 0 < N := trialCount_pos hη hηhalf
  let a₀ : Fin M := ⟨0, hM⟩
  obtain ⟨V, hV⟩ := exists_choiceGate hM a₀
  refine ⟨V, hV, ?_, ?_⟩
  · intro ι _ n F hF
    exact finalB_isCirc (N := N) V F hF o S
  intro U
  refine ⟨finalB_retained_original hM V U a₀ o S,
    finalB_success_exact hM V U a₀ o S hV, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hp0
    have hz := finalB_success_zero (N := N) hM V U a₀ o S hV hp0
    have hn : ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z))
        (finalB (N := N) V U o S
          (rket (finalOrigin (N := N) a₀ o)))‖ = 0 := by
      nlinarith [norm_nonneg (coordProj
        (finalSuccess (M := M) (N := N) (Z := Z))
        (finalB (N := N) V U o S
          (rket (finalOrigin (N := N) a₀ o))))]
    exact norm_eq_zero.mp hn
  · intro _
    exact finalB_success_gain hM hN V U a₀ o S hV
  · intro hp
    have h := finalB_success_norm_sq (N := N) hM V U a₀ o S
    rw [(prepOf U o (fun z => S z = true)).norm_goodState hp] at h
    simpa using h.symm
  · intro hp
    exact finalB_success_error U o S hγ hp hη V a₀ hV
  · intro b a y hb
    exact finalB_aux_no_success V U a₀ o S b a y hb
  · classical
    ext ⟨b, ⟨a, y⟩⟩
    rw [coordProj_apply]
    cases hb : firstSuccess b with
    | none =>
        have hz := finalB_aux_no_success V U a₀ o S b a y hb
        simpa [hb] using hz.symm
    | some j => simp

end QuarticQuery.Upper
end

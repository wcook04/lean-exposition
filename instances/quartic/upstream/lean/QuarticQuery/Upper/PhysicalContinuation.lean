module

public import QuarticQuery.Paper.ReadSpecOneQuery

/-! A uniform physical continuation wrapper for a fixed logical isometry.
The final amplifier can instantiate this with its own `B` and its exact
retained original-subsystem state theorem. -/

public section
namespace QuarticQuery.Upper

variable {ι Y : Type} [Fintype ι] [Inhabited ι] [Fintype Y]

/-- The compiler works for every chosen embedding of the same logical state,
and the same physical program works for every input, state and continuation.
The original register is retained as the encoded logical subsystem `clEmb e`. -/
theorem physicalContinuation_on_embedding {c w : ℕ}
    {B : BitInput ι → Reg Y ≃ₗᵢ[ℂ] Reg Y}
    (hB : IsCirc c B) (e : Y ↪ Fin (w + 1)) :
    ∃ K : AdaptiveProgram ι w → AdaptiveProgram ι w,
      ∀ next, (K next).queryCap ≤ c + next.queryCap ∧
        ∀ x ψ b, (K next).outputMass x (clEmb e ψ) b =
          next.outputMass x (clEmb e (B x ψ)) b :=
  compile_circ_one e hB

theorem physicalContinuation_of_isCirc {c : ℕ}
    {B : BitInput ι → Reg Y ≃ₗᵢ[ℂ] Reg Y}
    (hB : IsCirc c B) :
    ∃ (w : ℕ) (e : Y ↪ Fin (w + 1))
      (K : AdaptiveProgram ι w → AdaptiveProgram ι w),
      ∀ next, (K next).queryCap ≤ c + next.queryCap ∧
        ∀ x ψ b, (K next).outputMass x (clEmb e ψ) b =
          next.outputMass x (clEmb e (B x ψ)) b := by
  classical
  let w := Fintype.card Y
  have hcard : Fintype.card Y ≤ Fintype.card (Fin (w + 1)) := by
    simp only [Fintype.card_fin]
    exact Nat.le_succ _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨K, hK⟩ := physicalContinuation_on_embedding hB e
  exact ⟨w, e, K, hK⟩

end QuarticQuery.Upper
end

import Breakdown.CertCell.CertificateStatements

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

theorem stateTerminalTest : StateTerminalTest := by
  intro V A B _ _ Q v₀ z₀ L Ψ E P hQ hS hE hcard hpos x
  classical
  obtain ⟨hz₀, hbound⟩ := hS
  let N := {i : A // i ∉ E}
  let r : (A ⊕ B → ℝ) →ₗ[ℝ] (N ⊕ B → ℝ) := LinearMap.funLeft ℝ ℝ (Sum.map Subtype.val id)
  let s : (B → ℝ) →ₗ[ℝ] (A ⊕ B → ℝ) :=
    { toFun := fun u => Sum.elim (L *ᵥ u) u
      map_add' := fun u w => by
        funext k
        cases k <;> simp [Matrix.mulVec_add]
      map_smul' := fun c u => by
        funext k
        cases k <;> simp [Matrix.mulVec_smul] }
  let G : (P × (B → ℝ)) →ₗ[ℝ] (N ⊕ B → ℝ) :=
    r ∘ₗ P.subtype ∘ₗ LinearMap.fst ℝ P (B → ℝ) - r ∘ₗ s ∘ₗ LinearMap.snd ℝ P (B → ℝ)
  have hsame : ∀ y w : A ⊕ B → ℝ, r y = r w → quadValue Ψ y = quadValue Ψ w := by
    intro y w h
    refine hE y w (fun i hi => ?_) (fun j => ?_)
    · simpa [r, LinearMap.funLeft_apply] using congrFun h (Sum.inl ⟨i, hi⟩)
    · simpa [r, LinearMap.funLeft_apply] using congrFun h (Sum.inr j)
  have hneg : ∀ u, quadValue Ψ (s u) ≤ 0 := by
    intro u
    have h := hbound v₀ u
    rw [hz₀, zero_add] at h
    exact h.trans hQ
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨p, hp⟩, u⟩ hG
    have hr : r p = r (s u) := sub_eq_zero.mp hG
    have hp0 : p = 0 := by
      by_contra hne
      have h1 := hpos p hp hne
      have h2 := hsame _ _ hr
      have h3 := hneg u
      linarith
    subst hp0
    have hu : u = 0 := by
      funext j
      simpa [r, s, LinearMap.funLeft_apply] using (congrFun hr (Sum.inr j)).symm
    subst hu
    rfl
  have hsurj : Function.Surjective G := by
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hN : Fintype.card N + E.card = Fintype.card A := by
      have h1 : Fintype.card N = Fintype.card A - Fintype.card {i : A // i ∈ E} :=
        Fintype.card_subtype_compl _
      have h2 : Fintype.card {i : A // i ∈ E} = E.card := Fintype.card_coe E
      have h3 : E.card ≤ Fintype.card A := Finset.card_le_univ E
      omega
    have hge : Module.finrank ℝ (N ⊕ B → ℝ) ≤ Module.finrank ℝ (P × (B → ℝ)) := by
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
      omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle hge)).mp hinj
  obtain ⟨⟨⟨p, hp⟩, u⟩, hG⟩ := hsurj (r (Sum.elim (z₀ x) 0))
  have hG' : r p - r (s u) = r (Sum.elim (z₀ x) 0) := hG
  have hsplit : (Sum.elim (z₀ x + L *ᵥ u) u : A ⊕ B → ℝ) = Sum.elim (z₀ x) 0 + s u := by
    funext k
    cases k <;> simp [s]
  have hr : r p = r (Sum.elim (z₀ x + L *ᵥ u) u) := by
    rw [hsplit, map_add, ← hG']
    abel
  have hnn : 0 ≤ quadValue Ψ p := by
    by_cases h0 : p = 0
    · simp [h0, quadValue]
    · exact (hpos p hp h0).le
  rw [hsame _ _ hr] at hnn
  exact hnn.trans (hbound x u)

end Breakdown.CertCell.Certificate

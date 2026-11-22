import PCP.Complexity.NaturalListEncoding
import PCP.Complexity.MachineComposition

/-! # Polynomial-time maps and their composition -/

namespace PCP.Machine

open PCP

/-- **A polynomial-time map** between encoded objects, in the concrete `FinTM2` model. -/
def PolyTimeMap {α β : Type} (ea : α → List Sym) (eb : β → List Sym) (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- Polynomial-time maps compose using a concrete sequential machine at the fixed encodings. -/
theorem PolyTimeMap.comp {α β γ : Type} {ea : α → List Sym} {eb : β → List Sym}
    {ec : γ → List Sym} {f : α → β} {g : β → γ} (hf : PolyTimeMap ea eb f)
    (hg : PolyTimeMap eb ec g) : PolyTimeMap ea ec (g ∘ f) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact ⟨composeWitness hf hg⟩

end PCP.Machine

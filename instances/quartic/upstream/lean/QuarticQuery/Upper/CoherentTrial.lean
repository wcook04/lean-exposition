module

public import QuarticQuery.Upper.Amplify
public import QuarticQuery.Paper.QuantumTensor

/-!
Executable-circuit seam.
The theorem gives a single coherent circuit for a superposition
of iteration labels and all fresh trials. It does not assert the final
success marking, routing permutation, or retained-state theorem.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {ι Λ Z : Type} [Nonempty ι] [Fintype Λ] [Fintype Z]

/-- One label preparation, followed by the branch's Grover word. `V` is fixed
independently of the oracle. All branches see the same input `x`. -/
noncomputable def coherentTrial
    (V : Reg Λ ≃ₗᵢ[ℂ] Reg Λ)
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Prop) (C : Λ → Amplification.Circuit)
    (x : BitInput ι) :
    Reg (Σ _ : Λ, Z) ≃ₗᵢ[ℂ] Reg (Σ _ : Λ, Z) :=
  (leftOp V).trans (sigmaOp fun a => circU (F x) o S (C a))

/-- Exact logical read cap: branch circuits are padded to `q` using an idle
read, then `IsCirc.sigma` implements genuine coherent control. -/
theorem coherentTrial_isCirc
    (V : Reg Λ ≃ₗᵢ[ℂ] Reg Λ)
    {n q : ℕ} (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : IsCirc n F) (o : Z) (S : Z → Prop)
    (C : Λ → Amplification.Circuit)
    (hcap : ∀ a, (C a).calls * n ≤ q) :
    IsCirc q (coherentTrial V F o S C) := by
  have hbranches : ∀ a, IsCirc q (fun x => circU (F x) o S (C a)) :=
    fun a => (isCirc_circU hF o S (C a)).mono (hcap a)
  have hleft : IsCirc 0 (fun _ : BitInput ι => leftOp (W := Z) V) := IsCirc.gate _
  have h := hleft.comp (IsCirc.sigma hbranches)
  change IsCirc q (fun x =>
    (leftOp V).trans (sigmaOp fun a => circU (F x) o S (C a)))
  simpa only [Nat.zero_add] using h

/-- The same coherent trial on `N` disjoint complete registers; no measurement
or restart is used. The output still contains all trial labels and workspaces. -/
theorem coherentTrials_isCirc
    (V : Reg Λ ≃ₗᵢ[ℂ] Reg Λ)
    {n q : ℕ} (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : IsCirc n F) (o : Z) (S : Z → Prop)
    (C : Λ → Amplification.Circuit)
    (hcap : ∀ a, (C a).calls * n ≤ q) (N : ℕ) :
    IsCirc (N * q) (fun x =>
      QuarticQuery.Paper.tensorPreparation
        (fun _ => coherentTrial V F o S C x) N) := by
  exact QuarticQuery.Paper.tensorPreparation_isCirc
    (fun _ => coherentTrial V F o S C)
    (fun _ => coherentTrial_isCirc V F hF o S C hcap) N

end QuarticQuery.Upper

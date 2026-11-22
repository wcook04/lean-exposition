module

public import QuarticQuery.Upper.OpaqueSlot
public import QuarticQuery.Upper.GateStateDefs
public import QuarticQuery.Paper.TensorCoordinates

/-!
One globally named, uniform coherent amplifier circuit on the fixed enlarged
register. The whole selector+original register is one trial basis W. The
success predicate tests only its original Z component. The final output
reassociation into a literal fixed Z subsystem is in a downstream theorem.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Paper

abbrev AmpTrial (M : ℕ) (Z : Type) := Σ _ : Fin M, Z
abbrev AmpFlags (N : ℕ) := Fin N → Bool
abbrev AmpRaw (N : ℕ) (W : Type) :=
  Σ _ : AmpFlags N, Σ _ : W, TensorBasis W N

def rawToRoute {N : ℕ} {W : Type} :
    AmpRaw N W ≃ MarkRouteBasis N W where
  toFun p := (p.1, (p.2.1, (tensorCoordEquiv N).toFun p.2.2))
  invFun p := ⟨p.1, ⟨p.2.1, (tensorCoordEquiv N).symm.toFun p.2.2⟩⟩
  left_inv p := by cases p with | mk b q => cases q; simp
  right_inv p := by cases p with | mk b q => cases q; simp

variable {ι Z : Type} [Fintype Z] [Nonempty ι]

/-- The fixed, label-uniform opaque schedule after a fixed selector gate. -/
noncomputable def ampTrialGate {M : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) :
    Reg (AmpTrial M Z) ≃ₗᵢ[ℂ] Reg (AmpTrial M Z) :=
  (leftOp V).trans (opaquePrefix U o S (fun r a => r < a.val) (M - 1))

theorem ampTrialGate_isCirc {M n : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : IsCirc n F) (o : Z) (S : Z → Prop) :
    IsCirc ((2 * (M - 1) + 1) * n)
      (fun x => ampTrialGate V (F x) o S) := by
  have hV : IsCirc 0 (fun _ : BitInput ι => leftOp (W := Z) V) := IsCirc.gate _
  have h := hV.comp (opaquePrefix_isCirc F hF o S
    (fun (r : ℕ) (a : Fin M) => r < a.val) (M - 1))
  change IsCirc ((2 * (M - 1) + 1) * n)
    (fun x => (leftOp V).trans
      (opaquePrefix (F x) o S (fun (r : ℕ) (a : Fin M) => r < a.val) (M - 1)))
  simpa only [Nat.zero_add] using h

/-- Run all N complete trial registers under one fixed schedule, retaining
the output register and flag register in basis states. -/
noncomputable def rawAmpCircuit {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop) :
    Reg (AmpRaw N (AmpTrial M Z)) ≃ₗᵢ[ℂ]
      Reg (AmpRaw N (AmpTrial M Z)) :=
  sigmaOp fun _ : AmpFlags N => sigmaOp fun _ : AmpTrial M Z =>
    tensorPreparation (fun _ => ampTrialGate V U o S) N

/-- The very same circuit, with reversible flag marking and routing.
The output coordinate still belongs to W=selector×original state. -/
noncomputable def ampCircuit {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Bool) :
    Reg (MarkRouteBasis N (AmpTrial M Z)) ≃ₗᵢ[ℂ]
      Reg (MarkRouteBasis N (AmpTrial M Z)) :=
  ((regCongr (rawToRoute (N := N) (W := AmpTrial M Z))).symm.trans
      ((rawAmpCircuit V U o (fun z => S z = true)).trans
        (regCongr (rawToRoute (N := N) (W := AmpTrial M Z))))).trans
    (markWholeGate (fun p => S p.2)) |>.trans routeFlagsGate

theorem ampCircuit_isCirc {M N n : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (hF : IsCirc n F) (o : Z) (S : Z → Bool) :
    IsCirc (N * ((2 * (M - 1) + 1) * n))
      (fun x => ampCircuit (N := N) V (F x) o S) := by
  let q := (2 * (M - 1) + 1) * n
  have ht : IsCirc q (fun x => ampTrialGate V (F x) o (fun z => S z = true)) :=
    ampTrialGate_isCirc V F hF o _
  have hT : IsCirc (N * q) (fun x =>
      tensorPreparation (fun _ => ampTrialGate V (F x) o (fun z => S z = true)) N) :=
    tensorPreparation_isCirc
      (fun _ x => ampTrialGate V (F x) o (fun z => S z = true))
      (fun _ => ht) N
  have hRaw : IsCirc (N * q) (fun x =>
      rawAmpCircuit (N := N) V (F x) o (fun z => S z = true)) := by
    change IsCirc (N * q) (fun x => sigmaOp fun _ : AmpFlags N =>
      sigmaOp fun _ : AmpTrial M Z =>
        tensorPreparation (fun _ => ampTrialGate V (F x) o (fun z => S z = true)) N)
    exact IsCirc.sigma (fun _ : AmpFlags N =>
      IsCirc.sigma (fun _ : AmpTrial M Z => hT))
  have hRoute := hRaw.congr (rawToRoute (N := N) (W := AmpTrial M Z))
  have hMark := hRoute.post (markWholeGate (fun p : AmpTrial M Z => S p.2))
  have hFinal := hMark.post (routeFlagsGate (N := N) (Z := AmpTrial M Z))
  change IsCirc (N * q) (fun x => ampCircuit (N := N) V (F x) o S)
  exact hFinal

end QuarticQuery.Upper

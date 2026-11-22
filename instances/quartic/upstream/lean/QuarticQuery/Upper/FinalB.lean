module

public import QuarticQuery.Upper.LiftTrialsState
public import QuarticQuery.Upper.RetainedOriginal

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Paper

abbrev FinalAux (N M : ℕ) (Z : Type) :=
  (Fin N → Bool) × (Fin M × (Fin N → AmpTrial M Z))

abbrev FinalBasis (N M : ℕ) (Z : Type) := Σ _ : FinalAux N M Z, Z

variable {Z : Type} [Fintype Z]

/-- The fixed initial basis has one original Z subsystem and all auxiliary
selectors, flags, and trial workspaces in named positions. -/
def finalOrigin {M N : ℕ} (a₀ : Fin M) (o : Z) : FinalBasis N M Z :=
  retainedOriginalReassoc (ampOrigin (N := N) a₀ o)

/-- One uniform amplifier circuit acting on the literal fixed original Z
subsystem and a finite auxiliary register. -/
noncomputable def finalB {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Bool) :
    Reg (FinalBasis N M Z) ≃ₗᵢ[ℂ] Reg (FinalBasis N M Z) :=
  (regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))).symm.trans
    ((ampCircuit (N := N) V U o S).trans
      (regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))))

theorem finalB_isCirc {ι : Type} [Nonempty ι] {M N n : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (F : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z) (hF : IsCirc n F)
    (o : Z) (S : Z → Bool) :
    IsCirc (N * ((2 * (M - 1) + 1) * n))
      (fun x => finalB (N := N) V (F x) o S) := by
  have h := ampCircuit_isCirc (N := N) V F hF o S
  change IsCirc (N * ((2 * (M - 1) + 1) * n))
    (fun x =>
      (regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))).symm.trans
        ((ampCircuit (N := N) V (F x) o S).trans
          (regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z)))))
  exact h.congr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))

theorem finalB_state {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool) :
    finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o)) =
      regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))
        (assembledTrials (⟨a₀, o⟩ : AmpTrial M Z)
          (fun p => S p.2)
          (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)) := by
  have hr := regCongr_rket
    (retainedOriginalReassoc (N := N) (M := M) (Z := Z))
    (ampOrigin (N := N) a₀ o)
  change (regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))).symm.trans
      ((ampCircuit (N := N) V U o S).trans
        (regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))))
      (rket (retainedOriginalReassoc (ampOrigin (N := N) a₀ o))) = _
  rw [← hr, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply,
    ampCircuit_state]
  rfl

def finalSuccess {M N : ℕ} {Z : Type} (p : FinalBasis N M Z) : Prop :=
  (firstSuccess p.1.1).isSome = true

/-- The success event of the initialized final circuit is exactly the
success projection of the marked and routed trial state. -/
theorem finalB_success_eq {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool) :
    coordProj (finalSuccess (M := M) (N := N) (Z := Z))
      (finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o))) =
      regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))
        (assembledSuccess (⟨a₀, o⟩ : AmpTrial M Z)
          (fun p => S p.2)
          (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)) := by
  classical
  rw [finalB_state]
  ext ⟨⟨b, ⟨a, y⟩⟩, z⟩
  simp [coordProj_apply, finalSuccess, regCongr_apply, assembledSuccess,
    retainedOriginalReassoc]

theorem finalB_norm {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool) :
    ‖finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o))‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, norm_rket]

/-- On the success event the same circuit leaves the original Z register in
its normalized good state; all selector/flag/history information is auxiliary. -/
theorem finalB_retained_original {M N : ℕ} (hM : 0 < M)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool) :
    coordProj (finalSuccess (M := M) (N := N) (Z := Z))
      (finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o))) =
    retainedProduct
      (assembledOriginalAux (⟨a₀, o⟩ : AmpTrial M Z) S
        (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)
        (fun _ => trialSelectorGood (prepOf U o (fun z => S z = true)) V a₀))
      (prepOf U o (fun z => S z = true)).goodState := by
  classical
  rw [finalB_success_eq]
  exact opaqueTrials_retained_original hM U o S V a₀

theorem finalB_success_norm_sq {M N : ℕ} (hM : 0 < M)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool) :
    ‖coordProj (finalSuccess (M := M) (N := N) (Z := Z))
      (finalB (N := N) V U o S (rket (finalOrigin (N := N) a₀ o)))‖ ^ 2 =
      ‖assembledOriginalAux (N := N) (⟨a₀, o⟩ : AmpTrial M Z) S
        (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)
        (fun _ => trialSelectorGood (prepOf U o (fun z => S z = true)) V a₀)‖ ^ 2 *
        ‖(prepOf U o (fun z => S z = true)).goodState‖ ^ 2 := by
  rw [finalB_retained_original hM, retainedProduct_norm_sq]

theorem finalB_aux_no_success {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool)
    (b : Fin N → Bool) (a : Fin M) (y : Fin N → AmpTrial M Z)
    (h : firstSuccess b = none) :
    (assembledOriginalAux (⟨a₀, o⟩ : AmpTrial M Z) S
      (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)
      (fun _ => trialSelectorGood (prepOf U o (fun z => S z = true)) V a₀)).ofLp
        (b, (a, y)) = 0 := by
  exact assembledOriginalAux_no_success _ _ _ _ _ _ _ h

end QuarticQuery.Upper

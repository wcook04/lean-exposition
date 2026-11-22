module

public import QuarticQuery.Upper.LiftTrials

/-! State identification for the single fixed amplifier circuit. -/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Paper
open Classical

variable {Z : Type} [Fintype Z]

def ampOrigin {M N : ℕ} (a₀ : Fin M) (o : Z) :
    MarkRouteBasis N (AmpTrial M Z) :=
  (fun _ => false, (⟨a₀, o⟩, fun _ => ⟨a₀, o⟩))

def rawOrigin {M N : ℕ} (a₀ : Fin M) (o : Z) :
    AmpRaw N (AmpTrial M Z) :=
  ⟨fun _ => false, ⟨⟨a₀, o⟩, tensorOrigin ⟨a₀, o⟩ N⟩⟩

theorem rawToRoute_origin {M N : ℕ} (a₀ : Fin M) (o : Z) :
    rawToRoute (rawOrigin (N := N) a₀ o) = ampOrigin (N := N) a₀ o := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact tensorCoordEquiv_origin (⟨a₀, o⟩ : AmpTrial M Z) N

/-- A fixed initial product basis state becomes N copies of the same complete
trial state, with flags and the designated output untouched. -/
theorem rawAmpCircuit_state {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Prop)
    (b : AmpFlags N) (w : AmpTrial M Z) (t : TensorBasis (AmpTrial M Z) N) :
    (rawAmpCircuit (N := N) V U o S (rket (rawOrigin (N := N) a₀ o))).ofLp
        ⟨b, ⟨w, t⟩⟩ =
      if b = (fun _ => false) ∧ w = (⟨a₀, o⟩ : AmpTrial M Z) then
        (tensorVector (fun _ => ampTrialGate V U o S (rket ⟨a₀, o⟩)) N).ofLp t
      else 0 := by
  classical
  by_cases hb : b = (fun _ => false)
  · subst b
    by_cases hw : w = (⟨a₀, o⟩ : AmpTrial M Z)
    · subst w
      change (sigmaOp (fun _ : AmpFlags N => sigmaOp fun _ : AmpTrial M Z =>
          tensorPreparation (fun _ => ampTrialGate V U o S) N)
          (rket ⟨(fun _ => false), ⟨⟨a₀, o⟩,
            tensorOrigin ⟨a₀, o⟩ N⟩⟩)).ofLp
          ⟨(fun _ => false), ⟨⟨a₀, o⟩, t⟩⟩ = _
      rw [sigmaOp_apply, slice_rket_same, sigmaOp_apply, slice_rket_same,
        tensorPreparation_state]
      simp
    · change (sigmaOp (fun _ : AmpFlags N => sigmaOp fun _ : AmpTrial M Z =>
          tensorPreparation (fun _ => ampTrialGate V U o S) N)
          (rket ⟨(fun _ => false), ⟨⟨a₀, o⟩,
            tensorOrigin ⟨a₀, o⟩ N⟩⟩)).ofLp
          ⟨(fun _ => false), ⟨w, t⟩⟩ = _
      rw [sigmaOp_apply, slice_rket_same, sigmaOp_apply, slice_rket_ne hw]
      simp [hw]
  · change (sigmaOp (fun _ : AmpFlags N => sigmaOp fun _ : AmpTrial M Z =>
        tensorPreparation (fun _ => ampTrialGate V U o S) N)
        (rket ⟨(fun _ => false), ⟨⟨a₀, o⟩,
          tensorOrigin ⟨a₀, o⟩ N⟩⟩)).ofLp ⟨b, ⟨w, t⟩⟩ = _
    rw [sigmaOp_apply, slice_rket_ne hb]
    simp [hb]

/-- The pre-marker state of the very same `ampCircuit` is the `startTrials`
vector used by the verified route/factor and success-mass modules. -/
theorem ampCircuit_state {M N : ℕ}
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (a₀ : Fin M) (o : Z) (S : Z → Bool) :
    ampCircuit (N := N) V U o S (rket (ampOrigin (N := N) a₀ o)) =
      assembledTrials (⟨a₀, o⟩ : AmpTrial M Z)
        (fun p => S p.2)
        (fun _ => ampTrialGate V U o (fun z => S z = true) (rket ⟨a₀, o⟩)) := by
  classical
  have he := rawToRoute_origin (N := N) a₀ o
  have hstart :
      (regCongr (rawToRoute (N := N) (W := AmpTrial M Z))).symm
        (rket (ampOrigin (N := N) a₀ o)) =
      rket (rawOrigin (N := N) a₀ o) := by
    apply (regCongr (rawToRoute (N := N) (W := AmpTrial M Z))).injective
    rw [LinearIsometryEquiv.apply_symm_apply, regCongr_rket, he]
  unfold ampCircuit assembledTrials
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, hstart]
  congr 1
  congr 1
  ext ⟨b, ⟨w, ys⟩⟩
  change ((regCongr (rawToRoute (N := N) (W := AmpTrial M Z)))
    (rawAmpCircuit (N := N) V U o (fun z => S z = true)
      (rket (rawOrigin (N := N) a₀ o)))).ofLp (b, (w, ys)) = _
  rw [regCongr_apply]
  change (rawAmpCircuit (N := N) V U o (fun z => S z = true)
      (rket (rawOrigin (N := N) a₀ o))).ofLp
        ⟨b, ⟨w, (tensorCoordEquiv N).symm.toFun ys⟩⟩ = _
  rw [rawAmpCircuit_state]
  simp only [startTrials]
  by_cases hb : b = (fun _ => false)
  · have hb' : ∀ i, b i = false := by simpa [hb]
    simp [hb, hb', tensorVector_coord_product]
  · have hb' : ¬ ∀ i, b i = false := by
      intro h; exact hb (funext h)
    simp [hb, hb']

end QuarticQuery.Upper

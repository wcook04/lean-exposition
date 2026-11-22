module

public import QuarticQuery.Upper.OpaqueSlot
public import QuarticQuery.Upper.RetainedFactor

/-!
One fixed opaque schedule, one retained selector, one complete original H.
Compiled as part of the `QuarticQuery` library target.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {Z : Type} [Fintype Z]

noncomputable def opaqueTrialVector {M : ℕ}
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M) :
    Reg (Σ _ : Fin M, Z) :=
  opaquePrefix U o S (fun r a => r < a.val) (M - 1)
    (leftOp V (rket ⟨a₀, o⟩))

noncomputable def trialSelectorGood {M : ℕ}
    (A : Preparation (Reg Z)) (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M))
    (a₀ : Fin M) : Reg (Fin M) :=
  WithLp.toLp 2 fun a => (V (rket a₀)).ofLp a *
    (Real.sin ((2 * a.val + 1) * A.angle) : ℂ)

/-- The original normalized good state factors from the selector already
after one trial's success projection. Selector amplitudes may have either sign. -/
theorem opaqueTrial_good_factor {M : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Prop)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M) :
    coordProj (fun p : Σ _ : Fin M, Z => S p.2)
      (opaqueTrialVector U o S V a₀) =
      retainedProduct (trialSelectorGood (prepOf U o S) V a₀)
        (prepOf U o S).goodState := by
  classical
  ext ⟨a, z⟩
  have hslice := slice_opaquePrefix_full U o S hM
    (leftOp V (rket ⟨a₀, o⟩)) a
  rw [slice_leftOp_rket, map_smul, circU_apply] at hslice
  have hs : (opaqueTrialVector U o S V a₀).ofLp ⟨a, z⟩ =
      (V (rket a₀)).ofLp a * ((prepOf U o S).iterate a.val).ofLp z := by
    have h := congrArg (fun v : Reg Z => v.ofLp z) hslice
    change (opaqueTrialVector U o S V a₀).ofLp ⟨a, z⟩ =
      (V (rket a₀)).ofLp a *
        (Amplification.Circuit.run (prepOf U o S)
          (Amplification.groverCircuit a.val) (rket o)).ofLp z
    simpa [opaqueTrialVector, slice_apply,
      PiLp.smul_apply, smul_eq_mul] using h
  have hgood := congrArg (fun v : Reg Z => v.ofLp z)
    ((prepOf U o S).good_iterate a.val)
  by_cases hz : S z
  · have hgz : ((prepOf U o S).iterate a.val).ofLp z =
        (Real.sin ((2 * a.val + 1) * (prepOf U o S).angle) : ℂ) *
          (prepOf U o S).goodState.ofLp z := by
      simpa [prepOf, coordProj_apply, hz, PiLp.smul_apply, smul_eq_mul] using hgood
    simp [coordProj_apply, hz, retainedProduct_apply, trialSelectorGood, hs, hgz]
    ring
  · have hz0 : (prepOf U o S).goodState.ofLp z = 0 := by
      change (normalised (coordProj S (U (rket o)))).ofLp z = 0
      simp [normalised, coordProj_apply, hz]
    simp [coordProj_apply, hz, retainedProduct_apply, hz0]

end QuarticQuery.Upper

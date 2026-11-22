module

public import QuarticQuery.Upper.GateState
public import QuarticQuery.Upper.OneTrialFactor

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {N M : ℕ} {Z : Type} [Fintype Z]

abbrev OriginalTrial (M : ℕ) (Z : Type) := Σ _ : Fin M, Z

/-- Move the selector of the routed output into the auxiliary register;
the original Z coordinate is literally the final subsystem. -/
def retainedOriginalReassoc :
    MarkRouteBasis N (OriginalTrial M Z) ≃
      Σ _ : ((Fin N → Bool) × (Fin M × (Fin N → OriginalTrial M Z))), Z where
  toFun p := ⟨(p.1, (p.2.1.1, p.2.2)), p.2.1.2⟩
  invFun p := (p.1.1, (⟨p.1.2.1, p.2⟩, p.1.2.2))
  left_inv p := by rcases p with ⟨b, ⟨⟨a, z⟩, y⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨b, ⟨a, y⟩⟩, z⟩; rfl

open Classical in
noncomputable def routedOriginalAuxCoeff (o : OriginalTrial M Z) (S : Z → Bool)
    (v : Fin N → Reg (OriginalTrial M Z)) (q : Fin N → Reg (Fin M))
    (b : Fin N → Bool) (a : Fin M) (y : Fin N → OriginalTrial M Z) : ℂ :=
  match firstSuccess b with
  | none => 0
  | some j =>
      if y j = o ∧ ∀ i, i ≠ j → b i = S (y i).2 then
        (q j).ofLp a * ∏ i ∈ Finset.univ.filter (· ≠ j), (v i).ofLp (y i)
      else 0

noncomputable def assembledOriginalAux (o : OriginalTrial M Z) (S : Z → Bool)
    (v : Fin N → Reg (OriginalTrial M Z)) (q : Fin N → Reg (Fin M)) :
    Reg ((Fin N → Bool) × (Fin M × (Fin N → OriginalTrial M Z))) :=
  WithLp.toLp 2 fun p => routedOriginalAuxCoeff o S v q p.1 p.2.1 p.2.2

theorem assembledOriginalAux_no_success (o : OriginalTrial M Z) (S : Z → Bool)
    (v : Fin N → Reg (OriginalTrial M Z)) (q : Fin N → Reg (Fin M))
    (b : Fin N → Bool) (a : Fin M) (y : Fin N → OriginalTrial M Z)
    (h : firstSuccess b = none) :
    (assembledOriginalAux o S v q).ofLp (b, (a, y)) = 0 := by
  simp [assembledOriginalAux, routedOriginalAuxCoeff, h]

/-- A selected complete trial contributes its selector amplitude to the
auxiliary subsystem and the same original good vector to the fixed output. -/
theorem routedSuccessCoord_original_factor
    (o : OriginalTrial M Z) (S : Z → Bool)
    (v : Fin N → Reg (OriginalTrial M Z)) (q : Fin N → Reg (Fin M))
    (g : Reg Z)
    (hgood : ∀ j a z, S z = true → (v j).ofLp ⟨a, z⟩ = (q j).ofLp a * g.ofLp z)
    (hsupport : ∀ z, S z = false → g.ofLp z = 0)
    (b : Fin N → Bool) (a : Fin M) (y : Fin N → OriginalTrial M Z) (z : Z) :
    routedSuccessCoord o (fun p => S p.2) v b y ⟨a, z⟩ =
      routedOriginalAuxCoeff o S v q b a y * g.ofLp z := by
  classical
  unfold routedSuccessCoord routedOriginalAuxCoeff
  cases h : firstSuccess b with
  | none => simp
  | some j =>
      by_cases hz : S z = true
      · by_cases hc : y j = o ∧ ∀ i, i ≠ j → b i = S (y i).2
        · simp [routeCondition, hz, hc, hgood j a z hz]
          ring
        · simp [routeCondition, hz, hc]
      · have hf : S z = false := by cases hsz : S z <;> simp_all
        have hg := hsupport z hf
        simp [routeCondition, hz, hg]

theorem assembledSuccess_original_factor
    (o : OriginalTrial M Z) (S : Z → Bool)
    (v : Fin N → Reg (OriginalTrial M Z)) (q : Fin N → Reg (Fin M))
    (g : Reg Z)
    (hgood : ∀ j a z, S z = true → (v j).ofLp ⟨a, z⟩ = (q j).ofLp a * g.ofLp z)
    (hsupport : ∀ z, S z = false → g.ofLp z = 0) :
    regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))
      (assembledSuccess o (fun p => S p.2) v) =
      retainedProduct (assembledOriginalAux o S v q) g := by
  classical
  ext ⟨⟨b, ⟨a, y⟩⟩, z⟩
  rw [regCongr_apply]
  change (assembledSuccess o (fun p => S p.2) v).ofLp (b, (⟨a, z⟩, y)) = _
  rw [assembledSuccess_apply]
  exact routedSuccessCoord_original_factor o S v q g hgood hsupport b a y z

/-- Specialize the coordinate factor to the actual opaque Grover trial vector;
this includes zero-success inputs and keeps the original Z register intact. -/
theorem opaqueTrials_retained_original {M N : ℕ} (hM : 0 < M)
    (U : Reg Z ≃ₗᵢ[ℂ] Reg Z) (o : Z) (S : Z → Bool)
    (V : Reg (Fin M) ≃ₗᵢ[ℂ] Reg (Fin M)) (a₀ : Fin M) :
    regCongr (retainedOriginalReassoc (N := N) (M := M) (Z := Z))
      (assembledSuccess (⟨a₀, o⟩ : OriginalTrial M Z)
        (fun p => S p.2) (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)) =
      retainedProduct
        (assembledOriginalAux (⟨a₀, o⟩ : OriginalTrial M Z) S
          (fun _ => opaqueTrialVector U o (fun z => S z = true) V a₀)
          (fun _ => trialSelectorGood (prepOf U o (fun z => S z = true)) V a₀))
        (prepOf U o (fun z => S z = true)).goodState := by
  classical
  apply assembledSuccess_original_factor
  · intro j a z hz
    have h := congrArg (fun ψ : Reg (OriginalTrial M Z) => ψ.ofLp ⟨a, z⟩)
      (opaqueTrial_good_factor hM U o (fun z => S z = true) V a₀)
    simpa [coordProj_apply, hz, retainedProduct_apply] using h
  · intro z hz
    exact prepOf_goodState_support U o S z hz

end QuarticQuery.Upper

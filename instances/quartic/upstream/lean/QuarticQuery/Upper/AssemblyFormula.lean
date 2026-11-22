module

public import QuarticQuery.Upper.Amplify
public import QuarticQuery.Upper.RouteRegister
public import QuarticQuery.Upper.RetainedFactor

/-!
Finite-coordinate first-success factorization.
`v j` already includes the chosen iteration-label amplitude; the label vector
can be added to the auxiliary basis without altering the argument.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Amplification

variable {N : ℕ} {Z : Type} [Fintype Z]

/-- The good state is supported only on the fixed successful basis labels. -/
theorem prepOf_goodState_support (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Bool) (z : Z) (hz : S z = false) :
    ((prepOf U o (fun z => S z = true)).goodState).ofLp z = 0 := by
  change (normalised (coordProj (fun w => S w = true) (U (rket o)))).ofLp z = 0
  simp [normalised, coordProj_apply, hz]

/-- The local coefficient law used in every first-success history. -/
theorem prepOf_grover_good_coordinate (U : Reg Z ≃ₗᵢ[ℂ] Reg Z)
    (o : Z) (S : Z → Bool) (ℓ : ℕ) (z : Z) (hz : S z = true) :
    (((prepOf U o (fun z => S z = true)).iterate ℓ).ofLp z) =
      (Real.sin ((2 * ℓ + 1) * (prepOf U o (fun z => S z = true)).angle) : ℂ) *
        ((prepOf U o (fun z => S z = true)).goodState).ofLp z := by
  have h := (prepOf U o (fun z => S z = true)).good_iterate ℓ
  have hz' := congrArg (fun v : Reg Z => v.ofLp z) h
  change (coordProj (fun w => S w = true)
      ((prepOf U o (fun z => S z = true)).iterate ℓ)).ofLp z = _ at hz'
  simpa [coordProj_apply, hz, PiLp.smul_apply, smul_eq_mul] using hz'

def routeCondition (o : Z) (S : Z → Bool)
    (b : Fin N → Bool) (y : Fin N → Z) (j : Fin N) (z : Z) : Prop :=
  y j = o ∧ S z = true ∧ ∀ i, i ≠ j → b i = S (y i)

/-- The success-projected output coordinate after immutable-flag routing. -/
noncomputable def routedSuccessCoord (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (b : Fin N → Bool) (y : Fin N → Z) (z : Z) : ℂ :=
  by
    classical
    exact match firstSuccess b with
      | none => 0
      | some j =>
        if routeCondition o S b y j z then
          (v j).ofLp z * ∏ i ∈ Finset.univ.filter (· ≠ j), (v i).ofLp (y i)
        else 0

/-- The auxiliary coefficient after replacing the selected good coordinate
by its scalar multiple of the fixed original good state. -/
noncomputable def routedAuxCoeff (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (s : Fin N → ℂ)
    (b : Fin N → Bool) (y : Fin N → Z) : ℂ :=
  by
    classical
    exact match firstSuccess b with
      | none => 0
      | some j =>
        if y j = o ∧ ∀ i, i ≠ j → b i = S (y i) then
          s j * ∏ i ∈ Finset.univ.filter (· ≠ j), (v i).ofLp (y i)
        else 0

/-- Every success coordinate is the same original good vector times an
auxiliary coefficient; no nonzero-branch premise is needed. -/
theorem routedSuccessCoord_factor (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (s : Fin N → ℂ) (g : Reg Z)
    (hgood : ∀ j z, S z = true → (v j).ofLp z = s j * g.ofLp z)
    (hsupport : ∀ z, S z = false → g.ofLp z = 0)
    (b : Fin N → Bool) (y : Fin N → Z) (z : Z) :
    routedSuccessCoord o S v b y z =
      routedAuxCoeff o S v s b y * g.ofLp z := by
  classical
  unfold routedSuccessCoord routedAuxCoeff
  cases h : firstSuccess b with
  | none => simp
  | some j =>
    by_cases hs : S z = true
    · by_cases hc : y j = o ∧ ∀ i, i ≠ j → b i = S (y i)
      · simp [routeCondition, hs, hc, hgood j z hs]
        ring
      · simp [routeCondition, hs, hc]
    · have hfalse : S z = false := by
        cases hsz : S z <;> simp_all
      have hg : g.ofLp z = 0 := hsupport z hfalse
      simp [routeCondition, hs, hg]

end QuarticQuery.Upper

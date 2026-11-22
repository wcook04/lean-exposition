module

public import QuarticQuery.Upper.Circuit

/-!
The fixed original register and the immutable first-success selection record.
The rest of the auxiliary history may be
carried as an additional product factor and left untouched by `regCongr`.
-/

@[expose] public section

namespace QuarticQuery.Upper

/-- Designated original register followed by all complete trial registers. -/
abbrev RouteData (N : ℕ) (Z : Type) := Z × (Fin N → Z)

/-- Swap the designated original register with trial `j`. -/
def routeAt {N : ℕ} {Z : Type} (j : Fin N) (p : RouteData N Z) :
    RouteData N Z :=
  (p.2 j, Function.update p.2 j p.1)

theorem routeAt_involutive {N : ℕ} {Z : Type} (j : Fin N) :
    Function.Involutive (routeAt (Z := Z) j) := by
  classical
  intro p
  apply Prod.ext
  · simp [routeAt]
  · funext i
    by_cases h : i = j
    · subst h
      simp [routeAt]
    · simp [routeAt]

/-- The selected index is retained, so the route is a genuine permutation. -/
def routeWithRecord {N : ℕ} {Z : Type} :
    (Option (Fin N) × RouteData N Z) ≃
      (Option (Fin N) × RouteData N Z) where
  toFun p := (p.1, match p.1 with
      | none => p.2
      | some j => routeAt j p.2)
  invFun p := (p.1, match p.1 with
      | none => p.2
      | some j => routeAt j p.2)
  left_inv := by
      classical
      intro p
      rcases p with ⟨j, data⟩
      cases j with
      | none => rfl
      | some j => simpa using (routeAt_involutive j data)
  right_inv := by
    classical
    intro p
    rcases p with ⟨j, data⟩
    cases j with
    | none => rfl
    | some j => simpa using (routeAt_involutive j data)

/-- The least marked trial in the fixed Fin order. This depends on flags only,
so routing cannot change the decision. -/
def firstSuccess {N : ℕ} (flags : Fin N → Bool) : Option (Fin N) :=
  (List.finRange N).find? (fun j => flags j)

theorem firstSuccess_some {N : ℕ} {flags : Fin N → Bool} {j : Fin N}
    (h : firstSuccess flags = some j) : flags j = true := by
  exact List.find?_some h

theorem firstSuccess_none_iff {N : ℕ} (flags : Fin N → Bool) :
    firstSuccess flags = none ↔ ∀ j, flags j = false := by
  simp [firstSuccess, List.find?_eq_none]

/-- Reversible XOR marker for all trial success labels. -/
def markFlags {N : ℕ} {Z : Type} (S : Z → Bool)
    (p : (Fin N → Bool) × (Fin N → Z)) :
    (Fin N → Bool) × (Fin N → Z) :=
  (fun j => xor (p.1 j) (S (p.2 j)), p.2)

theorem markFlags_involutive {N : ℕ} {Z : Type} (S : Z → Bool) :
    Function.Involutive (markFlags (N := N) S) := by
  intro p
  apply Prod.ext
  · funext j
    simp [markFlags]
  · rfl

/-- Route according to immutable flags. The flag register also serves as the
selection record; no separate `J` register is required. -/
def routeWithFlags {N : ℕ} {Z : Type} :
    ((Fin N → Bool) × RouteData N Z) ≃
      ((Fin N → Bool) × RouteData N Z) where
  toFun p := (p.1, match firstSuccess p.1 with
      | none => p.2
      | some j => routeAt j p.2)
  invFun p := (p.1, match firstSuccess p.1 with
      | none => p.2
      | some j => routeAt j p.2)
  left_inv := by
      classical
      intro p
      rcases p with ⟨flags, data⟩
      cases h : firstSuccess flags with
      | none => simp [h]
      | some j => simpa [h] using (routeAt_involutive j data)
  right_inv := by
    classical
    intro p
    rcases p with ⟨flags, data⟩
    cases h : firstSuccess flags with
    | none => simp [h]
    | some j => simpa [h] using (routeAt_involutive j data)

/-- The marker is a query-free gate, as is the first-success routing. -/
noncomputable def markGate {N : ℕ} {Z : Type} [Fintype Z]
    (S : Z → Bool) :
    Reg ((Fin N → Bool) × (Fin N → Z)) ≃ₗᵢ[ℂ]
      Reg ((Fin N → Bool) × (Fin N → Z)) :=
  regCongr ⟨markFlags S, markFlags S, markFlags_involutive S,
    markFlags_involutive S⟩

noncomputable def routeFlagsGate {N : ℕ} {Z : Type} [Fintype Z] :
    Reg ((Fin N → Bool) × RouteData N Z) ≃ₗᵢ[ℂ]
      Reg ((Fin N → Bool) × RouteData N Z) :=
  regCongr routeWithFlags

/-- Routing is a query-free gate on any finite trial register basis. -/
noncomputable def routeGate {N : ℕ} {Z : Type} [Fintype Z] :
    Reg (Option (Fin N) × RouteData N Z) ≃ₗᵢ[ℂ]
      Reg (Option (Fin N) × RouteData N Z) :=
  regCongr routeWithRecord

end QuarticQuery.Upper

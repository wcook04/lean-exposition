module

public import QuarticQuery.Upper.GateStateDefs

/-! Exact gate-state factorization from the definitions in GateStateDefs.
-/

@[expose] public section

namespace QuarticQuery.Upper

variable {N : ℕ} {Z : Type} [Fintype Z]

/-- Intended gate-state bridge. After undoing the routing swap, its source
coordinate has old O=y_j and old trial j=z. Undoing XOR marking forces
all immutable flags to agree with the original trial success labels.
The factorization is in `AssemblyFormula.routedSuccessCoord_factor`. -/
theorem assembledSuccess_apply (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (b : Fin N → Bool)
    (y : Fin N → Z) (z : Z) :
    (assembledSuccess o S v).ofLp (b, (z, y)) =
      routedSuccessCoord o S v b y z := by
  classical
  unfold assembledSuccess assembledTrials
  cases h : firstSuccess b with
  | none => simp [routedSuccessCoord, h]
  | some j =>
    have hb : b j = true := firstSuccess_some h
    simp only [routedSuccessCoord, h, Option.isSome_some, ↓reduceIte]
    rw [routeFlagsGate, regCongr_apply, markWholeGate, regCongr_apply]
    change (startTrials o v).ofLp
      (markWhole S (b, match firstSuccess b with
        | none => (z, y)
        | some j => (y j, Function.update y j z))) = _
    rw [h]
    simp only [markWhole, startTrials]
    have hxor (u v : Bool) : (u ^^ v) = false ↔ u = v := by
      cases u <;> cases v <;> decide
    have hflag :
        (y j = o ∧ ∀ i, (b i ^^ S (Function.update y j z i)) = false) ↔
          routeCondition o S b y j z := by
      constructor
      · rintro ⟨ho, hh⟩
        refine ⟨ho, ?_, ?_⟩
        · have hj : b j = S z := by
            exact (hxor _ _).mp (by simpa using hh j)
          simpa [hb] using hj.symm
        · intro i hi
          have hi' := (hxor _ _).mp (hh i)
          simpa [hi] using hi'
      · rintro ⟨ho, hs, hrest⟩
        refine ⟨ho, fun i => (hxor _ _).mpr ?_⟩
        by_cases hi : i = j
        · subst i
          simp [hb, hs]
        · simpa [hi] using hrest i hi
    have hprod :
        (∏ i, (v i).ofLp (Function.update y j z i)) =
          (v j).ofLp z *
            ∏ i ∈ Finset.univ.filter (· ≠ j), (v i).ofLp (y i) := by
      calc
        (∏ i, (v i).ofLp (Function.update y j z i)) =
            (v j).ofLp (Function.update y j z j) *
              ∏ i ∈ (Finset.univ : Finset (Fin N)).erase j,
                (v i).ofLp (Function.update y j z i) :=
          (Finset.mul_prod_erase Finset.univ
            (fun i => (v i).ofLp (Function.update y j z i))
            (Finset.mem_univ j)).symm
        _ = _ := by
          simp only [Finset.filter_ne']
          congr 1
          · simp
          · apply Finset.prod_congr rfl
            intro i hi
            have hij : i ≠ j := Finset.ne_of_mem_erase hi
            simp [hij]
    simp only [hflag, hprod]

/-- The actual marked and routed success state has one fixed original vector
factor. All iteration labels may be carried in a further auxiliary sigma
block; this statement handles each fixed label vector. -/
theorem assembledSuccess_factor (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (s : Fin N → ℂ) (g : Reg Z)
    (hgood : ∀ j z, S z = true → (v j).ofLp z = s j * g.ofLp z)
    (hsupport : ∀ z, S z = false → g.ofLp z = 0) :
    regCongr (retainedReassoc (N := N) (Z := Z))
      (assembledSuccess o S v) =
      retainedProduct (assembledAux o S v s) g := by
  classical
  ext ⟨⟨b, y⟩, z⟩
  rw [regCongr_apply]
  change (assembledSuccess o S v).ofLp (b, (z, y)) = _
  rw [assembledSuccess_apply]
  exact routedSuccessCoord_factor o S v s g hgood hsupport b y z

/-- The auxiliary state has no coefficient in a no-success flag block. -/
theorem assembledAux_success_support (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (s : Fin N → ℂ)
    (b : Fin N → Bool) (y : Fin N → Z)
    (h : firstSuccess b = none) :
    (assembledAux o S v s).ofLp (b, y) = 0 := by
  simp [assembledAux, routedAuxCoeff, h]

end QuarticQuery.Upper

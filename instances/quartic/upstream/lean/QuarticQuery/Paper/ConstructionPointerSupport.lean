module

public import QuarticQuery.Paper.ConstructionTests

/-!
# Essential physical coordinates of a pointer test

Compiled as part of the `QuarticQuery` library target.

The pointer word and all possible targets occupy disjoint physical coordinates.
Extending Boolean inputs along this injection transports the schema witnesses to
full inputs, including agreement at every other physical coordinate. This closes
the schema-to-physical-input qualification in the earlier construction review.
-/

public section

namespace QuarticQuery.Paper

/-- Ledger: lem-2.2.i. The actual physical locations of the pointer word and the
entire target column, as in the corrected ledger's support qualification. -/
@[expose] def constructionPointerLoc {κ : Type} (C : Circuit κ) (ℓ r : ℕ)
    (i : Column ℓ) (s : Address r) (e : Fin (2 ^ ℓ - 1)) :
    Fin ℓ ⊕ Column ℓ → BitLoc ℓ r C.size κ
  | .inl b => .inr (.inr (.inl ⟨i, (s, otherColumn i e, b)⟩))
  | .inr j => .inl ((otherColumn i e).val, j)

/-- Ledger: lem-2.2.i. Auxiliary exact coordinate identity: all listed physical
locations are distinct; the pointer and target locations use disjoint branches. -/
theorem construction_pointerLoc_injective {κ : Type} (C : Circuit κ) (ℓ r : ℕ)
    (i : Column ℓ) (s : Address r) (e : Fin (2 ^ ℓ - 1)) :
    Function.Injective (constructionPointerLoc C ℓ r i s e) := by
  let tag : BitLoc ℓ r C.size κ → Option (Fin ℓ ⊕ Column ℓ) := fun p =>
    match p with
    | .inl (_, j) => some (.inr j)
    | .inr (.inr (.inl p)) => some (.inl p.2.2.2)
    | _ => none
  have htag (p : Fin ℓ ⊕ Column ℓ) :
      tag (constructionPointerLoc C ℓ r i s e p) = some p := by
    cases p <;> rfl
  intro p q hpq
  exact Option.some.inj ((htag p).symm.trans ((congrArg tag hpq).trans (htag q)))

/-- Ledger: lem-2.2.i. Auxiliary proof of the unchanged support claim: an
essential Boolean coordinate stays essential after an injective input renaming. -/
theorem construction_essential_coordinate_lift {α β : Type}
    (f : α → β) (hf : Function.Injective f)
    (g : BitInput α → Bool) (q : α)
    (h : ∃ x y : BitInput α,
      (∀ p, p ≠ q → x p = y p) ∧ g x ≠ g y) :
    ∃ X Y : BitInput β,
      (∀ p, p ≠ f q → X p = Y p) ∧
        g (fun a => X (f a)) ≠ g (fun a => Y (f a)) := by
  classical
  obtain ⟨x, y, hxy, hdiff⟩ := h
  let extend : BitInput α → BitInput β := fun z b =>
    if h : ∃ a, f a = b then z (Classical.choose h) else false
  have hext (z : BitInput α) (a : α) : extend z (f a) = z a := by
    have h : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [extend, dif_pos h]
    exact congrArg z (hf (Classical.choose_spec h))
  have hextfun (z : BitInput α) : (fun a => extend z (f a)) = z :=
    funext (hext z)
  refine ⟨extend x, extend y, ?_, ?_⟩
  · intro p hp
    by_cases h : ∃ a, f a = p
    · have hpre : Classical.choose h ≠ q := by
        intro heq
        apply hp
        exact (Classical.choose_spec h).symm.trans (congrArg f heq)
      simp only [extend, dif_pos h]
      exact hxy _ hpre
    · simp only [extend, dif_neg h]
  · rw [hextfun x, hextfun y]
    exact hdiff

/-- Ledger: lem-2.2.i. Verbatim corrected-ledger scope on full physical inputs:
each of the `ℓ + m` pointer and target locations is essential to its local test. -/
theorem construction_pointer_every_physical_coordinate {κ : Type} (C : Circuit κ)
    (ℓ r : ℕ) (i : Column ℓ) (s : Address r) (e : Fin (2 ^ ℓ - 1))
    (q : Fin ℓ ⊕ Column ℓ) :
    ∃ X Y : BitInput (BitLoc ℓ r C.size κ),
      (∀ p, p ≠ constructionPointerLoc C ℓ r i s e q → X p = Y p) ∧
        localTest C ℓ r X i s (.inr (.inl e)) ≠
          localTest C ℓ r Y i s (.inr (.inl e)) := by
  obtain ⟨X, Y, hXY, hdiff⟩ := construction_essential_coordinate_lift
    (constructionPointerLoc C ℓ r i s e)
    (construction_pointerLoc_injective C ℓ r i s e)
    (constructionPointerLookup ℓ) q (construction_pointer_every_coordinate ℓ q)
  refine ⟨X, Y, hXY, ?_⟩
  have hnot : Function.Injective Bool.not := by
    intro a b h
    cases a <;> cases b <;> cases h <;> rfl
  intro hsame
  apply hdiff
  apply hnot
  change localTest C ℓ r X i s (.inr (.inl e)) =
    localTest C ℓ r Y i s (.inr (.inl e))
  exact hsame

end QuarticQuery.Paper

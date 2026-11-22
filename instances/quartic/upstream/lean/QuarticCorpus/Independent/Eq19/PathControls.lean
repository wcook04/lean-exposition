module

public import QuarticCorpus.Independent.Eq19.Spec

/-!
Independent expectations for the shared tree/path interface used by Spec.
They close a specific blind spot: defining path to discard queries, or depth to
ignore repeated queries, would make an erased-zero comparison misleading.
Native validation: `research/adjudication/round3_formal.json`.
-/

@[expose] public section

namespace QuarticQuery.Independent.Eq19

def askTwice {ι : Type} (q : ι) : QueryTree ι :=
  .query q (.query q (.leaf false) (.leaf false))
    (.query q (.leaf false) (.leaf false))

theorem askTwice_path {ι : Type} (q : ι) (x : BitInput ι) :
    (askTwice q).path x = [q, q] := by
  simp [askTwice, QueryTree.path]

theorem askTwice_depth {ι : Type} (q : ι) : (askTwice q).depth = 2 := by
  simp [askTwice, QueryTree.depth]

theorem designatedZero_is_false {κ : Type} {ℓ r S : ℕ}
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ)
    (i : Column ℓ) : referenceInput (S := S) J A (.inl (i, J i)) = false := by
  simp [referenceInput]

theorem otherRow_is_true {κ : Type} {ℓ r S : ℕ}
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ)
    (i j : Column ℓ) (hj : j ≠ J i) :
    referenceInput (S := S) J A (.inl (i, j)) = true := by
  simp [referenceInput, hj]

theorem repeatedZero_counts_once {κ : Type} {ℓ r S : ℕ}
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ)
    (i : Column ℓ) :
    zerosSeen (S := S) (askTwice (.inl (i, J i))) A J = 1 := by
  classical
  have hs :
      (Finset.univ.filter fun c : Column ℓ =>
        zeroWasQueried (S := S) (askTwice (.inl (i, J i))) A J c) = {i} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hz
      have he : (Sum.inl (c, J c) : BitLoc ℓ r S κ) = .inl (i, J i) := by
        simpa only [zeroWasQueried, askTwice_path, List.mem_cons,
          List.not_mem_nil, or_false, or_self] using hz
      exact congrArg Prod.fst (Sum.inl.inj he)
    · intro hc
      subst c
      simp [zeroWasQueried, askTwice_path]
  simpa only [zerosSeen, hs, Finset.card_singleton]

end QuarticQuery.Independent.Eq19

module

public import QuarticQuery.Statement

/-!
# The coupled dummy and planted inputs

The dummy input has one zero in every column and blank cells. The planted input
fills in one column as a true winner. The two differ only at the removed zero and
inside the planted cell. The address of a column is a total function here: on
strings off the promise it takes a default value, and such strings have weight
zero under the hard distribution.
-/

@[expose] public section

namespace QuarticQuery

variable {κ : Type} {ℓ r S : ℕ}

/-- Ledger: def-planted. `s_i` of equation (7) as a total function: the default
`false` is used only off the promise. -/
def trueAddr (f : PartialBool κ) (U : Fin r → BitInput κ) : Address r :=
  fun h => (f (U h)).getD false

theorem f_eq_trueAddr {f : PartialBool κ} {U : Fin r → BitInput κ} {h : Fin r}
    (hU : promised f (U h)) : f (U h) = some (trueAddr f U h) := by
  obtain ⟨b, hb⟩ := hU
  simp [trueAddr, hb]

/-- The column and address of a cell bit, either pointer or transcript. -/
def cellOf : BitLoc ℓ r S κ → Option (Column ℓ × Address r)
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr (.inl ⟨i, (s, _, _)⟩)) => some (i, s)
  | .inr (.inr (.inr (i, s, _, _))) => some (i, s)

/-- Whether a location is a bit of `X_i`. -/
def xColumn (i : Column ℓ) : BitLoc ℓ r S κ → Bool
  | .inl (c, _) => decide (c = i)
  | .inr _ => false

/-- The instance and coordinate of a location inside `A_{i,1}, …, A_{i,r}`. -/
def aTarget [DecidableEq κ] (i : Column ℓ) : BitLoc ℓ r S κ → Option (Fin r × κ)
  | .inr (.inl (c, h, q)) => if c = i then some (h, q) else none
  | _ => none

/-- Ledger: def-dummy. `Y⁽⁰⁾`: one zero in `X_i`, at `J i`; the given `A`; blank
cells. -/
def dummy (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) :
    BitInput (BitLoc ℓ r S κ)
  | .inl (i, j) => decide (j ≠ J i)
  | .inr (.inl (i, h, q)) => A i h q
  | .inr (.inr _) => false

/-- Ledger: def-planted. `Y⁽¹⁾`: `X_I` is all ones and the cell of `I` at its true
address holds the transcripts `tr` and pointers to the zeros of the other columns. -/
def planted (f : PartialBool κ) (tr : BitInput κ → Fin S → Bool)
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ) :
    BitInput (BitLoc ℓ r S κ)
  | .inl (i, j) => if i = I then true else decide (j ≠ J i)
  | .inr (.inl (i, h, q)) => A i h q
  | .inr (.inr (.inl ⟨i, (s, j, b)⟩)) =>
      if i = I ∧ s = trueAddr f (A I) then (pointerEquiv ℓ).symm (J j.val) b else false
  | .inr (.inr (.inr (i, s, h, g))) =>
      if i = I ∧ s = trueAddr f (A I) then tr (A I h) g else false

/-- Ledger: eq-18. The coupled inputs differ only at `X_I[J_I]` and inside the cell
`B_{I, s_I}`. -/
theorem eq_of_dummy_ne_planted {f : PartialBool κ} {tr : BitInput κ → Fin S → Bool}
    {J : Column ℓ → Column ℓ} {A : Column ℓ → Fin r → BitInput κ} {I : Column ℓ}
    {q : BitLoc ℓ r S κ} (h : dummy J A q ≠ planted f tr J A I q) :
    q = .inl (I, J I) ∨ cellOf q = some (I, trueAddr f (A I)) := by
  rcases q with ⟨i, j⟩ | ⟨i, a, q⟩ | ⟨i, s, j, b⟩ | ⟨i, s, a, g⟩
  · left
    by_cases hi : i = I
    · subst hi
      by_cases hj : j = J i
      · rw [hj]
      · simp [dummy, planted, hj] at h
    · simp [dummy, planted, hi] at h
  · exact absurd rfl h
  · right
    by_cases hc : i = I ∧ s = trueAddr f (A I)
    · obtain ⟨rfl, rfl⟩ := hc
      rfl
    · simp [dummy, planted, hc] at h
  · right
    by_cases hc : i = I ∧ s = trueAddr f (A I)
    · obtain ⟨rfl, rfl⟩ := hc
      rfl
    · simp [dummy, planted, hc] at h

variable {f : PartialBool κ} {C : Circuit κ}

/-- Ledger: claim-Y-values. Every column of `Y⁽⁰⁾` has a zero, so nothing wins. -/
theorem addressedF_dummy (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) :
    addressedF f C ℓ r (dummy J A) = false := by
  simp only [addressedF, decide_eq_false_iff_not]
  rintro ⟨i, s, hX, -⟩
  have := hX (J i)
  simp [readX, dummy] at this

/-- Ledger: claim-Y-values. On strings in the domain, column `I` of `Y⁽¹⁾` wins at
its true address. -/
theorem addressedF_planted {tr : BitInput κ → Fin C.size → Bool}
    (htr : ∀ x, GateConsistent C x (tr x)) (J : Column ℓ → Column ℓ)
    (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ) (hA : ∀ h, promised f (A I h)) :
    addressedF f C ℓ r (planted f tr J A I) = true := by
  have hw : WinsAt f C ℓ r (planted f tr J A I) I (trueAddr f (A I)) := by
    refine ⟨fun j => ?_, fun h => ?_, fun h => ?_, fun j => ?_⟩
    · simp [readX, planted]
    · have : readA (planted f tr J A I) I h = A I h := rfl
      rw [this]
      exact f_eq_trueAddr (hA h)
    · have : readTranscript (planted f tr J A I) I (trueAddr f (A I)) h = tr (A I h) := by
        funext g
        simp [readTranscript, planted]
      rw [this]
      exact htr _
    · have hp : readPointerBit (planted f tr J A I) I (trueAddr f (A I)) j =
          (pointerEquiv ℓ).symm (J j.val) := by
        funext b
        simp [readPointerBit, planted]
      rw [hp, Equiv.apply_symm_apply]
      simp [readX, planted, j.2]
  simp only [addressedF, decide_eq_true_eq]
  exact ⟨I, _, hw⟩

end QuarticQuery

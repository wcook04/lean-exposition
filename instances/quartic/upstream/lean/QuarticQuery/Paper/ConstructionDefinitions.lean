module

public import QuarticQuery.Construction.LocalTests
public import QuarticQuery.Results.Exponent

/-!
# Section 2.2: exact definitions and their agreement

Compiled as part of the `QuarticQuery` library target.
Every theorem below has a proof term.


The preprint fixes `m = 4 ^ t`. Its zero-based coordinate representation is
`Column (2 * t)`, and its address length is `40 * t`. The generic lemmas below
also apply to arbitrary address lengths and arbitrary circuits.
-/

public section

namespace QuarticQuery.Paper

/-! ## Transcripts and physical input coordinates -/

/-- Ledger: def-transcript. Verbatim definition: a transcript is one bit per
non-input gate; the consistency equations use actual input wires. -/
theorem construction_transcript_definition {κ : Type} (C : Circuit κ)
    (x : BitInput κ) (tr : Fin C.size → Bool) :
    GateConsistent C x tr ↔ ∀ g : Fin C.size,
      tr g = (C.gate g).table
        (predecessorValue C x tr g (C.gate g).left)
        (predecessorValue C x tr g (C.gate g).right) := Iff.rfl

/-- Ledger: def-transcript. Verbatim representation of input predecessors:
their values come directly from `x`, independently of the proposed transcript. -/
theorem construction_transcript_input_wire {κ : Type} (C : Circuit κ)
    (x : BitInput κ) (tr : Fin C.size → Bool) (g : Fin C.size) (q : κ) :
    predecessorValue C x tr g (some (.inl q)) = x q := rfl

/-- Ledger: def-transcript. Verbatim representation of non-input predecessors:
their proposed values are the earlier transcript bits. -/
theorem construction_transcript_gate_wire {κ : Type} (C : Circuit κ)
    (x : BitInput κ) (tr : Fin C.size → Bool) (g : Fin C.size) (h : Fin g.val) :
    predecessorValue C x tr g (some (.inr h)) =
      tr ⟨h.val, lt_trans h.isLt g.isLt⟩ := rfl

/-- Ledger: def-transcript. The topological evaluation gives the unique correct
transcript, on every input; this is the existing semantic characterization. -/
theorem construction_transcript_correct {κ : Type} (C : Circuit κ)
    (x : BitInput κ) (tr : Fin C.size → Bool) :
    (GateConsistent C x tr ↔ tr = circuitEval C x) ∧
      ∃! tr' : Fin C.size → Bool, GateConsistent C x tr' :=
  ⟨gateConsistent_iff_eq_circuitEval, existsUnique_gateConsistent C x⟩

/-- Ledger: eq-6. Verbatim at the paper's powers of four, including the ceiling
identity that was absent from the older reviewed tie. -/
theorem construction_eq6 (t : ℕ) :
    Real.logb 2 (mValue t : ℝ) = (2 * t : ℕ) ∧
      ⌈20 * Real.logb 2 (mValue t : ℝ)⌉₊ = 40 * t := by
  constructor
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using logb_mValue t
  · rw [logb_mValue]
    have he : (20 : ℝ) * (2 * (t : ℝ)) = ((40 * t : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he]
    simp only [Nat.ceil_natCast]

/-- Ledger: def-column-layout. Verbatim layout as a type equality. The four
summands are `X`, `A`, pointer bits, and transcript bits; all functions on this
type are allowed inputs. -/
theorem construction_column_layout (ℓ r S : ℕ) (κ : Type) :
    BitLoc ℓ r S κ =
      ((Column ℓ × Column ℓ) ⊕
        (Column ℓ × Fin r × κ) ⊕
        (Σ i : Column ℓ, Address r × {j : Column ℓ // j ≠ i} × Fin ℓ) ⊕
        (Column ℓ × Address r × Fin r × Fin S)) := rfl

/-- Ledger: def-column-layout. Verbatim pointer encoding: every bit string is a
valid destination, and every destination has exactly one encoding. -/
theorem construction_pointer_encoding (ℓ : ℕ) :
    Function.Bijective (pointerEquiv ℓ) ∧
      ∀ j : Column ℓ, ∃! w : Fin ℓ → Bool, pointerEquiv ℓ w = j :=
  ⟨pointerEquiv_bijective ℓ, existsUnique_pointer ℓ⟩

/-- Ledger: def-column-layout. Verbatim dimensions at the Forrelation instance:
there are `m` columns, `km` bits per partial-function input, and `2^r` addresses. -/
theorem construction_layout_cardinalities (k t : ℕ) :
    Fintype.card (Column (2 * t)) = mValue t ∧
    Fintype.card (ForrelationCoord k t) = k * mValue t ∧
    Fintype.card (Address (40 * t)) = 2 ^ (40 * t) := by
  refine ⟨by simp [Column, mValue], ?_, by simp [Address]⟩
  exact (Fintype.card_congr (finProdFinEquiv (m := k) (n := mValue t))).trans
    (Fintype.card_fin _)

/-! ## Addresses, outward pointers and winners -/

section Winners

variable {κ : Type} {f : PartialBool κ} {C : Circuit κ} {ℓ r : ℕ}

/-- Ledger: eq-7. Verbatim characterization of the true address; a promise is
required for each of this column's instances, and no promise is imposed elsewhere. -/
theorem construction_trueAddress_iff
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ)
    (hdef : ∀ h, promised f (readA x i h)) (s : Address r) :
    (∀ h, f (readA x i h) = some (s h)) ↔ s = trueAddress f x i hdef := by
  constructor
  · intro hs
    funext h
    exact Option.some.inj ((hs h).symm.trans (apply_eq_trueAddress x i hdef h))
  · intro hs
    subst s
    exact apply_eq_trueAddress x i hdef

/-- Ledger: eq-8. Verbatim pointer condition at a proposed address `s`; the
paper's display specializes it to the true address `s_i`. -/
@[expose] def constructionOutwardPointers {S : ℕ} (x : BitInput (BitLoc ℓ r S κ))
    (i : Column ℓ) (s : Address r) : Prop :=
  ∀ j : {j : Column ℓ // j ≠ i},
    readX x j.val (pointerEquiv ℓ (readPointerBit x i s j)) = false

/-- Ledger: eq-8. The named condition is definitionally the fourth clause of
`WinsAt`, with every competing column quantified. -/
theorem construction_eq8_of_winsAt
    {x : BitInput (BitLoc ℓ r C.size κ)} {i : Column ℓ} {s : Address r}
    (hw : WinsAt f C ℓ r x i s) : constructionOutwardPointers x i s :=
  hw.2.2.2

/-- Ledger: def-winner. Verbatim paper definition: the column is all ones and
its true-address cell has the true transcripts and the outward zero witnesses. -/
@[expose] def constructionWinner (f : PartialBool κ) (C : Circuit κ) (ℓ r : ℕ)
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) : Prop :=
  (∀ j, readX x i j = true) ∧
  ∃ hdef : ∀ h, promised f (readA x i h),
    (∀ h, readTranscript x i (trueAddress f x i hdef) h =
      circuitEval C (readA x i h)) ∧
    constructionOutwardPointers x i (trueAddress f x i hdef)

/-- Ledger: def-winner. Equivalent to the existential of the public `WinsAt`
definition, without any assumption that the circuit realizes `f`. -/
theorem construction_winner_iff_exists_winsAt
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) :
    constructionWinner f C ℓ r x i ↔ ∃ s, WinsAt f C ℓ r x i s := by
  constructor
  · rintro ⟨hX, hdef, hT, hP⟩
    refine ⟨trueAddress f x i hdef, winsAt_iff_paperWinsAt.mpr ?_⟩
    exact ⟨hX, ⟨hdef, rfl⟩, hT, hP⟩
  · rintro ⟨s, hw⟩
    obtain ⟨hX, ⟨hdef, hs⟩, hT, hP⟩ := winsAt_iff_paperWinsAt.mp hw
    subst s
    exact ⟨hX, hdef, hT, hP⟩

/-- Ledger: def-win-at-address. Verbatim paper wording: the column is a winner
and the supplied address is the vector of its defined answers. -/
theorem construction_winsAt_iff_winner_and_address
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) (s : Address r) :
    WinsAt f C ℓ r x i s ↔
      constructionWinner f C ℓ r x i ∧
        ∃ hdef : ∀ h, promised f (readA x i h), s = trueAddress f x i hdef := by
  constructor
  · intro hw
    exact ⟨(construction_winner_iff_exists_winsAt x i).mpr ⟨s, hw⟩,
      (winsAt_iff_paperWinsAt.mp hw).2.1⟩
  · rintro ⟨hwin, hdef, hs⟩
    obtain ⟨s', hw⟩ := (construction_winner_iff_exists_winsAt x i).mp hwin
    have hs' : s' = trueAddress f x i hdef :=
      (construction_trueAddress_iff x i hdef s').mp hw.2.1
    rw [hs', ← hs] at hw
    exact hw

/-- Ledger: def-win-at-address. The corrected ledger's output-test wording is
equivalent, provided the circuit realizes the partial function on every input. -/
theorem construction_win_at_address_outputs (hC : CircuitRealises C f)
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) (s : Address r) :
    WinsAt f C ℓ r x i s ↔
      (∀ j, readX x i j = true) ∧
      (∀ h, readTranscript x i s h = circuitEval C (readA x i h)) ∧
      (∀ h, readTranscript x i s h C.domainOut = true) ∧
      (∀ h, readTranscript x i s h C.valueOut = s h) ∧
      constructionOutwardPointers x i s :=
  winsAt_iff_outputs hC

/-- Ledger: cor-unique-winner. Verbatim, strengthened to arbitrary circuits and
partial functions: every input has at most one winning column. -/
theorem construction_unique_winner (x : BitInput (BitLoc ℓ r C.size κ))
    (i j : Column ℓ) (hi : constructionWinner f C ℓ r x i)
    (hj : constructionWinner f C ℓ r x j) : i = j := by
  obtain ⟨s, hs⟩ := (construction_winner_iff_exists_winsAt x i).mp hi
  obtain ⟨s', hs'⟩ := (construction_winner_iff_exists_winsAt x j).mp hj
  exact winsAt_column_unique hs hs'

end Winners

end QuarticQuery.Paper

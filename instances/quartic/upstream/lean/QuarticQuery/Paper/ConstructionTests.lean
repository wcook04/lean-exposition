module

public import QuarticQuery.Paper.ConstructionDefinitions
public import QuarticQuery.Forrelation.Circuit

/-!
# Lemma 2.2(i), test counts and the local dichotomy

Compiled as part of the `QuarticQuery` library target.
The classical query bound is adaptive depth. This is the meaning of the attached
preprint; the fixed-coordinate-support error belonged to an older ledger entry.
-/

public section

namespace QuarticQuery.Paper

/-! ## The classical part of Lemma 2.2 -/

/-- Ledger: lem-2.2.i. Verbatim query statement, with the exact depth in place
of `O(log m)`: the same index type works at every column and address. -/
theorem construction_lemma_2_2_i {κ : Type} {f : PartialBool κ} (C : Circuit κ)
    (ℓ r : ℕ) (hC : CircuitRealises C f) :
    (∀ (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) (s : Address r),
      PaperWinsAt f C ℓ r x i s ↔
        ∀ e : TestIndex ℓ r C.size, localTest C ℓ r x i s e = true) ∧
    (∀ (i : Column ℓ) (s : Address r) (e : TestIndex ℓ r C.size),
      (∀ x, (localTestTree C ℓ r i s e).eval x = localTest C ℓ r x i s e) ∧
      (localTestTree C ℓ r i s e).depth ≤ max 3 (ℓ + 1)) := by
  constructor
  · intro x i s
    exact winsAt_iff_paperWinsAt.symm.trans (winsAt_iff_localTests hC)
  · intro i s e
    exact ⟨fun x => localTestTree_eval C ℓ r x i s e,
      localTestTree_depth_le C ℓ r i s e⟩

/-- Ledger: lem-2.2.i. Verbatim specialization to the paper's range `m ≥ 4`:
the classical query depth is at most `log₂ m + 1 = 2t + 1`. -/
theorem construction_test_depth (t : ℕ) (ht : 1 ≤ t)
    {κ : Type} (C : Circuit κ) (r : ℕ) (i : Column (2 * t))
    (s : Address r) (e : TestIndex (2 * t) r C.size) :
    (localTestTree C (2 * t) r i s e).depth ≤ 2 * t + 1 := by
  have hmax : max 3 (2 * t + 1) = 2 * t + 1 := by omega
  rw [← hmax]
  exact localTestTree_depth_le C (2 * t) r i s e

/-- Ledger: lem-2.2.i. The pointer-lookup schema, with separate physical bits
for the pointer word and for all possible target positions. -/
@[expose] def constructionPointerLookup (ℓ : ℕ)
    (x : BitInput (Fin ℓ ⊕ Column ℓ)) : Bool :=
  x (.inr (pointerEquiv ℓ (fun b => x (.inl b))))

/-- Ledger: lem-2.2.i. A local pointer test is the negation of the lookup
schema, with its physical input locations substituted. -/
theorem construction_pointer_test_eq_lookup {κ : Type} (C : Circuit κ) (ℓ r : ℕ)
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) (s : Address r)
    (e : Fin (2 ^ ℓ - 1)) :
    localTest C ℓ r x i s (.inr (.inl e)) =
      !constructionPointerLookup ℓ (Sum.elim
        (readPointerBit x i s (otherColumn i e))
        (readX x (otherColumn i e).val)) := rfl

/-- Ledger: lem-2.2.i. The corrected ledger's support qualification: every one
of the `ℓ + 2^ℓ` coordinates of the lookup schema is essential, even though its
adaptive decision-tree depth is `ℓ + 1`. -/
theorem construction_pointer_every_coordinate (ℓ : ℕ)
    (q : Fin ℓ ⊕ Column ℓ) :
    ∃ x y : BitInput (Fin ℓ ⊕ Column ℓ),
      (∀ p, p ≠ q → x p = y p) ∧
        constructionPointerLookup ℓ x ≠ constructionPointerLookup ℓ y := by
  classical
  cases q with
  | inl b =>
    let u : Fin ℓ → Bool := fun _ => false
    let v : Fin ℓ → Bool := fun c => decide (c = b)
    have huv : u ≠ v := by
      intro h
      have hh := congrFun h b
      simp [u, v] at hh
    have hp : pointerEquiv ℓ u ≠ pointerEquiv ℓ v :=
      fun h => huv ((pointerEquiv ℓ).injective h)
    let target : Column ℓ → Bool := fun j => decide (j = pointerEquiv ℓ u)
    let x : BitInput (Fin ℓ ⊕ Column ℓ) := Sum.elim u target
    let y : BitInput (Fin ℓ ⊕ Column ℓ) := Sum.elim v target
    refine ⟨x, y, ?_, ?_⟩
    · intro p hp'
      cases p with
      | inl c =>
        have hcb : c ≠ b := fun he => hp' (by cases he; rfl)
        simp [x, y, u, v, hcb]
      | inr j => rfl
    · change decide (pointerEquiv ℓ u = pointerEquiv ℓ u) ≠
        decide (pointerEquiv ℓ v = pointerEquiv ℓ u)
      simp [Ne.symm hp]
  | inr j =>
    let w : Fin ℓ → Bool := (pointerEquiv ℓ).symm j
    let x : BitInput (Fin ℓ ⊕ Column ℓ) := Sum.elim w (fun _ => false)
    let y : BitInput (Fin ℓ ⊕ Column ℓ) := Sum.elim w (fun p => decide (p = j))
    refine ⟨x, y, ?_, ?_⟩
    · intro p hp
      cases p with
      | inl b => rfl
      | inr c =>
        have hcj : c ≠ j := fun he => hp (by cases he; rfl)
        simp [x, y, hcj]
    · simp [constructionPointerLookup, x, y, w]

/-- Ledger: cor-local-dichotomy. Verbatim, for arbitrary addressed constructions:
a winner has an all-passing address, and every address of a nonwinner fails. -/
theorem construction_local_dichotomy {κ : Type} {f : PartialBool κ}
    {C : Circuit κ} {ℓ r : ℕ} (hC : CircuitRealises C f)
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) :
    (constructionWinner f C ℓ r x i →
      ∃ s : Address r, ∀ e : TestIndex ℓ r C.size,
        localTest C ℓ r x i s e = true) ∧
    (¬ constructionWinner f C ℓ r x i →
      ∀ s : Address r, ∃ e : TestIndex ℓ r C.size,
        localTest C ℓ r x i s e = false) := by
  constructor
  · intro hwin
    obtain ⟨s, hw⟩ := (construction_winner_iff_exists_winsAt x i).mp hwin
    exact ⟨s, (winsAt_iff_localTests hC).mp hw⟩
  · intro hnot s
    apply exists_failing_localTest hC
    intro hex
    exact hnot ((construction_winner_iff_exists_winsAt x i).mpr hex)

/-! ## The exact count and its logarithmic bound -/

/-- Ledger: def-K. Verbatim exact count, independent of `(i,s)`. -/
theorem construction_K_count (t S : ℕ) :
    Fintype.card (TestIndex (2 * t) (40 * t) S) =
      mValue t + (mValue t - 1) + 40 * t * (S + 2) :=
  card_testIndex (2 * t) (40 * t) S

/-- Ledger: def-K. The paper's asymptotic claim with an explicit constant:
`S ≤ A m (log₂ m)^2` implies `K ≤ (42 + 20A) m (log₂ m)^3` for `m ≥ 4`.
This exports the arithmetic previously local to `Upper.budget_le`. -/
theorem construction_K_bound (t S A : ℕ) (ht : 1 ≤ t)
    (hS : S ≤ A * mValue t * (2 * t) ^ 2) :
    Fintype.card (TestIndex (2 * t) (40 * t) S) ≤
      (42 + 20 * A) * mValue t * (2 * t) ^ 3 := by
  rw [construction_K_count]
  have hm1 : 1 ≤ mValue t := Nat.two_pow_pos _
  have hτ1 : 1 ≤ 2 * t := by omega
  have h40 : 40 * t = 20 * (2 * t) := by omega
  rw [h40]
  have hτ3 : 2 * t ≤ (2 * t) ^ 3 := Nat.le_self_pow (by norm_num) (2 * t)
  have h3 : 1 ≤ (2 * t) ^ 3 := Nat.one_le_pow _ _ hτ1
  have hA : mValue t ≤ mValue t * (2 * t) ^ 3 :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hB : 2 * t ≤ mValue t * (2 * t) ^ 3 := by
    calc 2 * t ≤ (2 * t) ^ 3 := hτ3
      _ ≤ mValue t * (2 * t) ^ 3 := Nat.le_mul_of_pos_left _ hm1
  have hC : 20 * (2 * t) * (S + 2) ≤
      20 * A * (mValue t * (2 * t) ^ 3) + 40 * (2 * t) := by
    calc
      20 * (2 * t) * (S + 2) ≤
          20 * (2 * t) * (A * mValue t * (2 * t) ^ 2 + 2) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hS 2)
      _ = _ := by ring
  have hgoal : (42 + 20 * A) * mValue t * (2 * t) ^ 3 =
      42 * (mValue t * (2 * t) ^ 3) + 20 * A * (mValue t * (2 * t) ^ 3) := by ring
  omega

/-- Ledger: def-K. The constant is fixed before `t`; the circuit is the exact
Forrelation circuit already constructed in the development. -/
theorem construction_K_family (k : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℕ, ∀ t : ℕ, 1 ≤ t → ∃ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) ∧
      Fintype.card (TestIndex (2 * t) (40 * t) C.size) ≤
        B * mValue t * (2 * t) ^ 3 := by
  cases k with
  | zero => omega
  | succ l =>
    refine ⟨42 + 20 * Forrelation.forrConstant (l + 1), fun t ht =>
      ⟨Forrelation.forrCircuit l t, Forrelation.forrCircuit_realises l t, ?_⟩⟩
    exact construction_K_bound t _ _ ht (Forrelation.forrCircuit_size_le l t ht)

end QuarticQuery.Paper

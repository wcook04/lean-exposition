module

public import QuarticQuery.Construction.Transcript
public import QuarticQuery.Construction.Winner

/-!
# The local tests of Lemma 2.2

`WinsAt` at `(i, s)` is a conjunction of `2 ^ ℓ + (2 ^ ℓ - 1) + r * (S + 2)` exact
tests, with one index type for every `(i, s)`. Each test is computed by a decision
tree of depth at most `max 3 (ℓ + 1)`. A pointer test is adaptive: it reads `ℓ`
pointer bits, then the one target bit they select, so it is a shallow tree and
not a function of a small fixed set of bits.

The trees carry the classical query cost only. Coherent evaluation is not modelled.
-/

public section

namespace QuarticQuery

/-! ## Decision-tree combinators -/

section Trees

variable {ι : Type}

/-- Read an optional location; `none` costs nothing and reads `false`. -/
@[expose] def readOpt (x : BitInput ι) : Option ι → Bool
  | none => false
  | some l => x l

@[expose] def queryOpt : Option ι → (Bool → QueryTree ι) → QueryTree ι
  | none, k => k false
  | some l, k => .query l (k false) (k true)

theorem queryOpt_eval (x : BitInput ι) (p : Option ι) (k : Bool → QueryTree ι) :
    (queryOpt p k).eval x = (k (readOpt x p)).eval x := by
  cases p with
  | none => rfl
  | some l => cases h : x l <;> simp [queryOpt, readOpt, QueryTree.eval, h]

theorem queryOpt_depth_le {p : Option ι} {k : Bool → QueryTree ι} {d : ℕ}
    (hk : ∀ b, (k b).depth ≤ d) : (queryOpt p k).depth ≤ d + 1 := by
  cases p with
  | none => exact (hk _).trans (Nat.le_succ d)
  | some l =>
    have h1 := hk false
    have h2 := hk true
    simp only [queryOpt, QueryTree.depth]
    omega

/-- Read `n` locations in order, then continue with the word read. -/
@[expose] def queryWord : (n : ℕ) → (Fin n → ι) → ((Fin n → Bool) → QueryTree ι) → QueryTree ι
  | 0, _, k => k Fin.elim0
  | n + 1, loc, k =>
      .query (loc 0)
        (queryWord n (fun b => loc b.succ) fun w => k (Fin.cons false w))
        (queryWord n (fun b => loc b.succ) fun w => k (Fin.cons true w))

theorem queryWord_eval (x : BitInput ι) (n : ℕ) (loc : Fin n → ι)
    (k : (Fin n → Bool) → QueryTree ι) :
    (queryWord n loc k).eval x = (k fun b => x (loc b)).eval x := by
  induction n with
  | zero =>
    have : (fun b : Fin 0 => x (loc b)) = Fin.elim0 := funext fun b => b.elim0
    rw [this]
    rfl
  | succ n ih =>
    have hword : ∀ c : Bool, x (loc 0) = c →
        (Fin.cons c fun b : Fin n => x (loc b.succ)) = fun b : Fin (n + 1) => x (loc b) := by
      intro c hc
      funext b
      refine Fin.cases ?_ (fun _ => ?_) b
      · simpa using hc.symm
      · simp
    cases hc : x (loc 0) with
    | false => simp [queryWord, QueryTree.eval, hc, ih, hword false hc]
    | true => simp [queryWord, QueryTree.eval, hc, ih, hword true hc]

theorem queryWord_depth_le {n : ℕ} {loc : Fin n → ι} {k : (Fin n → Bool) → QueryTree ι} {d : ℕ}
    (hk : ∀ w, (k w).depth ≤ d) : (queryWord n loc k).depth ≤ n + d := by
  induction n generalizing d with
  | zero => simpa [queryWord] using hk _
  | succ n ih =>
    have h1 := ih (loc := fun b => loc b.succ)
      (k := fun w => k (Fin.cons false w)) (d := d) fun _ => hk _
    have h2 := ih (loc := fun b => loc b.succ)
      (k := fun w => k (Fin.cons true w)) (d := d) fun _ => hk _
    simp only [queryWord, QueryTree.depth]
    omega

end Trees

/-! ## One index type for every column -/

/-- The `e`-th column other than `i`, skipping `i`. This is what lets the pointer
tests share an index type across columns. -/
@[expose] def otherColumn {ℓ : ℕ} (i : Column ℓ) (e : Fin (2 ^ ℓ - 1)) :
    {j : Column ℓ // j ≠ i} :=
  if he : e.val < i.val then
    ⟨⟨e.val, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
  else
    ⟨⟨e.val + 1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩

theorem otherColumn_bijective {ℓ : ℕ} (i : Column ℓ) :
    Function.Bijective (otherColumn i) := by
  constructor
  · intro a b hab
    have := congrArg (fun j => j.val.val) hab
    simp only [otherColumn] at this
    ext
    split_ifs at this <;> simp at this <;> omega
  · rintro ⟨j, hj⟩
    have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
    by_cases hlt : j.val < i.val
    · refine ⟨⟨j.val, by have := j.isLt; have := i.isLt; omega⟩, ?_⟩
      ext
      simp [otherColumn, hlt]
    · refine ⟨⟨j.val - 1, by have := j.isLt; omega⟩, ?_⟩
      have h1 : ¬ j.val - 1 < i.val := by omega
      ext
      simp [otherColumn, h1]
      omega

/-- Ledger: lem-2.2.i. The test indices: one per bit of `X_i`, one per other
column, and for each `h` one per gate plus the output tests `false` (`d = 1`) and
`true` (`b = s h`). The type does not mention `(i, s)`. -/
abbrev TestIndex (ℓ r S : ℕ) := Column ℓ ⊕ Fin (2 ^ ℓ - 1) ⊕ Fin r × (Fin S ⊕ Bool)

/-- Ledger: def-K. -/
theorem card_testIndex (ℓ r S : ℕ) :
    Fintype.card (TestIndex ℓ r S) = 2 ^ ℓ + (2 ^ ℓ - 1) + r * (S + 2) := by
  simp [Fintype.card_sum, Fintype.card_prod, add_assoc]

/-! ## The tests -/

section Tests

variable {κ : Type}

/-- Ledger: lem-2.2.i. The exact test with index `t` at `(i, s)`. -/
@[expose] def localTest (C : Circuit κ) (ℓ r : ℕ) (x : BitInput (BitLoc ℓ r C.size κ))
    (i : Column ℓ) (s : Address r) : TestIndex ℓ r C.size → Bool
  | .inl b => readX x i b
  | .inr (.inl e) =>
      !readX x (otherColumn i e).val
        (pointerEquiv ℓ (readPointerBit x i s (otherColumn i e)))
  | .inr (.inr (h, .inl g)) =>
      readTranscript x i s h g ==
        (C.gate g).table
          (predecessorValue C (readA x i h) (readTranscript x i s h) g (C.gate g).left)
          (predecessorValue C (readA x i h) (readTranscript x i s h) g (C.gate g).right)
  | .inr (.inr (h, .inr false)) => readTranscript x i s h C.domainOut
  | .inr (.inr (h, .inr true)) => readTranscript x i s h C.valueOut == s h

/-- Where a predecessor of gate `g` of the `h`-th transcript sits in the input. -/
@[expose] def predecessorLoc (C : Circuit κ) (ℓ r : ℕ) (i : Column ℓ) (s : Address r)
    (h : Fin r) (g : Fin C.size) :
    Option (κ ⊕ Fin g.val) → Option (BitLoc ℓ r C.size κ)
  | none => none
  | some (.inl q) => some (.inr (.inl (i, h, q)))
  | some (.inr e) => some (.inr (.inr (.inr (i, s, h, ⟨e.val, lt_trans e.isLt g.isLt⟩))))

theorem readOpt_predecessorLoc (C : Circuit κ) (ℓ r : ℕ) (x : BitInput (BitLoc ℓ r C.size κ))
    (i : Column ℓ) (s : Address r) (h : Fin r) (g : Fin C.size)
    (p : Option (κ ⊕ Fin g.val)) :
    readOpt x (predecessorLoc C ℓ r i s h g p) =
      predecessorValue C (readA x i h) (readTranscript x i s h) g p := by
  rcases p with _ | q | e <;> rfl

/-- Ledger: lem-2.2.i. The tree for test `t`, fixed before the input. A gate test
reads at most three bits. A pointer test reads `ℓ` pointer bits, then the target. -/
@[expose] def localTestTree (C : Circuit κ) (ℓ r : ℕ) (i : Column ℓ) (s : Address r) :
    TestIndex ℓ r C.size → QueryTree (BitLoc ℓ r C.size κ)
  | .inl b => .query (.inl (i, b)) (.leaf false) (.leaf true)
  | .inr (.inl e) =>
      queryWord ℓ (fun b => .inr (.inr (.inl ⟨i, (s, otherColumn i e, b)⟩))) fun w =>
        .query (.inl ((otherColumn i e).val, pointerEquiv ℓ w)) (.leaf true) (.leaf false)
  | .inr (.inr (h, .inl g)) =>
      queryOpt (predecessorLoc C ℓ r i s h g (C.gate g).left) fun a =>
        queryOpt (predecessorLoc C ℓ r i s h g (C.gate g).right) fun b =>
          .query (.inr (.inr (.inr (i, s, h, g))))
            (.leaf (false == (C.gate g).table a b))
            (.leaf (true == (C.gate g).table a b))
  | .inr (.inr (h, .inr false)) =>
      .query (.inr (.inr (.inr (i, s, h, C.domainOut)))) (.leaf false) (.leaf true)
  | .inr (.inr (h, .inr true)) =>
      .query (.inr (.inr (.inr (i, s, h, C.valueOut))))
        (.leaf (false == s h)) (.leaf (true == s h))

/-- Ledger: lem-2.2.i. Each tree computes its test exactly, on every input. -/
theorem localTestTree_eval (C : Circuit κ) (ℓ r : ℕ) (x : BitInput (BitLoc ℓ r C.size κ))
    (i : Column ℓ) (s : Address r) (t : TestIndex ℓ r C.size) :
    (localTestTree C ℓ r i s t).eval x = localTest C ℓ r x i s t := by
  rcases t with b | e | ⟨h, g | _ | _⟩
  · change (if x (.inl (i, b)) then _ else _) = x (.inl (i, b))
    cases x (.inl (i, b)) <;> rfl
  · simp only [localTestTree, localTest, queryWord_eval]
    have key : ∀ b : Bool, (if b = true then QueryTree.eval (.leaf false) x
        else QueryTree.eval (.leaf true) x) = !b := by
      intro b
      cases b <;> rfl
    exact key (readX x (otherColumn i e).val
      (pointerEquiv ℓ (readPointerBit x i s (otherColumn i e))))
  · simp only [localTestTree, localTest, queryOpt_eval, readOpt_predecessorLoc]
    change (if readTranscript x i s h g then _ else _) = _
    cases readTranscript x i s h g <;> rfl
  · change (if x _ then _ else _) = readTranscript x i s h C.domainOut
    cases hx : readTranscript x i s h C.domainOut
    · simp only [readTranscript] at hx; simp [hx, QueryTree.eval]
    · simp only [readTranscript] at hx; simp [hx, QueryTree.eval]
  · change (if x _ then _ else _) = (readTranscript x i s h C.valueOut == s h)
    cases hx : readTranscript x i s h C.valueOut
    · simp only [readTranscript] at hx; simp [hx, QueryTree.eval]
    · simp only [readTranscript] at hx; simp [hx, QueryTree.eval]

/-- Ledger: lem-2.2.i. Every test costs at most `max 3 (ℓ + 1)` queries. -/
theorem localTestTree_depth_le (C : Circuit κ) (ℓ r : ℕ) (i : Column ℓ) (s : Address r)
    (t : TestIndex ℓ r C.size) : (localTestTree C ℓ r i s t).depth ≤ max 3 (ℓ + 1) := by
  rcases t with b | e | ⟨h, g | _ | _⟩
  · simp [localTestTree, QueryTree.depth]
  · have : (localTestTree C ℓ r i s (.inr (.inl e))).depth ≤ ℓ + 1 :=
      queryWord_depth_le fun w => by simp [QueryTree.depth]
    exact this.trans (le_max_right _ _)
  · have : (localTestTree C ℓ r i s (.inr (.inr (h, .inl g)))).depth ≤ 1 + 1 + 1 :=
      queryOpt_depth_le fun a => queryOpt_depth_le fun b => by simp [QueryTree.depth]
    exact this.trans (le_max_left _ _)
  · simp [localTestTree, QueryTree.depth]
  · simp [localTestTree, QueryTree.depth]

variable {f : PartialBool κ} {C : Circuit κ} {ℓ r : ℕ}
  {x : BitInput (BitLoc ℓ r C.size κ)} {i : Column ℓ} {s : Address r}

/-- Ledger: lem-2.2.i. Lemma 2.2: at every input, `WinsAt` at `(i, s)` is exactly
the conjunction of the tests. -/
theorem winsAt_iff_localTests (hC : CircuitRealises C f) :
    WinsAt f C ℓ r x i s ↔ ∀ t, localTest C ℓ r x i s t = true := by
  constructor
  · rintro ⟨hX, hf, hG, hP⟩ (b | e | ⟨h, g | _ | _⟩)
    · exact hX b
    · simpa [localTest] using hP (otherColumn i e)
    · simpa [localTest] using hG h g
    · exact (hC.correct _ _ (hG h)).1.2 ⟨s h, hf h⟩
    · have hd := (hC.correct _ _ (hG h)).1.2 ⟨s h, hf h⟩
      have hv := (hC.correct _ _ (hG h)).2 hd
      have : s h = readTranscript x i s h C.valueOut :=
        Option.some.inj ((hf h).symm.trans hv)
      simp [localTest, this]
  · intro ht
    have hG : ∀ h, GateConsistent C (readA x i h) (readTranscript x i s h) := fun h g => by
      simpa [localTest] using ht (.inr (.inr (h, .inl g)))
    refine ⟨fun b => ht (.inl b), fun h => ?_, hG, fun j => ?_⟩
    · have hd : readTranscript x i s h C.domainOut = true := ht (.inr (.inr (h, .inr false)))
      have hb : readTranscript x i s h C.valueOut = s h := by
        simpa [localTest] using ht (.inr (.inr (h, .inr true)))
      rw [(hC.correct _ _ (hG h)).2 hd, hb]
    · obtain ⟨e, rfl⟩ := (otherColumn_bijective i).2 j
      simpa [localTest] using ht (.inr (.inl e))

/-- A winning column has exactly one address at which every test passes. -/
theorem localTests_iff_eq_of_winsAt (hC : CircuitRealises C f) (hw : WinsAt f C ℓ r x i s)
    (s' : Address r) : (∀ t, localTest C ℓ r x i s' t = true) ↔ s' = s :=
  ⟨fun ht => winsAt_address_unique ((winsAt_iff_localTests hC).mpr ht) hw,
    fun h => h ▸ (winsAt_iff_localTests hC).mp hw⟩

/-- Ledger: lem-2.2.i. A nonwinning column has a failing test at every address. -/
theorem exists_failing_localTest (hC : CircuitRealises C f)
    (hn : ¬ ∃ s, WinsAt f C ℓ r x i s) (s : Address r) :
    ∃ t, localTest C ℓ r x i s t = false := by
  by_contra hall
  push Not at hall
  exact hn ⟨s, (winsAt_iff_localTests hC).mpr fun t => by simpa using hall t⟩

/-- Ledger: def-F. -/
theorem addressedF_eq_true_iff :
    addressedF f C ℓ r x = true ↔ ∃ i s, WinsAt f C ℓ r x i s := by
  simp [addressedF]

/-- Ledger: def-F. The total function is decided by the local tests. -/
theorem addressedF_eq_true_iff_localTests (hC : CircuitRealises C f) :
    addressedF f C ℓ r x = true ↔ ∃ i s, ∀ t, localTest C ℓ r x i s t = true := by
  simp only [addressedF_eq_true_iff, winsAt_iff_localTests hC]

/-- Ledger: lem-2.2.i. `WinsAt` read through the output tests `d = 1` and
`b = s h` on correct transcripts. This is where `f` enters through the circuit. -/
theorem winsAt_iff_outputs (hC : CircuitRealises C f) :
    WinsAt f C ℓ r x i s ↔
      (∀ j, readX x i j = true) ∧
      (∀ h, readTranscript x i s h = circuitEval C (readA x i h)) ∧
      (∀ h, readTranscript x i s h C.domainOut = true) ∧
      (∀ h, readTranscript x i s h C.valueOut = s h) ∧
      (∀ j : {j : Column ℓ // j ≠ i},
        readX x j.val (pointerEquiv ℓ (readPointerBit x i s j)) = false) := by
  constructor
  · rintro ⟨hX, hf, hG, hP⟩
    have hd := fun h => (hC.correct _ _ (hG h)).1.2 ⟨s h, hf h⟩
    exact ⟨hX, fun h => gateConsistent_iff_eq_circuitEval.mp (hG h), hd,
      fun h => (Option.some.inj ((hf h).symm.trans ((hC.correct _ _ (hG h)).2 (hd h)))).symm,
      hP⟩
  · rintro ⟨hX, hT, hd, hb, hP⟩
    have hG := fun h => gateConsistent_iff_eq_circuitEval.mpr (hT h)
    refine ⟨hX, fun h => ?_, hG, hP⟩
    rw [(hC.correct _ _ (hG h)).2 (hd h), hb]

/-- `s_i` of equation (7), once every `f(A_{i,h})` is defined. -/
@[expose] noncomputable def trueAddress (f : PartialBool κ) (x : BitInput (BitLoc ℓ r C.size κ))
    (i : Column ℓ) (hdef : ∀ h, promised f (readA x i h)) : Address r :=
  fun h => Classical.choose (hdef h)

theorem apply_eq_trueAddress (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ)
    (hdef : ∀ h, promised f (readA x i h)) (h : Fin r) :
    f (readA x i h) = some (trueAddress f x i hdef h) :=
  Classical.choose_spec (hdef h)

/-- Column `i` wins at `s` in the paper's words: `X_i` is all ones, every `f(A_{i,h})`
is defined, `s = s_i`, the transcripts at `s` are the true evaluations, and (8). -/
@[expose] def PaperWinsAt (f : PartialBool κ) (C : Circuit κ) (ℓ r : ℕ)
    (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) (s : Address r) : Prop :=
  (∀ j, readX x i j = true) ∧
  (∃ hdef : ∀ h, promised f (readA x i h), s = trueAddress f x i hdef) ∧
  (∀ h, readTranscript x i s h = circuitEval C (readA x i h)) ∧
  (∀ j : {j : Column ℓ // j ≠ i},
    readX x j.val (pointerEquiv ℓ (readPointerBit x i s j)) = false)

/-- Ledger: claim-winner-fidelity. `WinsAt` is the paper's condition. The statement's
`WinsAt` names `f` directly, so no circuit hypothesis is needed here;
`winsAt_iff_outputs` is the form that uses circuit correctness. -/
theorem winsAt_iff_paperWinsAt :
    WinsAt f C ℓ r x i s ↔ PaperWinsAt f C ℓ r x i s := by
  constructor
  · rintro ⟨hX, hf, hG, hP⟩
    have hdef : ∀ h, promised f (readA x i h) := fun h => ⟨s h, hf h⟩
    refine ⟨hX, ⟨hdef, funext fun h => ?_⟩,
      fun h => gateConsistent_iff_eq_circuitEval.mp (hG h), hP⟩
    exact Option.some.inj ((hf h).symm.trans (apply_eq_trueAddress x i hdef h))
  · rintro ⟨hX, ⟨hdef, rfl⟩, hT, hP⟩
    exact ⟨hX, apply_eq_trueAddress x i hdef,
      fun h => gateConsistent_iff_eq_circuitEval.mpr (hT h), hP⟩

end Tests

theorem Fkm_eq_true_iff_localTests {k t : ℕ} {C : Circuit (ForrelationCoord k t)}
    (hC : CircuitRealises C (P k t))
    {x : BitInput (BitLoc (2 * t) (40 * t) C.size (ForrelationCoord k t))} :
    Fkm k t C x = true ↔ ∃ i s, ∀ e, localTest C (2 * t) (40 * t) x i s e = true :=
  addressedF_eq_true_iff_localTests hC

end QuarticQuery

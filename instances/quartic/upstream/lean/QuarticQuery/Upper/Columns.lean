module

public import QuarticQuery.Upper.Decode
public import QuarticQuery.Upper.Tournament
public import QuarticQuery.Construction.LocalTests

/-!
# Section 3.3: comparing columns and verifying the list

Everything is fixed before the input: `k`, `t`, the circuit, and the repetition count.
`addrLaw` is the law of the decoded address of a column. The comparison decodes two
addresses, reads each pointer toward the other at its decoded address, and applies the
rule of Section 3.3. A column's verification decodes an address, then searches for a
failing local test at it.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Forrelation QuarticQuery.Tournament QuarticQuery.Amplification

variable {k t : ℕ} {C : Circuit (ForrelationCoord k t)}

/-- The input coordinates of `F_{k,m}`. -/
abbrev Loc (k t : ℕ) (C : Circuit (ForrelationCoord k t)) :=
  BitLoc (2 * t) (40 * t) C.size (ForrelationCoord k t)

instance (priority := high) : Inhabited (Loc k t C) :=
  ⟨.inl (⟨0, Nat.two_pow_pos _⟩, ⟨0, Nat.two_pow_pos _⟩)⟩

instance (priority := high) : Nonempty (Loc k t C) := ⟨default⟩

/-- Column indices. -/
abbrev Col (t : ℕ) := Column (2 * t)

/-- Addresses. -/
abbrev Addr (t : ℕ) := Address (40 * t)

theorem card_col (t : ℕ) : Fintype.card (Col t) = mValue t := by simp [mValue]

/-! ## Decoding an address -/

/-- Ledger: claim-coherent-access. The law of the address decoded from column `i` by the
`n`-fold threshold test on each instance. -/
noncomputable def addrLaw (n : ℕ) (x : BitInput (Loc k t C)) (i : Col t) (s : Addr t) : ℝ :=
  ∏ h, bern (decodeProb k t n (readA x i h)) (s h)

/-- The reads of one address decoding. -/
def addrCost (k t n : ℕ) : ℕ := 40 * t * (n * k)

/-- The locations of the instance `A_{i,h}`. -/
def instLoc (i : Col t) (h : Fin (40 * t)) (c : ForrelationCoord k t) : Loc k t C :=
  .inr (.inl (i, h, c))

theorem addr_samples (hk : 1 ≤ k) (n : ℕ) (i : Col t) :
    Samples (addrCost k t n) fun (x : BitInput (Loc k t C)) s => addrLaw n x i s := by
  have hd : ∀ h : Fin (40 * t), Samples (n * k) fun (x : BitInput (Loc k t C)) b =>
      bern (decodeProb k t n fun c => x (instLoc i h c)) b :=
    fun h => decode_samples hk (instLoc i h) n
  exact Samples.pi hd

/-- Ledger: claim-coherent-access. If all instances of a column are defined, its address
decodes correctly with probability at least `1 - ε`. -/
theorem addrLaw_good (hk : 1 ≤ k) {n : ℕ} {ε : ℝ} (ht : 1 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : repetitions k (ε / (40 * t : ℕ)) ≤ n) {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t}
    (hs : ∀ h, P k t (readA x i h) = some (s h)) : 1 - ε ≤ addrLaw n x i s := by
  have hr : (0 : ℝ) < (40 * t : ℕ) := by
    have : 0 < 40 * t := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (40 * t : ℕ) := by
    have : 1 ≤ 40 * t := by omega
    exact_mod_cast this
  have hη : 0 < ε / (40 * t : ℕ) := div_pos hε hr
  have := one_sub_le_prod (r := 40 * t) (f := fun h => bern (decodeProb k t n (readA x i h)) (s h))
    (η := ε / (40 * t : ℕ)) ((div_le_self hε.le hr1).trans hε1)
    fun h => decodeProb_correct hk hη hn _ (hs h)
  rw [mul_div_cancel₀ _ hr.ne'] at this
  exact this

/-! ## One disqualification -/

/-- The bit: does the pointer of column `i`, at address `s`, find a zero in column `j`? -/
def disq (x : BitInput (Loc k t C)) (i : Col t) (s : Addr t) (j : Col t) (hij : j ≠ i) : Bool :=
  !readX x j (pointerEquiv (2 * t) (readPointerBit x i s ⟨j, hij⟩))

/-- Read the pointer, then the bit it selects. -/
def disqTree (i : Col t) (s : Addr t) (j : Col t) (hij : j ≠ i) : QueryTree (Loc k t C) :=
  queryWord (2 * t) (fun b => .inr (.inr (.inl ⟨i, (s, ⟨j, hij⟩, b)⟩))) fun w =>
    .query (.inl (j, pointerEquiv (2 * t) w)) (.leaf true) (.leaf false)

theorem disqTree_eval (x : BitInput (Loc k t C)) (i : Col t) (s : Addr t) (j : Col t)
    (hij : j ≠ i) : (disqTree i s j hij).eval x = disq x i s j hij := by
  simp only [disqTree, disq, queryWord_eval]
  have key : ∀ b : Bool, (if b = true then QueryTree.eval (.leaf false) x
      else QueryTree.eval (.leaf true) x) = !b := by
    intro b
    cases b <;> rfl
  exact key (readX x j (pointerEquiv (2 * t) (readPointerBit x i s ⟨j, hij⟩)))

theorem disqTree_depth (i : Col t) (s : Addr t) (j : Col t) (hij : j ≠ i) :
    (disqTree (C := C) i s j hij).depth ≤ 2 * t + 1 :=
  queryWord_depth_le fun w => by simp [QueryTree.depth]

theorem Samples.pt_bind {ι β γ : Type} [Fintype β] {n m : ℕ} {g : BitInput ι → β}
    {K : β → BitInput ι → γ → ℝ} (h : Samples n fun x b => pt (g x) b)
    (hK : ∀ b, Samples m (K b)) : Samples (n + m) fun x c => K (g x) x c :=
  (h.bind hK).congr fun x c => (sum_pt_mul (fun b => K b x c) (g x)).symm

theorem Samples.disq (i : Col t) (s : Addr t) (j : Col t) (hij : j ≠ i) :
    Samples (2 * t + 1) fun (x : BitInput (Loc k t C)) b => pt (disq x i s j hij) b :=
  ((Samples.tree (disqTree i s j hij)).mono (disqTree_depth i s j hij)).congr fun x b => by
    rw [disqTree_eval]

/-! ## Comparison -/

/-- The first of a sorted pair wins unless only the second disqualifies its opponent. -/
def firstWins (d₁ d₂ : Bool) : Bool := !(d₂ && !d₁)

/-- The probability that the first of a sorted pair wins. -/
noncomputable def coreProb (n : ℕ) (x : BitInput (Loc k t C)) (i j : Col t) (hij : j ≠ i) : ℝ :=
  ∑ s₁, addrLaw n x i s₁ * ∑ s₂, addrLaw n x j s₂ *
    (if firstWins (disq x i s₁ j hij) (disq x j s₂ i hij.symm) then 1 else 0)

/-- The reads of one comparison. -/
def cmpCost (k t n : ℕ) : ℕ := addrCost k t n + (addrCost k t n + ((2 * t + 1) + (2 * t + 1)))

/-- A Bernoulli law on `Bool` is its probability of `true`. -/
theorem Samples.toBern {ι : Type} {n : ℕ} {L : BitInput ι → Bool → ℝ} (h : Samples n L) :
    Samples n fun x b => bern (L x true) b :=
  h.congr fun x b => by
    have := h.sum_eq_one x
    rw [Fintype.sum_bool] at this
    cases b
    · simp only [bern, Bool.false_eq_true, ite_false]
      linarith
    · simp [bern]

theorem bern_pt_true {p : ℝ} : bern p true = p := by simp [bern]

/-- Ledger: claim-coherent-access. The coherent comparison of a sorted pair, with both
address decodings, both pointers and both target bits retained. -/
theorem core_samples (hk : 1 ≤ k) (n : ℕ) (i j : Col t) (hij : j ≠ i) :
    Samples (cmpCost k t n) fun (x : BitInput (Loc k t C)) b =>
      bern (coreProb n x i j hij) b := by
  let K₂ : Addr t → Addr t → BitInput (Loc k t C) → Bool → ℝ := fun s₁ s₂ x b =>
    pt (firstWins (disq x i s₁ j hij) (disq x j s₂ i hij.symm)) b
  have hK₂ : ∀ s₁ s₂, Samples ((2 * t + 1) + (2 * t + 1)) (K₂ s₁ s₂) := fun s₁ s₂ => by
    refine ((Samples.disq i s₁ j hij).pt_bind (K := fun d₁ x b =>
      pt (firstWins d₁ (disq x j s₂ i hij.symm)) b) (m := 2 * t + 1) fun d₁ => ?_)
    refine ((Samples.disq j s₂ i hij.symm).pt_bind (K := fun d₂ _ b =>
      pt (firstWins d₁ d₂) b) (m := 0) fun d₂ => Samples.pure _)
  have hK₁ : ∀ s₁, Samples (addrCost k t n + ((2 * t + 1) + (2 * t + 1)))
      fun x b => ∑ s₂, addrLaw n x j s₂ * K₂ s₁ s₂ x b := fun s₁ =>
    (addr_samples hk n j).bind (hK₂ s₁)
  have hb := ((addr_samples (C := C) hk n i).bind hK₁).toBern
  refine hb.congr fun x b => ?_
  congr 1
  simp only [coreProb, K₂]
  refine Finset.sum_congr rfl fun s₁ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun s₂ _ => ?_
  congr 1
  cases firstWins (disq x i s₁ j hij) (disq x j s₂ i hij.symm) <;> simp [pt_self, pt_of_ne]

theorem coreProb_mem (hk : 1 ≤ k) (n : ℕ) (x : BitInput (Loc k t C)) (i j : Col t) (hij : j ≠ i) :
    0 ≤ coreProb n x i j hij ∧ coreProb n x i j hij ≤ 1 := by
  have h := core_samples (C := C) hk n i j hij
  have h0 := h.nonneg x true
  have h1 := h.le_one x true
  simpa [bern] using And.intro h0 h1

/-- Ledger: eq-10. The comparison probabilities, from the fixed sorted circuit. -/
noncomputable def cmpProb (n : ℕ) (x : BitInput (Loc k t C)) (i j : Col t) : ℝ :=
  if h : i = j then 0
  else if i < j then coreProb n x i j (Ne.symm h)
  else 1 - coreProb n x j i h

theorem cmp_samples (hk : 1 ≤ k) (n : ℕ) (i j : Col t) :
    Samples (cmpCost k t n) fun (x : BitInput (Loc k t C)) b => bern (cmpProb n x i j) b := by
  unfold cmpProb
  by_cases h : i = j
  · refine (Samples.pure false).mono (Nat.zero_le _) |>.congr fun x b => ?_
    cases b <;> simp [h, bern, pt_self, pt_of_ne]
  · by_cases h' : i < j
    · simpa only [h, h', ↓reduceDIte, ↓reduceIte] using core_samples hk n i j (Ne.symm h)
    · have hm := ((core_samples (C := C) hk n j i h).map not).toBern
      refine hm.congr fun x b => ?_
      simp only [h, h', ↓reduceDIte, ↓reduceIte]
      congr 1
      simp only [Fintype.sum_bool, bern, ite_true, Bool.false_eq_true, ite_false, Bool.not_true,
        Bool.not_false]
      simp [pt_self, pt_of_ne]

theorem cmpProb_isComparison (x : BitInput (Loc k t C)) (n : ℕ) :
    IsComparison (cmpProb (C := C) n x) := by
  refine ⟨fun i j hne => ?_, fun i => by simp [cmpProb]⟩
  simp only [cmpProb, hne, Ne.symm hne, ↓reduceDIte]
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

theorem cmpProb_unit (hk : 1 ≤ k) (x : BitInput (Loc k t C)) (n : ℕ) :
    UnitValued (cmpProb (C := C) n x) := by
  intro i j
  have h := cmp_samples (C := C) hk n i j
  have h0 := h.nonneg x true
  have h1 := h.le_one x true
  simpa [bern] using And.intro h0 h1

/-! ## The winner dominates -/

theorem sum_addrLaw (hk : 1 ≤ k) (n : ℕ) (x : BitInput (Loc k t C)) (i : Col t) :
    ∑ s, addrLaw n x i s = 1 :=
  (addr_samples hk n i).sum_eq_one x

theorem addrLaw_nonneg (hk : 1 ≤ k) (n : ℕ) (x : BitInput (Loc k t C)) (i : Col t) (s : Addr t) :
    0 ≤ addrLaw n x i s :=
  (addr_samples hk n i).nonneg x s

/-- Ledger: claim-winner-dominates. A winner beats every other column with probability
at least that of decoding its own address, whatever the opponent's instances are. -/
theorem cmpProb_winner (hk : 1 ≤ k) {n : ℕ} {x : BitInput (Loc k t C)} {i j : Col t}
    {s : Addr t} (hw : WinsAt (P k t) C (2 * t) (40 * t) x i s) (hne : j ≠ i) :
    addrLaw n x i s ≤ cmpProb n x i j := by
  classical
  have hd1 : ∀ hij : j ≠ i, disq x i s j hij = true := fun hij => by
    simp only [disq]
    rw [show readPointerBit x i s ⟨j, hij⟩ = readPointerBit x i s ⟨j, hne⟩ from rfl,
      winner_finds_zero hw j hne]
    rfl
  have hd2 : ∀ (a : Addr t) (hij : i ≠ j), disq x j a i hij = false := fun a hij => by
    simp only [disq]
    rw [hw.1]
    rfl
  have hu := fun s' => addrLaw_nonneg (C := C) hk n x i s'
  have hu' := fun s' => addrLaw_nonneg (C := C) hk n x j s'
  rcases lt_or_gt_of_ne hne with h | h
  · -- `j < i`: the winner is second
    simp only [cmpProb, Ne.symm hne, not_lt.2 h.le, ↓reduceDIte, ↓reduceIte]
    have hc : coreProb n x j i (Ne.symm hne) ≤ 1 - addrLaw n x i s := by
      unfold coreProb
      calc _ ≤ ∑ s₁, addrLaw n x j s₁ * (1 - addrLaw n x i s) := by
            refine Finset.sum_le_sum fun s₁ _ => mul_le_mul_of_nonneg_left ?_ (hu' s₁)
            have hsum := sum_addrLaw (C := C) hk n x i
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hsum
            have hfirst : ∀ s₂, firstWins (disq x j s₁ i (Ne.symm hne))
                (disq x i s₂ j hne) = !disq x i s₂ j hne := fun s₂ => by
              rw [hd2 s₁ (Ne.symm hne)]
              simp [firstWins]
            simp only [hfirst]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hd1]
            simp only [Bool.not_true, Bool.false_eq_true, ite_false, mul_zero, zero_add]
            calc _ ≤ ∑ s₂ ∈ Finset.univ.erase s, addrLaw n x i s₂ := by
                  refine Finset.sum_le_sum fun s₂ _ => ?_
                  have := hu s₂
                  split_ifs <;> linarith
              _ = 1 - addrLaw n x i s := by linarith
        _ = 1 - addrLaw n x i s := by
            rw [← Finset.sum_mul, sum_addrLaw hk, one_mul]
    linarith
  · -- `i < j`: the winner is first
    simp only [cmpProb, Ne.symm hne, h, ↓reduceDIte, ↓reduceIte]
    unfold coreProb
    have hin : ∑ s₂, addrLaw n x j s₂ *
        (if firstWins (disq x i s j hne) (disq x j s₂ i (Ne.symm hne)) then (1 : ℝ) else 0) = 1 := by
      have e : ∀ s₂, addrLaw n x j s₂ *
          (if firstWins (disq x i s j hne) (disq x j s₂ i (Ne.symm hne)) then (1 : ℝ) else 0) =
          addrLaw n x j s₂ := fun s₂ => by simp [firstWins, hd1 hne]
      rw [Finset.sum_congr rfl fun s₂ _ => e s₂, sum_addrLaw hk]
    calc addrLaw n x i s = addrLaw n x i s * ∑ s₂, addrLaw n x j s₂ *
          (if firstWins (disq x i s j hne) (disq x j s₂ i (Ne.symm hne)) then (1 : ℝ) else 0) := by
          rw [hin, mul_one]
      _ ≤ _ := Finset.single_le_sum (f := fun s₁ => addrLaw n x i s₁ * ∑ s₂, addrLaw n x j s₂ *
          (if firstWins (disq x i s₁ j hne) (disq x j s₂ i (Ne.symm hne)) then (1 : ℝ) else 0))
          (fun s₁ _ => mul_nonneg (hu s₁) (Finset.sum_nonneg fun s₂ _ => mul_nonneg (hu' s₂)
            (by split_ifs <;> norm_num))) (Finset.mem_univ s)

end QuarticQuery.Upper

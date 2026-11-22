module

public import QuarticQuery.Upper.Bound
public import QuarticQuery.Paper.QuantumAmplification

/-!
# Section 3.3: the actual decoder, comparison, verifier and error law

Compiled as part of the `QuarticQuery` library target.
These statements expose the already implemented procedures, then give the
paper's probability and worst-case bit-query guarantees as separate theorems.
The existing `Samples` budget counts logical reads; `Runs` counts physical
bit-oracle queries. The latter budget includes the compiler's factor of two.

The proofs use the compiled `Upper` modules.
They do not import the earlier `Paper.Section3` statements.
-/

@[expose] public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Forrelation
open QuarticQuery.Tournament QuarticQuery.Amplification
open scoped BigOperators

variable {k t : ℕ} {C : Circuit (ForrelationCoord k t)}

/-! ## Decoding, including inputs outside the promise -/

/-- Ledger: def-decode. The independent retained-workspace decodings have the
product address law used by the existing implementation. -/
theorem quantumDecode (hk : 1 ≤ k) (n : ℕ) (i : Col t) :
    Samples (addrCost k t n) fun (x : BitInput (Loc k t C)) s =>
      addrLaw n x i s :=
  addr_samples hk n i

/-- Ledger: def-decode. Every input, including an unpromised input, gives a
nonnegative probability law of total mass one on the address strings. -/
theorem quantumDecode_total (hk : 1 ≤ k) (n : ℕ)
    (x : BitInput (Loc k t C)) (i : Col t) :
    (∀ s, 0 ≤ addrLaw n x i s) ∧ ∑ s, addrLaw n x i s = 1 :=
  ⟨fun s => addrLaw_nonneg hk n x i s, sum_addrLaw hk n x i⟩

/-- Ledger: claim-decode-cost. The physical decoder uses at most twice its
logical read count, on every branch and every input. -/
theorem quantumDecode_runs (hk : 1 ≤ k) (n : ℕ) (i : Col t) :
    Runs (2 * addrCost k t n) fun (x : BitInput (Loc k t C)) s =>
      addrLaw n x i s :=
  (addr_samples hk n i).runs

/-- Ledger: claim-decode-cost. If the instances specify address `s`, the actual
product decoder returns `s` with probability at least `1 - ε`. -/
theorem quantumDecode_correct (hk : 1 ≤ k) (ht : 1 ≤ t)
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : repetitions k (ε / (40 * t : ℕ)) ≤ n)
    {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t}
    (hs : ∀ h, P k t (readA x i h) = some (s h)) :
    1 - ε ≤ addrLaw n x i s :=
  addrLaw_good hk ht hε hε1 hn hs

/-- Ledger: claim-decode-cost. At the least prescribed repetition count the
bit-query budget is at most `80 t k (1 + 16·2^(10k)·ln(40t/ε))`.
This is the numeric statement behind the paper's `O_k(r log(r/ε))`. -/
theorem quantumDecode_query_bound_real (ht : 1 ≤ t) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2 * addrCost k t (repetitions k (ε / (40 * t : ℕ))) : ℕ) : ℝ) ≤
      80 * (t : ℝ) * (k : ℝ) *
        (1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log ((40 * t : ℕ) / ε)) := by
  have hr0 : (0 : ℝ) < (40 * t : ℕ) := by
    have : 0 < 40 * t := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (40 * t : ℕ) := by
    have : 1 ≤ 40 * t := by omega
    exact_mod_cast this
  have hη : 0 < ε / (40 * t : ℕ) := div_pos hε hr0
  have hη1 : ε / (40 * t : ℕ) ≤ 1 :=
    ((div_le_self hε.le hr1).trans hε1)
  have hn := repetitions_le k hη hη1
  have hdiv : 1 / (ε / (40 * t : ℕ)) = (40 * t : ℕ) / ε := by
    field_simp [hε.ne', hr0.ne']
  rw [hdiv] at hn
  calc ((2 * addrCost k t (repetitions k (ε / (40 * t : ℕ))) : ℕ) : ℝ)
      = (80 * (t : ℝ) * (k : ℝ)) *
          (repetitions k (ε / (40 * t : ℕ)) : ℝ) := by
            simp only [addrCost]
            push_cast
            ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

/-- Ledger: claim-decode-cost. At the paper's error parameter the repetition
count is polynomial in `log₂ m = 2t`. This exposes the local estimate used
inside `Upper.budget_le`. -/
theorem quantumDecode_repetitions_polylog (ht : 1 ≤ t) :
    repetitions k (epsval (mValue t) / (40 * t : ℕ)) ≤
      (1 + 1920000 * 2 ^ (10 * k)) * (2 * t) ^ 2 := by
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = 2 * t := ⟨_, rfl⟩
  have hτ2 : 2 ≤ τ := by omega
  have hm : 2 ≤ mValue t := by
    change 2 ≤ 2 ^ (2 * t)
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨T, hTd⟩ : ∃ T, T = Tval (mValue t) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε, ε = epsval (mValue t) := ⟨_, rfl⟩
  have hT : T ≤ 6 * τ := by
    have := Tval_mValue_le t
    omega
  have hTpos : 0 < T := by rw [hTd]; exact Tval_pos hm
  have hTR : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hTle : (T : ℝ) ≤ 6 * τ := by exact_mod_cast hT
  have hτR : (2 : ℝ) ≤ τ := by exact_mod_cast hτ2
  have hε : ε = 1 / (1000 * (T : ℝ)) := by rw [hεd, hTd, epsval]
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
    linarith
  obtain ⟨n, hnd⟩ : ∃ n, n = repetitions k (ε / (40 * t : ℕ)) := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = 1 + 1920000 * 2 ^ (10 * k) := ⟨_, rfl⟩
  have hr : (0 : ℝ) < (40 * t : ℕ) := by
    have : 0 < 40 * t := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (40 * t : ℕ) := by
    have : 1 ≤ 40 * t := by omega
    exact_mod_cast this
  have hη0 : 0 < ε / (40 * t : ℕ) := div_pos hε0 hr
  have hη1 : ε / (40 * t : ℕ) ≤ 1 := (div_le_self hε0.le hr1).trans hε1
  have h := repetitions_le k hη0 hη1
  have hlog : Real.log (1 / (ε / (40 * t : ℕ))) ≤ 1 / (ε / (40 * t : ℕ)) :=
    Real.log_le_self (by positivity)
  have hinv : 1 / (ε / (40 * t : ℕ)) ≤ 120000 * (τ : ℝ) ^ 2 := by
    have e : 1 / (ε / (40 * t : ℕ)) = 20 * (τ : ℝ) * (1000 * T) := by
      rw [hε, hτd]
      push_cast
      field_simp
      ring
    rw [e]
    nlinarith
  have ha : (0 : ℝ) < 2 ^ (10 * k) := by positivity
  have hstep := mul_le_mul_of_nonneg_left (hlog.trans hinv)
    (by positivity : (0 : ℝ) ≤ 16 * 2 ^ (10 * k))
  have hY : (1 : ℝ) ≤ (τ : ℝ) ^ 2 := by nlinarith
  rw [← hnd] at h
  have hgoal : (n : ℝ) ≤ (R : ℝ) * (τ : ℝ) ^ 2 := by
    rw [hRd]
    push_cast
    nlinarith
  have hn : n ≤ R * τ ^ 2 := by exact_mod_cast hgoal
  simpa only [hnd, hRd, hτd, hεd] using hn

/-- Ledger: claim-decode-cost. A finite polynomial decoder cap at the exact
error parameter chosen by the paper. -/
theorem quantumDecode_polylog (ht : 1 ≤ t) :
    2 * addrCost k t (repetitions k (epsval (mValue t) / (40 * t : ℕ))) ≤
      40 * (1 + 1920000 * 2 ^ (10 * k)) * k * (2 * t) ^ 3 := by
  have hn := quantumDecode_repetitions_polylog (k := k) ht
  unfold addrCost
  calc 2 * (40 * t * (repetitions k (epsval (mValue t) / (40 * t : ℕ)) * k))
      ≤ 2 * (40 * t * (((1 + 1920000 * 2 ^ (10 * k)) * (2 * t) ^ 2) * k)) := by
        gcongr
    _ = _ := by ring

/-! ## The sorted-pair comparison -/

/-- Ledger: def-comparison. The first, hence smaller, index wins precisely when
it is the sole disqualifier or the two disqualification bits agree. -/
theorem quantumComparison_rule (d₁ d₂ : Bool) :
    firstWins d₁ d₂ = if d₁ = d₂ then true else d₁ := by
  cases d₁ <;> cases d₂ <;> rfl

/-- Ledger: def-comparison. The disqualification bit is exactly the negation of
the selected bit in the opponent's string. -/
theorem quantumComparison_disqualification (x : BitInput (Loc k t C))
    (i : Col t) (s : Addr t) (j : Col t) (hji : j ≠ i) :
    disq x i s j hji =
      !readX x j (pointerEquiv (2 * t) (readPointerBit x i s ⟨j, hji⟩)) := rfl

/-- Ledger: def-comparison. One pointer test is an adaptive tree of depth
`2t+1`, realized with at most `2(2t+1)` physical bit queries. -/
theorem quantumComparison_pointer_queries (i : Col t) (s : Addr t)
    (j : Col t) (hji : j ≠ i) :
    Runs (2 * (2 * t + 1)) fun (x : BitInput (Loc k t C)) b =>
      pt (disq x i s j hji) b :=
  (Samples.disq i s j hji).runs

/-- Ledger: def-comparison. The exact measurement probability for the smaller
index is the classical mixture over the two retained address registers. -/
theorem quantumComparison_sorted (n : ℕ) (x : BitInput (Loc k t C))
    (i j : Col t) (hij : i < j) :
    cmpProb n x i j =
      ∑ s₁, addrLaw n x i s₁ * ∑ s₂, addrLaw n x j s₂ *
        (if firstWins (disq x i s₁ j hij.ne')
          (disq x j s₂ i hij.ne) then (1 : ℝ) else 0) := by
  simp only [cmpProb, hij.ne, hij, ↓reduceDIte, ↓reduceIte, coreProb]

/-- Ledger: eq-10. Complementarity holds for the implemented comparison on
all inputs. No promise is made about either decoded column. -/
theorem quantumComparison_complementary (n : ℕ)
    (x : BitInput (Loc k t C)) (i j : Col t) (hij : i ≠ j) :
    cmpProb n x i j + cmpProb n x j i = 1 :=
  (cmpProb_isComparison x n).complementary i j hij

/-- Ledger: eq-10. A candidate never defeats itself in the implemented law. -/
theorem quantumComparison_self (n : ℕ)
    (x : BitInput (Loc k t C)) (i : Col t) : cmpProb n x i i = 0 :=
  (cmpProb_isComparison x n).self_zero i

/-- Ledger: def-comparison. The self-comparison law has a zero-read
implementation. The uniform controlled implementation may pad this branch
with identity reads, which do not inspect a pointer. -/
theorem quantumComparison_self_zero_reads (n : ℕ) (i : Col t) :
    Samples 0 fun (x : BitInput (Loc k t C)) b => bern (cmpProb n x i i) b := by
  refine (Samples.pure (ι := Loc k t C) false).congr fun x b => ?_
  cases b <;> simp [cmpProb, bern, pt_self, pt_of_ne]

/-- Ledger: claim-comparison-state. An actual retained-workspace circuit and
its inverse have the same logical read budget and the required output law. -/
theorem quantumComparison_state (hk : 1 ≤ k) (n : ℕ) (i j : Col t) :
    ∃ (Z : Type) (_ : Fintype Z) (o : Z) (out : Z → Bool)
      (F : BitInput (Loc k t C) → Reg Z ≃ₗᵢ[ℂ] Reg Z),
      IsCirc (cmpCost k t n) F ∧
      IsCirc (cmpCost k t n) (fun x => (F x).symm) ∧
      ∀ x b, lawOf (F x (rket o)) out b = bern (cmpProb n x i j) b := by
  obtain ⟨Z, instZ, o, out, F, hF, hL⟩ := cmp_samples (C := C) hk n i j
  exact ⟨Z, instZ, o, out, F, hF, hF.symm, fun x b => (hL x b).symm⟩

/-- Ledger: def-aij. One retained-workspace preparation for an unordered
pair supplies both ordered comparison laws by complementing only the output
label. This is a common-circuit witness, not just an algebraic table identity. -/
theorem quantumComparison_unordered_state (hk : 1 ≤ k) (n : ℕ)
    (i j : Col t) (hij : i ≠ j) :
    ∃ (Z : Type) (_ : Fintype Z) (o : Z) (out : Z → Bool)
      (F : BitInput (Loc k t C) → Reg Z ≃ₗᵢ[ℂ] Reg Z),
      IsCirc (cmpCost k t n) F ∧
      ∀ x b,
        lawOf (F x (rket o)) out b = bern (cmpProb n x i j) b ∧
        lawOf (F x (rket o)) (fun z => !(out z)) b = bern (cmpProb n x j i) b := by
  classical
  obtain ⟨Z, instZ, o, out, F, hF, _, hL⟩ := quantumComparison_state (C := C) hk n i j
  refine ⟨Z, instZ, o, out, F, hF, ?_⟩
  intro x b
  refine ⟨hL x b, ?_⟩
  have hflip : lawOf (F x (rket o)) (fun z => !(out z)) b =
      lawOf (F x (rket o)) out (!b) := by
    unfold lawOf
    refine Finset.sum_congr rfl fun z _ => ?_
    cases h : out z <;> cases b <;> simp [h]
  rw [hflip, hL x (!b)]
  have hc := quantumComparison_complementary n x i j hij
  cases b <;> simp [bern] <;> linarith

/-- Ledger: claim-comparison-state. The physical comparison has a worst-case
budget of twice the logical read count. -/
theorem quantumComparison_runs (hk : 1 ≤ k) (n : ℕ) (i j : Col t) :
    Runs (2 * cmpCost k t n) fun (x : BitInput (Loc k t C)) b =>
      bern (cmpProb n x i j) b :=
  (cmp_samples hk n i j).runs

/-- Ledger: claim-comparison-state. Expanded physical-query budget. -/
theorem quantumComparison_cost_exact (k t n : ℕ) :
    2 * cmpCost k t n = 4 * addrCost k t n + 8 * t + 4 := by
  unfold cmpCost
  ring

/-- Ledger: claim-comparison-state. Explicit logarithmic decoding cost for
both columns plus the two adaptive pointer tests. -/
theorem quantumComparison_query_bound (ht : 1 ≤ t) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2 * cmpCost k t (repetitions k (ε / (40 * t : ℕ))) : ℕ) : ℝ) ≤
      160 * (t : ℝ) * (k : ℝ) *
        (1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log ((40 * t : ℕ) / ε)) +
      8 * (t : ℝ) + 4 := by
  have h := quantumDecode_query_bound_real (k := k) ht hε hε1
  rw [quantumComparison_cost_exact]
  push_cast at h ⊢
  nlinarith

/-- Ledger: claim-comparison-state. A finite polynomial bound for the actual
comparison at the paper's parameters. -/
theorem quantumComparison_polylog (ht : 1 ≤ t) :
    2 * cmpCost k t (repetitions k (epsval (mValue t) / (40 * t : ℕ))) ≤
      2 * (40 * (1 + 1920000 * 2 ^ (10 * k)) * k + 4) * (2 * t) ^ 3 := by
  have hA := quantumDecode_polylog (k := k) ht
  have hτ : 1 ≤ 2 * t := by omega
  have hP : 2 * t ≤ (2 * t) ^ 3 := Nat.le_self_pow (by norm_num) (2 * t)
  have hP1 : 1 ≤ (2 * t) ^ 3 := Nat.one_le_pow _ _ hτ
  rw [quantumComparison_cost_exact]
  have hE : 2 * (40 * (1 + 1920000 * 2 ^ (10 * k)) * k + 4) * (2 * t) ^ 3 =
      2 * (40 * (1 + 1920000 * 2 ^ (10 * k)) * k * (2 * t) ^ 3) +
        8 * (2 * t) ^ 3 := by ring
  rw [hE]
  omega

/-- Ledger: claim-winner-dominates. The actual comparison favors a winner
with probability at least `1-ε`, regardless of the opponent's promises. -/
theorem quantumWinner_dominates (hk : 1 ≤ k) (ht : 1 ≤ t)
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : repetitions k (ε / (40 * t : ℕ)) ≤ n)
    {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t}
    (hw : WinsAt (P k t) C (2 * t) (40 * t) x i s)
    (j : Col t) (hji : j ≠ i) :
    1 - ε ≤ cmpProb n x i j := by
  have hd : 1 - ε ≤ addrLaw n x i s :=
    addrLaw_good hk ht hε hε1 hn hw.2.1
  exact hd.trans (cmpProb_winner hk hw hji)

/-- Ledger: claim-winner-dominates. The same guarantee in the tournament's
`Dominant` predicate. -/
theorem quantumWinner_isDominant (hk : 1 ≤ k) (ht : 1 ≤ t)
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : repetitions k (ε / (40 * t : ℕ)) ≤ n)
    {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t}
    (hw : WinsAt (P k t) C (2 * t) (40 * t) x i s) :
    Dominant (cmpProb n x) ε i :=
  fun j hji => quantumWinner_dominates hk ht hε hε1 hn hw j hji

/-! ## Fixed-address search and fresh-address verification -/

/-- Ledger: def-verify. Exact cardinality of the local-test family. -/
theorem quantumTests_card (t : ℕ) (C : Circuit (ForrelationCoord k t)) :
    Fintype.card (Tests t C) =
      mValue t + (mValue t - 1) + 40 * t * (C.size + 2) := by
  simpa only [Tests, mValue] using card_testIndex (2 * t) (40 * t) C.size

/-- Ledger: def-verify. The local-test family contains all `m` bit tests. -/
theorem quantumTests_card_ge_m (t : ℕ) (C : Circuit (ForrelationCoord k t)) :
    mValue t ≤ Fintype.card (Tests t C) := by
  rw [quantumTests_card]
  omega

/-- Ledger: def-verify. The search parameter is in the range of Lemma 3.1
when the paper's `m=4^t`, `t≥1`, is used. -/
theorem quantumTests_card_ge_four (ht : 1 ≤ t) :
    4 ≤ Fintype.card (Tests t C) := by
  have hm : 4 ≤ mValue t := by
    change 4 ≤ 2 ^ (2 * t)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hm.trans (quantumTests_card_ge_m t C)

/-- Ledger: def-verify. At a fixed address the actual amplified search
accepts surely when every exact test passes, and with probability at most
`ε` if any test fails. Its branch cap is independent of the input. -/
theorem quantumVerify_fixedAddress (i : Col t) (s : Addr t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : BitInput (Loc k t C) → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x e, localTest C (2 * t) (40 * t) x i s e = false → f x ≤ ε) ∧
      (∀ x, (∀ e, localTest C (2 * t) (40 * t) x i s e = true) → f x = 1) ∧
      Runs (searchCost t (Fintype.card (Tests t C)) ε) fun x b => bern (f x) b :=
  search_runs i s hε

/-- Ledger: def-verify. Freshly decoding the address, measuring it, and
running the appropriate fixed-address search realizes `verifyProb`. -/
theorem quantumVerify_runs (hk : 1 ≤ k) (n cS : ℕ)
    (f : Col t → Addr t → BitInput (Loc k t C) → ℝ)
    (hRun : ∀ c s, Runs cS fun x b => bern (f c s x) b) (c : Col t) :
    Runs (2 * addrCost k t n + cS) fun x b => bern (verifyProb n f x c) b := by
  have hb := (addr_samples (C := C) hk n c).runs.bind
    (K := fun s x b => bern (f c s x) b) (fun s => hRun c s)
  refine hb.congr fun x b => ?_
  cases b with
  | true => simp [bern, verifyProb]
  | false =>
    simp only [bern, Bool.false_eq_true, ite_false, verifyProb, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, sum_addrLaw hk]

/-- Ledger: def-verify. The acceptance probability is the mixture over the
fresh address measurement. -/
theorem quantumVerify_probability (n : ℕ)
    (f : Col t → Addr t → BitInput (Loc k t C) → ℝ)
    (x : BitInput (Loc k t C)) (c : Col t) :
    verifyProb n f x c = ∑ s, addrLaw n x c s * f c s x := rfl

/-- Ledger: claim-verify. Verification defines a probability in `[0,1]`
on every input, without a promise on any Forrelation instance. -/
theorem quantumVerify_unit (hk : 1 ≤ k) (n : ℕ)
    (f : Col t → Addr t → BitInput (Loc k t C) → ℝ)
    (hf : ∀ c s x, 0 ≤ f c s x ∧ f c s x ≤ 1)
    (x : BitInput (Loc k t C)) (c : Col t) :
    0 ≤ verifyProb n f x c ∧ verifyProb n f x c ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (addrLaw_nonneg hk n x c s) (hf c s x).1
  · calc verifyProb n f x c ≤ ∑ s, addrLaw n x c s :=
          Finset.sum_le_sum fun s _ =>
            mul_le_of_le_one_right (addrLaw_nonneg hk n x c s) (hf c s x).2
      _ = 1 := sum_addrLaw hk n x c

/-- Ledger: claim-verify. Every address of a nonwinner has a failed test,
so averaging over any decoded address still gives acceptance at most `ε`. -/
theorem quantumVerify_nonwinner (hk : 1 ≤ k)
    (hC : CircuitRealises C (P k t)) (n : ℕ) {ε : ℝ}
    (f : Col t → Addr t → BitInput (Loc k t C) → ℝ)
    (hf : ∀ c s x e, localTest C (2 * t) (40 * t) x c s e = false → f c s x ≤ ε)
    {x : BitInput (Loc k t C)} {c : Col t}
    (hno : ¬ ∃ s, WinsAt (P k t) C (2 * t) (40 * t) x c s) :
    verifyProb n f x c ≤ ε := by
  calc verifyProb n f x c ≤ ∑ s, addrLaw n x c s * ε := by
        refine Finset.sum_le_sum fun s _ => ?_
        obtain ⟨e, he⟩ := exists_failing_localTest hC hno s
        exact mul_le_mul_of_nonneg_left (hf c s x e he) (addrLaw_nonneg hk n x c s)
    _ = ε := by rw [← Finset.sum_mul, sum_addrLaw hk, one_mul]

/-- Ledger: claim-verify. A winner is accepted whenever its own address is
correct. Exact testing adds no loss on that event. -/
theorem quantumVerify_winner (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hC : CircuitRealises C (P k t)) {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : repetitions k (ε / (40 * t : ℕ)) ≤ n)
    (f : Col t → Addr t → BitInput (Loc k t C) → ℝ)
    (hf0 : ∀ c s x, 0 ≤ f c s x)
    (hf1 : ∀ c s x, (∀ e, localTest C (2 * t) (40 * t) x c s e = true) → f c s x = 1)
    {x : BitInput (Loc k t C)} {c : Col t} {s : Addr t}
    (hw : WinsAt (P k t) C (2 * t) (40 * t) x c s) :
    1 - ε ≤ verifyProb n f x c := by
  have h1 : f c s x = 1 := hf1 c s x fun e => (winsAt_iff_localTests hC).1 hw e
  calc 1 - ε ≤ addrLaw n x c s := addrLaw_good hk ht hε hε1 hn hw.2.1
    _ = addrLaw n x c s * f c s x := by rw [h1, mul_one]
    _ ≤ verifyProb n f x c :=
      Finset.single_le_sum (f := fun a => addrLaw n x c a * f c a x)
        (fun a _ => mul_nonneg (addrLaw_nonneg hk n x c a) (hf0 c a x))
        (Finset.mem_univ s)

/-- Ledger: claim-verify. For `t≥1` the exact local-test read cap is
`2t+1`, so the final factor in the search cost is `O(log m)`. -/
theorem quantumVerify_testCost (ht : 1 ≤ t) : testCost t = 2 * t + 1 := by
  unfold testCost
  omega

/-- Ledger: claim-verify. The search-only physical query budget has the
paper's square-root and logarithmic dependence, with constant `276`. -/
theorem quantumVerify_search_query_bound (t K : ℕ) (hK : 2 ≤ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    (searchCost t K ε : ℝ) ≤
      276 * Real.sqrt (K : ℝ) * Real.log (1 / ε) * (testCost t : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hγ : (0 : ℝ) < (K : ℝ)⁻¹ := inv_pos.mpr hKpos
  have hγ1 : (K : ℝ)⁻¹ ≤ 1 / 2 := by
    have h : 1 / (K : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hKpos]
      linarith
    simpa only [one_div] using h
  have hB := amplification_budget_le hγ hγ1 hε hε1
  rw [Real.sqrt_inv, inv_inv] at hB
  calc (searchCost t K ε : ℝ) =
      (2 * (testCost t : ℝ)) *
        ((trialCount ε : ℝ) * (2 * (iterationBound ((K : ℝ)⁻¹) : ℝ) + 1)) := by
          simp only [searchCost]
          push_cast
          ring
    _ ≤ (2 * (testCost t : ℝ)) *
        (138 * Real.sqrt (K : ℝ) * Real.log (1 / ε)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by ring

/-- Ledger: claim-verify. Under the explicit circuit-size bound, the complete
single-candidate physical cap, including fresh decoding, is at most
`budgetConst k * 2^t * (2t)^6`. Here `2^t = sqrt(m)` and `2t = log₂(m)`.
This deliberately loose bound follows by including one verification in the
already bounded complete-algorithm budget. -/
theorem quantumVerify_polylog (ht : 1 ≤ t)
    (hSz : C.size ≤ forrConstant k * mValue t * (2 * t) ^ 2) :
    2 * addrCost k t (repetitions k (epsval (mValue t) / (40 * t : ℕ))) +
      searchCost t (Fintype.card (Tests t C)) (epsval (mValue t)) ≤
        budgetConst k * 2 ^ t * (2 * t) ^ 6 := by
  let n := repetitions k (epsval (mValue t) / (40 * t : ℕ))
  let cV := 2 * addrCost k t n +
    searchCost t (Fintype.card (Tests t C)) (epsval (mValue t))
  have hm : 2 ≤ mValue t := by
    change 2 ≤ 2 ^ (2 * t)
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT : 1 ≤ Tval (mValue t) := Nat.succ_le_of_lt (Tval_pos hm)
  change cV ≤ budgetConst k * 2 ^ t * (2 * t) ^ 6
  calc cV ≤ Tval (mValue t) * cV := by
        simpa only [one_mul] using Nat.mul_le_mul_right cV hT
    _ ≤ budget k t n (Fintype.card (Tests t C)) := by
        change Tval (mValue t) * cV ≤
          Tval (mValue t) * stageCost (mValue t) (Tval (mValue t))
            (cmpCost k t n) (epsval (mValue t)) + Tval (mValue t) * cV
        omega
    _ ≤ budgetConst k * 2 ^ t * (2 * t) ^ 6 := budget_le ht hSz

/-- Ledger: claim-verify. The selected `forrCircuit` satisfies the size premise
of `quantumVerify_polylog`, yielding the paper's finite square-root-times-polylog
verification bound for every `k = l+1`. -/
theorem quantumVerify_forrCircuit_polylog (l : ℕ) (ht : 1 ≤ t) :
    2 * addrCost (l + 1) t
      (repetitions (l + 1) (epsval (mValue t) / (40 * t : ℕ))) +
      searchCost t (Fintype.card (Tests t (forrCircuit l t))) (epsval (mValue t)) ≤
        budgetConst (l + 1) * 2 ^ t * (2 * t) ^ 6 :=
  quantumVerify_polylog ht (forrCircuit_size_le l t ht)

/-- Ledger: claim-verify. One verifier is fixed before the input and has the
stated branch cap and both correctness guarantees on every input. -/
theorem quantumVerify (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hC : CircuitRealises C (P k t)) {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : repetitions k (ε / (40 * t : ℕ)) ≤ n) :
    ∃ v : BitInput (Loc k t C) → Col t → ℝ,
      (∀ c, Runs (2 * addrCost k t n + searchCost t (Fintype.card (Tests t C)) ε)
        fun x b => bern (v x c) b) ∧
      (∀ x c, 0 ≤ v x c ∧ v x c ≤ 1) ∧
      (∀ x c, (¬ ∃ s, WinsAt (P k t) C (2 * t) (40 * t) x c s) → v x c ≤ ε) ∧
      (∀ x c s, WinsAt (P k t) C (2 * t) (40 * t) x c s → 1 - ε ≤ v x c) := by
  classical
  choose f hf01 hfε hf1 hrun using fun p : Col t × Addr t =>
    search_runs (C := C) p.1 p.2 hε
  let g : Col t → Addr t → BitInput (Loc k t C) → ℝ := fun c s => f (c, s)
  have hg01 : ∀ c s x, 0 ≤ g c s x ∧ g c s x ≤ 1 := fun c s x => hf01 (c, s) x
  have hgε : ∀ c s x e, localTest C (2 * t) (40 * t) x c s e = false → g c s x ≤ ε :=
    fun c s x e he => hfε (c, s) x e he
  have hg1 : ∀ c s x, (∀ e, localTest C (2 * t) (40 * t) x c s e = true) → g c s x = 1 :=
    fun c s x he => hf1 (c, s) x he
  refine ⟨fun x c => verifyProb n g x c, ?_, ?_, ?_, ?_⟩
  · exact quantumVerify_runs hk n _ g (fun c s => hrun (c, s))
  · exact quantumVerify_unit hk n g hg01
  · intro x c hno
    exact quantumVerify_nonwinner hk hC n g hgε hno
  · intro x c s hw
    exact quantumVerify_winner hk ht hC hε hε1 hn g
      (fun c s x => (hg01 c s x).1) hg1 hw

/-- Ledger: def-verify. A list is consumed by testing its candidates until
one accepts. The physical branch cap is its length times the single budget. -/
theorem quantumVerify_list {cV : ℕ}
    {v : BitInput (Loc k t C) → Col t → ℝ}
    (hv : ∀ c, Runs cV fun x b => bern (v x c) b) (L : List (Col t)) :
    Runs (L.length * cV) fun x b => bern (vall (v x) L) b :=
  vall_runs hv L

/-! ## The paper's separate zero-input and one-input error bounds -/

/-- Ledger: claim-error. The complete implemented algorithm has zero-input
error at most `T ε` and one-input error at most `2m/2^T + Tε + ε`.
The existential program is chosen before the universal input quantifiers. -/
theorem quantumError_bound (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hC : CircuitRealises C (P k t)) {n : ℕ}
    (hn : repetitions k (epsval (mValue t) / (40 * t : ℕ)) ≤ n) :
    ∃ val : BitInput (Loc k t C) → ℝ,
      Runs (budget k t n (Fintype.card (Tests t C)))
        (fun x b => bern (val x) b) ∧
      (∀ x, Fkm k t C x = false →
        val x ≤ (Tval (mValue t) : ℝ) * epsval (mValue t)) ∧
      (∀ x, Fkm k t C x = true →
        1 - val x ≤ 2 * (mValue t : ℝ) / 2 ^ Tval (mValue t) +
          (Tval (mValue t) : ℝ) * epsval (mValue t) + epsval (mValue t)) := by
  classical
  have hm : 2 ≤ Fintype.card (Col t) := by
    rw [card_col]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm' : 2 ≤ mValue t := card_col t ▸ hm
  have hε : 0 < epsval (mValue t) := by
    have hT : 0 < Tval (mValue t) := Tval_pos hm'
    have hTr : (0 : ℝ) < Tval (mValue t) := by exact_mod_cast hT
    unfold epsval
    positivity
  have hε1 : epsval (mValue t) ≤ 1 := (epsval_le hm').trans (by norm_num)
  obtain ⟨v, hvrun, hv01, hvno, hvwin⟩ := quantumVerify hk ht hC hε hε1 hn
  have htour := tournament_runs (ι := Loc k t C) (Col := Col t)
    (a := fun x => cmpProb (C := C) n x) (v := v) hm
    (fun x => cmpProb_isComparison x n) (fun x => cmpProb_unit hk x n)
    (fun i j => cmp_samples hk n i j) hvrun hv01
  dsimp only at htour
  rw [card_col] at htour
  obtain ⟨val, hrun, hzero, hone⟩ := htour
  refine ⟨val, ?_, ?_, ?_⟩
  · simpa only [budget] using hrun
  · intro x hF
    have hno : ∀ c, ¬ ∃ s, WinsAt (P k t) C (2 * t) (40 * t) x c s := by
      intro c hs
      obtain ⟨s, hw⟩ := hs
      have htrue : Fkm k t C x = true := addressedF_eq_true_iff.2 ⟨c, s, hw⟩
      rw [hF] at htrue
      exact Bool.noConfusion htrue
    exact hzero x (fun c => hvno x c (hno c))
  · intro x hF
    obtain ⟨i, s, hw⟩ := addressedF_eq_true_iff.1 hF
    have hd : Dominant (cmpProb n x) (epsval (mValue t)) i :=
      quantumWinner_isDominant hk ht hε hε1 hn hw
    have h := hone x i hd (hvwin x i s hw)
    linarith

/-- Ledger: claim-error. Exact arithmetic at the paper's base-two parameters. -/
theorem quantumError_numeric {m : ℕ} (hm : 2 ≤ m) :
    (Tval m : ℝ) * epsval m = 1 / 1000 ∧
    2 * (m : ℝ) / 2 ^ Tval m + (Tval m : ℝ) * epsval m + epsval m < 1 / 3 :=
  ⟨Tval_mul_epsval hm, total_error_lt hm⟩

end QuarticQuery.Paper

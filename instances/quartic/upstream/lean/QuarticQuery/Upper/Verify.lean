module

public import QuarticQuery.Upper.Columns
public import QuarticQuery.Results.Exponent
public import QuarticQuery.Forrelation.Circuit

/-!
# Verification and Proposition 3.3

Each listed column decodes an address afresh and searches for a failing local test at
it, by bounded amplification with `γ = 1/K`. Exact tests mean a true winner at its true
address has no failing test, so it can only be lost by decoding. Assembling with the
tournament gives `Fkm_QLe`, and `budget_le` is the explicit count.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Forrelation QuarticQuery.Tournament QuarticQuery.Amplification

variable {k t : ℕ} {C : Circuit (ForrelationCoord k t)}

/-- The local tests of `F_{k,m}`. -/
abbrev Tests (t : ℕ) (C : Circuit (ForrelationCoord k t)) :=
  TestIndex (2 * t) (40 * t) C.size

/-- The label of test `e`: `none` if it passes, and its own index if it fails. -/
noncomputable def testRes (x : BitInput (Loc k t C)) (i : Col t) (s : Addr t) (e : Tests t C) :
    Option (Tests t C) :=
  if localTest C (2 * t) (40 * t) x i s e then none else some e

/-- A uniform test and its exact result. -/
noncomputable def testLaw (x : BitInput (Loc k t C)) (i : Col t) (s : Addr t)
    (o : Option (Tests t C)) : ℝ :=
  ∑ e, (Fintype.card (Tests t C) : ℝ)⁻¹ * pt (testRes x i s e) o

/-- The reads of one exact test. -/
def testCost (t : ℕ) : ℕ := max 3 (2 * t + 1)

/-- Ledger: lem-2.2.ii. A uniform test index and an exact failing-test flag, coherently. -/
theorem test_samples (i : Col t) (s : Addr t) :
    Samples (testCost t) fun (x : BitInput (Loc k t C)) o => testLaw x i s o := by
  have hne : Nonempty (Tests t C) := ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩
  have hcard : (Fintype.card (Tests t C) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hg : Samples (ι := Loc k t C) 0
      fun _ (_ : Tests t C) => (Fintype.card (Tests t C) : ℝ)⁻¹ :=
    Samples.gate (fun _ => by positivity) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ hcard)
  have hK : ∀ e : Tests t C, Samples (testCost t + 0)
      fun (x : BitInput (Loc k t C)) o => pt (testRes x i s e) o := fun e => by
    have h := ((Samples.tree (localTestTree C (2 * t) (40 * t) i s e)).mono
      (localTestTree_depth_le C (2 * t) (40 * t) i s e)).congr
      (L' := fun x b => pt (localTest C (2 * t) (40 * t) x i s e) b) fun x b => by
        rw [localTestTree_eval]
    exact (h.pt_bind (K := fun b _ o => pt (if b then none else some e) o) (m := 0)
      fun b => Samples.pure _)
  exact (hg.bind hK).cast (by omega)

theorem testLaw_pass {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t}
    (h : ∀ e, localTest C (2 * t) (40 * t) x i s e = true) :
    ∑ b, testLaw x i s (some b) = 0 := by
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_
  simp [testRes, h, pt_of_ne]

theorem testLaw_fail {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t} {e₀ : Tests t C}
    (h : localTest C (2 * t) (40 * t) x i s e₀ = false) :
    (Fintype.card (Tests t C) : ℝ)⁻¹ ≤ ∑ b, testLaw x i s (some b) := by
  have hnn : ∀ o : Option (Tests t C), ∀ e,
      0 ≤ (Fintype.card (Tests t C) : ℝ)⁻¹ * pt (testRes x i s e) o :=
    fun o e => mul_nonneg (by positivity) (pt_nonneg _ _)
  have h1 : (Fintype.card (Tests t C) : ℝ)⁻¹ ≤ testLaw x i s (some e₀) := by
    have : (Fintype.card (Tests t C) : ℝ)⁻¹ * pt (testRes x i s e₀) (some e₀) ≤
        testLaw x i s (some e₀) :=
      Finset.single_le_sum (f := fun e => (Fintype.card (Tests t C) : ℝ)⁻¹ *
        pt (testRes x i s e) (some e₀)) (fun e _ => hnn _ e) (Finset.mem_univ e₀)
    simpa [testRes, h, pt_self] using this
  exact h1.trans (Finset.single_le_sum (f := fun b => testLaw x i s (some b))
    (fun b _ => Finset.sum_nonneg fun e _ => hnn _ e) (Finset.mem_univ e₀))

/-- An amplified search read as accept (`none`) or reject. -/
theorem Runs.ofAmp {ι β : Type} [Fintype ι] [Inhabited ι] [Fintype β] {c : ℕ}
    {f : BitInput ι → ℝ} {q : BitInput ι → β → ℝ}
    (h : Runs c fun x => ampLaw (f x) (q x))
    (hsum : ∀ x, f x + (1 - f x) * ∑ p, q x p / ∑ b, q x b = 1) :
    Runs c fun x b => bern (f x) b := by
  let K : Option β → BitInput ι → Bool → ℝ := fun o _ b =>
    match o with
    | none => bern 1 b
    | some _ => bern 0 b
  have hK : ∀ o, Runs 0 (K o) := fun o => by
    cases o with
    | none => exact (Runs.pure (ι := ι) true).congr fun _ b => by cases b <;> simp [K, bern, pt_self, pt_of_ne]
    | some _ => exact (Runs.pure (ι := ι) false).congr fun _ b => by cases b <;> simp [K, bern, pt_self, pt_of_ne]
  refine (h.bind hK).congr fun x b => ?_
  have := ampLaw_step (f x) 1 (q x) (fun _ => 0) (hsum x) b
  simp only [mul_zero, Finset.sum_const_zero, add_zero, mul_one] at this
  exact this.symm

/-- The queries of one search at a fixed address. -/
noncomputable def searchCost (t K : ℕ) (ε : ℝ) : ℕ :=
  trialCount ε * (2 * ((2 * iterationBound ((K : ℝ)⁻¹) + 1) * testCost t))

/-- Ledger: lem-2.2.ii. The search for a failing test at a fixed address: accept
probability `f`, one if no test fails, at most `ε` otherwise. -/
theorem search_runs (i : Col t) (s : Addr t) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : BitInput (Loc k t C) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x e, localTest C (2 * t) (40 * t) x i s e = false → f x ≤ ε) ∧
      (∀ x, (∀ e, localTest C (2 * t) (40 * t) x i s e = true) → f x = 1) ∧
      Runs (searchCost t (Fintype.card (Tests t C)) ε) fun x b => bern (f x) b := by
  have hne : Nonempty (Tests t C) := ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩
  have hK : (0 : ℝ) < (Fintype.card (Tests t C) : ℝ)⁻¹ := by
    have : 0 < Fintype.card (Tests t C) := Fintype.card_pos
    positivity
  obtain ⟨f, h01, hfγ, hfz, hrun⟩ :=
    (test_samples (C := C) i s).amplify hK hε
  refine ⟨f, h01, fun x e he => hfγ x (testLaw_fail he), fun x h => hfz x (testLaw_pass h),
    hrun.ofAmp fun x => ?_⟩
  by_cases h0 : ∑ b, testLaw x i s (some b) = 0
  · rw [hfz x h0]; ring
  · rw [← Finset.sum_div, div_self h0]; ring

/-- Ledger: lem-2.2.ii. The acceptance probability of verifying column `c`, given the
search outcomes. -/
noncomputable def verifyProb (n : ℕ) (f : Col t → Addr t → BitInput (Loc k t C) → ℝ)
    (x : BitInput (Loc k t C)) (c : Col t) : ℝ :=
  ∑ s, addrLaw n x c s * f c s x

/-- The total query budget. -/
noncomputable def budget (k t n K : ℕ) : ℕ :=
  Tval (mValue t) * stageCost (mValue t) (Tval (mValue t)) (cmpCost k t n) (epsval (mValue t)) +
    Tval (mValue t) * (2 * addrCost k t n + searchCost t K (epsval (mValue t)))

/-- Ledger: prop-3.3. Proposition 3.3 at one `t`, for any circuit realising `P`, with `n`
repetitions per instance. -/
theorem Fkm_QLe (hk : 1 ≤ k) (ht : 1 ≤ t) (hC : CircuitRealises C (P k t)) {n : ℕ}
    (hn : repetitions k (epsval (mValue t) / (40 * t : ℕ)) ≤ n) :
    QLe (totalise (Fkm k t C)) (budget k t n (Fintype.card (Tests t C))) := by
  classical
  have hm : 2 ≤ Fintype.card (Col t) := by
    rw [card_col]
    calc 2 ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm' : 2 ≤ mValue t := card_col t ▸ hm
  obtain ⟨ε, hεd⟩ : ∃ ε, ε = epsval (mValue t) := ⟨_, rfl⟩
  have hTε : (Tval (mValue t) : ℝ) * ε = 1 / 1000 := by rw [hεd]; exact Tval_mul_epsval hm'
  have hε0 : 0 ≤ ε := by rw [hεd]; exact epsval_nonneg _
  have hε1 : ε ≤ 1 / 1000 := by rw [hεd]; exact epsval_le hm'
  have hε : 0 < ε := by
    rcases hε0.eq_or_lt with h | h
    · rw [← h] at hTε; norm_num at hTε
    · exact h
  choose f hf01 hfε hf1 hrun using fun p : Col t × Addr t =>
    search_runs (C := C) p.1 p.2 hε
  let g : Col t → Addr t → BitInput (Loc k t C) → ℝ := fun c s => f (c, s)
  have hA0 := fun x c s => addrLaw_nonneg (C := C) hk n x c s
  have hA1 := fun x c => sum_addrLaw (C := C) hk n x c
  have hv : ∀ c, Runs (2 * addrCost k t n + searchCost t (Fintype.card (Tests t C)) ε)
      fun x b => bern (verifyProb n g x c) b := fun c => by
    have hb := (addr_samples (C := C) hk n c).runs.bind (K := fun s x b => bern (g c s x) b)
      fun s => hrun (c, s)
    refine hb.congr fun x b => ?_
    cases b with
    | true => simp [bern, verifyProb]
    | false =>
      simp only [bern, Bool.false_eq_true, ite_false, verifyProb, mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hA1]
  have hv01 : ∀ x c, 0 ≤ verifyProb n g x c ∧ verifyProb n g x c ≤ 1 := fun x c => by
    constructor
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (hA0 x c s) (hf01 _ x).1
    · calc verifyProb n g x c ≤ ∑ s, addrLaw n x c s :=
            Finset.sum_le_sum fun s _ =>
              mul_le_of_le_one_right (hA0 x c s) (hf01 _ x).2
        _ = 1 := hA1 x c
  have htour := tournament_runs (ι := Loc k t C) (Col := Col t)
    (a := fun x => cmpProb (C := C) n x) (v := fun x c => verifyProb n g x c)
    hm (fun x => cmpProb_isComparison x n) (fun x => cmpProb_unit hk x n)
    (fun i p => cmp_samples hk n i p) hv hv01
  dsimp only at htour
  rw [card_col, ← hεd] at htour
  obtain ⟨val, hrunT, hlow, hhigh⟩ := htour
  have hgood : ∀ {x : BitInput (Loc k t C)} {i : Col t} {s : Addr t},
      WinsAt (P k t) C (2 * t) (40 * t) x i s → 1 - ε ≤ addrLaw n x i s := fun {x i s} hw =>
    addrLaw_good hk ht hε (by linarith) (by rw [hεd]; exact hn) hw.2.1
  refine (hrunT.toQLe (Fkm k t C) fun x => ?_).mono (by rw [budget, ← hεd])
  cases hF : Fkm k t C x with
  | true =>
    obtain ⟨i, s, hw⟩ := addressedF_eq_true_iff.1 hF
    have hd : Dominant (cmpProb n x) ε i := fun j hj =>
      (hgood hw).trans (cmpProb_winner hk hw hj)
    have hvi : 1 - ε ≤ verifyProb n g x i := by
      have h1 : g i s x = 1 := hf1 (i, s) x fun e => (winsAt_iff_localTests hC).1 hw e
      calc 1 - ε ≤ addrLaw n x i s := hgood hw
        _ = addrLaw n x i s * g i s x := by rw [h1, mul_one]
        _ ≤ verifyProb n g x i :=
          Finset.single_le_sum (f := fun s => addrLaw n x i s * g i s x)
            (fun s _ => mul_nonneg (hA0 x i s) (hf01 _ x).1) (Finset.mem_univ s)
    have h := hhigh x i hd hvi
    have herr := total_error_lt hm'
    rw [← hεd] at herr
    simp only [bern, ite_true]
    linarith
  | false =>
    have hno : ∀ c, ¬ ∃ s, WinsAt (P k t) C (2 * t) (40 * t) x c s := fun c ⟨s, hw⟩ => by
      have := addressedF_eq_true_iff.2 ⟨c, s, hw⟩
      rw [show addressedF (P k t) C (2 * t) (40 * t) x = Fkm k t C x from rfl, hF] at this
      exact Bool.noConfusion this
    have hle : ∀ c, verifyProb n g x c ≤ ε := fun c => by
      calc verifyProb n g x c ≤ ∑ s, addrLaw n x c s * ε :=
            Finset.sum_le_sum fun s _ => by
              obtain ⟨e, he⟩ := exists_failing_localTest hC (hno c) s
              exact mul_le_mul_of_nonneg_left (hfε (c, s) x e he) (hA0 x c s)
        _ = ε := by rw [← Finset.sum_mul, hA1, one_mul]
    have h := hlow x hle
    simp only [bern, Bool.false_eq_true, ite_false]
    linarith

end QuarticQuery.Upper

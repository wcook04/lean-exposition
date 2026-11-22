module

public import QuarticQuery.Results.Exponent
public import QuarticQuery.Construction.LocalTests
public import QuarticQuery.Upper.Verify
public import QuarticQuery.Upper.Decode
public import QuarticQuery.Forrelation.Circuit
public import QuarticQuery.ForrelationLower.Main
public import QuarticQuery.Paper.ConstructionModels
public import QuarticQuery.Paper.ConstructionFamily
public import QuarticQuery.Paper.ConstructionForrelationComparison
public import QuarticQuery.Paper.ConstructionForrelationComplete
public import QuarticQuery.Paper.ConstructionComplete
public import QuarticQuery.Paper.ConstructionPointerSupport
public import QuarticQuery.Paper.ConstructionPhase
public import QuarticQuery.Paper.ConstructionArithmetic

/-!
# Section 2 of the preprint, statement by statement

Each declaration here states one named result of Section 2 as the preprint writes it,
or in a documented corrected form, and derives it from the existing development.
`F_{k,m}` is `Fkm k t C` with `m = 4 ^ t`, `ℓ = 2 t`, `r = 40 t`, for a circuit `C`
realising `P k t`.

The `Construction*` modules expose the retained-state physical witnesses, arbitrary
test-index superpositions, exact definitions and explicit finite bounds supplied by
the round-two integration. The declarations below retain the earlier public names.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper

/-! ## The comparison closing the proof of Lemma 2.1(i) -/

/-- The arithmetic behind `claim-bs-to-L`: once `1 ≤ Λ ≤ A + B t`, the quantity
`c' (m / Λ)^(1 - 1/k)` eventually exceeds `L`. -/
theorem Lvalue_lt_of_le_affine {k : ℕ} (hk : 2 ≤ k) {c' A B : ℝ} (hc : 0 < c')
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t → ∀ Λ : ℝ, 1 ≤ Λ → Λ ≤ A + B * t →
      (Lvalue k t : ℝ) < c' * ((mValue t : ℝ) / Λ) ^ (1 - 1 / (k : ℝ)) := by
  refine ⟨⌈(A + B) / (4 * c')⌉₊ + 1, by omega, fun t ht Λ hΛ1 hΛ => ?_⟩
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have ha1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ) < t := by linarith
  have hm : (0 : ℝ) < (mValue t : ℝ) := by
    have : 0 < mValue t := by simp [mValue]
    exact_mod_cast this
  have hMpos : 0 < (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) := Real.rpow_pos_of_pos hm _
  have hL : (Lvalue k t : ℝ) ≤ (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 := by
    rw [Lvalue, logb_mValue, Real.rpow_eq_pow]
    exact Nat.floor_le (div_nonneg hMpos.le (sq_nonneg _))
  have hΛpos : 0 < Λ := by linarith
  have hpow : Λ ^ (1 - 1 / (k : ℝ)) ≤ Λ := by
    calc Λ ^ (1 - 1 / (k : ℝ)) ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ1 ha1
      _ = Λ := Real.rpow_one Λ
  have hΛa : 0 < Λ ^ (1 - 1 / (k : ℝ)) := Real.rpow_pos_of_pos hΛpos _
  have hdiv : ((mValue t : ℝ) / Λ) ^ (1 - 1 / (k : ℝ)) =
      (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ ^ (1 - 1 / (k : ℝ)) :=
    Real.div_rpow hm.le hΛpos.le _
  have h1 : c' * ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ) ≤
      c' * ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ ^ (1 - 1 / (k : ℝ))) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hMpos.le hΛa hpow) hc.le
  have hT : (A + B) / (4 * c') < t := by
    have h := Nat.le_ceil ((A + B) / (4 * c'))
    have : ((⌈(A + B) / (4 * c')⌉₊ + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    push_cast at this
    linarith
  have hAB : A + B < t * (4 * c') := (div_lt_iff₀ (by positivity)).1 hT
  have hAt : A ≤ A * t := by nlinarith
  have hΛlt : Λ < c' * (2 * (t : ℝ)) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hAB ht0, mul_le_mul_of_nonneg_left htR hB]
  have hgt : 1 < c' * (2 * (t : ℝ)) ^ 2 / Λ := (one_lt_div hΛpos).2 hΛlt
  have e : c' * ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ) =
      (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 *
        (c' * (2 * (t : ℝ)) ^ 2 / Λ) := by
    have := hΛpos.ne'
    have := ht0.ne'
    field_simp <;> ring_nf
  have h2 : (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 <
      c' * ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ) := by
    rw [e]
    exact lt_mul_of_one_lt_right (div_pos hMpos (by positivity)) hgt
  rw [hdiv]
  linarith

theorem log_mValue (t : ℕ) : Real.log (mValue t : ℝ) = 2 * (t : ℝ) * Real.log 2 := by
  have : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  rw [this, Real.log_pow]
  push_cast
  ring

/-- Ledger: claim-bs-to-L. The paper's statement verbatim, with `log` the natural
logarithm: for fixed `k ≥ 2` and every constant `c > 0` (in particular the
Bansal–Sinha constant), `c k^(-29) (m / log(km))^(1 - 1/k) > L` for all large powers of
four `m`. The comparison holds for every `c > 0`, so nothing depends on the unnamed
constant. -/
theorem claim_bs_to_L (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (Lvalue k t : ℝ) < c * (k : ℝ) ^ (-29 : ℤ) *
        ((mValue t : ℝ) / Real.log ((k : ℝ) * (mValue t : ℝ))) ^ (1 - 1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hc' : 0 < c * (k : ℝ) ^ (-29 : ℤ) := mul_pos hc (zpow_pos hk0 _)
  obtain ⟨t₀, ht₀1, ht₀⟩ := Lvalue_lt_of_le_affine hk hc' (Real.log_nonneg hk1)
    (zero_le_two : (0 : ℝ) ≤ 2)
  refine ⟨t₀, fun t ht => ht₀ t ht _ ?_ ?_⟩
  all_goals
    have hm : (0 : ℝ) < (mValue t : ℝ) := by
      have : 0 < mValue t := by simp [mValue]
      exact_mod_cast this
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    rw [Real.log_mul hk0.ne' hm.ne', log_mValue]
    have h2 := Real.log_two_gt_d9
    have h2' := Real.log_two_lt_d9
    have hlk := Real.log_nonneg hk1
  · nlinarith
  · nlinarith

/-- Ledger: claim-bs-to-L. The corrected form recorded in the statement changes, with
base-two logarithms, `c > 0` explicit, and the unfloored middle term:
`c k^(-29) (m / log₂(km))^(1 - 1/k) > m^(1 - 1/k) / (log₂ m)² ≥ L`. -/
theorem claim_bs_to_L_log2 (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (Lvalue k t : ℝ) < c * (k : ℝ) ^ (-29 : ℤ) *
        ((mValue t : ℝ) / Real.logb 2 ((k : ℝ) * (mValue t : ℝ))) ^ (1 - 1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hc' : 0 < c * (k : ℝ) ^ (-29 : ℤ) := mul_pos hc (zpow_pos hk0 _)
  have hlk : 0 ≤ Real.logb 2 (k : ℝ) := Real.logb_nonneg one_lt_two hk1
  obtain ⟨t₀, ht₀1, ht₀⟩ := Lvalue_lt_of_le_affine hk hc' hlk (zero_le_two : (0 : ℝ) ≤ 2)
  refine ⟨t₀, fun t ht => ht₀ t ht _ ?_ ?_⟩
  all_goals
    have hm : (0 : ℝ) < (mValue t : ℝ) := by
      have : 0 < mValue t := by simp [mValue]
      exact_mod_cast this
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    rw [Real.logb_mul hk0.ne' hm.ne', logb_mValue] <;> linarith

/-- The unfloored middle comparison of the corrected `claim-bs-to-L`:
`L ≤ m^(1 - 1/k) / (log₂ m)²`. -/
theorem Lvalue_le_unfloored (k t : ℕ) :
    (Lvalue k t : ℝ) ≤ (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Real.logb 2 (mValue t : ℝ) ^ 2 := by
  rw [Lvalue, Real.rpow_eq_pow]
  exact Nat.floor_le (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))

/-! ## Lemma 2.1 -/

/-- Ledger: lem-2.1. Lemma 2.1 as one statement, for each fixed `k ≥ 2`, with the
paper's quantifiers: (i) `R(P_{k,m}) > L` for all large powers of four `m`;
(ii) one constant `A_k`, uniform in `m` and `η`, such that for every `0 < η < 1/2`
there is a coherent sampler (`Samples`, all workspace retained) with at most
`A_k (1 + log(1/η))` bit queries when compiled (`Runs`), whose output is a bit on every
input, promised or not, and which has error at most `η` on the domain;
(iii) one constant `S_k` with a circuit of size `S_k m (log₂ m)²` realising `P_{k,m}`
exactly, for every power of four `m ≥ 4`.
This is the paper's statement. In (ii) the coherence is the repository's `Samples`
model (a reversible circuit of reads whose measured label has the stated law); the
query count is in bit queries, two per read. -/
theorem lemma_2_1 (k : ℕ) (hk : 2 ≤ k) :
    (∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Lvalue k t < R (P k t)) ∧
    (∃ A : ℝ, 0 < A ∧ ∀ (t : ℕ) (η : ℝ), 0 < η → η < 1 / 2 →
      ∃ (n : ℕ) (L : BitInput (ForrelationCoord k t) → Bool → ℝ),
        ((2 * (n * k) : ℕ) : ℝ) ≤ A * (1 + Real.log (1 / η)) ∧
        Samples (n * k) L ∧
        (∀ [Inhabited (ForrelationCoord k t)], Runs (2 * (n * k)) L) ∧
        (∀ z, 0 ≤ L z false ∧ 0 ≤ L z true ∧ L z false + L z true = 1) ∧
        ∀ z b, P k t z = some b → 1 - η ≤ L z b) ∧
    (∃ S : ℕ, ∀ t : ℕ, 1 ≤ t → ∃ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) ∧
        (C.size : ℝ) ≤ (S : ℝ) * (mValue t : ℝ) * Real.logb 2 (mValue t : ℝ) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  refine ⟨ForrelationLower.bansalSinhaLower k hk, ?_,
    ⟨Forrelation.forrConstant k, fun t ht => Forrelation.exists_circuit k t hk1 ht⟩⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨32 * k * 2 ^ (10 * k), by positivity, fun t η hη0 hη1 => ?_⟩
  have hm : 0 < mValue t := by simp [mValue]
  haveI : Nonempty (ForrelationCoord k t) := ⟨(⟨0, by omega⟩, ⟨0, hm⟩)⟩
  refine ⟨Forrelation.repetitions k η, fun z b => bern (decodeProb k t (Forrelation.repetitions k η) z) b,
    ?_, decode_samples hk1 id _, (decode_samples hk1 id _).runs, fun z => ?_,
    fun z b hz => decodeProb_correct hk1 hη0 le_rfl z hz⟩
  · have hrep := Forrelation.repetitions_le k hη0 (by linarith)
    have hlog : 0 ≤ Real.log (1 / η) :=
      Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (10 * k) := one_le_pow₀ (by norm_num)
    push_cast
    have hr0 : (0 : ℝ) ≤ (Forrelation.repetitions k η : ℝ) := Nat.cast_nonneg _
    have e1 : 2 * ((Forrelation.repetitions k η : ℝ) * k) ≤
        2 * k * (1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η)) := by
      nlinarith [mul_le_mul_of_nonneg_left hrep hk0.le]
    have e2 : 2 * (k : ℝ) * (1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η)) ≤
        32 * k * 2 ^ (10 * k) * (1 + Real.log (1 / η)) := by
      have : 0 ≤ (k : ℝ) * Real.log (1 / η) * (2 : ℝ) ^ (10 * k) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hp hk0.le]
    linarith
  · have h0 : 0 ≤ decodeProb k t (Forrelation.repetitions k η) z := by
      simpa [bern] using (decode_samples hk1 (id : ForrelationCoord k t → _)
        (Forrelation.repetitions k η)).nonneg z true
    have h1 : 0 ≤ 1 - decodeProb k t (Forrelation.repetitions k η) z := by
      simpa [bern] using (decode_samples hk1 (id : ForrelationCoord k t → _)
        (Forrelation.repetitions k η)).nonneg z false
    refine ⟨?_, ?_, ?_⟩
    · simpa [bern] using h1
    · simpa [bern] using h0
    · simp [bern]

/-! ## The total function: winners and local tests -/

section Winners

variable {k t : ℕ} {C : Circuit (ForrelationCoord k t)}

/-- Ledger: cor-unique-winner. The paper's statement: for every input to `F_{k,m}`, at
most one column is a winner. A winner is read in the paper's words (`PaperWinsAt`).
No property of the circuit is used, so the statement holds for every circuit, in
particular the paper's `C_{k,m}`. -/
theorem cor_unique_winner (C : Circuit (ForrelationCoord k t))
    (x : BitInput (BitLoc (2 * t) (40 * t) C.size (ForrelationCoord k t)))
    (i i' : Column (2 * t))
    (hi : ∃ s, PaperWinsAt (P k t) C (2 * t) (40 * t) x i s)
    (hi' : ∃ s', PaperWinsAt (P k t) C (2 * t) (40 * t) x i' s') : i = i' := by
  obtain ⟨s, hs⟩ := hi
  obtain ⟨s', hs'⟩ := hi'
  exact winsAt_column_unique (winsAt_iff_paperWinsAt.mpr hs) (winsAt_iff_paperWinsAt.mpr hs')

/-- Ledger: lem-2.2. Lemma 2.2 in the corrected form. For every input to `F_{k,m}` and
every `(i, s)`, "i wins at address s" (`PaperWinsAt`: `i` is a winner and `s = s_i`) is
the conjunction of the tests indexed by `TestIndex`, whose number is
`K = m + (m - 1) + r (S + 2)` and whose index type does not depend on `(i, s)`.
Each test is computed exactly on every input by a deterministic adaptive decision tree
of depth at most `max 3 (ℓ + 1)`, with `ℓ = log₂ m = 2 t`. Coherently, each test, and a
uniform superposition of test indices with the exact failing flag, is a reversible read
circuit with at most the same number of reads.

Correction: the paper says each test uses `O(log m)` queries; its proof reads the
pointer test as `ℓ + 1` queries. That is true of adaptive depth, but the pointer test is
not a function of a fixed set of `ℓ + 1` bits: the target bit is chosen by the pointer
read. The statement therefore bounds decision-tree depth, not the support of a test.
Coherent evaluation is stated for the uniform superposition of indices that
Section 3.3 uses, not for arbitrary superpositions. -/
theorem lemma_2_2 (hC : CircuitRealises C (P k t)) :
    Fintype.card (TestIndex (2 * t) (40 * t) C.size) =
        mValue t + (mValue t - 1) + 40 * t * (C.size + 2) ∧
    (∀ (x : BitInput (BitLoc (2 * t) (40 * t) C.size (ForrelationCoord k t)))
        (i : Column (2 * t)) (s : Address (40 * t)),
      PaperWinsAt (P k t) C (2 * t) (40 * t) x i s ↔
        ∀ e, localTest C (2 * t) (40 * t) x i s e = true) ∧
    (∀ (i : Column (2 * t)) (s : Address (40 * t)) (e : TestIndex (2 * t) (40 * t) C.size),
      (∀ x, (localTestTree C (2 * t) (40 * t) i s e).eval x =
        localTest C (2 * t) (40 * t) x i s e) ∧
      (localTestTree C (2 * t) (40 * t) i s e).depth ≤ max 3 (2 * t + 1)) ∧
    (∀ (i : Column (2 * t)) (s : Address (40 * t)),
      (∀ e : TestIndex (2 * t) (40 * t) C.size,
        Samples (max 3 (2 * t + 1)) fun (x : BitInput (Loc k t C)) b =>
          pt (localTest C (2 * t) (40 * t) x i s e) b) ∧
      Samples (max 3 (2 * t + 1)) fun (x : BitInput (Loc k t C)) o => testLaw x i s o) := by
  refine ⟨card_testIndex (2 * t) (40 * t) C.size, fun x i s => ?_, fun i s e =>
    ⟨fun x => localTestTree_eval C _ _ x i s e, localTestTree_depth_le C _ _ i s e⟩,
    fun i s => ⟨fun e => ?_, test_samples i s⟩⟩
  · rw [← winsAt_iff_paperWinsAt]
    exact winsAt_iff_localTests hC
  · exact ((Samples.tree (localTestTree C (2 * t) (40 * t) i s e)).mono
      (localTestTree_depth_le C (2 * t) (40 * t) i s e)).congr fun x b => by
        rw [localTestTree_eval]

/-- Ledger: lem-2.2. For `m ≥ 4` (`t ≥ 1`) the depth bound `max 3 (ℓ + 1)` is `ℓ + 1`. -/
theorem testDepth_eq (t : ℕ) (ht : 1 ≤ t) : max 3 (2 * t + 1) = 2 * t + 1 := by
  omega

/-- Ledger: cor-local-dichotomy. The paper's statement: a winning column has an address
at which every test passes, and a nonwinning column has a failing test at every
address. -/
theorem cor_local_dichotomy (hC : CircuitRealises C (P k t))
    (x : BitInput (BitLoc (2 * t) (40 * t) C.size (ForrelationCoord k t)))
    (i : Column (2 * t)) :
    ((∃ s, PaperWinsAt (P k t) C (2 * t) (40 * t) x i s) →
        ∃ s, ∀ e, localTest C (2 * t) (40 * t) x i s e = true) ∧
    ((¬ ∃ s, PaperWinsAt (P k t) C (2 * t) (40 * t) x i s) →
        ∀ s, ∃ e, localTest C (2 * t) (40 * t) x i s e = false) := by
  refine ⟨fun ⟨s, hs⟩ => ⟨s, (winsAt_iff_localTests hC).mp (winsAt_iff_paperWinsAt.mpr hs)⟩,
    fun hn s => exists_failing_localTest hC ?_ s⟩
  rintro ⟨s', hs'⟩
  exact hn ⟨s', winsAt_iff_paperWinsAt.mp hs'⟩

end Winners

end QuarticQuery.Paper

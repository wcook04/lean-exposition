module

public import QuarticQuery.Upper.Decode
public import QuarticQuery.ForrelationLower.Main
public import QuarticQuery.Paper.ConstructionForrelationCircuit

/-!
# Lemma 2.1 and the projection test

Compiled as part of the `QuarticQuery` library target.
`Samples n` retains the entire coherent workspace and counts abstract reads.
The supplied generic compiler gives `Runs (2*n)` in physical bit queries.
Lemma 2.1(ii) permits this constant overhead. The paper's more precise local
one-query phase implementation is a separate phase-kickback identity.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Forrelation QuarticQuery.Upper

/-- Ledger: claim-proj-prob. Verbatim projection law and promise gap, together
with the supplied coherent `k`-read implementation. Its generic compilation
uses `2k` physical bit queries; it does not assert a tight `k`-query compiler. -/
theorem construction_projection_test (k t : ℕ) (hk : 1 ≤ k) :
    (∀ z : BitInput (ForrelationCoord k t),
      successProb z = Phi k t z ^ 2 ∧
      (P k t z = some true → delta k ^ 2 ≤ successProb z) ∧
      (P k t z = some false → successProb z ≤ delta k ^ 2 / 4)) ∧
    Samples k (fun (z : BitInput (ForrelationCoord k t)) b => bern (Phi k t z ^ 2) b) ∧
    (∀ [Inhabited (ForrelationCoord k t)],
      Runs (2 * k) (fun (z : BitInput (ForrelationCoord k t)) b => bern (Phi k t z ^ 2) b)) := by
  have hm : 0 < mValue t := by simp only [mValue]; positivity
  haveI : Nonempty (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  have hs : Samples k (fun (z : BitInput (ForrelationCoord k t)) b => bern (Phi k t z ^ 2) b) :=
    forr_samples hk id
  refine ⟨fun z => ⟨successProb_eq k t hk z,
    successProb_of_true k t hk z, successProb_of_false k t hk z⟩, hs, ?_⟩
  intro inst
  exact hs.runs

/-- Ledger: lem-2.1.ii. Partial helper: a coherent logical sampler and a
measured/reset physical implementation share the same accurate Boolean law
and a uniform query bound. The retained physical witness is supplied separately
by `construction_lemma_2_1_ii_complete`. -/
theorem construction_lemma_2_1_ii (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t : ℕ) (η : ℝ), 0 < η → η < 1 / 2 →
      ∃ (n : ℕ) (L : BitInput (ForrelationCoord k t) → Bool → ℝ),
        ((2 * (n * k) : ℕ) : ℝ) ≤ A * (1 + Real.log (1 / η)) ∧
        Samples (n * k) L ∧
        (∀ [Inhabited (ForrelationCoord k t)], Runs (2 * (n * k)) L) ∧
        (∀ z, 0 ≤ L z false ∧ 0 ≤ L z true ∧ L z false + L z true = 1) ∧
        ∀ z b, P k t z = some b → 1 - η ≤ L z b := by
  let A : ℝ := 2 * (k : ℝ) * (1 + 16 * (2 : ℝ) ^ (10 * k))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨A, by dsimp only [A]; positivity, fun t η hη0 hη1 => ?_⟩
  have hm : 0 < mValue t := by simp only [mValue]; positivity
  haveI : Nonempty (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  let L : BitInput (ForrelationCoord k t) → Bool → ℝ :=
    fun z b => bern (decodeProb k t (repetitions k η) z) b
  have hs : Samples (repetitions k η * k) L := decode_samples hk id (repetitions k η)
  refine ⟨repetitions k η, L, ?_, hs, ?_, ?_, ?_⟩
  · have hrep := repetitions_le k hη0 (by linarith : η ≤ 1)
    have hlog : 0 ≤ Real.log (1 / η) :=
      Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
    have hp : 0 ≤ (2 : ℝ) ^ (10 * k) := by positivity
    have hprod : 1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η) ≤
        (1 + 16 * (2 : ℝ) ^ (10 * k)) * (1 + Real.log (1 / η)) := by
      nlinarith
    calc
      ((2 * (repetitions k η * k) : ℕ) : ℝ) =
          (2 * (k : ℝ)) * (repetitions k η : ℝ) := by push_cast; ring
      _ ≤ (2 * (k : ℝ)) * (1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η)) :=
        mul_le_mul_of_nonneg_left hrep (by positivity)
      _ ≤ (2 * (k : ℝ)) *
          ((1 + 16 * (2 : ℝ) ^ (10 * k)) * (1 + Real.log (1 / η))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = A * (1 + Real.log (1 / η)) := by dsimp only [A]; ring
  · intro inst
    exact hs.runs
  · intro z
    refine ⟨hs.nonneg z false, hs.nonneg z true, ?_⟩
    dsimp only [L, bern]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  · intro z b hz
    exact decodeProb_correct hk hη0 le_rfl z hz

/-- Ledger: lem-2.1.i. Verbatim fixed-`k` lower bound. The source proof takes
the alternative single-block Gaussian route, rather than importing the
published theorem as an unproved hypothesis. -/
theorem construction_lemma_2_1_i (k : ℕ) (hk : 2 ≤ k) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Lvalue k t < R (P k t) :=
  ForrelationLower.bansalSinhaLower k hk

/-- Ledger: lem-2.1. Partial helper conjunction on the paper's power-of-four
domain. Its logical sampler and measured/reset physical implementation have
the same law; the full retained physical witness is added in
`construction_lemma_2_1_complete`. -/
theorem construction_lemma_2_1 (k : ℕ) (hk : 2 ≤ k) :
    (∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Lvalue k t < R (P k t)) ∧
    (∃ A : ℝ, 0 < A ∧ ∀ (t : ℕ) (η : ℝ), 0 < η → η < 1 / 2 →
      ∃ (n : ℕ) (L : BitInput (ForrelationCoord k t) → Bool → ℝ),
        ((2 * (n * k) : ℕ) : ℝ) ≤ A * (1 + Real.log (1 / η)) ∧
        Samples (n * k) L ∧
        (∀ [Inhabited (ForrelationCoord k t)], Runs (2 * (n * k)) L) ∧
        (∀ z, 0 ≤ L z false ∧ 0 ≤ L z true ∧ L z false + L z true = 1) ∧
        ∀ z b, P k t z = some b → 1 - η ≤ L z b) ∧
    (∃ S : ℕ, 0 < S ∧ ∀ t : ℕ, 1 ≤ t → ∃ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) ∧
      (C.size : ℝ) ≤ (S : ℝ) * (mValue t : ℝ) * (Real.logb 2 (mValue t : ℝ)) ^ 2) :=
  ⟨construction_lemma_2_1_i k hk,
    construction_lemma_2_1_ii k (by omega),
    construction_lemma_2_1_iii k (by omega)⟩

end QuarticQuery.Paper

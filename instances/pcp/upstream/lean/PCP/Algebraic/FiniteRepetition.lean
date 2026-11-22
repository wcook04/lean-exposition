/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Distance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Independent repetition of finite Boolean tests

Accepting every independently sampled test raises the normalized acceptance
probability to the number of repetitions, including zero repetitions. An explicit
base expansion splits a fixed-length integer seed into independent blocks.
The amplification threshold is proved entirely over the rationals.
-/

namespace PCP.Algebraic.FiniteRepetition

variable {S : Type*}

/-- Accept precisely when every independently sampled copy accepts. -/
def allTest (k : ℕ) (f : S → Bool) (s : Fin k → S) : Bool :=
  decide (∀ i, f (s i) = true)

@[simp] theorem allTest_eq_true (k : ℕ) (f : S → Bool) (s : Fin k → S) :
    allTest k f s = true ↔ ∀ i, f (s i) = true := by
  simp only [allTest, decide_eq_true_eq]

@[simp] theorem allTest_zero (f : S → Bool) (s : Fin 0 → S) :
    allTest 0 f s = true := by simp [allTest]

/-- An accepting tuple is exactly a tuple of individually accepting seeds. -/
def acceptingSeedsEquiv (k : ℕ) (f : S → Bool) :
    {s : Fin k → S // allTest k f s = true} ≃ (Fin k → {s : S // f s = true}) where
  toFun s i := ⟨s.1 i, (allTest_eq_true k f s.1).mp s.2 i⟩
  invFun s := ⟨fun i => (s i).1, (allTest_eq_true k f _).mpr fun i => (s i).2⟩
  left_inv s := by rfl
  right_inv s := by rfl

/-- Exact count of accepting tuples; no nonemptiness assumption is needed. -/
theorem card_acceptingSeeds [Fintype S] (k : ℕ) (f : S → Bool) :
    Fintype.card {s : Fin k → S // allTest k f s = true} =
      (Fintype.card {s : S // f s = true}) ^ k := by
  rw [Fintype.card_congr (acceptingSeedsEquiv k f), Fintype.card_fun, Fintype.card_fin]

/-- Independent repetition gives the exact power of the acceptance probability. -/
theorem relativeAgreement_allTest [Fintype S] (k : ℕ) (f : S → Bool) :
    relativeAgreement (allTest k f) (fun _ => true) =
      (relativeAgreement f (fun _ => true)) ^ k := by
  unfold relativeAgreement
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, card_acceptingSeeds,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, div_pow]

/-- The rejection probability is the complement of the exact acceptance power. -/
theorem relativeDistance_allTest [Fintype S] [Nonempty S] (k : ℕ) (f : S → Bool) :
    relativeDistance (allTest k f) (fun _ => true) =
      1 - (1 - relativeDistance f (fun _ => true)) ^ k := by
  have ha := relativeAgreement_allTest k f
  rw [relativeAgreement_eq_one_sub_relativeDistance,
    relativeAgreement_eq_one_sub_relativeDistance] at ha
  linarith

/-- A uniform integer seed splits into exactly `k` independent blocks of `b` bits. -/
def blockSeedEquiv (k b : ℕ) : Fin (2 ^ (k * b)) ≃ (Fin k → Fin (2 ^ b)) :=
  (finCongr (by rw [Nat.mul_comm k b, pow_mul])).trans
    (@finFunctionFinEquiv (2 ^ b) k).symm

/-- An arbitrary finite equivalence preserves normalized agreement. -/
theorem relativeAgreement_comp_equiv {T A : Type*} [Fintype S] [Fintype T]
    [DecidableEq A] (e : T ≃ S) (f g : S → A) :
    relativeAgreement (fun s => f (e s)) (fun s => g (e s)) = relativeAgreement f g := by
  unfold relativeAgreement
  rw [Fintype.card_congr e]
  congr 1
  apply congrArg Nat.cast
  exact Finset.card_equiv e (by simp)

/-- The actual fixed-length block sampler has exactly the independent acceptance law. -/
theorem relativeAgreement_allTest_fin (k b : ℕ) (f : Fin (2 ^ b) → Bool) :
    relativeAgreement (fun s : Fin (2 ^ (k * b)) => allTest k f (blockSeedEquiv k b s))
      (fun _ => true) = (relativeAgreement f (fun _ => true)) ^ k :=
  (relativeAgreement_comp_equiv (blockSeedEquiv k b) (allTest k f) (fun _ => true)).trans
    (relativeAgreement_allTest k f)

/-- The actual block sampler has rejection equal to one minus the acceptance power. -/
theorem relativeDistance_allTest_fin (k b : ℕ) (f : Fin (2 ^ b) → Bool) :
    relativeDistance (fun s : Fin (2 ^ (k * b)) => allTest k f (blockSeedEquiv k b s))
      (fun _ => true) = (1 - (1 - relativeDistance f (fun _ => true)) ^ k) :=
  (relativeDistance_comp_equiv (blockSeedEquiv k b) (allTest k f) (fun _ => true)).trans
    (relativeDistance_allTest k f)

/-- Every positive rational rejection gap admits a positive constant repetition count. -/
theorem exists_repetitions (δ : ℚ) (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ (1 - δ) ^ k ≤ 1 / 2 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℚ) < 1 / 2)
    (show 1 - δ < 1 by linarith)
  refine ⟨k, ?_, hk.le⟩
  by_contra h
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
  norm_num [hk0] at hk

end PCP.Algebraic.FiniteRepetition

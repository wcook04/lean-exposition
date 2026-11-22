/-
Portions adapted from complexitylib, Copyright (c) 2026 Samuel Schlesinger.
Released under the Apache 2.0 license. See the return's LICENSE and attribution.
-/

module

public import QuarticQuery.Statement
public import Complexity.Computability.QueryComplexity.SpectralSensitivity
public import Complexity.Foundations.BooleanAnalysis.Fourier
public import Complexity.Foundations.Data.BitString.Parity

/-!
# Appendix A: the Huang spectral inequality

Compiled as part of the `QuarticQuery` library target.

The names and proof steps below are taken from the supplied complexitylib source
at `62ca5c21461b2482e8bd12b7cb9b4937d887a33a`. These declarations use the paper's
total-function type. The spectral sensitivity is the Euclidean operator norm,
with no normalization by the cardinality of the cube.

The intermediate large-fiber argument acts on the full cube in the directions of
a maximum Fourier support. It is an alternative to the paper's preliminary
restriction to a `degree f`-dimensional face. Its endpoint is exactly Lemma A.4,
and also covers constant functions. These wrappers do not certify the literal
restriction step or the recursive matrix convention in the paper; those are
supplied in the companion restriction, matrix and route modules.
-/

public section

namespace QuarticQuery.Paper

open Finset Function Cslib
open Cslib.BitString Cslib.QueryComplexity

variable {n : ℕ}

/-- Ledger: claim-restrict-parity. A nonzero sign Fourier coefficient gives a
large parity fiber on the full cube. This states the large-fiber implication;
the companion `AppendixARestriction` file supplies the genuine face transport. -/
theorem appendixA_parityFiber_of_fourier {f : TotalBool (Fin n)}
    {S : Finset (Fin n)}
    (h : fourierCoeff (fun x => signVal (f x)) S ≠ 0) :
    ∃ V : Finset (BitInput (Fin n)), 2 ^ n < 2 * #V ∧
      ∀ x ∈ V, ∀ i ∈ S,
        update x i (!x i) ∈ V → IsSensitiveCoord f x i :=
  exists_two_pow_lt_two_mul_card_forall_isSensitiveCoord h

/-- Ledger: claim-restrict-parity. An explicit parity fiber, including its
Boolean sign parameter. Under `signVal`, `c` corresponds to the paper's
`sigma = (-1)^c`. -/
theorem appendixA_parityFiber_explicit {f : TotalBool (Fin n)}
    {S : Finset (Fin n)}
    (h : fourierCoeff (fun x => signVal (f x)) S ≠ 0) :
    ∃ c : Bool, 2 ^ n < 2 * #{x : BitInput (Fin n) | (f x ^^ parityOn S x) = c} ∧
      ∀ x, (f x ^^ parityOn S x) = c → ∀ i ∈ S,
        (f (update x i (!x i)) ^^ parityOn S (update x i (!x i))) = c →
          IsSensitiveCoord f x i := by
  set g : BitInput (Fin n) → Bool := fun x => f x ^^ parityOn S x with hg
  have hf (y : BitInput (Fin n)) : f y = (g y ^^ parityOn S y) := by
    simp only [hg, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  have hsum : ∑ x, signVal (g x) =
      (#{x | ¬g x = true} : ℝ) - #{x | g x = true} := by
    simp only [signVal, sum_ite, sum_const, nsmul_eq_mul, mul_neg, mul_one]
    ring
  have hne : #{x | g x = true} ≠ #{x | ¬g x = true} := fun heq => h (by
    simp only [Cslib.BitString.fourierCoeff, chi_eq_signVal_parityOn, ← signVal_xor]
    rw [expect_eq_sum_div_card, hsum, heq, sub_self, zero_div])
  have hcard := card_filter_add_card_filter_not (s := univ)
    fun x : BitInput (Fin n) => g x = true
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  obtain ⟨c, hc⟩ : ∃ c : Bool, 2 ^ n < 2 * #{x | g x = c} := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨false, ?_⟩
      simp only [Bool.not_eq_true] at hcard hlt
      omega
    · exact ⟨true, by omega⟩
  refine ⟨c, hc, fun x hx i hi hxi => ?_⟩
  change g x = c at hx
  change g (update x i (!x i)) = c at hxi
  rw [IsSensitiveCoord, hf, hf x, hxi, hx, parityOn_update_not hi]
  cases c <;> cases parityOn S x <;> decide

/-- Ledger: claim-restrict-parity. Nonzero degree has a sign Fourier support
with exactly that cardinality. The degree convention gives degree zero to all
constant functions. -/
theorem appendixA_topFourierSupport (f : TotalBool (Fin n))
    (hf : degree f ≠ 0) :
    ∃ S : Finset (Fin n), #S = degree f ∧
      fourierCoeff (fun x => signVal (f x)) S ≠ 0 := by
  have hf' : Cslib.BitString.totalDegree (fun x => signVal (f x)) ≠ 0 := by
    simpa only [← degree_eq_totalDegree_signVal f] using hf
  obtain ⟨S, hS, hne⟩ :=
    Cslib.BitString.exists_card_eq_totalDegree_fourierCoeff_ne_zero hf'
  refine ⟨S, ?_, hne⟩
  simpa only [← degree_eq_totalDegree_signVal f] using hS

/-- Ledger: claim-restrict-parity. The full-cube large fiber for a maximum
Fourier support. Its cardinality is measured in the ambient `n`-cube, while
the sensitive directions have cardinality `degree f`. -/
theorem appendixA_degreeSupport_parityFiber (f : TotalBool (Fin n))
    (hf : degree f ≠ 0) :
    ∃ S : Finset (Fin n), #S = degree f ∧
      ∃ V : Finset (BitInput (Fin n)), 2 ^ n < 2 * #V ∧
        ∀ x ∈ V, ∀ i ∈ S,
          update x i (!x i) ∈ V → IsSensitiveCoord f x i := by
  obtain ⟨S, hS, hne⟩ := appendixA_topFourierSupport f hf
  exact ⟨S, hS, appendixA_parityFiber_of_fourier hne⟩

/-- Ledger: claim-interlace. The signed-cube witness gives the required
spectral lower bound when all internal edges in the directions `S` are
sensitive. The invoked library witness is the full-cube directional form
of Huang's dimension argument. This statement does not expose the signed
eigenvector itself or assert equality to the paper's recursive matrix. -/
theorem appendixA_spectral_of_large_sensitive_fiber
    (f : TotalBool (Fin n)) (S : Finset (Fin n))
    (V : Finset (BitInput (Fin n))) (hV : 2 ^ n < 2 * #V)
    (hsens : ∀ x ∈ V, ∀ i ∈ S,
      update x i (!x i) ∈ V → IsSensitiveCoord f x i) :
    √(#S : ℝ) ≤ spectralSensitivity f := by
  obtain ⟨v, hv, hv0, hvV, hvS⟩ :=
    exists_nonneg_ne_zero_sqrt_card_mul_le_sum
      (by rwa [Fintype.card_fin]) S
  refine le_spectralSensitivity_of_le_sum hv hv0 fun x => ?_
  by_cases hx : x ∈ V
  · refine (hvS x).trans
      (sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => hv _)
    obtain ⟨hiS, hiV⟩ := mem_filter.1 hi
    exact mem_sensitiveCoords.2 (hsens x hx i hiS hiV)
  · rw [hvV x hx, mul_zero]
    exact sum_nonneg fun i _ => hv _

/-- Ledger: lem-A.4. Huang's spectral inequality, assembled from the preceding
large-fiber and signed-cube steps. It holds also for constant functions.
The full-cube directional route replaces the literal face restriction. -/
theorem appendixA4 (f : TotalBool (Fin n)) :
    (degree f : ℝ) ≤ spectralSensitivity f ^ 2 := by
  rcases Nat.eq_zero_or_pos (degree f) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    positivity
  obtain ⟨S, hS, V, hV, hsens⟩ := appendixA_degreeSupport_parityFiber f hpos.ne'
  have h := appendixA_spectral_of_large_sensitive_fiber f S V hV hsens
  rw [← hS]
  calc
    (#S : ℝ) = √(#S : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
    _ ≤ spectralSensitivity f ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- Ledger: lem-A.4. The square-root version of the spectral inequality. -/
theorem appendixA4_sqrt (f : TotalBool (Fin n)) :
    √(degree f : ℝ) ≤ spectralSensitivity f :=
  (Real.sqrt_le_left (spectralSensitivity_nonneg f)).2 (appendixA4 f)

end QuarticQuery.Paper

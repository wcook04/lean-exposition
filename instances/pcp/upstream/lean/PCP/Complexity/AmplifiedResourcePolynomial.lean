import PCP.Complexity.AmplifiedSequenceCost
import PCP.Complexity.PolynomialPrefixLang
import PCP.Complexity.InputReductionRuntime

/-! Fixed resource polynomials for the complete amplified input protocol. -/

namespace PCP.Lang.AmplifiedStream

open Polynomial
open PCP.Machine

/-- Actual costs and query storage, measured against the three stored Boolean words. -/
structure PolynomialResources (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (C d : ℕ) : Prop where
  cost : ∀ x bits answers : List Bool,
    (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
      (answers.map Bool.toNat))).2 ≤ C*(x.length+bits.length+answers.length+1)^d
  queries : ∀ x bits : List Bool,
    listSize (qs x bits) ≤ C*(x.length+bits.length+1)^d

def streamSize (n : ℕ) : ℕ := 96000000*(n+1)
noncomputable def sizePolynomial : Polynomial ℕ := Polynomial.C 96000000*(Polynomial.X+1)
noncomputable def queryPolynomial (C d : ℕ) : Polynomial ℕ :=
  Polynomial.C C*(Polynomial.C 3*sizePolynomial+1)^d

@[simp] theorem sizePolynomial_eval (n : ℕ) : sizePolynomial.eval n = streamSize n := by
  simp [sizePolynomial, streamSize]

@[simp] theorem queryPolynomial_eval (C d n : ℕ) :
    (queryPolynomial C d).eval n = C*(3*streamSize n+1)^d := by
  simp [queryPolynomial]

theorem resources_bounded (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (C d : ℕ) (h : PolynomialResources P qs C d) (n : ℕ) :
    Bounded P qs (streamSize n) ((queryPolynomial C d).eval n) := by
  constructor
  · intro x bits answers hx hb ha
    rw [queryPolynomial_eval]
    exact (h.cost x bits answers).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d))
  · intro x bits hx hb
    rw [queryPolynomial_eval]
    exact (h.queries x bits).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d))

theorem streamSize_bounds (t : List Bool × List Bool × List Bool) :
    PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget t.1.length ≤
      streamSize (encodeTriple t).length ∧
    t.1.length ≤ streamSize (encodeTriple t).length ∧
    t.2.1.length ≤ streamSize (encodeTriple t).length ∧
    t.2.2.length ≤ streamSize (encodeTriple t).length := by
  have hlog : Nat.clog 2 (t.1.length+2) ≤ t.1.length+2 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  simp only [streamSize, length_encodeTriple,
    PCP.Algebraic.ThreeColorCanonicalVerifier.randomBudget]
  omega

end PCP.Lang.AmplifiedStream

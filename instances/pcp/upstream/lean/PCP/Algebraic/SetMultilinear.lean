import PCP.Algebraic.Digits
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Set-multilinear encoding of univariate polynomials

Definition 3.1 and Claim 3.2 of Amireddy–Behera–Srinivasan–Sudan–Willumsgaard,
*A Simple Algebraic Proof of the PCP Theorem*, PCP-SOSA27, §3.1.

There are `c` blocks of `m` variables. The monomial `Y ^ k` is sent to the
product of `X (i, digit m k i)` over the blocks. In particular, `1` is sent to
the product of the zero-digit variables, not to the constant polynomial `1`.
The encoding is linear, not a ring homomorphism.

We define the linear map on all polynomials; recovery requires all exponents
to be below `m ^ c`. The algebra works over a commutative semiring. The base is
positive, and both `m = 1` and the empty-block case `c = 0` are allowed.
-/

namespace PCP.Algebraic.SetMultilinear

open Finset

variable {R : Type*} [CommSemiring R]
variable (m : ℕ) [NeZero m] (c : ℕ)

/-- One variable for each possible digit in each block. -/
abbrev Variables := Fin c × Fin m

/-- The image of `Y ^ k`: one selected variable from every block. -/
noncomputable def digitMonomial (k : ℕ) : MvPolynomial (Variables m c) R :=
  ∏ i : Fin c, MvPolynomial.X (i, digit m k i)

/-- Definition 3.1, extended linearly to all univariate polynomials. -/
noncomputable def encode : Polynomial R →ₗ[R] MvPolynomial (Variables m c) R :=
  Polynomial.lsum fun k => (LinearMap.id : R →ₗ[R] R).smulRight (digitMonomial m c k)

theorem encode_apply (P : Polynomial R) :
    encode m c P = ∑ k ∈ P.support, P.coeff k • digitMonomial m c k := rfl

@[simp] theorem encode_monomial (k : ℕ) (a : R) :
    encode m c (Polynomial.monomial k a) = a • digitMonomial m c k := by
  simp [encode, Polynomial.lsum_apply]

@[simp] theorem encode_C (a : R) :
    encode m c (Polynomial.C a) = a • digitMonomial m c 0 := by
  simpa only [Polynomial.monomial_zero_left] using encode_monomial m c 0 a

@[simp] theorem encode_one :
    encode m c (1 : Polynomial R) = digitMonomial m c 0 := by
  simpa only [map_one, one_smul] using encode_C m c (1 : R)

@[simp] theorem encode_X_pow (k : ℕ) :
    encode m c ((Polynomial.X : Polynomial R) ^ k) = digitMonomial m c k := by
  rw [Polynomial.X_pow_eq_monomial, encode_monomial, one_smul]

/-- Equation (3.1): the point at which the encoded polynomial recovers `P(λ)`. -/
def evaluationPoint (x : R) : Variables m c → R :=
  fun ij => x ^ ((ij.2 : ℕ) * m ^ (ij.1 : ℕ))

/-- Substitute powers of `Y` for the block variables, before evaluating `Y`. -/
noncomputable def decode : MvPolynomial (Variables m c) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun ij => Polynomial.X ^ ((ij.2 : ℕ) * m ^ (ij.1 : ℕ)))

theorem decode_digitMonomial (k : ℕ) :
    decode m c (digitMonomial m c k : MvPolynomial _ R) =
      Polynomial.X ^ (k % m ^ c) := by
  simp only [decode, digitMonomial, map_prod, MvPolynomial.eval₂Hom_X']
  rw [Finset.prod_pow_eq_pow_sum, sum_digit_mul_pow]

theorem eval_digitMonomial (k : ℕ) (x : R) :
    MvPolynomial.eval (evaluationPoint m c x) (digitMonomial m c k) =
      x ^ (k % m ^ c) := by
  simp only [digitMonomial, map_prod, MvPolynomial.eval_X, evaluationPoint]
  rw [Finset.prod_pow_eq_pow_sum, sum_digit_mul_pow]

omit [NeZero m] in
@[simp] theorem decode_smul (a : R) (P : MvPolynomial (Variables m c) R) :
    decode m c (a • P) = Polynomial.C a * decode m c P := by
  simp [decode, smul_eq_mul]

/-- Formal polynomial recovery. The exponent bound is essential. -/
theorem decode_encode (P : Polynomial R) (hP : P.natDegree < m ^ c) :
    decode m c (encode m c P) = P := by
  rw [encode_apply, map_sum]
  simp_rw [decode_smul, decode_digitMonomial]
  calc
    _ = ∑ k ∈ P.support, Polynomial.C (P.coeff k) * Polynomial.X ^ k := by
      apply sum_congr rfl
      intro k hk
      rw [Nat.mod_eq_of_lt ((Polynomial.le_natDegree_of_mem_supp k hk).trans_lt hP)]
    _ = P := Polynomial.sum_C_mul_X_pow_eq P

/-- Claim 3.2: evaluating the encoding at the power point recovers `P(x)`. -/
theorem eval_encode (P : Polynomial R) (hP : P.natDegree < m ^ c) (x : R) :
    MvPolynomial.eval (evaluationPoint m c x) (encode m c P) = P.eval x := by
  rw [encode_apply, map_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply sum_congr rfl
  intro k hk
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    eval_digitMonomial, Nat.mod_eq_of_lt ((Polynomial.le_natDegree_of_mem_supp k hk).trans_lt hP)]

/-- The input bound in the paper's `degree ≤ d`, `d < m ^ c` form. -/
theorem eval_encode_of_degree_le (d : ℕ) (hd : d < m ^ c)
    (P : Polynomial R) (hP : P.natDegree ≤ d) (x : R) :
    MvPolynomial.eval (evaluationPoint m c x) (encode m c P) = P.eval x :=
  eval_encode m c P (hP.trans_lt hd) x

/-- Recovery proves injectivity on the bounded-degree domain, even over finite fields. -/
theorem encode_injective_on :
    Set.InjOn (encode m c : Polynomial R → MvPolynomial (Variables m c) R)
      {P | P.natDegree < m ^ c} := by
  intro P hP Q hQ h
  have := congrArg (decode m c) h
  simpa only [decode_encode m c P hP, decode_encode m c Q hQ] using this

theorem encode_eq_zero_iff (P : Polynomial R) (hP : P.natDegree < m ^ c) :
    encode m c P = 0 ↔ P = 0 := by
  constructor
  · intro h
    calc P = decode m c (encode m c P) := (decode_encode m c P hP).symm
      _ = 0 := by rw [h, map_zero]
  · rintro rfl
    exact map_zero _

/-- Every basis image is homogeneous of degree `c`, including the image of `1`. -/
theorem digitMonomial_isHomogeneous (k : ℕ) :
    (digitMonomial m c k : MvPolynomial _ R).IsHomogeneous c := by
  simpa [digitMonomial] using MvPolynomial.IsHomogeneous.prod
    (univ : Finset (Fin c))
    (fun i => (MvPolynomial.X (i, digit m k i) : MvPolynomial (Variables m c) R))
    (fun _ => 1) (fun _ _ => MvPolynomial.isHomogeneous_X R _)

theorem encode_isHomogeneous (P : Polynomial R) :
    (encode m c P).IsHomogeneous c := by
  rw [encode_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (digitMonomial_isHomogeneous m c k).C_mul _

/-- Definition 3.1's constant total-degree bound. -/
theorem totalDegree_encode_le (P : Polynomial R) :
    (encode m c P).totalDegree ≤ c :=
  (encode_isHomogeneous m c P).totalDegree_le

theorem totalDegree_encode (P : Polynomial R) (hP : P.natDegree < m ^ c) (hne : P ≠ 0) :
    (encode m c P).totalDegree = c :=
  (encode_isHomogeneous m c P).totalDegree ((encode_eq_zero_iff m c P hP).not.mpr hne)

/-- The exponent vector of a basis image. -/
noncomputable def digitExponents (k : ℕ) : Variables m c →₀ ℕ :=
  ∑ i : Fin c, Finsupp.single (i, digit m k i) 1

theorem digitExponents_apply (k : ℕ) (i : Fin c) (j : Fin m) :
    digitExponents m c k (i, j) = if digit m k i = j then 1 else 0 := by
  simp [digitExponents, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq, ite_and]

theorem digitMonomial_eq_monomial (k : ℕ) :
    (digitMonomial m c k : MvPolynomial _ R) =
      MvPolynomial.monomial (digitExponents m c k) 1 := by
  simp only [digitExponents, MvPolynomial.monomial_sum_one, digitMonomial, MvPolynomial.X]

omit [NeZero m] in
/-- Every monomial contains exactly one variable from each block. The zero
polynomial satisfies this condition because its support is empty. -/
def IsSetMultilinear (P : MvPolynomial (Variables m c) R) : Prop :=
  ∀ s ∈ P.support, ∀ i : Fin c, ∑ j : Fin m, s (i, j) = 1

theorem digitMonomial_isSetMultilinear (k : ℕ) :
    IsSetMultilinear m c (digitMonomial m c k : MvPolynomial _ R) := by
  intro s hs i
  rw [digitMonomial_eq_monomial] at hs
  have heq := mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
  subst s
  simp [digitExponents_apply]

/-- The precise block condition in Definition 3.1, stronger than a total-degree bound. -/
theorem encode_isSetMultilinear (P : Polynomial R) :
    IsSetMultilinear m c (encode m c P) := by
  intro s hs i
  rw [encode_apply] at hs
  obtain ⟨k, _, hk⟩ := mem_biUnion.mp (MvPolynomial.support_sum hs)
  exact digitMonomial_isSetMultilinear m c k s (MvPolynomial.support_smul hk) i

/-- Every individual variable has degree at most one. -/
theorem degreeOf_encode_le_one (P : Polynomial R) (ij : Variables m c) :
    (encode m c P).degreeOf ij ≤ 1 := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro s hs
  have h := encode_isSetMultilinear m c P s hs ij.1
  exact (single_le_sum (fun j _ => Nat.zero_le (s (ij.1, j))) (mem_univ ij.2)).trans h.le

/-- The linear map on the paper's actual domain of polynomials of degree at most `d`. -/
noncomputable def boundedEncode (d : ℕ) :
    Polynomial.degreeLE R d →ₗ[R] MvPolynomial (Variables m c) R :=
  (encode m c).comp (Polynomial.degreeLE R d).subtype

theorem decode_boundedEncode (d : ℕ) (hd : d < m ^ c)
    (P : Polynomial.degreeLE R d) :
    decode m c (boundedEncode m c d P) = (P : Polynomial R) := by
  change decode m c (encode m c (P : Polynomial R)) = (P : Polynomial R)
  apply decode_encode
  have hp : (P : Polynomial R).degree ≤ (d : WithBot ℕ) :=
    Polynomial.mem_degreeLE.mp P.property
  exact (Polynomial.natDegree_le_of_degree_le hp).trans_lt hd

theorem eval_boundedEncode (d : ℕ) (hd : d < m ^ c)
    (P : Polynomial.degreeLE R d) (x : R) :
    MvPolynomial.eval (evaluationPoint m c x) (boundedEncode m c d P) =
      (P : Polynomial R).eval x := by
  change MvPolynomial.eval (evaluationPoint m c x) (encode m c (P : Polynomial R)) =
    (P : Polynomial R).eval x
  apply eval_encode
  have hp : (P : Polynomial R).degree ≤ (d : WithBot ℕ) :=
    Polynomial.mem_degreeLE.mp P.property
  exact (Polynomial.natDegree_le_of_degree_le hp).trans_lt hd

theorem boundedEncode_injective (d : ℕ) (hd : d < m ^ c) :
    Function.Injective (boundedEncode m c d :
      Polynomial.degreeLE R d → MvPolynomial (Variables m c) R) := by
  intro P Q h
  apply Subtype.ext
  have := congrArg (decode m c) h
  simpa only [decode_boundedEncode m c d hd] using this

end PCP.Algebraic.SetMultilinear

module

public import QuarticQuery.Paper.AppendixAAdversary
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Appendix A: a nonnegative eigenvector at the Euclidean operator norm

Compiled as part of the `QuarticQuery` library target.
It is written against the pinned Mathlib sources.

The proof is the symmetric, entrywise nonnegative case of Perron--Frobenius.
It maximizes the Rayleigh quadratic form on the unit sphere. Taking coordinatewise
absolute values cannot decrease the absolute value of that form. The resulting
nonnegative maximizer has Rayleigh quotient equal to the operator norm, and the
Rayleigh extremum theorem makes it an eigenvector. Irreducibility is unnecessary.

The file uses only the public, pinned Mathlib API, in particular
`Matrix.isSymmetric_toEuclideanLin_iff`,
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`, and
`IsSelfAdjoint.eq_smul_self_of_isLocalExtrOn_real`.
-/

public section

namespace QuarticQuery.Paper

open Finset
open scoped BigOperators

section FiniteRealMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Ledger: claim-perron. Coordinatewise absolute value in Euclidean space. -/
noncomputable def appendixAAbsVector (z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => |z.ofLp i|)

/-- Ledger: claim-perron. Absolute values preserve the Euclidean norm. -/
theorem appendixAAbsVector_norm (z : EuclideanSpace ℝ ι) :
    ‖appendixAAbsVector z‖ = ‖z‖ := by
  have hs : ‖appendixAAbsVector z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, appendixAAbsVector,
      WithLp.ofLp_toLp, sq_abs]
  nlinarith [norm_nonneg (appendixAAbsVector z), norm_nonneg z]

/-- Ledger: claim-perron. The real quadratic form as a double coordinate sum. -/
theorem appendixA_matrix_quadratic_form (A : Matrix ι ι ℝ)
    (z : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).reApplyInnerSelf z =
      ∑ i, ∑ j, z.ofLp i * A i j * z.ofLp j := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
    real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, mul_sum, mul_assoc]

/-- Ledger: claim-perron. Entrywise nonnegativity allows absolute values inside
the quadratic form, even if the original value is negative. -/
theorem appendixA_abs_quadratic_le (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (z : EuclideanSpace ℝ ι) :
    |(Matrix.toEuclideanCLM (𝕜 := ℝ) A).reApplyInnerSelf z| ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).reApplyInnerSelf
        (appendixAAbsVector z) := by
  rw [appendixA_matrix_quadratic_form, appendixA_matrix_quadratic_form]
  calc
    |∑ i, ∑ j, z.ofLp i * A i j * z.ofLp j|
        ≤ ∑ i, |∑ j, z.ofLp i * A i j * z.ofLp j| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |z.ofLp i * A i j * z.ofLp j| :=
      sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, (appendixAAbsVector z).ofLp i * A i j *
          (appendixAAbsVector z).ofLp j := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      simp only [appendixAAbsVector, WithLp.ofLp_toLp, abs_mul,
        abs_of_nonneg (hA i j)]

/-- Ledger: claim-perron. Every real symmetric entrywise nonnegative matrix has
a nonnegative unit eigenvector for its Euclidean operator norm. This includes
the zero matrix; the paper only needs the nonzero case. -/
theorem appendixA_exists_nonneg_unit_eigenvector
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j) :
    ∃ z : EuclideanSpace ℝ ι,
      (∀ i, 0 ≤ z.ofLp i) ∧ ‖z‖ = 1 ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) A z =
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ • z := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hsym : T.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsym
  obtain ⟨e, he⟩ := exists_norm_eq (EuclideanSpace ℝ ι) (by norm_num : (0 : ℝ) ≤ 1)
  have hcompact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ ι) 1) :=
    isCompact_sphere _ _
  have hnonempty : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty :=
    ⟨e, by simpa using he⟩
  obtain ⟨z₀, hz₀, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty T.reApplyInnerSelf_continuous.continuousOn
  have hz₀norm : ‖z₀‖ = 1 := by simpa using hz₀
  let z := appendixAAbsVector z₀
  have hznorm : ‖z‖ = 1 := (appendixAAbsVector_norm z₀).trans hz₀norm
  have hzpos : ∀ i, 0 ≤ z.ofLp i := fun i => abs_nonneg _
  have hquad : T.reApplyInnerSelf z₀ ≤ T.reApplyInnerSelf z :=
    (le_abs_self _).trans (appendixA_abs_quadratic_le A hpos z₀)
  have hmaxz : IsMaxOn T.reApplyInnerSelf
      (Metric.sphere (0 : EuclideanSpace ℝ ι) 1) z := by
    intro x hx
    exact (hmax hx).trans hquad
  have hqnonneg : 0 ≤ T.reApplyInnerSelf z :=
    (abs_nonneg _).trans (appendixA_abs_quadratic_le A hpos z₀)
  have hbound : ∀ x : EuclideanSpace ℝ ι,
      |T.rayleighQuotient x| ≤ T.reApplyInnerSelf z := by
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hqnonneg
    have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let y : EuclideanSpace ℝ ι := ‖x‖⁻¹ • x
    have hynorm : ‖y‖ = 1 := by
      simp only [y, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
      exact inv_mul_cancel₀ hxnorm
    have habsy : appendixAAbsVector y ∈
        Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := by
      simpa [appendixAAbsVector_norm] using hynorm
    have hh : |T.reApplyInnerSelf y| ≤ T.reApplyInnerSelf z :=
      (appendixA_abs_quadratic_le A hpos y).trans (hmaxz habsy)
    have hr : T.rayleighQuotient y = T.rayleighQuotient x :=
      T.rayleigh_smul x (inv_ne_zero hxnorm)
    rw [← hr, ContinuousLinearMap.rayleighQuotient, hynorm, one_pow, div_one]
    exact hh
  have hqeq : T.reApplyInnerSelf z = ‖T‖ := by
    apply le_antisymm
    · have hb := T.rayleighQuotient_le_norm z
      rw [ContinuousLinearMap.rayleighQuotient, hznorm, one_pow, div_one] at hb
      exact (le_abs_self _).trans hb
    · rw [T.norm_eq_iSup_rayleighQuotient hsym]
      exact ciSup_le hbound
  have hmaxz' : IsMaxOn T.reApplyInnerSelf
      (Metric.sphere (0 : EuclideanSpace ℝ ι) ‖z‖) z := by
    simpa only [hznorm] using hmaxz
  have heigen := hsa.eq_smul_self_of_isLocalExtrOn_real
    (Or.inr hmaxz'.isLocalMaxOn)
  refine ⟨z, hzpos, hznorm, ?_⟩
  simpa only [ContinuousLinearMap.rayleighQuotient, hznorm, one_pow, div_one,
    hqeq] using heigen

end FiniteRealMatrix

/-- Ledger: claim-perron. The paper's exact coordinate-level Perron witness.
Nonzero Γ is not needed, and no irreducibility assumption is introduced. -/
theorem appendixA_perron {n : ℕ} (Γ : AppendixAMatrix n)
    (hsym : ∀ x y, Γ x y = Γ y x) (hpos : ∀ x y, 0 ≤ Γ x y) :
    ∃ v, AppendixAPerronWitness Γ v := by
  classical
  have hH : Γ.IsHermitian := by
    ext x y
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym y x
  obtain ⟨z, hzpos, hznorm, hze⟩ :=
    appendixA_exists_nonneg_unit_eigenvector Γ hH hpos
  refine ⟨z.ofLp, hzpos, ?_, ?_⟩
  · have hn := EuclideanSpace.real_norm_sq_eq z
    rw [hznorm, one_pow] at hn
    exact hn.symm
  · intro x
    have he := congrArg (fun w : EuclideanSpace ℝ (BitInput (Fin n)) => w.ofLp x) hze
    simpa only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
      PiLp.smul_apply, smul_eq_mul, appendixAMatrixNorm] using he

/-- Ledger: claim-perron. The previously explicit Perron obligation is discharged. -/
theorem appendixA_perronObligation {n : ℕ} (Γ : AppendixAMatrix n) :
    AppendixAPerronObligation Γ := by
  intro hsym hpos _hne
  exact appendixA_perron Γ hsym hpos

end QuarticQuery.Paper

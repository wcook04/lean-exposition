import Breakdown.CertCell.RowsMatchNormalRadial
import Breakdown.CertCell.RowsMatchNormalHeight
import Breakdown.CertCell.RowsMatchDerivedNormal

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SegmentNormal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula LocalField SegmentLine
open Breakdown.CertCell.Assembly

namespace Internal

theorem strip_int {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hf : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3)
    {α β γ δ : ℝ} (hα : 0 ≤ α) (κ : ℂ) (w : ℝ × ℝ → ℂ) (hw : Continuous w) :
    IntegrableOn (fun p : ℝ × ℝ => κ * modeVec m n v p.1 p.2 a + w p * gradMode m n G a b p)
      (Icc α β ×ˢ Icc γ δ) := by
  have h := localModeStripIntegrable m v G H hf n β γ δ
  have hc : IsCompact (Icc 0 β ×ˢ Icc γ δ) := isCompact_Icc.prod isCompact_Icc
  have i : IntegrableOn (fun p : ℝ × ℝ => κ * modeVec m n v p.1 p.2 a + w p * gradMode m n G a b p)
      (Icc 0 β ×ˢ Icc γ δ) :=
    ((h.1 a).const_mul κ).add ((h.2 a b).continuousOn_mul hw.continuousOn hc)
  exact i.mono_set (prod_mono (Icc_subset_Icc_left hα) subset_rfl)

theorem radialStripMoment_sum {c o lo hi : ℝ} {F dF : ℝ × ℝ → ℂ}
    (hI : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (s : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) :
    radialStripMoment c o lo hi F dF (fun u => ∑ i ∈ s, w i * f i u) =
      ∑ i ∈ s, ((w i : ℝ) : ℂ) * radialStripMoment c o lo hi F dF (f i) := by
  unfold radialStripMoment
  have hc : IsCompact (Icc (min c o) (max c o) ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  have hX : ∀ i ∈ s, IntegrableOn (fun p : ℝ × ℝ => ((w i : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((f i p.2 : ℝ) : ℂ))) (Icc (min c o) (max c o) ×ˢ Icc lo hi) :=
    fun i _ => (hI.mul_continuousOn (Complex.continuous_ofReal.comp ((hf i).comp continuous_snd)).continuousOn
      hc).const_mul _
  have h1 : ∫ p in Icc (min c o) (max c o) ×ˢ Icc lo hi, ((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * (((fun u => ∑ i ∈ s, w i * f i u) p.2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∫ p in Icc (min c o) (max c o) ×ˢ Icc lo hi, ((w i : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((f i p.2 : ℝ) : ℂ)) := by
    rw [← integral_finsetSum s hX]
    congr 1
    funext p
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [integral_const_mul]; ring)

theorem heightStripMoment_sum {c o lo hi : ℝ} {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (hwt : Continuous wt)
    (hI : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (s : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) :
    heightStripMoment c o lo hi wt F dF (fun u => ∑ i ∈ s, w i * f i u) =
      ∑ i ∈ s, ((w i : ℝ) : ℂ) * heightStripMoment c o lo hi wt F dF (f i) := by
  unfold heightStripMoment
  have hc : IsCompact (Icc lo hi ×ˢ Icc (min c o) (max c o)) := isCompact_Icc.prod isCompact_Icc
  have hX : ∀ i ∈ s, IntegrableOn (fun p : ℝ × ℝ => ((w i : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * f i p.1 : ℝ) : ℂ)))
      (Icc lo hi ×ˢ Icc (min c o) (max c o)) :=
    fun i _ => (hI.mul_continuousOn (Complex.continuous_ofReal.comp ((hwt.comp continuous_fst).mul
      ((hf i).comp continuous_fst))).continuousOn hc).const_mul _
  have h1 : ∫ p in Icc lo hi ×ˢ Icc (min c o) (max c o), ((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * (fun u => ∑ i ∈ s, w i * f i u) p.1 : ℝ) : ℂ) =
      ∑ i ∈ s, ∫ p in Icc lo hi ×ˢ Icc (min c o) (max c o), ((w i : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * f i p.1 : ℝ) : ℂ)) := by
    rw [← integral_finsetSum s hX]
    congr 1
    funext p
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [integral_const_mul]; ring)

def testPoly (S : FaceSegment) (d : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C (S.testCoef d j) * Polynomial.X ^ j

theorem testPoly_eval (S : FaceSegment) (d : ℕ) (u : ℝ) : (testPoly S d).eval u = S.test d u := by
  simp [testPoly, FaceSegment.test, Polynomial.eval_finsetSum]

theorem testPoly_natDegree (S : FaceSegment) (d : ℕ) : (testPoly S d).natDegree ≤ d := by
  unfold testPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

theorem testPoly_coeff_gt (S : FaceSegment) (d k : ℕ) (h : d < k) : (testPoly S d).coeff k = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((testPoly_natDegree S d).trans_lt h)

theorem testPoly_coeff_self (S : FaceSegment) (d : ℕ) : (testPoly S d).coeff d = S.testCoef d d := by
  simp [testPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

theorem coef_zero_above (S : FaceSegment) (hS : ∀ d, S.testCoef d d ≠ 0) (Q : Polynomial ℝ) (D : ℕ)
    (hQ : Q.natDegree ≤ D) : ∀ (N : ℕ) (w : ℕ → ℝ), (∀ u, Q.eval u = ∑ i ∈ Finset.range N, w i * S.test i u) →
      ∀ i, D < i → i < N → w i = 0 := by
  intro N
  induction N with
  | zero => intro w _ i _ hi; exact absurd hi (Nat.not_lt_zero _)
  | succ N ih =>
    intro w hw i hDi hiN
    have hpoly : Q = ∑ j ∈ Finset.range (N + 1), Polynomial.C (w j) * testPoly S j := by
      apply Polynomial.funext
      intro u
      rw [hw u, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl (fun j _ => by rw [Polynomial.eval_mul, Polynomial.eval_C, testPoly_eval])
    by_cases hDN : D < N
    · have hN : w N = 0 := by
        have hc := congrArg (fun P => Polynomial.coeff P N) hpoly
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ hDN), Polynomial.finsetSum_coeff,
          Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
            rw [Polynomial.coeff_C_mul, testPoly_coeff_gt S j N (Finset.mem_range.1 hj), mul_zero]),
          zero_add, Polynomial.coeff_C_mul, testPoly_coeff_self] at hc
        exact (mul_eq_zero.1 hc.symm).resolve_right (hS N)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hiN with h | h
      · refine ih w (fun u => ?_) i hDi h
        rw [hw u, Finset.sum_range_succ, hN, zero_mul, add_zero]
      · rw [h]
        exact hN
    · exact absurd (lt_of_lt_of_le hDi (Nat.lt_succ_iff.1 hiN)) hDN

def slopePoly (S : FaceSegment) (d : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C ((j : ℝ) * S.testCoef d j) * Polynomial.X ^ (j - 1)

theorem slopePoly_eval (S : FaceSegment) (d : ℕ) (u : ℝ) :
    (slopePoly S d).eval u = ∑ j ∈ Finset.range (d + 1), ((j : ℝ) * S.testCoef d j) * u ^ (j - 1) := by
  simp [slopePoly, Polynomial.eval_finsetSum]

theorem slopePoly_natDegree (S : FaceSegment) (d : ℕ) : (slopePoly S d).natDegree ≤ d := by
  unfold slopePoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem test_contDiff (S : FaceSegment) (d : ℕ) : ContDiff ℝ ∞ (S.test d) := by
  unfold FaceSegment.test
  exact ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_id.pow i))

theorem test_deriv (S : FaceSegment) (d : ℕ) (u : ℝ) :
    deriv (S.test d) u = ∑ j ∈ Finset.range (d + 1), ((j : ℝ) * S.testCoef d j) * u ^ (j - 1) := by
  have h : HasDerivAt (S.test d) (∑ j ∈ Finset.range (d + 1), S.testCoef d j * ((j : ℝ) * u ^ (j - 1))) u := by
    unfold FaceSegment.test
    exact HasDerivAt.fun_sum (fun j _ => (hasDerivAt_pow j u).const_mul _)
  rw [h.deriv]
  exact Finset.sum_congr rfl (fun j _ => by ring)

end Internal

end Breakdown.CertCell.SegmentNormal

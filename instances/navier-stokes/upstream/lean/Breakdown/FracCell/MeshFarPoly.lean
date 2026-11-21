import Breakdown.FracCell.MeshFarSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshFarPolyInternal

theorem lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  fun_prop

theorem heightPoly_continuous (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  fun_prop

theorem radial_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    ∀ i j : ℕ, i < j → ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * B.radialPoly j r * r ^ i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hij
    have hC := hB.radial_leading i
    have hw := lineWeight_continuous K
    have hpj := radialPoly_continuous B j
    have hpt : ∀ r, r ^ i = (1 / B.radialCoef i i) * B.radialPoly i r
        - ∑ t ∈ Finset.range i, (B.radialCoef i t / B.radialCoef i i) * r ^ t := by
      intro r
      have hC0 : B.radialCoef i i ≠ 0 := hC.ne'
      unfold CellBases.radialPoly
      rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
      have e : ∑ t ∈ Finset.range i, 1 / B.radialCoef i i * (B.radialCoef i t * r ^ t)
          = ∑ t ∈ Finset.range i, B.radialCoef i t / B.radialCoef i i * r ^ t :=
        Finset.sum_congr rfl (fun t _ => by ring)
      rw [e, add_sub_cancel_left]
      field_simp
    have hint : ∀ r, K.lineWeight r * B.radialPoly j r * r ^ i =
        (1 / B.radialCoef i i) * (K.lineWeight r * B.radialPoly j r * B.radialPoly i r)
          - ∑ t ∈ Finset.range i, (B.radialCoef i t / B.radialCoef i i) * (K.lineWeight r * B.radialPoly j r * r ^ t) := by
      intro r
      rw [hpt r, mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl (fun t _ => by ring)
    simp_rw [hint]
    rw [integral_sub, integral_finsetSum, integral_const_mul]
    · rw [hB.radial_orthonormal j i, if_neg (by omega), mul_zero, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero (fun t ht => ?_)
      rw [integral_const_mul, ih t (by simp at ht; omega) j (by simp at ht; omega), mul_zero]
    · intro t _
      exact ((continuous_const.mul ((hw.mul hpj).mul (continuous_pow t)))).integrableOn_Icc
    · exact (continuous_const.mul ((hw.mul hpj).mul (radialPoly_continuous B i))).integrableOn_Icc
    · exact (continuous_finsetSum _ (fun t _ => continuous_const.mul ((hw.mul hpj).mul (continuous_pow t)))).integrableOn_Icc

theorem height_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    ∀ i j : ℕ, i < j → ∫ z in Set.Icc K.z₁ K.z₂, B.heightPoly j z * z ^ i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hij
    have hC := hB.height_leading i
    have hpj := heightPoly_continuous B j
    have hpt : ∀ r, r ^ i = (1 / B.heightCoef i i) * B.heightPoly i r
        - ∑ t ∈ Finset.range i, (B.heightCoef i t / B.heightCoef i i) * r ^ t := by
      intro r
      have hC0 : B.heightCoef i i ≠ 0 := hC.ne'
      unfold CellBases.heightPoly
      rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
      have e : ∑ t ∈ Finset.range i, 1 / B.heightCoef i i * (B.heightCoef i t * r ^ t)
          = ∑ t ∈ Finset.range i, B.heightCoef i t / B.heightCoef i i * r ^ t :=
        Finset.sum_congr rfl (fun t _ => by ring)
      rw [e, add_sub_cancel_left]
      field_simp
    have hint : ∀ r, B.heightPoly j r * r ^ i =
        (1 / B.heightCoef i i) * (B.heightPoly j r * B.heightPoly i r)
          - ∑ t ∈ Finset.range i, (B.heightCoef i t / B.heightCoef i i) * (B.heightPoly j r * r ^ t) := by
      intro r
      rw [hpt r, mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl (fun t _ => by ring)
    simp_rw [hint]
    rw [integral_sub, integral_finsetSum, integral_const_mul]
    · rw [hB.height_orthonormal j i, if_neg (by omega), mul_zero, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero (fun t ht => ?_)
      rw [integral_const_mul, ih t (by simp at ht; omega) j (by simp at ht; omega), mul_zero]
    · intro t _
      exact ((continuous_const.mul (hpj.mul (continuous_pow t)))).integrableOn_Icc
    · exact (continuous_const.mul (hpj.mul (heightPoly_continuous B i))).integrableOn_Icc
    · exact (continuous_finsetSum _ (fun t _ => continuous_const.mul (hpj.mul (continuous_pow t)))).integrableOn_Icc

theorem poly_continuous (D : ℕ) (P : ℝ × ℝ → ℂ) (hP : P ∈ polyFn D D) : Continuous P := by
  obtain ⟨cf, hcf⟩ := hP
  rw [show P = fun p => ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)) from funext hcf]
  fun_prop

theorem coef_poly_far (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (D : ℕ) (P : ℝ × ℝ → ℂ)
    (hP : P ∈ polyFn D D) (j l : ℕ) (hjl : D < max j l) : B.coef K P j l = 0 := by
  obtain ⟨cf, hcf⟩ := hP
  have hw := lineWeight_continuous K
  have hpj := radialPoly_continuous B j
  have hql := heightPoly_continuous B l
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  unfold CellBases.coef
  have hfun : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * P p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
      = ∑ a : Fin (D + 1), ∑ b : Fin (D + 1), cf a b *
        (((K.lineWeight p.1 * B.radialPoly j p.1 * p.1 ^ (a : ℕ) : ℝ) : ℂ)
          * ((B.heightPoly l p.2 * p.2 ^ (b : ℕ) : ℝ) : ℂ)) := by
    intro p
    rw [hcf p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_const_mul]
      have hprod : ∫ p in K.rect, (((K.lineWeight p.1 * B.radialPoly j p.1 * p.1 ^ (a : ℕ) : ℝ) : ℂ)
          * ((B.heightPoly l p.2 * p.2 ^ (b : ℕ) : ℝ) : ℂ))
          = (∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r * B.radialPoly j r * r ^ (a : ℕ) : ℝ) : ℂ))
            * ∫ z in Set.Icc K.z₁ K.z₂, ((B.heightPoly l z * z ^ (b : ℕ) : ℝ) : ℂ) := by
        unfold CellBox.rect
        rw [Measure.volume_eq_prod]
        exact setIntegral_prod_mul (fun r => ((K.lineWeight r * B.radialPoly j r * r ^ (a : ℕ) : ℝ) : ℂ))
          (fun z => ((B.heightPoly l z * z ^ (b : ℕ) : ℝ) : ℂ)) _ _
      rw [hprod, integral_complex_ofReal, integral_complex_ofReal]
      rcases lt_max_iff.mp hjl with h | h
      · rw [radial_orth K B hB a j (by omega)]
        simp
      · rw [height_orth K B hB b l (by omega)]
        simp
    · intro b _
      exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))
  · intro a _
    exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))

theorem coef_add_poly (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (D : ℕ) (G P : ℝ × ℝ → ℂ)
    (hP : P ∈ polyFn D D) (j l : ℕ) (hjl : D < max j l) :
    B.coef K (fun p => G p + P p) j l = B.coef K G j l := by
  have h0 := coef_poly_far K B hB D P hP j l hjl
  have hw := lineWeight_continuous K
  have hpj := radialPoly_continuous B j
  have hql := heightPoly_continuous B l
  have hPc := poly_continuous D P hP
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  unfold CellBases.coef at h0 ⊢
  have hIP : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * P p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
      K.rect := ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop))
  have hsplit : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * (G p + P p) * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
      = (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
        + (K.lineWeight p.1 : ℂ) * P p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := fun p => by ring
  simp_rw [hsplit]
  by_cases hG : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
      K.rect
  · rw [integral_add hG hIP, h0, add_zero]
  · have hS : ¬ IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
        + (K.lineWeight p.1 : ℂ) * P p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
      intro h'
      apply hG
      convert h'.sub hIP using 1
      funext p
      simp
    rw [integral_undef hS, integral_undef hG]

theorem coef_congr_off_axis (K : CellBox) (B : CellBases) (F G : ℝ × ℝ → ℂ)
    (h : ∀ p ∈ K.rect, p.1 ≠ 0 → F p = G p) (j l : ℕ) : B.coef K F j l = B.coef K G j l := by
  unfold CellBases.coef
  have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
  filter_upwards [hae] with p hp hpr
  rw [h p hpr hp]

theorem coef_far_off_axis (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (D : ℕ) (F G P : ℝ × ℝ → ℂ)
    (hP : P ∈ polyFn D D) (h : ∀ p ∈ K.rect, p.1 ≠ 0 → F p = G p + P p) (j l : ℕ) (hjl : D < max j l) :
    B.coef K F j l = B.coef K G j l := by
  rw [coef_congr_off_axis K B F (fun p => G p + P p) h j l]
  exact coef_add_poly K B hB D G P hP j l hjl

end MeshFarPolyInternal

end CellAnalysis

end CellCert

end Breakdown

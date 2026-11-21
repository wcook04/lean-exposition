import Breakdown.CertCell.RowLowPartPoly

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem rect_restrict (A B : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (A ×ˢ B) = (volume.restrict A).prod (volume.restrict B) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

theorem rect_iter_snd {A B : Set ℝ} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (A ×ˢ B)) :
    ∫ p in A ×ˢ B, f p = ∫ z in B, ∫ r in A, f (r, z) := by
  rw [rect_restrict]
  rw [IntegrableOn, rect_restrict] at hf
  exact integral_prod_symm f hf

theorem rect_iter_fst {A B : Set ℝ} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (A ×ˢ B)) :
    ∫ p in A ×ˢ B, f p = ∫ r in A, ∫ z in B, f (r, z) := by
  rw [rect_restrict]
  rw [IntegrableOn, rect_restrict] at hf
  exact integral_prod f hf

theorem cont_int_rect {f : ℝ × ℝ → ℂ} (hf : Continuous f) (a b c d : ℝ) :
    IntegrableOn f (Icc a b ×ˢ Icc c d) :=
  hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem icc_ftc {u du : ℝ → ℂ} (hdu : Continuous du) (hu : ∀ x, HasDerivAt u (du x) x) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, du x = u b - u a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hu x) (hdu.intervalIntegrable a b)

theorem rect_ftc_fst {F dF : ℝ × ℝ → ℂ} (hdF : Continuous dF)
    (hF : ∀ p : ℝ × ℝ, HasDerivAt (fun r => F (r, p.2)) (dF p) p.1) {a b c d : ℝ} (hab : a ≤ b) :
    ∫ p in Icc a b ×ˢ Icc c d, dF p = ∫ z in Icc c d, (F (b, z) - F (a, z)) := by
  rw [rect_iter_snd (cont_int_rect hdF a b c d)]
  refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
  exact icc_ftc (u := fun r => F (r, z)) (hdF.comp (continuous_id.prodMk continuous_const))
    (fun x => hF (x, z)) hab

theorem rect_ftc_snd {F dF : ℝ × ℝ → ℂ} (hdF : Continuous dF)
    (hF : ∀ p : ℝ × ℝ, HasDerivAt (fun z => F (p.1, z)) (dF p) p.2) {a b c d : ℝ} (hcd : c ≤ d) :
    ∫ p in Icc a b ×ˢ Icc c d, dF p = ∫ r in Icc a b, (F (r, d) - F (r, c)) := by
  rw [rect_iter_fst (cont_int_rect hdF a b c d)]
  refine setIntegral_congr_fun measurableSet_Icc (fun r _ => ?_)
  exact icc_ftc (u := fun z => F (r, z)) (hdF.comp (continuous_const.prodMk continuous_id))
    (fun x => hF (r, x)) hcd

theorem radialStrip_of_smooth {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {c o lo hi : ℝ} (hco : c ≠ o)
    {t : ℝ → ℝ} (ht : Continuous t) :
    radialStripMoment c o lo hi φ (CellBox.radialDeriv φ) t = ∫ z in Icc lo hi, φ (c, z) * (t z : ℂ) := by
  unfold radialStripMoment
  set F : ℝ × ℝ → ℂ := fun p => (((p.1 - o) / (c - o) : ℝ) : ℂ) * φ p * ((t p.2 : ℝ) : ℂ) with hFdef
  have hco' : c - o ≠ 0 := sub_ne_zero.2 hco
  have hdF : Continuous (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * φ p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv φ p) * ((t p.2 : ℝ) : ℂ)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)
    have h2 : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (ht.comp continuous_snd)
    exact ((continuous_const.mul hφ.continuous).add (h1.mul (continuous_radialDeriv hφ))).mul h2
  have hF : ∀ p : ℝ × ℝ, HasDerivAt (fun r => F (r, p.2)) (((((1 / (c - o) : ℝ)) : ℂ) * φ p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv φ p) * ((t p.2 : ℝ) : ℂ)) p.1 := by
    intro p
    have hl : HasDerivAt (fun r : ℝ => (((r - o) / (c - o) : ℝ) : ℂ)) (((1 / (c - o) : ℝ)) : ℂ) p.1 := by
      have := (((hasDerivAt_id p.1).sub_const o).div_const (c - o)).ofReal_comp
      simpa [one_div] using this
    have := (hl.fun_mul (hasDerivAt_fst hφ p)).mul_const ((t p.2 : ℝ) : ℂ)
    simp only [Prod.mk.eta] at this
    exact this
  rw [rect_ftc_fst hdF hF (min_le_max)]
  rcases lt_or_gt_of_ne hco with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    have he : edgeSign c o = -1 := by unfold edgeSign; rw [if_neg (not_lt.2 h.le)]
    rw [he, neg_one_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    simp only [hFdef, sub_self, zero_div, Complex.ofReal_zero, zero_mul, div_self hco', Complex.ofReal_one, one_mul]
    have : (((o - o) / (c - o) : ℝ) : ℂ) = 0 := by simp
    simp
  · rw [min_eq_right h.le, max_eq_left h.le]
    have he : edgeSign c o = 1 := by unfold edgeSign; rw [if_pos h]
    rw [he, one_mul]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    simp only [hFdef, sub_self, zero_div, Complex.ofReal_zero, zero_mul, div_self hco', Complex.ofReal_one, one_mul,
      sub_zero]

theorem heightStrip_of_smooth {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {c o lo hi : ℝ} (hco : c ≠ o)
    {wt t : ℝ → ℝ} (hw : Continuous wt) (ht : Continuous t) :
    heightStripMoment c o lo hi wt φ (CellBox.heightDeriv φ) t =
      ∫ r in Icc lo hi, φ (r, c) * ((wt r * t r : ℝ) : ℂ) := by
  unfold heightStripMoment
  set F : ℝ × ℝ → ℂ := fun p => (((p.2 - o) / (c - o) : ℝ) : ℂ) * φ p * ((wt p.1 * t p.1 : ℝ) : ℂ) with hFdef
  have hco' : c - o ≠ 0 := sub_ne_zero.2 hco
  have hdF : Continuous (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * φ p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * CellBox.heightDeriv φ p) * ((wt p.1 * t p.1 : ℝ) : ℂ)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)
    have h2 : Continuous (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hw.comp continuous_fst).mul (ht.comp continuous_fst))
    exact ((continuous_const.mul hφ.continuous).add (h1.mul (continuous_heightDeriv hφ))).mul h2
  have hF : ∀ p : ℝ × ℝ, HasDerivAt (fun z => F (p.1, z)) (((((1 / (c - o) : ℝ)) : ℂ) * φ p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * CellBox.heightDeriv φ p) * ((wt p.1 * t p.1 : ℝ) : ℂ)) p.2 := by
    intro p
    have hl : HasDerivAt (fun z : ℝ => (((z - o) / (c - o) : ℝ) : ℂ)) (((1 / (c - o) : ℝ)) : ℂ) p.2 := by
      have := (((hasDerivAt_id p.2).sub_const o).div_const (c - o)).ofReal_comp
      simpa [one_div] using this
    have := (hl.fun_mul (hasDerivAt_snd hφ p)).mul_const ((wt p.1 * t p.1 : ℝ) : ℂ)
    simp only [Prod.mk.eta] at this
    exact this
  rw [rect_ftc_snd hdF hF (min_le_max)]
  rcases lt_or_gt_of_ne hco with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    have he : edgeSign c o = -1 := by unfold edgeSign; rw [if_neg (not_lt.2 h.le)]
    rw [he, neg_one_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    have hc1 : ((c : ℂ) - o) / ((c : ℂ) - o) = 1 := div_self (by exact_mod_cast hco')
    simp [hFdef, hc1]
  · rw [min_eq_right h.le, max_eq_left h.le]
    have he : edgeSign c o = 1 := by unfold edgeSign; rw [if_pos h]
    rw [he, one_mul]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    have hc1 : ((c : ℂ) - o) / ((c : ℂ) - o) = 1 := div_self (by exact_mod_cast hco')
    simp [hFdef, hc1]

theorem test_cont (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

theorem basisValue_cont (B : CellBases) (j l : ℕ) : Continuous (basisValue B j l) := by
  unfold basisValue CellBases.radialPoly CellBases.heightPoly
  fun_prop

theorem conj_basisValue (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (basisValue B j l p) = basisValue B j l p := by
  unfold basisValue
  exact Complex.conj_ofReal _

theorem seg_expand_snd (hexp : SegmentTestExpansionStatement) {S : FaceSegment} {N : ℕ}
    (hlead : ∀ d, S.testCoef d d ≠ 0)
    (horth : ∀ d d', d < N → d' < N →
      ∫ u in Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    {P : ℝ → ℂ} (hP : IsUnivariatePoly N P) {a b : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b ×ˢ Icc S.lo S.hi)) :
    ∑ d ∈ Finset.range N, (starRingEnd ℂ) (∫ w in Icc S.lo S.hi, P w * (S.test d w : ℂ)) *
        ∫ p in Icc a b ×ˢ Icc S.lo S.hi, f p * (S.test d p.2 : ℂ)
      = ∫ p in Icc a b ×ˢ Icc S.lo S.hi, f p * (starRingEnd ℂ) (P p.2) := by
  have hE := hexp S N hlead horth P hP
  have hc : ∀ p : ℝ × ℝ, f p * (starRingEnd ℂ) (P p.2) = ∑ d ∈ Finset.range N,
      (starRingEnd ℂ) (∫ w in Icc S.lo S.hi, P w * (S.test d w : ℂ)) * (f p * (S.test d p.2 : ℂ)) := by
    intro p
    rw [hE p.2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hc]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [integral_const_mul]
  · intro d _
    refine Integrable.const_mul ?_ _
    exact hf.mul_continuousOn
      (Complex.continuous_ofReal.comp ((test_cont S d).comp continuous_snd)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)

theorem seg_expand_fst (hexp : SegmentTestExpansionStatement) {S : FaceSegment} {N : ℕ}
    (hlead : ∀ d, S.testCoef d d ≠ 0)
    (horth : ∀ d d', d < N → d' < N →
      ∫ u in Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    {P : ℝ → ℂ} (hP : IsUnivariatePoly N P) {a b : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f (Icc S.lo S.hi ×ˢ Icc a b)) :
    ∑ d ∈ Finset.range N, (starRingEnd ℂ) (∫ w in Icc S.lo S.hi, P w * (S.test d w : ℂ)) *
        ∫ p in Icc S.lo S.hi ×ˢ Icc a b, f p * (S.test d p.1 : ℂ)
      = ∫ p in Icc S.lo S.hi ×ˢ Icc a b, f p * (starRingEnd ℂ) (P p.1) := by
  have hE := hexp S N hlead horth P hP
  have hc : ∀ p : ℝ × ℝ, f p * (starRingEnd ℂ) (P p.1) = ∑ d ∈ Finset.range N,
      (starRingEnd ℂ) (∫ w in Icc S.lo S.hi, P w * (S.test d w : ℂ)) * (f p * (S.test d p.1 : ℂ)) := by
    intro p
    rw [hE p.1, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hc]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [integral_const_mul]
  · intro d _
    refine Integrable.const_mul ?_ _
    exact hf.mul_continuousOn
      (Complex.continuous_ofReal.comp ((test_cont S d).comp continuous_fst)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem cell_expand_pairing (hexp : CellBasisExpansionStatement) {K : CellBox} {B : CellBases} (hK : IsCellBox K)
    (hB : IsCellBases K B) {N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly N N h) {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) :
    ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, B.coef K F j l *
        (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B j l x)
      = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (h p) := by
  have hE := hexp K B hK hB N h hh
  have hc : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (h p) =
      ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B j l x) *
          ((K.lineWeight p.1 : ℂ) * F p * basisValue B j l p) := by
    intro p
    rw [hE p, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, conj_basisValue]
    ring
  have hint : ∀ j l, Integrable (fun p => (K.lineWeight p.1 : ℂ) * F p * basisValue B j l p)
      (volume.restrict K.rect) :=
    fun j l => hF.mul_continuousOn (basisValue_cont B j l).continuousOn (rect_compact K)
  simp_rw [hc]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => (hint j l).const_mul _))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finsetSum _ (fun l _ => (hint j l).const_mul _)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [integral_const_mul, mul_comm]
  rfl

end Breakdown.CertCell.CellCalculus.RowLow.Internal

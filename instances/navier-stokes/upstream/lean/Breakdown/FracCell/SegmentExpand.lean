import Breakdown.FracCell.StrainFaceDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

theorem faceSegment_test_continuous (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

private theorem span_test (S : FaceSegment) (hlead : ∀ d, S.testCoef d d ≠ 0) :
    ∀ q : ℕ, ∀ p : Polynomial ℝ, p.natDegree ≤ q →
      ∃ c : ℕ → ℝ, ∀ u, p.eval u = ∑ d ∈ Finset.range (q + 1), c d * S.test d u := by
  intro q
  induction q with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0 / S.testCoef 0 0, fun u => ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]
    simp [FaceSegment.test, hlead 0]
  | succ q ih =>
    intro p hp
    set a : ℝ := p.coeff (q + 1) / S.testCoef (q + 1) (q + 1) with ha
    set P : Polynomial ℝ := ∑ i ∈ Finset.range (q + 1 + 1), Polynomial.C (S.testCoef (q + 1) i) * Polynomial.X ^ i
      with hP
    have hPe : ∀ u, P.eval u = S.test (q + 1) u := by
      intro u
      simp [hP, FaceSegment.test, Polynomial.eval_finsetSum]
    have hPc : ∀ N, P.coeff N = if N < q + 1 + 1 then S.testCoef (q + 1) N else 0 := by
      intro N
      simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [Finset.mem_range]
    have hdeg : (p - Polynomial.C a * P).natDegree ≤ q := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hPc]
      rcases Nat.lt_or_ge (q + 1) N with h | h
      · have h1 : p.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [h1, if_neg (by omega)]
        ring
      · have hN' : N = q + 1 := by omega
        subst hN'
        rw [if_pos (by omega), ha]
        field_simp [hlead (q + 1)]
        ring
    obtain ⟨c, hc⟩ := ih _ hdeg
    refine ⟨fun d => if d = q + 1 then a else c d, fun u => ?_⟩
    have h1 := hc u
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hPe] at h1
    rw [Finset.sum_range_succ]
    dsimp only
    rw [if_pos rfl]
    have h2 : ∑ d ∈ Finset.range (q + 1), (if d = q + 1 then a else c d) * S.test d u =
        ∑ d ∈ Finset.range (q + 1), c d * S.test d u := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [if_neg (by simp [Finset.mem_range] at hd; omega)]
    rw [h2, ← h1]
    ring

theorem segment_expand (S : FaceSegment) (q : ℕ) (hlead : ∀ d, S.testCoef d d ≠ 0)
    (horth : ∀ d d', d ≤ q → d' ≤ q →
      ∫ u in Set.Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    (f : ℝ → ℝ) (hf : IsPolyFn q f) (u : ℝ) :
    ∑ d ∈ Finset.range (q + 1), (∫ w in Set.Icc S.lo S.hi, f w * S.test d w) * S.test d u = f u := by
  obtain ⟨p, hp, hfp⟩ := hf
  obtain ⟨c, hc⟩ := span_test S hlead q p hp
  have hfe : ∀ w, f w = ∑ d ∈ Finset.range (q + 1), c d * S.test d w := fun w => (hfp w).trans (hc w)
  have hcoef : ∀ d' ∈ Finset.range (q + 1), (∫ w in Set.Icc S.lo S.hi, f w * S.test d' w) = c d' := by
    intro d' hd'
    have hd'q : d' ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd')
    have hrw : (fun w => f w * S.test d' w) = fun w => ∑ d ∈ Finset.range (q + 1), c d * (S.test d w * S.test d' w) := by
      funext w
      rw [hfe w, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    rw [hrw, integral_finsetSum]
    · rw [Finset.sum_eq_single d']
      · rw [integral_const_mul, horth d' d' hd'q hd'q, if_pos rfl, mul_one]
      · intro b hb hbd
        rw [integral_const_mul, horth b d' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hd'q, if_neg hbd, mul_zero]
      · intro h
        exact absurd hd' h
    · intro d _
      exact ((((faceSegment_test_continuous S d).mul (faceSegment_test_continuous S d')).const_smul (c d)).integrableOn_Icc).congr_fun
        (fun w _ => by simp [smul_eq_mul]) measurableSet_Icc
  rw [hfe u]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hcoef d hd]

private theorem ico_union_ae {ι : Type*} (T : Finset ι) (lo hi : ι → ℝ) (z₁ z₂ : ℝ)
    (hsub : ∀ s ∈ T, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u → u ≤ z₂ → ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s) :
    (⋃ s ∈ T, Set.Ico (lo s) (hi s)) =ᵐ[volume] Set.Icc z₁ z₂ := by
  rw [ae_eq_set]
  constructor
  · have : (⋃ s ∈ T, Set.Ico (lo s) (hi s)) \ Set.Icc z₁ z₂ = ∅ := by
      ext u
      simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_Ico, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨s, hs, h1, h2⟩, h3⟩
      obtain ⟨h4, h5⟩ := hsub s hs
      exact h3 ⟨le_trans h4 h1, le_trans h2.le h5⟩
    rw [this, measure_empty]
  · apply measure_mono_null (t := (insert z₂ (T.image hi) : Finset ℝ))
    · intro u hu
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_iUnion, Set.mem_Ico, not_exists, not_and] at hu
      obtain ⟨⟨h1, h2⟩, h3⟩ := hu
      obtain ⟨s, hs, h4, h5⟩ := hcov u h1 h2
      have h6 : u = hi s := by
        by_contra h7
        exact h3 s hs h4 (lt_of_le_of_ne h5 h7)
      simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe]
      exact Or.inr ⟨s, hs, h6.symm⟩
    · exact (Finset.finite_toSet _).measure_zero _

theorem strip_union_right {ι : Type*} (A : Set ℝ) (hA : MeasurableSet A) (T : Finset ι) (lo hi : ι → ℝ)
    (z₁ z₂ : ℝ) (hsub : ∀ s ∈ T, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u → u ≤ z₂ → ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s)
    (hdisj : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (A ×ˢ Set.Icc z₁ z₂)) :
    ∑ s ∈ T, ∫ p in A ×ˢ Set.Icc (lo s) (hi s), g p = ∫ p in A ×ˢ Set.Icc z₁ z₂, g p := by
  have h1 : ∀ s ∈ T, ∫ p in A ×ˢ Set.Icc (lo s) (hi s), g p = ∫ p in A ×ˢ Set.Ico (lo s) (hi s), g p := by
    intro s _
    exact setIntegral_congr_set (Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ A) Ico_ae_eq_Icc).symm
  rw [Finset.sum_congr rfl h1, ← integral_biUnion_finset T]
  · apply setIntegral_congr_set
    have he : (⋃ s ∈ T, A ×ˢ Set.Ico (lo s) (hi s)) = A ×ˢ (⋃ s ∈ T, Set.Ico (lo s) (hi s)) := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_prod, exists_and_left, exists_prop]
    rw [he]
    exact Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ A) (ico_union_ae T lo hi z₁ z₂ hsub hcov)
  · intro s _
    exact hA.prod measurableSet_Ico
  · intro s hs s' hs' hne
    simp only [Function.onFun]
    rw [Set.disjoint_prod]
    right
    rw [Set.Ico_disjoint_Ico]
    rcases hdisj s hs s' hs' hne with h | h
    · exact le_trans (min_le_left _ _) (le_trans h (le_max_right _ _))
    · exact le_trans (min_le_right _ _) (le_trans h (le_max_left _ _))
  · intro s hs
    obtain ⟨h2, h3⟩ := hsub s hs
    exact hg.mono_set (Set.prod_mono le_rfl (fun u hu => ⟨le_trans h2 hu.1, le_trans hu.2.le h3⟩))

theorem strip_union_left {ι : Type*} (A : Set ℝ) (hA : MeasurableSet A) (T : Finset ι) (lo hi : ι → ℝ)
    (z₁ z₂ : ℝ) (hsub : ∀ s ∈ T, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u → u ≤ z₂ → ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s)
    (hdisj : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (Set.Icc z₁ z₂ ×ˢ A)) :
    ∑ s ∈ T, ∫ p in Set.Icc (lo s) (hi s) ×ˢ A, g p = ∫ p in Set.Icc z₁ z₂ ×ˢ A, g p := by
  have h1 : ∀ s ∈ T, ∫ p in Set.Icc (lo s) (hi s) ×ˢ A, g p = ∫ p in Set.Ico (lo s) (hi s) ×ˢ A, g p := by
    intro s _
    exact setIntegral_congr_set (Measure.set_prod_ae_eq Ico_ae_eq_Icc (Filter.EventuallyEq.refl _ A)).symm
  rw [Finset.sum_congr rfl h1, ← integral_biUnion_finset T]
  · apply setIntegral_congr_set
    have he : (⋃ s ∈ T, Set.Ico (lo s) (hi s) ×ˢ A) = (⋃ s ∈ T, Set.Ico (lo s) (hi s)) ×ˢ A := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_prod, exists_prop]
      constructor
      · rintro ⟨s, hs, h2, h3⟩
        exact ⟨⟨s, hs, h2⟩, h3⟩
      · rintro ⟨⟨s, hs, h2⟩, h3⟩
        exact ⟨s, hs, h2, h3⟩
    rw [he]
    exact Measure.set_prod_ae_eq (ico_union_ae T lo hi z₁ z₂ hsub hcov) (Filter.EventuallyEq.refl _ A)
  · intro s _
    exact measurableSet_Ico.prod hA
  · intro s hs s' hs' hne
    simp only [Function.onFun]
    rw [Set.disjoint_prod]
    left
    rw [Set.Ico_disjoint_Ico]
    rcases hdisj s hs s' hs' hne with h | h
    · exact le_trans (min_le_left _ _) (le_trans h (le_max_right _ _))
    · exact le_trans (min_le_right _ _) (le_trans h (le_max_left _ _))
  · intro s hs
    obtain ⟨h2, h3⟩ := hsub s hs
    exact hg.mono_set (Set.prod_mono (fun u hu => ⟨le_trans h2 hu.1, le_trans hu.2.le h3⟩) le_rfl)

private theorem seg_inner_right (lo hi : ℝ) (A : Set ℝ) (hA : IsCompact A) (hAm : MeasurableSet A)
    (S : FaceSegment) (q : ℕ)
    (hlead : ∀ d, S.testCoef d d ≠ 0)
    (horth : ∀ d d', d ≤ q → d' ≤ q →
      ∫ u in Set.Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : IsPolyFn q t) (G : ℝ × ℝ → ℂ) (hG : IntegrableOn G (A ×ˢ Set.Icc lo hi)) :
    ∑ d ∈ Finset.range (q + 1), (((∫ u in Set.Icc S.lo S.hi, t u * S.test d u) : ℝ) : ℂ) *
        ∫ p in A ×ˢ Set.Icc lo hi, G p * ((S.test d p.2 : ℝ) : ℂ) =
      ∫ p in A ×ˢ Set.Icc lo hi, G p * ((t p.2 : ℝ) : ℂ) := by
  have hK : IsCompact (A ×ˢ Set.Icc lo hi) := hA.prod isCompact_Icc
  have hint : ∀ d, IntegrableOn (fun p : ℝ × ℝ => G p * ((S.test d p.2 : ℝ) : ℂ)) (A ×ˢ Set.Icc lo hi) := by
    intro d
    refine hG.mul_continuousOn ?_ hK
    exact (Complex.continuous_ofReal.comp ((faceSegment_test_continuous S d).comp continuous_snd)).continuousOn
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (hAm.prod measurableSet_Icc)
    intro p _
    have he := segment_expand S q hlead horth t ht p.2
    simp only
    rw [← he]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · intro d _
    exact (hint d).const_mul _

private theorem seg_inner_left (lo hi : ℝ) (A : Set ℝ) (hA : IsCompact A) (hAm : MeasurableSet A)
    (S : FaceSegment) (q : ℕ)
    (hlead : ∀ d, S.testCoef d d ≠ 0)
    (horth : ∀ d d', d ≤ q → d' ≤ q →
      ∫ u in Set.Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    (wt : ℝ → ℝ)
    (t : ℝ → ℝ) (ht : IsPolyFn q t) (G : ℝ × ℝ → ℂ)
    (hG : IntegrableOn (fun p : ℝ × ℝ => G p * ((wt p.1 : ℝ) : ℂ)) (Set.Icc lo hi ×ˢ A)) :
    ∑ d ∈ Finset.range (q + 1), (((∫ u in Set.Icc S.lo S.hi, t u * S.test d u) : ℝ) : ℂ) *
        ∫ p in Set.Icc lo hi ×ˢ A, G p * ((wt p.1 * S.test d p.1 : ℝ) : ℂ) =
      ∫ p in Set.Icc lo hi ×ˢ A, G p * ((wt p.1 * t p.1 : ℝ) : ℂ) := by
  have hK : IsCompact (Set.Icc lo hi ×ˢ A) := isCompact_Icc.prod hA
  have hint : ∀ d, IntegrableOn (fun p : ℝ × ℝ => G p * ((wt p.1 * S.test d p.1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ A) := by
    intro d
    refine (hG.mul_continuousOn (Complex.continuous_ofReal.comp ((faceSegment_test_continuous S d).comp
      continuous_fst)).continuousOn hK).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod hAm)
    simp only [Function.comp]
    push_cast
    ring
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (measurableSet_Icc.prod hAm)
    intro p _
    have he := segment_expand S q hlead horth t ht p.1
    simp only
    rw [← he]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · intro d _
    exact (hint d).const_mul _

theorem radial_segments_sum {ι : Type*} (T : Finset ι) (seg : ι → FaceSegment) (c o z₁ z₂ : ℝ) (q : ℕ)
    (hlead : ∀ s ∈ T, ∀ d, (seg s).testCoef d d ≠ 0)
    (horth : ∀ s ∈ T, ∀ d d', d ≤ q → d' ≤ q →
      ∫ u in Set.Icc (seg s).lo (seg s).hi, (seg s).test d u * (seg s).test d' u = if d = d' then 1 else 0)
    (hsub : ∀ s ∈ T, z₁ ≤ (seg s).lo ∧ (seg s).hi ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u → u ≤ z₂ → ∃ s ∈ T, (seg s).lo ≤ u ∧ u ≤ (seg s).hi)
    (hdisj : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → (seg s).hi ≤ (seg s').lo ∨ (seg s').hi ≤ (seg s).lo)
    (F dF : ℝ × ℝ → ℂ)
    (hG : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc z₁ z₂))
    (t : ℝ → ℝ) (ht : IsPolyFn q t) :
    ∑ s ∈ T, ∑ d ∈ Finset.range (q + 1),
        (((∫ u in Set.Icc (seg s).lo (seg s).hi, t u * (seg s).test d u) : ℝ) : ℂ) *
          radialStripMoment c o (seg s).lo (seg s).hi F dF ((seg s).test d) =
      radialStripMoment c o z₁ z₂ F dF t := by
  unfold radialStripMoment
  set G : ℝ × ℝ → ℂ := fun p => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p with hGdef
  have hinner : ∀ s ∈ T, ∑ d ∈ Finset.range (q + 1),
      (((∫ u in Set.Icc (seg s).lo (seg s).hi, t u * (seg s).test d u) : ℝ) : ℂ) *
        (edgeSign c o * ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc (seg s).lo (seg s).hi,
          G p * (((seg s).test d p.2 : ℝ) : ℂ)) =
      edgeSign c o * ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc (seg s).lo (seg s).hi, G p * ((t p.2 : ℝ) : ℂ) := by
    intro s hs
    rw [← seg_inner_right (seg s).lo (seg s).hi _ isCompact_Icc measurableSet_Icc (seg s) q (hlead s hs)
      (horth s hs) t ht G (hG.mono_set (Set.prod_mono le_rfl
        (fun u hu => ⟨le_trans (hsub s hs).1 hu.1, le_trans hu.2 (hsub s hs).2⟩))), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have htc : Continuous t := by
    obtain ⟨P, _, hP⟩ := ht
    rw [show t = fun u => P.eval u from funext hP]
    exact P.continuous
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  congr 1
  exact strip_union_right _ measurableSet_Icc T (fun s => (seg s).lo) (fun s => (seg s).hi) z₁ z₂ hsub hcov hdisj
    _ (hG.mul_continuousOn (Complex.continuous_ofReal.comp (htc.comp continuous_snd)).continuousOn
      (isCompact_Icc.prod isCompact_Icc))

theorem height_segments_sum {ι : Type*} (T : Finset ι) (seg : ι → FaceSegment) (c o z₁ z₂ : ℝ) (q : ℕ)
    (hlead : ∀ s ∈ T, ∀ d, (seg s).testCoef d d ≠ 0)
    (horth : ∀ s ∈ T, ∀ d d', d ≤ q → d' ≤ q →
      ∫ u in Set.Icc (seg s).lo (seg s).hi, (seg s).test d u * (seg s).test d' u = if d = d' then 1 else 0)
    (hsub : ∀ s ∈ T, z₁ ≤ (seg s).lo ∧ (seg s).hi ≤ z₂)
    (hcov : ∀ u, z₁ ≤ u → u ≤ z₂ → ∃ s ∈ T, (seg s).lo ≤ u ∧ u ≤ (seg s).hi)
    (hdisj : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → (seg s).hi ≤ (seg s').lo ∨ (seg s').hi ≤ (seg s).lo)
    (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ)
    (hG : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((wt p.1 : ℝ) : ℂ)) (Set.Icc z₁ z₂ ×ˢ Set.Icc (min c o) (max c o)))
    (t : ℝ → ℝ) (ht : IsPolyFn q t) :
    ∑ s ∈ T, ∑ d ∈ Finset.range (q + 1),
        (((∫ u in Set.Icc (seg s).lo (seg s).hi, t u * (seg s).test d u) : ℝ) : ℂ) *
          heightStripMoment c o (seg s).lo (seg s).hi wt F dF ((seg s).test d) =
      heightStripMoment c o z₁ z₂ wt F dF t := by
  unfold heightStripMoment
  set G : ℝ × ℝ → ℂ := fun p => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p with hGdef
  have hinner : ∀ s ∈ T, ∑ d ∈ Finset.range (q + 1),
      (((∫ u in Set.Icc (seg s).lo (seg s).hi, t u * (seg s).test d u) : ℝ) : ℂ) *
        (edgeSign c o * ∫ p in Set.Icc (seg s).lo (seg s).hi ×ˢ Set.Icc (min c o) (max c o),
          G p * ((wt p.1 * (seg s).test d p.1 : ℝ) : ℂ)) =
      edgeSign c o * ∫ p in Set.Icc (seg s).lo (seg s).hi ×ˢ Set.Icc (min c o) (max c o),
        G p * ((wt p.1 * t p.1 : ℝ) : ℂ) := by
    intro s hs
    rw [← seg_inner_left (seg s).lo (seg s).hi _ isCompact_Icc measurableSet_Icc (seg s) q (hlead s hs)
      (horth s hs) wt t ht G (hG.mono_set (Set.prod_mono
        (fun u hu => ⟨le_trans (hsub s hs).1 hu.1, le_trans hu.2 (hsub s hs).2⟩) le_rfl)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have htc : Continuous t := by
    obtain ⟨P, _, hP⟩ := ht
    rw [show t = fun u => P.eval u from funext hP]
    exact P.continuous
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  congr 1
  exact strip_union_left _ measurableSet_Icc T (fun s => (seg s).lo) (fun s => (seg s).hi) z₁ z₂ hsub hcov hdisj
    _ ((hG.mul_continuousOn (Complex.continuous_ofReal.comp (htc.comp continuous_fst)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)).congr_fun (fun p _ => by simp only [Function.comp, hGdef]; push_cast; ring)
      (measurableSet_Icc.prod measurableSet_Icc))

end CellFormula

end CellCert

end Breakdown

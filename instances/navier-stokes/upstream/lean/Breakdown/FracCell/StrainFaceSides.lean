import Breakdown.FracCell.SegmentExpand

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

private theorem row_sum {L : CellLayout} {k : ℕ} (x : FieldTuple k) (T : Finset (Fin L.segCount)) (m : ℕ)
    (w : Fin L.segCount → ℕ → ℂ) (D : Fin L.segCount → Fin m → L.Datum) :
    ∑ d, (∑ s ∈ T, ∑ d' : Fin m, w s d' • L.unitAt (D s d')) d * L.trueData x d =
      ∑ s ∈ T, ∑ d' ∈ Finset.range m, (if h : d' < m then w s d' * L.trueData x (D s ⟨d', h⟩) else 0) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro d' _
  rw [dif_pos d'.isLt]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single (D s d')]
  · rw [CellLayout.unitAt, Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [CellLayout.unitAt, Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sideGradientEval_of (hI : SideStripIntegrableStatement) : SideGradientEvalStatement := by
  intro k N c K S B L hL x hx n e a t he ht
  have hb := hL.box_eq
  subst hb
  unfold CellLayout.sideGradientRow
  rw [row_sum x (L.sideSegments e) (L.degSide + 1) (fun s d => ((L.segmentTestPair s t d : ℝ) : ℂ))
    (fun s d => CellDatum.sideGradient n s a d)]
  have hlead : ∀ s ∈ L.sideSegments e, ∀ d, (L.segment s).testCoef d d ≠ 0 :=
    fun s _ d => (hL.segment_valid s).test_leading d
  have horth : ∀ s ∈ L.sideSegments e, ∀ d d', d ≤ L.degSide → d' ≤ L.degSide →
      ∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, (L.segment s).test d u * (L.segment s).test d' u =
        if d = d' then 1 else 0 :=
    fun s _ d d' h1 h2 => hL.segment_orthonormal s d d' (by omega) (by omega)
  have hdisj := hL.sideSegments_disjoint e
  have hcov := hL.sideSegments_cover e he
  obtain ⟨hIr, hIh⟩ := hI c L.box S B L hL x hx n e a he
  by_cases he2 : e.val < 2
  · have hspec : ∀ s ∈ L.sideSegments e, (L.segment s).radial = true ∧ (L.segment s).level = L.sideLevel e ∧
        (L.segment s).other = L.sideOther e ∧ L.box.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ L.box.z₂ := by
      intro s hs
      obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = true := h1.mpr he2
      have hlev : (L.segment s).level = L.sideLevel e := by
        rw [h2]
        unfold CellLayout.sideLevel
        rfl
      refine ⟨hr, hlev, ?_, ?_⟩
      · rw [((hL.segment_other_in_box s).1 hr), hlev]
        unfold CellLayout.sideOther
        rw [if_pos he2]
      · rcases hL.segment_on_side s with h3 | h3
        · exact ⟨h3.2.2.1, h3.2.2.2.1⟩
        · exact absurd hr h3.1
    have hterm : ∀ s ∈ L.sideSegments e, ∑ d' ∈ Finset.range (L.degSide + 1),
        (if h : d' < L.degSide + 1 then ((L.segmentTestPair s t d' : ℝ) : ℂ) *
          L.trueData x (CellDatum.sideGradient n s a ⟨d', h⟩) else 0) =
        ∑ d' ∈ Finset.range (L.degSide + 1),
          (((∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, t u * (L.segment s).test d' u) : ℝ) : ℂ) *
            radialStripMoment (L.sideLevel e) (L.sideOther e) (L.segment s).lo (L.segment s).hi
              (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) ((L.segment s).test d') := by
      intro s hs
      obtain ⟨hr, hlev, hoth, _, _⟩ := hspec s hs
      apply Finset.sum_congr rfl
      intro d' hd'
      rw [dif_pos (Finset.mem_range.mp hd')]
      show _ * (if (L.segment s).radial then _ else _) = _
      rw [if_pos hr]
      simp only [FaceSegment.moment, hr, if_true, hlev, hoth]
      rfl
    rw [Finset.sum_congr rfl hterm]
    rw [radial_segments_sum (L.sideSegments e) L.segment (L.sideLevel e) (L.sideOther e) L.box.z₁ L.box.z₂
      L.degSide hlead horth (fun s hs => ⟨(hspec s hs).2.2.2.1, (hspec s hs).2.2.2.2⟩)
      (fun u h1 h2 => hcov u (by rw [if_pos he2]; exact ⟨h1, h2⟩)) hdisj _ _ (hIr he2).2 t ht]
    unfold CellLayout.sideGradientValue radialFaceMoment CellLayout.sideRadialIndex CellLayout.sideLevel
      CellLayout.sideOther
    rw [if_pos he2, if_pos he2]
    by_cases h0 : e.val = 0
    · rw [if_pos h0, if_pos h0, if_neg (by decide)]
      congr 1
      rw [CellLayout.sideLevel, if_pos h0]
      ring
    · have h1 : e.val = 1 := by omega
      rw [if_neg h0, if_neg h0, if_pos h1, if_pos rfl]
      congr 1
      rw [CellLayout.sideLevel, if_neg h0, if_pos h1]
      ring
  · have he2' : 2 ≤ e.val := by omega
    have hspec : ∀ s ∈ L.sideSegments e, (L.segment s).radial = false ∧ (L.segment s).level = L.sideLevel e ∧
        (L.segment s).other = L.sideOther e ∧ L.box.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ L.box.r₂ := by
      intro s hs
      obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = false := by
        by_contra h
        exact he2 (h1.mp (by simpa using h))
      have hlev : (L.segment s).level = L.sideLevel e := by
        rw [h2]
        unfold CellLayout.sideLevel
        rfl
      refine ⟨hr, hlev, ?_, ?_⟩
      · rw [((hL.segment_other_in_box s).2 (by simp [hr])), hlev]
        unfold CellLayout.sideOther
        rw [if_neg he2]
      · rcases hL.segment_on_side s with h3 | h3
        · exact absurd h3.1 (by simp [hr])
        · exact ⟨h3.2.2.1, h3.2.2.2⟩
    have hterm : ∀ s ∈ L.sideSegments e, ∑ d' ∈ Finset.range (L.degSide + 1),
        (if h : d' < L.degSide + 1 then ((L.segmentTestPair s t d' : ℝ) : ℂ) *
          L.trueData x (CellDatum.sideGradient n s a ⟨d', h⟩) else 0) =
        ∑ d' ∈ Finset.range (L.degSide + 1),
          (((∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, t u * (L.segment s).test d' u) : ℝ) : ℂ) *
            heightStripMoment (L.sideLevel e) (L.sideOther e) (L.segment s).lo (L.segment s).hi (fun r => r)
              (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2) ((L.segment s).test d') := by
      intro s hs
      obtain ⟨hr, hlev, hoth, _, _⟩ := hspec s hs
      apply Finset.sum_congr rfl
      intro d' hd'
      rw [dif_pos (Finset.mem_range.mp hd')]
      show _ * (if (L.segment s).radial then _ else _) = _
      rw [hr, if_neg (by simp)]
      simp only [FaceSegment.moment, hr, hlev, hoth]
      rfl
    rw [Finset.sum_congr rfl hterm]
    rw [height_segments_sum (L.sideSegments e) L.segment (L.sideLevel e) (L.sideOther e) L.box.r₁ L.box.r₂
      L.degSide hlead horth (fun s hs => ⟨(hspec s hs).2.2.2.1, (hspec s hs).2.2.2.2⟩)
      (fun u h1 h2 => hcov u (by rw [if_neg he2]; exact ⟨h1, h2⟩)) hdisj (fun r => r) _ _ (hIh he2').2 t ht]
    unfold CellLayout.sideGradientValue heightFaceMoment CellLayout.sideHeightIndex CellLayout.sideLevel
      CellLayout.sideOther
    rw [if_neg he2, if_neg he2]
    have h0 : e.val ≠ 0 := by omega
    have h1 : e.val ≠ 1 := by omega
    rw [if_neg h0, if_neg h1]
    by_cases h2 : e.val = 2
    · rw [if_pos h2, if_pos h2, if_neg (by decide)]
      congr 1
      rw [CellLayout.sideLevel, if_neg h0, if_neg h1, if_pos h2]
      ring
    · rw [if_neg h2, if_neg h2, if_pos rfl]
      congr 1
      rw [CellLayout.sideLevel, if_neg h0, if_neg h1, if_neg h2]
      ring

theorem sideVelocityEval_of (hI : SideStripIntegrableStatement) : SideVelocityEvalStatement := by
  intro k N c K S B L hL x hx n e a t he ht
  have hb := hL.box_eq
  subst hb
  unfold CellLayout.sideVelocityRow
  rw [row_sum x (L.sideSegments e) (L.degSide + 2) (fun s d => ((L.segmentTestPair s t d : ℝ) : ℂ))
    (fun s d => CellDatum.sideVelocity n s a d)]
  have hlead : ∀ s ∈ L.sideSegments e, ∀ d, (L.segment s).testCoef d d ≠ 0 :=
    fun s _ d => (hL.segment_valid s).test_leading d
  have horth : ∀ s ∈ L.sideSegments e, ∀ d d', d ≤ L.degSide + 1 → d' ≤ L.degSide + 1 →
      ∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, (L.segment s).test d u * (L.segment s).test d' u =
        if d = d' then 1 else 0 :=
    fun s _ d d' h1 h2 => hL.segment_orthonormal s d d' (by omega) (by omega)
  have hdisj := hL.sideSegments_disjoint e
  have hcov := hL.sideSegments_cover e he
  obtain ⟨hIr, hIh⟩ := hI c L.box S B L hL x hx n e a he
  by_cases he2 : e.val < 2
  · have hspec : ∀ s ∈ L.sideSegments e, (L.segment s).radial = true ∧ (L.segment s).level = L.sideLevel e ∧
        (L.segment s).other = L.sideOther e ∧ L.box.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ L.box.z₂ := by
      intro s hs
      obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = true := h1.mpr he2
      have hlev : (L.segment s).level = L.sideLevel e := by
        rw [h2]
        unfold CellLayout.sideLevel
        rfl
      refine ⟨hr, hlev, ?_, ?_⟩
      · rw [((hL.segment_other_in_box s).1 hr), hlev]
        unfold CellLayout.sideOther
        rw [if_pos he2]
      · rcases hL.segment_on_side s with h3 | h3
        · exact ⟨h3.2.2.1, h3.2.2.2.1⟩
        · exact absurd hr h3.1
    have hterm : ∀ s ∈ L.sideSegments e, ∑ d' ∈ Finset.range (L.degSide + 1 + 1),
        (if h : d' < L.degSide + 2 then ((L.segmentTestPair s t d' : ℝ) : ℂ) *
          L.trueData x (CellDatum.sideVelocity n s a ⟨d', h⟩) else 0) =
        ∑ d' ∈ Finset.range (L.degSide + 1 + 1),
          (((∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, t u * (L.segment s).test d' u) : ℝ) : ℂ) *
            radialStripMoment (L.sideLevel e) (L.sideOther e) (L.segment s).lo (L.segment s).hi
              (L.velMode n x a) (L.gradModeOf n x a 0) ((L.segment s).test d') := by
      intro s hs
      obtain ⟨hr, hlev, hoth, _, _⟩ := hspec s hs
      apply Finset.sum_congr rfl
      intro d' hd'
      rw [dif_pos (Finset.mem_range.mp hd')]
      show _ * (if (L.segment s).radial then _ else _) = _
      rw [if_pos hr]
      simp only [FaceSegment.moment, hr, if_true, hlev, hoth]
      rfl
    rw [Finset.sum_congr rfl hterm]
    rw [radial_segments_sum (L.sideSegments e) L.segment (L.sideLevel e) (L.sideOther e) L.box.z₁ L.box.z₂
      (L.degSide + 1) hlead horth (fun s hs => ⟨(hspec s hs).2.2.2.1, (hspec s hs).2.2.2.2⟩)
      (fun u h1 h2 => hcov u (by rw [if_pos he2]; exact ⟨h1, h2⟩)) hdisj _ _ (hIr he2).1 t ht]
    unfold CellLayout.sideVelocityValue radialFaceMoment CellLayout.sideRadialIndex CellLayout.sideLevel
      CellLayout.sideOther
    rw [if_pos he2, if_pos he2]
    by_cases h0 : e.val = 0
    · rw [if_pos h0, if_pos h0, if_neg (by decide)]
      congr 1
      rw [CellLayout.sideLevel, if_pos h0]
      ring
    · have h1 : e.val = 1 := by omega
      rw [if_neg h0, if_neg h0, if_pos h1, if_pos rfl]
      congr 1
      rw [CellLayout.sideLevel, if_neg h0, if_pos h1]
      ring
  · have he2' : 2 ≤ e.val := by omega
    have hspec : ∀ s ∈ L.sideSegments e, (L.segment s).radial = false ∧ (L.segment s).level = L.sideLevel e ∧
        (L.segment s).other = L.sideOther e ∧ L.box.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ L.box.r₂ := by
      intro s hs
      obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = false := by
        by_contra h
        exact he2 (h1.mp (by simpa using h))
      have hlev : (L.segment s).level = L.sideLevel e := by
        rw [h2]
        unfold CellLayout.sideLevel
        rfl
      refine ⟨hr, hlev, ?_, ?_⟩
      · rw [((hL.segment_other_in_box s).2 (by simp [hr])), hlev]
        unfold CellLayout.sideOther
        rw [if_neg he2]
      · rcases hL.segment_on_side s with h3 | h3
        · exact absurd h3.1 (by simp [hr])
        · exact ⟨h3.2.2.1, h3.2.2.2⟩
    have hterm : ∀ s ∈ L.sideSegments e, ∑ d' ∈ Finset.range (L.degSide + 1 + 1),
        (if h : d' < L.degSide + 2 then ((L.segmentTestPair s t d' : ℝ) : ℂ) *
          L.trueData x (CellDatum.sideVelocity n s a ⟨d', h⟩) else 0) =
        ∑ d' ∈ Finset.range (L.degSide + 1 + 1),
          (((∫ u in Set.Icc (L.segment s).lo (L.segment s).hi, t u * (L.segment s).test d' u) : ℝ) : ℂ) *
            heightStripMoment (L.sideLevel e) (L.sideOther e) (L.segment s).lo (L.segment s).hi (fun _ => 1)
              (L.velMode n x a) (L.gradModeOf n x a 2) ((L.segment s).test d') := by
      intro s hs
      obtain ⟨hr, hlev, hoth, _, _⟩ := hspec s hs
      apply Finset.sum_congr rfl
      intro d' hd'
      rw [dif_pos (Finset.mem_range.mp hd')]
      show _ * (if (L.segment s).radial then _ else _) = _
      rw [hr, if_neg (by simp)]
      simp only [FaceSegment.moment, hr, hlev, hoth, Bool.false_eq_true, if_false]
      rfl
    rw [Finset.sum_congr rfl hterm]
    rw [height_segments_sum (L.sideSegments e) L.segment (L.sideLevel e) (L.sideOther e) L.box.r₁ L.box.r₂
      (L.degSide + 1) hlead horth (fun s hs => ⟨(hspec s hs).2.2.2.1, (hspec s hs).2.2.2.2⟩)
      (fun u h1 h2 => hcov u (by rw [if_neg he2]; exact ⟨h1, h2⟩)) hdisj (fun _ => 1) _ _ (hIh he2').1 t ht]
    unfold CellLayout.sideVelocityValue CellLayout.sideHeightIndex CellLayout.sideLevel CellLayout.sideOther
    rw [if_neg he2, if_neg he2]
    have h0 : e.val ≠ 0 := by omega
    have h1 : e.val ≠ 1 := by omega
    rw [if_neg h0, if_neg h1]
    by_cases h2 : e.val = 2
    · rw [if_pos h2, if_pos h2, if_neg (by decide)]
      congr 1
      rw [CellLayout.sideLevel, if_neg h0, if_neg h1, if_pos h2]
      ring
    · rw [if_neg h2, if_neg h2, if_pos rfl]
      congr 1
      rw [CellLayout.sideLevel, if_neg h0, if_neg h1, if_neg h2]
      ring

end CellFormula

end CellCert

end Breakdown

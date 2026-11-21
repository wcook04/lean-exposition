import Breakdown.FracCell.FormulaDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open CellAnalysis

theorem FaceSegment.test_sum_monomial (S : FaceSegment) (D : ℕ) (cf : Fin (D + 1) → ℂ) (t : ℝ) :
    ∑ d : Fin (D + 1), cf d * ((S.test d t : ℝ) : ℂ) =
      ∑ i : Fin (D + 1), (∑ d : Fin (D + 1), if (i : ℕ) ≤ d then cf d * (S.testCoef d i : ℂ) else 0) *
        (t : ℂ) ^ (i : ℕ) := by
  have h1 : ∀ d : Fin (D + 1), ((S.test d t : ℝ) : ℂ) =
      ∑ i : Fin (D + 1), if (i : ℕ) ≤ d then (S.testCoef d i : ℂ) * (t : ℂ) ^ (i : ℕ) else 0 := by
    intro d
    have e1 : ((S.test d t : ℝ) : ℂ) = ∑ i ∈ Finset.range (d + 1), (S.testCoef d i : ℂ) * (t : ℂ) ^ i := by
      simp only [FaceSegment.test, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
    have e2 : ∑ i ∈ Finset.range (d + 1), (S.testCoef d i : ℂ) * (t : ℂ) ^ i =
        ∑ i ∈ Finset.range (D + 1), if i ≤ (d : ℕ) then (S.testCoef d i : ℂ) * (t : ℂ) ^ i else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have := d.is_lt
      omega
    rw [e1, e2]
    exact (Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ (d : ℕ) then (S.testCoef d i : ℂ) * (t : ℂ) ^ i else 0) (D + 1)).symm
  simp only [h1, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> ring

theorem rowFacePoly_of_segment_row {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {L : CellLayout} (hL : IsCellLayout c K S B L) (a : Fin N) (n : ℤ)
    (hseg : ∀ s i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1))
    (e : Fin 4) (he : ¬ (e.val = 0 ∧ K.r₁ = 0)) :
    ∃ Pl : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * (t : ℂ) ^ (d : ℕ)) ∧
      ∀ p ∈ K.rect, (e.val < 2 → p.1 = faceLevel L e → rowModeVec c a n p 0 = Pl p.2) ∧
        (2 ≤ e.val → p.2 = faceLevel L e → rowModeVec c a n p 2 = Pl p.1) := by
  have hK := hL.box_valid
  have hu : (if e.val < 2 then K.z₁ ≤ K.z₁ ∧ K.z₁ ≤ K.z₂ else K.r₁ ≤ K.z₁ ∧ K.z₁ ≤ K.r₂) ∨
      (if e.val < 2 then K.z₁ ≤ K.r₁ ∧ K.r₁ ≤ K.z₂ else K.r₁ ≤ K.r₁ ∧ K.r₁ ≤ K.r₂) := by
    by_cases he2 : e.val < 2
    · left
      rw [if_pos he2]
      exact ⟨le_rfl, hK.z_order.2.le⟩
    · right
      rw [if_neg he2]
      exact ⟨le_rfl, hK.r_order.2.le⟩
  have hcov : ∃ s ∈ L.sideSegments e, True := by
    rcases hu with hu | hu
    · obtain ⟨s, hs, -⟩ := hL.sideSegments_cover e (fun h0 hr => he ⟨h0, hr⟩) K.z₁ hu
      exact ⟨s, hs, trivial⟩
    · obtain ⟨s, hs, -⟩ := hL.sideSegments_cover e (fun h0 hr => he ⟨h0, hr⟩) K.r₁ hu
      exact ⟨s, hs, trivial⟩
  obtain ⟨s, hs, -⟩ := hcov
  obtain ⟨hrad, hlev⟩ := hL.sideSegments_spec e s hs
  have hlevel : (L.segment s).level = faceLevel L e := by
    rw [hlev, faceLevel, hL.box_eq]
  by_cases he2 : e.val < 2
  · have hr : (L.segment s).radial := hrad.2 he2
    obtain ⟨P, ⟨cf, hcf⟩, hP⟩ := hseg s 0
    refine ⟨P, ⟨fun i => ∑ d : Fin (L.degSide + 1),
        if (i : ℕ) ≤ d then cf d * ((L.segment s).testCoef d i : ℂ) else 0,
      fun t => by rw [hcf t, FaceSegment.test_sum_monomial]⟩, fun p hp =>
        ⟨fun _ hp1 => (hP p hp).1 hr (hp1.trans hlevel.symm), fun h => absurd h (by omega)⟩⟩
  · have hr : ¬ (L.segment s).radial := fun h => he2 (hrad.1 h)
    obtain ⟨P, ⟨cf, hcf⟩, hP⟩ := hseg s 2
    refine ⟨P, ⟨fun i => ∑ d : Fin (L.degSide + 1),
        if (i : ℕ) ≤ d then cf d * ((L.segment s).testCoef d i : ℂ) else 0,
      fun t => by rw [hcf t, FaceSegment.test_sum_monomial]⟩, fun p hp =>
        ⟨fun h => absurd h he2, fun _ hp2 => (hP p hp).2 hr (hp2.trans hlevel.symm)⟩⟩

theorem rowFacePoly_of_segments {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {R : CellRows N slots k} {L : CellLayout} (hL : IsCellLayout c K S B L)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1)) :
    ∀ a ∈ R.rowSet, ∀ (n : ℤ) (e : Fin 4), ¬ (e.val = 0 ∧ K.r₁ = 0) → ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * (t : ℂ) ^ (d : ℕ)) ∧
      ∀ p ∈ K.rect, (e.val < 2 → p.1 = faceLevel L e → rowModeVec c a n p 0 = Pl p.2) ∧
        (2 ≤ e.val → p.2 = faceLevel L e → rowModeVec c a n p 2 = Pl p.1) :=
  fun a ha n e he => rowFacePoly_of_segment_row hL a n (fun s i => hseg a ha s n i) e he

end CellFormula

end CellCert

end Breakdown

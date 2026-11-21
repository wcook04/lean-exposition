import Breakdown.FracCell.LayoutRowPressureBoundary

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.LayoutRowPressureModeIdentity

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly

private theorem test_cont (F : FaceSegment) (d : ℕ) : Continuous (F.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

private theorem coef_of_trace (F : FaceSegment) (m : ℕ)
    (horth : ∀ d d', d < m → d' < m →
      ∫ u in Set.Icc F.lo F.hi, F.test d u * F.test d' u = if d = d' then 1 else 0)
    (cf : Fin m → ℂ) (d : Fin m) :
    ∫ t in Set.Icc F.lo F.hi, (∑ d', cf d' * ((F.test d' t : ℝ) : ℂ)) * ((F.test d t : ℝ) : ℂ) = cf d := by
  have hI : ∀ d' : Fin m, IntegrableOn (fun t => cf d' * (((F.test d' t * F.test d t : ℝ)) : ℂ))
      (Set.Icc F.lo F.hi) volume := by
    intro d'
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((test_cont F d').mul (test_cont F d)))).continuousOn
  have hsplit : (fun t => (∑ d', cf d' * ((F.test d' t : ℝ) : ℂ)) * ((F.test d t : ℝ) : ℂ)) =
      fun t => ∑ d', cf d' * (((F.test d' t * F.test d t : ℝ)) : ℂ) := by
    funext t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    push_cast
    ring
  rw [hsplit, integral_finsetSum _ (fun d' _ => hI d')]
  have hterm : ∀ d' : Fin m, ∫ t in Set.Icc F.lo F.hi, cf d' * (((F.test d' t * F.test d t : ℝ)) : ℂ) =
      if d' = d then cf d else 0 := by
    intro d'
    rw [integral_const_mul, integral_complex_ofReal, horth d' d d'.isLt d.isLt]
    by_cases h : d' = d
    · subst h; simp
    · have h' : (d' : ℕ) ≠ d := fun e => h (Fin.ext e)
      simp [h, h']
  simp_rw [hterm]
  simp

theorem mode_identity {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hpres : ∀ a ∈ R.rowSet, ∀ s n, ∃ P : ℝ → ℂ, (∃ cf : Fin L.degSide → ℂ, ∀ t, P t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = P p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = P p.1))
    (n : ℤ) :
    ∫ p in K.rect, (p.1 : ℂ) * pairC (modeVec c.order n x.2.2.2.2 p.1 p.2) (rowModeVec c a n p) =
      ∑ s : Fin L.presCount, ∑ d : Fin L.degSide, presSideRowCoef c L a n s d *
        (L.presSegment s).moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d := by
  choose P hPcf hPtr using fun s => hpres a ha s n
  choose cf hcf using hPcf
  have htr : ∀ s, ∀ p ∈ K.rect,
      ((L.presSegment s).radial → p.1 = (L.presSegment s).level →
          rowModeVec c a n p 0 = ∑ d, cf s d * ((L.presSegment s).test d p.2 : ℂ)) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level →
          rowModeVec c a n p 2 = ∑ d, cf s d * ((L.presSegment s).test d p.1 : ℂ)) := by
    intro s p hp
    refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · rw [(hPtr s p hp).1 h1 h2, hcf s]
    · rw [(hPtr s p hp).2 h1 h2, hcf s]
  have hcoef : ∀ s (d : Fin L.degSide), presSideRowCoef c L a n s d =
      edgeSign (L.presSegment s).level (L.presSegment s).other *
        (if (L.presSegment s).radial then ((L.presSegment s).level : ℂ) else 1) * (starRingEnd ℂ) (cf s d) := by
    intro s d
    unfold presSideRowCoef
    rw [LayoutRowPressureBoundary.trace_coef hα1 hα2 hc hD hR hL ha n s (P s) (hPtr s) d]
    have hP : P s = fun t => ∑ d', cf s d' * (((L.presSegment s).test d' t : ℝ) : ℂ) := funext (hcf s)
    rw [hP, coef_of_trace (L.presSegment s) L.degSide (hL.presSegment_orthonormal s) (cf s) d]
  simp_rw [hcoef]
  exact LayoutRowPressureBoundary.boundary_pairing hα1 hα2 hc hD hR hL hx ha n cf htr

end Breakdown.FracInternal.LayoutRowPressureModeIdentity

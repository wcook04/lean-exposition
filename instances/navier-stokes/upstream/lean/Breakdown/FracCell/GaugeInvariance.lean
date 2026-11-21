import Breakdown.FracCell.GaugeInvarianceParts

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

private def presShiftValue (L : CellLayout) {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) (s : Fin L.presCount)
    (d : ℕ) : ℂ :=
  if (L.presSegment s).radial then
    (((if (L.presSegment s).level = L.box.r₁ then g.left x else g.right x) *
        ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (L.presSegment s).test d z : ℝ) : ℂ)
  else ((g.point x (L.presSegment s).hi *
          radialWeightIntegral ((L.presSegment s).test d) (L.presSegment s).hi
        - g.point x (L.presSegment s).lo *
          radialWeightIntegral ((L.presSegment s).test d) (L.presSegment s).lo : ℝ) : ℂ)

private theorem test_continuous (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test; fun_prop

private theorem coef_of_orth (S : FaceSegment) (q : ℕ)
    (horth : ∀ d d', d < q → d' < q →
      ∫ u in Set.Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    (cf : Fin q → ℂ) (dd : Fin q) :
    ∫ u in Set.Icc S.lo S.hi, (∑ d : Fin q, cf d * (S.test d u : ℂ)) * (S.test dd u : ℂ) = cf dd := by
  have hc := test_continuous S
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · have h1 : ∀ d : Fin q, ∫ u in Set.Icc S.lo S.hi, cf d * (S.test d u : ℂ) * (S.test dd u : ℂ) =
        cf d * (if d = dd then 1 else 0) := by
      intro d
      simp_rw [mul_assoc, ← Complex.ofReal_mul]
      rw [integral_const_mul, integral_complex_ofReal, horth d dd d.2 dd.2]
      by_cases h : d = dd
      · simp [h]
      · have h' : (d : ℕ) ≠ dd := fun e => h (Fin.ext e)
        simp [h, h']
    simp_rw [h1, mul_ite, mul_one, mul_zero]
    simp
  · intro d _
    exact (by fun_prop : Continuous fun u => cf d * (S.test d u : ℂ) * (S.test dd u : ℂ)).integrableOn_Icc

private theorem conj_poly (S : FaceSegment) (q : ℕ) (cf : Fin q → ℂ) (u : ℝ) :
    (starRingEnd ℂ) (∑ d : Fin q, cf d * (S.test d u : ℂ)) =
      ∑ d : Fin q, (starRingEnd ℂ) (cf d) * (S.test d u : ℂ) := by
  simp [map_sum, map_mul, Complex.conj_ofReal]

private theorem interval_poly (S : FaceSegment) (q : ℕ) (cf : Fin q → ℂ) (u v : ℝ) :
    ∫ z in u..v, ∑ d : Fin q, cf d * (S.test d z : ℂ) =
      ∑ d : Fin q, cf d * ((∫ z in u..v, S.test d z : ℝ) : ℂ) := by
  have hc := test_continuous S
  rw [intervalIntegral.integral_finsetSum]
  · congr 1; ext d
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  · intro d _
    exact (by fun_prop : Continuous fun z => cf d * (S.test d z : ℂ)).intervalIntegrable _ _

private theorem weighted_poly (S : FaceSegment) (q : ℕ) (cf : Fin q → ℂ) (v : ℝ) :
    ∫ ρ in (0 : ℝ)..v, (ρ : ℂ) * ∑ d : Fin q, cf d * (S.test d ρ : ℂ) =
      ∑ d : Fin q, cf d * ((radialWeightIntegral (S.test d) v : ℝ) : ℂ) := by
  have hc := test_continuous S
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · congr 1; ext d
    unfold radialWeightIntegral
    rw [intervalIntegral.integral_ofReal.symm, ← intervalIntegral.integral_const_mul]
    congr 1; ext ρ; push_cast; ring
  · intro d _
    exact (by fun_prop : Continuous fun ρ : ℝ => (ρ : ℂ) * (cf d * (S.test d ρ : ℂ))).intervalIntegrable _ _


private theorem tele_family {ι : Type} (T : Finset ι) (lo hi : ι → ℝ) (a b : ℝ) (F : ι → ℝ → ℂ) (F0 : ℝ → ℂ)
    (hF : ∀ i ∈ T, ∀ y, a ≤ y → y ≤ b → F i y = F0 y)
    (hlt : ∀ i ∈ T, lo i < hi i) (hin : ∀ i ∈ T, a ≤ lo i ∧ hi i ≤ b)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hcov : ∀ u, a ≤ u → u ≤ b → ∃ i ∈ T, lo i ≤ u ∧ u ≤ hi i) (hab : a < b) :
    ∑ i ∈ T, (F i (hi i) - F i (lo i)) = F0 b - F0 a := by
  rw [← tiling_telescope T lo hi a b F0 hlt hin hdis hcov hab]
  refine Finset.sum_congr rfl (fun i hi' => ?_)
  have h := hin i hi'
  have h2 := hlt i hi'
  rw [hF i hi' (hi i) (by linarith) h.2, hF i hi' (lo i) h.1 (by linarith)]

private theorem radial_side {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsPressureLayout c K S B L) (a : Fin N) (ρ0 : ℝ) (hρ : K.r₁ ≤ ρ0 ∧ ρ0 ≤ K.r₂)
    (T : Finset (Fin L.presCount)) (hT : ∀ s ∈ T, (L.presSegment s).radial ∧ (L.presSegment s).level = ρ0)
    (hcov : ∀ u, K.z₁ ≤ u → u ≤ K.z₂ → ∃ s ∈ T, (L.presSegment s).lo ≤ u ∧ u ≤ (L.presSegment s).hi)
    (Pl : Fin L.presCount → ℝ → ℂ) (hcont : ∀ s, Continuous (Pl s))
    (hPlv : ∀ s, ∀ p ∈ K.rect, (L.presSegment s).radial → p.1 = (L.presSegment s).level →
      rowModeVec c a 0 p 0 = Pl s p.2) :
    ∑ s ∈ T, ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (starRingEnd ℂ) (Pl s z) =
      ∫ z in K.z₁..K.z₂, (starRingEnd ℂ) (rowModeVec c a 0 (ρ0, z) 0) := by
  have hz := hL.layout.box_valid.z_order
  have hin : ∀ s ∈ T, K.z₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.z₂ := by
    intro s hs
    rcases hL.presSegment_on_side s with h | h
    · exact ⟨h.2.2.1, h.2.2.2.1⟩
    · exact absurd (hT s hs).1 h.1
  have hlt : ∀ s ∈ T, (L.presSegment s).lo < (L.presSegment s).hi :=
    fun s _ => (hL.layout.presSegment_valid s).lo_lt_hi
  have heq : ∀ s ∈ T, ∀ y, K.z₁ ≤ y → y ≤ K.z₂ →
      ∫ z in K.z₁..y, (starRingEnd ℂ) (Pl s z) = ∫ z in K.z₁..y, (starRingEnd ℂ) (rowModeVec c a 0 (ρ0, z) 0) := by
    intro s hs y hy1 hy2
    refine intervalIntegral.integral_congr (fun z hzm => ?_)
    rw [Set.uIcc_of_le hy1] at hzm
    have hp : (ρ0, z) ∈ K.rect := ⟨hρ, hzm.1, hzm.2.trans hy2⟩
    rw [hPlv s (ρ0, z) hp (hT s hs).1 (hT s hs).2.symm]
  have key := tele_family T (fun s => (L.presSegment s).lo) (fun s => (L.presSegment s).hi) K.z₁ K.z₂
    (fun s y => ∫ z in K.z₁..y, (starRingEnd ℂ) (Pl s z))
    (fun y => ∫ z in K.z₁..y, (starRingEnd ℂ) (rowModeVec c a 0 (ρ0, z) 0)) heq hlt hin
    (fun s hs s' hs' hne => hL.presSides_disjoint s s' hne (by rw [(hT s hs).1, (hT s' hs').1])
      (by rw [(hT s hs).2, (hT s' hs').2])) hcov hz.2
  simp only [intervalIntegral.integral_same, sub_zero] at key
  rw [← key]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [intervalIntegral.integral_interval_sub_left]
  · exact (Complex.continuous_conj.comp (hcont s)).intervalIntegrable _ _
  · exact (Complex.continuous_conj.comp (hcont s)).intervalIntegrable _ _

private theorem height_side {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsPressureLayout c K S B L) (ζ0 : ℝ)
    (T : Finset (Fin L.presCount)) (hT : ∀ s ∈ T, ¬ (L.presSegment s).radial ∧ (L.presSegment s).level = ζ0)
    (hcov : ∀ u, K.r₁ ≤ u → u ≤ K.r₂ → ∃ s ∈ T, (L.presSegment s).lo ≤ u ∧ u ≤ (L.presSegment s).hi)
    (F : Fin L.presCount → ℝ → ℂ) (F0 : ℝ → ℂ) (hF : ∀ s ∈ T, ∀ y, K.r₁ ≤ y → y ≤ K.r₂ → F s y = F0 y) :
    ∑ s ∈ T, (F s (L.presSegment s).hi - F s (L.presSegment s).lo) = F0 K.r₂ - F0 K.r₁ := by
  have hr := hL.layout.box_valid.r_order
  have hin : ∀ s ∈ T, K.r₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.r₂ := by
    intro s hs
    rcases hL.presSegment_on_side s with h | h
    · exact absurd h.1 (hT s hs).1
    · exact ⟨h.2.2.1, h.2.2.2⟩
  exact tele_family T (fun s => (L.presSegment s).lo) (fun s => (L.presSegment s).hi) K.r₁ K.r₂ F F0 hF
    (fun s _ => (hL.layout.presSegment_valid s).lo_lt_hi) hin
    (fun s hs s' hs' hne => hL.presSides_disjoint s s' hne
      (by simp only [Bool.not_eq_true] at hT; rw [(hT s hs).1, (hT s' hs').1])
      (by rw [(hT s hs).2, (hT s' hs').2])) hcov hr.2

private theorem segment_value {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N slots : ℕ} {c : FracCellData k N}
    (hc : IsFormData α c) {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {L : CellLayout}
    (hL : IsPressureLayout c K S B L) {a : Fin N} (ha : a ∈ R.rowSet) (g : GaugeShift k) (x : FieldTuple k)
    (s : Fin L.presCount) (Pl : ℝ → ℂ) (cf : Fin L.degSide → ℂ)
    (hcf : ∀ t, Pl t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (hPl : ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a 0 p 0 = Pl p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a 0 p 2 = Pl p.1)) :
    ∑ dd : Fin L.degSide, presSideRowCoef c L a 0 s dd * presShiftValue L g x s dd =
      edgeSign (L.presSegment s).level (L.presSegment s).other *
        (if (L.presSegment s).radial then
          ((L.presSegment s).level : ℂ) * ((((if (L.presSegment s).level = L.box.r₁ then g.left x else g.right x) : ℝ) : ℂ) *
            ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (starRingEnd ℂ) (Pl z))
        else (g.point x (L.presSegment s).hi : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).hi, (ρ : ℂ) * (starRingEnd ℂ) (Pl ρ))
          - (g.point x (L.presSegment s).lo : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).lo, (ρ : ℂ) * (starRingEnd ℂ) (Pl ρ))) := by
  have htr : ∀ dd : Fin L.degSide, segmentTrace (L.presSegment s)
      (fun p => rowModeVec c a 0 p (if (L.presSegment s).radial then 0 else 2)) dd = cf dd := by
    intro dd
    rw [presSide_trace hα1 hα2 hc hR hsh hL ha s Pl hPl dd]
    simp_rw [hcf]
    exact coef_of_orth _ _ (hL.presSegment_orthonormal s) cf dd
  have hconj : ∀ t, (starRingEnd ℂ) (Pl t) = ∑ d, (starRingEnd ℂ) (cf d) * ((L.presSegment s).test d t : ℂ) := by
    intro t; rw [hcf]; exact conj_poly _ _ cf t
  simp_rw [hconj]
  rw [interval_poly _ _ (fun d => (starRingEnd ℂ) (cf d)),
    weighted_poly (L.presSegment s) L.degSide (fun d => (starRingEnd ℂ) (cf d)) (L.presSegment s).hi,
    weighted_poly (L.presSegment s) L.degSide (fun d => (starRingEnd ℂ) (cf d)) (L.presSegment s).lo]
  simp only [presSideRowCoef, htr, presShiftValue]
  split_ifs <;>
  · push_cast
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring

private theorem pres_total {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N slots : ℕ} {c : FracCellData k N}
    (hc : IsFormData α c) {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {L : CellLayout}
    (hL : IsPressureLayout c K S B L)
    (hP : ∀ a ∈ R.rowSet, ∀ s n, ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin L.degSide → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = Pl p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = Pl p.1))
    {g : GaugeShift k} (hg : IsGaugeShift c L g) (x : FieldTuple k) {a : Fin N} (ha : a ∈ R.rowSet) :
    ∑ s : Fin L.presCount, ∑ dd : Fin L.degSide, presSideRowCoef c L a 0 s dd * presShiftValue L g x s dd = 0 := by
  have h0 := fun s => hP a ha s 0
  choose Pl hPlp hPlv using h0
  choose cf hcf using hPlp
  have hcont : ∀ s, Continuous (Pl s) := fun s => by
    rw [show Pl s = fun t => ∑ d, cf s d * ((L.presSegment s).test d t : ℂ) from funext (hcf s)]
    have := test_continuous (L.presSegment s)
    fun_prop
  rw [Finset.sum_congr rfl (fun s _ => segment_value hα1 hα2 hc hR hsh hL ha g x s (Pl s) (cf s) (hcf s) (hPlv s))]
  have hbox := hL.layout.box_eq
  obtain ⟨hr0, hr12⟩ := hL.layout.box_valid.r_order
  obtain ⟨hz0, hz12⟩ := hL.layout.box_valid.z_order
  rw [hbox]
  have hside : ∀ s, ((L.presSegment s).radial ∧ ((L.presSegment s).level = K.r₁ ∨ (L.presSegment s).level = K.r₂) ∧
      (L.presSegment s).level ≠ 0) ∨
      (¬ (L.presSegment s).radial ∧ ((L.presSegment s).level = K.z₁ ∨ (L.presSegment s).level = K.z₂)) := by
    intro s
    rcases hL.presSegment_on_side s with h | h
    · exact Or.inl ⟨h.1, h.2.1, h.2.2.2.2⟩
    · exact Or.inr ⟨h.1, h.2.1⟩
  have hoth := hL.presSegment_other_in_box
  obtain ⟨s2, hs2r, hs2l, -, -⟩ := hL.presSides_cover 2 (fun h => absurd h (by decide)) K.r₁
    (by simp; exact hr12.le)
  obtain ⟨s3, hs3r, hs3l, -, -⟩ := hL.presSides_cover 3 (fun h => absurd h (by decide)) K.r₁
    (by simp; exact hr12.le)
  simp at hs2r hs2l hs3r hs3l
  have hz1 : ∀ s, ¬ (L.presSegment s).radial → (L.presSegment s).level = K.z₁ →
      ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₁) 2 = Pl s r := by
    intro s h1 h2 r hr
    exact (hPlv s (r, K.z₁) ⟨hr, le_rfl, hz12.le⟩).2 h1 h2.symm
  have hz2 : ∀ s, ¬ (L.presSegment s).radial → (L.presSegment s).level = K.z₂ →
      ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₂) 2 = Pl s r := by
    intro s h1 h2 r hr
    exact (hPlv s (r, K.z₂) ⟨hr, hz12.le, le_rfl⟩).2 h1 h2.symm
  have hfl : ∀ s s', ¬ (L.presSegment s).radial → (L.presSegment s).level = K.z₂ →
      ¬ (L.presSegment s').radial → (L.presSegment s').level = K.z₁ → ∀ y ∈ Set.Icc K.r₁ K.r₂,
      (y : ℂ) * (∫ z in K.z₁..K.z₂, (starRingEnd ℂ) (rowModeVec c a 0 (y, z) 0))
        + (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))
        - (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * (starRingEnd ℂ) (Pl s' ρ)) = 0 := by
    intro s s' h1 h2 h3 h4 y hy
    exact presSide_flux hα1 hα2 hc hR hsh hL ha (Pl s') (Pl s) ⟨s', cf s', hcf s'⟩ ⟨s, cf s, hcf s⟩
      (hz1 s' h3 h4) (hz2 s h1 h2) y hy
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => (L.presSegment s).radial = true)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun s => (L.presSegment s).radial = true))
    (fun s => (L.presSegment s).level = K.r₂)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun s => ¬ (L.presSegment s).radial = true))
    (fun s => (L.presSegment s).level = K.z₂)]
  have hA : ∑ s ∈ (Finset.univ.filter (fun s => (L.presSegment s).radial = true)).filter
      (fun s => (L.presSegment s).level = K.r₂),
      edgeSign (L.presSegment s).level (L.presSegment s).other *
        (if (L.presSegment s).radial then
          ((L.presSegment s).level : ℂ) * ((((if (L.presSegment s).level = K.r₁ then g.left x else g.right x) : ℝ) : ℂ) *
            ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (starRingEnd ℂ) (Pl s z))
        else (g.point x (L.presSegment s).hi : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).hi, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))
          - (g.point x (L.presSegment s).lo : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).lo, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))) =
      (K.r₂ : ℂ) * ((g.right x : ℂ) * ∫ z in K.z₁..K.z₂, (starRingEnd ℂ) (rowModeVec c a 0 (K.r₂, z) 0)) := by
    have hT : ∀ s ∈ (Finset.univ.filter (fun s => (L.presSegment s).radial = true)).filter
        (fun s => (L.presSegment s).level = K.r₂), (L.presSegment s).radial ∧ (L.presSegment s).level = K.r₂ := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact hs
    rw [← radial_side hL a K.r₂ ⟨hr12.le, le_rfl⟩ _ hT ?_ Pl hcont (fun s p hp => (hPlv s p hp).1),
      Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl (fun s hs => ?_)
      obtain ⟨hrad, hlev⟩ := hT s hs
      have ho := (hoth s).1 hrad
      have hes : edgeSign (L.presSegment s).level (L.presSegment s).other = 1 := by
        unfold edgeSign; rw [if_pos (by rw [ho, hlev]; linarith)]
      rw [hes, one_mul, if_pos hrad, hlev, if_neg (ne_of_gt hr12)]
    · intro u hu1 hu2
      obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 1 (fun h => absurd h (by decide)) u (by simp; exact ⟨hu1, hu2⟩)
      simp at h1 h2
      exact ⟨s, by simp [h1, h2], h3, h4⟩
  have hB : ∑ s ∈ (Finset.univ.filter (fun s => (L.presSegment s).radial = true)).filter
      (fun s => ¬ (L.presSegment s).level = K.r₂),
      edgeSign (L.presSegment s).level (L.presSegment s).other *
        (if (L.presSegment s).radial then
          ((L.presSegment s).level : ℂ) * ((((if (L.presSegment s).level = K.r₁ then g.left x else g.right x) : ℝ) : ℂ) *
            ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (starRingEnd ℂ) (Pl s z))
        else (g.point x (L.presSegment s).hi : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).hi, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))
          - (g.point x (L.presSegment s).lo : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).lo, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))) =
      -((K.r₁ : ℂ) * ((g.left x : ℂ) * ∫ z in K.z₁..K.z₂, (starRingEnd ℂ) (rowModeVec c a 0 (K.r₁, z) 0))) := by
    have hT : ∀ s ∈ (Finset.univ.filter (fun s => (L.presSegment s).radial = true)).filter
        (fun s => ¬ (L.presSegment s).level = K.r₂), (L.presSegment s).radial ∧ (L.presSegment s).level = K.r₁ := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rcases hside s with h | h
      · exact ⟨hs.1, h.2.1.resolve_right hs.2⟩
      · exact absurd hs.1 h.1
    by_cases hr1 : K.r₁ = 0
    · rw [Finset.sum_eq_zero]
      · simp [hr1]
      · intro s hs
        exfalso
        rcases hside s with h | h
        · exact h.2.2 ((hT s hs).2.trans hr1)
        · exact h.1 (hT s hs).1
    rw [← radial_side hL a K.r₁ ⟨le_rfl, hr12.le⟩ _ hT ?_ Pl hcont (fun s p hp => (hPlv s p hp).1),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    · refine Finset.sum_congr rfl (fun s hs => ?_)
      obtain ⟨hrad, hlev⟩ := hT s hs
      have ho := (hoth s).1 hrad
      have hes : edgeSign (L.presSegment s).level (L.presSegment s).other = -1 := by
        unfold edgeSign; rw [if_neg (by rw [ho, hlev]; linarith)]
      rw [hes, if_pos hrad, hlev, if_pos rfl]
      ring
    · intro u hu1 hu2
      obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 0 (fun _ => hr1) u (by simp; exact ⟨hu1, hu2⟩)
      simp at h1 h2
      exact ⟨s, by simp [h1, h2, ne_of_lt hr12], h3, h4⟩
  have hs2n : ¬ (L.presSegment s2).radial := by simp [hs2r]
  have hs3n : ¬ (L.presSegment s3).radial := by simp [hs3r]
  have hC : ∑ s ∈ (Finset.univ.filter (fun s => ¬ (L.presSegment s).radial = true)).filter
      (fun s => (L.presSegment s).level = K.z₂), edgeSign (L.presSegment s).level (L.presSegment s).other *
        (if (L.presSegment s).radial then
          ((L.presSegment s).level : ℂ) * ((((if (L.presSegment s).level = K.r₁ then g.left x else g.right x) : ℝ) : ℂ) *
            ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (starRingEnd ℂ) (Pl s z))
        else (g.point x (L.presSegment s).hi : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).hi, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))
          - (g.point x (L.presSegment s).lo : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).lo, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))) =
      (g.point x K.r₂ : ℂ) * (∫ ρ in (0 : ℝ)..K.r₂, (ρ : ℂ) * (starRingEnd ℂ) (Pl s3 ρ)) - (g.point x K.r₁ : ℂ) * (∫ ρ in (0 : ℝ)..K.r₁, (ρ : ℂ) * (starRingEnd ℂ) (Pl s3 ρ)) := by
    have hT : ∀ s ∈ (Finset.univ.filter (fun s => ¬ (L.presSegment s).radial = true)).filter
        (fun s => (L.presSegment s).level = K.z₂), ¬ (L.presSegment s).radial ∧ (L.presSegment s).level = K.z₂ := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact hs
    rw [← height_side hL K.z₂ _ hT ?_ (fun s y => (g.point x y : ℂ) * (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ)))
      (fun y => (g.point x y : ℂ) * (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * (starRingEnd ℂ) (Pl s3 ρ))) ?_]
    · refine Finset.sum_congr rfl (fun s hs => ?_)
      obtain ⟨hrad, hlev⟩ := hT s hs
      have ho := (hoth s).2 hrad
      have hes : edgeSign (L.presSegment s).level (L.presSegment s).other = 1 := by
        unfold edgeSign; rw [if_pos (by rw [ho, hlev]; linarith)]
      rw [hes, one_mul, if_neg hrad]
    · intro u hu1 hu2
      obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 3 (fun h => absurd h (by decide)) u (by simp; exact ⟨hu1, hu2⟩)
      simp at h1 h2
      exact ⟨s, by simp [h1, h2], h3, h4⟩
    · intro s hs y hy1 hy2
      obtain ⟨hrad, hlev⟩ := hT s hs
      have e1 := hfl s s2 hrad hlev hs2n hs2l y ⟨hy1, hy2⟩
      have e2 := hfl s3 s2 hs3n hs3l hs2n hs2l y ⟨hy1, hy2⟩
      linear_combination (g.point x y : ℂ) * (e1 - e2)
  have hD : ∑ s ∈ (Finset.univ.filter (fun s => ¬ (L.presSegment s).radial = true)).filter
      (fun s => ¬ (L.presSegment s).level = K.z₂), edgeSign (L.presSegment s).level (L.presSegment s).other *
        (if (L.presSegment s).radial then
          ((L.presSegment s).level : ℂ) * ((((if (L.presSegment s).level = K.r₁ then g.left x else g.right x) : ℝ) : ℂ) *
            ∫ z in (L.presSegment s).lo..(L.presSegment s).hi, (starRingEnd ℂ) (Pl s z))
        else (g.point x (L.presSegment s).hi : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).hi, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))
          - (g.point x (L.presSegment s).lo : ℂ) *
            (∫ ρ in (0 : ℝ)..(L.presSegment s).lo, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ))) =
      -((g.point x K.r₂ : ℂ) * (∫ ρ in (0 : ℝ)..K.r₂, (ρ : ℂ) * (starRingEnd ℂ) (Pl s2 ρ)) - (g.point x K.r₁ : ℂ) * (∫ ρ in (0 : ℝ)..K.r₁, (ρ : ℂ) * (starRingEnd ℂ) (Pl s2 ρ))) := by
    have hT : ∀ s ∈ (Finset.univ.filter (fun s => ¬ (L.presSegment s).radial = true)).filter
        (fun s => ¬ (L.presSegment s).level = K.z₂), ¬ (L.presSegment s).radial ∧ (L.presSegment s).level = K.z₁ := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rcases hside s with h | h
      · exact absurd h.1 hs.1
      · exact ⟨hs.1, h.2.resolve_right hs.2⟩
    rw [← height_side hL K.z₁ _ hT ?_ (fun s y => (g.point x y : ℂ) * (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * (starRingEnd ℂ) (Pl s ρ)))
      (fun y => (g.point x y : ℂ) * (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * (starRingEnd ℂ) (Pl s2 ρ))) ?_, ← Finset.sum_neg_distrib]
    · refine Finset.sum_congr rfl (fun s hs => ?_)
      obtain ⟨hrad, hlev⟩ := hT s hs
      have ho := (hoth s).2 hrad
      have hes : edgeSign (L.presSegment s).level (L.presSegment s).other = -1 := by
        unfold edgeSign; rw [if_neg (by rw [ho, hlev]; linarith)]
      rw [hes, if_neg hrad]
      ring
    · intro u hu1 hu2
      obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 2 (fun h => absurd h (by decide)) u (by simp; exact ⟨hu1, hu2⟩)
      simp at h1 h2
      exact ⟨s, by simp [h1, h2, ne_of_lt hz12], h3, h4⟩
    · intro s hs y hy1 hy2
      obtain ⟨hrad, hlev⟩ := hT s hs
      have e1 := hfl s3 s hs3n hs3l hrad hlev y ⟨hy1, hy2⟩
      have e2 := hfl s3 s2 hs3n hs3l hs2n hs2l y ⟨hy1, hy2⟩
      linear_combination (g.point x y : ℂ) * (e2 - e1)
  rw [hA, hB, hC, hD]
  have pr := hg.point_right x
  rw [hbox] at pr
  have e2 := hfl s3 s2 hs3n hs3l hs2n hs2l K.r₂ ⟨hr12.le, le_rfl⟩
  rw [pr]
  by_cases hr1 : K.r₁ = 0
  · simp only [hr1, intervalIntegral.integral_same, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, sub_zero,
      add_zero]
    linear_combination (g.right x : ℂ) * e2
  · have pl := hg.point_left (by rw [hbox]; exact hr1) x
    rw [hbox] at pl
    have e1 := hfl s3 s2 hs3n hs3l hs2n hs2l K.r₁ ⟨le_rfl, hr12.le⟩
    rw [pl]
    linear_combination (g.right x : ℂ) * e2 - (g.left x : ℂ) * e1

private theorem cornerAt_presSlot (L : CellLayout) (n : L.modes) (i j : Fin 2) (a : Fin 3)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.cornerAt n i j a (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.cornerAt
  rcases h : L.cellCorner i j with _ | c
  · rfl
  · simp [CellLayout.unitAt, CellDatum.cornerVelocity]

private theorem sideVelocityRow_presSlot (L : CellLayout) (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.sideVelocityRow n e a f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  simp [CellLayout.sideVelocityRow, CellLayout.unitAt, CellDatum.sideVelocity]

private theorem sideGradientRow_presSlot (L : CellLayout) (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.sideGradientRow n e a f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  simp [CellLayout.sideGradientRow, CellLayout.unitAt, CellDatum.sideGradient]

private theorem turnSideRow_presSlot (L : CellLayout) (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.turnSideRow n e a f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.turnSideRow
  split_ifs <;> simp [sideVelocityRow_presSlot]

private theorem faceBaseRow_presSlot (L : CellLayout) (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.faceBaseRow n e a b l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.faceBaseRow
  split_ifs <;> simp [cornerAt_presSlot, sideVelocityRow_presSlot, sideGradientRow_presSlot, turnSideRow_presSlot]

private theorem strainFaceRow_presSlot (L : CellLayout) (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.strainFaceRow n e a b l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.strainFaceRow
  split_ifs <;> simp [faceBaseRow_presSlot]

private theorem normalFace_pressureShift {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (a : Fin N)
    (g : GaugeShift k) (x : FieldTuple k) :
    ∑ d : L.Datum, normalFaceRowData c L a d * L.pressureShift g x d = 0 := by
  apply Finset.sum_eq_zero
  intro d _
  rcases d with d | d | d | d | d | d | d | d
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [normalFaceRowData, strainFaceRow_presSlot]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]

theorem gaugeInvariance_holds : GaugeInvarianceStatement := by
  intro α hα1 hα2 k N slots c hc K S B Cl R hR hsh L hL hP g hg x hx a ha u κ
  have key : ∑ d : L.Datum, layoutRowData c α L R a d * L.pressureShift g x d = 0 := by
    have hsplit : ∀ d, layoutRowData c α L R a d * L.pressureShift g x d =
        (layoutRowData c α L R a d - normalFaceRowData c L a d) * L.pressureShift g x d +
          normalFaceRowData c L a d * L.pressureShift g x d := fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hsplit d), Finset.sum_add_distrib, normalFace_pressureShift, add_zero]
    simp only [layoutRowData, add_sub_cancel_right]
    simp only [Fintype.sum_sum_type, CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr,
      mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero (fun n _ => ?_)
    obtain ⟨n, hn⟩ := n
    by_cases h : n = 0
    · subst h
      rw [Fintype.sum_prod_type]
      simp only [if_true]
      exact pres_total hα1 hα2 hc hR hsh hL hP hg x ha
    · simp [h]
  unfold layoutRowValue
  congr 2
  simp only [mul_add, Finset.sum_add_distrib, key, add_zero]

end CellFormula

end CellCert

end Breakdown

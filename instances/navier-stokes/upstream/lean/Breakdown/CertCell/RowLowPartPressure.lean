import Breakdown.CertCell.RowLowPartSegment

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

section Layout

variable {k N' : ℕ} {c0 : FracCellData k N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

def presFiber (K : CellBox) (L : CellLayout) (e : Fin 4) : Finset (Fin L.presCount) :=
  Finset.univ.filter (fun s => segSide K (L.presSegment s) = e)

theorem pres_radial_facts (hL : IsCellLayout c0 K S0 B L) (hps : IsPressureSegmentation L) {e : Fin 4}
    (he : e.val < 2) {s : Fin L.presCount} (hs : s ∈ presFiber K L e) :
    (L.presSegment s).radial = true ∧ (L.presSegment s).level = (if e.val = 0 then K.r₁ else K.r₂) ∧
      (L.presSegment s).other = K.r₁ + K.r₂ - (L.presSegment s).level ∧
      K.z₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.z₂ := by
  have hb := hL.box_eq
  subst hb
  simp only [presFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  unfold segSide at hs
  have hr := hL.box_valid.r_order.2
  rcases hps.1 s with ⟨hrad, hlev⟩ | ⟨hrad, hlev⟩
  · obtain ⟨h1, h2, h3⟩ := hps.2.2.2.2.1 s hrad
    refine ⟨hrad, ?_, h3, h1, h2⟩
    rw [if_pos hrad] at hs
    split_ifs at hs with h
    · rw [← hs]; simp [h]
    · rw [← hs]; simp; rcases hlev with h' | h'
      · exact absurd h' h
      · exact h'
  · rw [if_neg hrad] at hs
    split_ifs at hs <;> (rw [← hs] at he; simp at he)

theorem pres_height_facts (hL : IsCellLayout c0 K S0 B L) (hps : IsPressureSegmentation L) {e : Fin 4}
    (he : 2 ≤ e.val) {s : Fin L.presCount} (hs : s ∈ presFiber K L e) :
    (L.presSegment s).radial = false ∧ (L.presSegment s).level = (if e.val = 2 then K.z₁ else K.z₂) ∧
      (L.presSegment s).other = K.z₁ + K.z₂ - (L.presSegment s).level ∧
      K.r₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.r₂ := by
  have hb := hL.box_eq
  subst hb
  simp only [presFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  unfold segSide at hs
  rcases hps.1 s with ⟨hrad, hlev⟩ | ⟨hrad, hlev⟩
  · rw [if_pos hrad] at hs
    split_ifs at hs <;> (rw [← hs] at he; simp at he)
  · have hrad' : (L.presSegment s).radial = false := by simpa using hrad
    obtain ⟨h1, h2, h3⟩ := hps.2.2.2.2.2.1 s hrad
    refine ⟨hrad', ?_, h3, h1, h2⟩
    rw [if_neg hrad] at hs
    split_ifs at hs with h
    · rw [← hs]; simp [h]
    · rw [← hs]; simp; rcases hlev with h' | h'
      · exact absurd h' h
      · exact h'

theorem pres_radial_side (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L)
    (hps : IsPressureSegmentation L) {e : Fin 4} (he : e.val < 2) {c : ℝ}
    (hc : c = if e.val = 0 then L.box.r₁ else L.box.r₂) (φ : Fin 3 → CellPoly)
    (hφ : IsBivariatePoly (L.degSide + 1) L.degSide (fun p => (φ 0).eval L.box p))
    (F dF X : ℝ × ℝ → ℂ)
    (hint : c ≠ 0 → IntegrableOn (radialIntegrand c (L.box.r₁ + L.box.r₂ - c) F dF) L.box.rect) :
    ∑ s ∈ presFiber L.box L e, ∑ d : Fin L.degSide,
        sidePresRow L φ s d * (L.presSegment s).moment true F dF X d
      = (c : ℂ) * ∫ p in L.box.rect,
          radialIntegrand c (L.box.r₁ + L.box.r₂ - c) F dF p * (starRingEnd ℂ) ((φ 0).eval L.box (c, p.2)) := by
  have hb := hL.box_eq
  subst hb
  have hr := hL.box_valid.r_order.2
  by_cases hc0 : c = 0
  · rw [Finset.sum_eq_zero, hc0]
    · simp
    · intro s hs
      obtain ⟨hrad, hlev, _⟩ := pres_radial_facts hL hps he hs
      rw [← hc, hc0] at hlev
      refine Finset.sum_eq_zero (fun d _ => ?_)
      unfold sidePresRow
      simp [hrad, hlev]
  have hcx : c = L.box.r₁ ∨ c = L.box.r₂ := by rw [hc]; split_ifs <;> simp
  obtain ⟨hmin, hmax⟩ := minmax_of hr hcx
  have hper : ∀ s ∈ presFiber L.box L e, ∑ d : Fin L.degSide,
      sidePresRow L φ s d * (L.presSegment s).moment true F dF X d
      = (c : ℂ) * ∫ p in Icc L.box.r₁ L.box.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi,
          radialIntegrand c (L.box.r₁ + L.box.r₂ - c) F dF p * (starRingEnd ℂ) ((φ 0).eval L.box (c, p.2)) := by
    intro s hs
    obtain ⟨hrad, hlev, hoth, hlo, hhi⟩ := pres_radial_facts hL hps he hs
    rw [← hc] at hlev
    rw [hlev] at hoth
    have hseg := grad_seg_radial (M := L.degSide + 1) (N := L.degSide) hexp (hL.presSegment_valid s) hrad
      (fun d d' hd hd' => hps.2.2.2.2.2.2 s d d' hd hd') hφ
      (F := F) (dF := dF) (dF' := X) (by
        rw [hlev, hoth, hmin, hmax]
        exact (hint hc0).mono_set (prod_mono subset_rfl (Icc_subset_Icc hlo hhi)))
    rw [hlev, hoth, hmin, hmax] at hseg
    unfold sidePresRow
    simp only [hrad, if_true, hlev, hoth]
    rw [Fin.sum_univ_eq_sum_range (fun d => edgeSign c (L.box.r₁ + L.box.r₂ - c) * (c : ℂ) *
        (starRingEnd ℂ) (sideTestMoment (L.presSegment s) (fun p => (φ 0).eval L.box p) d) *
          (L.presSegment s).moment true F dF X d) L.degSide]
    have : ∀ d ∈ Finset.range L.degSide, edgeSign c (L.box.r₁ + L.box.r₂ - c) * (c : ℂ) *
        (starRingEnd ℂ) (sideTestMoment (L.presSegment s) (fun p => (φ 0).eval L.box p) d) *
          (L.presSegment s).moment true F dF X d =
        (edgeSign c (L.box.r₁ + L.box.r₂ - c) * (c : ℂ)) *
          ((starRingEnd ℂ) (sideTestMoment (L.presSegment s) (fun p => (φ 0).eval L.box p) d) *
          (L.presSegment s).moment true F dF X d) := fun d _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hseg]
    have h2 := edgeSign_sq c (L.box.r₁ + L.box.r₂ - c)
    linear_combination ((c : ℂ) * ∫ p in Icc L.box.r₁ L.box.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi,
          radialIntegrand c (L.box.r₁ + L.box.r₂ - c) F dF p *
            (starRingEnd ℂ) ((φ 0).eval L.box (c, p.2))) * h2
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]
  congr 1
  have hf : IntegrableOn (fun p => radialIntegrand c (L.box.r₁ + L.box.r₂ - c) F dF p *
      (starRingEnd ℂ) ((φ 0).eval L.box (c, p.2))) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) :=
    (hint hc0).mul_continuousOn
      ((Complex.continuous_conj.comp ((bi_contDiff hφ).continuous.comp
        (continuous_const.prodMk continuous_snd))).continuousOn) (rect_compact L.box)
  symm
  refine Breakdown.FracInternal.LayoutRowPressureBoundaryParts.strip_partition (presFiber L.box L e)
    (fun s => (L.presSegment s).lo) (fun s => (L.presSegment s).hi) ?_ ?_ ?_ measurableSet_Icc hf
  · intro u hu
    have hlev : c = L.box.r₂ ∨ (c = L.box.r₁ ∧ L.box.r₁ ≠ 0) := by
      rcases hcx with h | h
      · exact Or.inr ⟨h, h ▸ hc0⟩
      · exact Or.inl h
    obtain ⟨s, hrad, hl, h1, h2⟩ := hps.2.2.1 u hu.1 hu.2 c hlev
    refine ⟨s, ?_, h1, h2⟩
    simp only [presFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold segSide
    rw [if_pos hrad, hl, hc]
    fin_cases e
    · simp
    · simp [hr.ne']
    · simp at he
    · simp at he
  · intro s hs
    obtain ⟨_, _, _, hlo, hhi⟩ := pres_radial_facts hL hps he hs
    exact ⟨hlo, hhi⟩
  · intro s hs s' hs' hne
    obtain ⟨hrad, hlev, _⟩ := pres_radial_facts hL hps he hs
    obtain ⟨hrad', hlev', _⟩ := pres_radial_facts hL hps he hs'
    exact hps.2.1 s s' hne (by rw [hrad, hrad']) (by rw [hlev, hlev'])

theorem pres_height_side (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L)
    (hps : IsPressureSegmentation L) {e : Fin 4} (he : 2 ≤ e.val) {c : ℝ}
    (hc : c = if e.val = 2 then L.box.z₁ else L.box.z₂) (φ : Fin 3 → CellPoly)
    (hφ : IsBivariatePoly L.degSide (L.degSide + 1) (fun p => (φ 2).eval L.box p))
    (F dF Y : ℝ × ℝ → ℂ)
    (hint : IntegrableOn (fun p => heightIntegrand c (L.box.z₁ + L.box.z₂ - c) F dF p * (p.1 : ℂ)) L.box.rect) :
    ∑ s ∈ presFiber L.box L e, ∑ d : Fin L.degSide,
        sidePresRow L φ s d * (L.presSegment s).moment true F Y dF d
      = ∫ p in L.box.rect, heightIntegrand c (L.box.z₁ + L.box.z₂ - c) F dF p * (p.1 : ℂ) *
          (starRingEnd ℂ) ((φ 2).eval L.box (p.1, c)) := by
  have hb := hL.box_eq
  subst hb
  have hz := hL.box_valid.z_order.2
  have hcx : c = L.box.z₁ ∨ c = L.box.z₂ := by rw [hc]; split_ifs <;> simp
  obtain ⟨hmin, hmax⟩ := minmax_of hz hcx
  have hper : ∀ s ∈ presFiber L.box L e, ∑ d : Fin L.degSide,
      sidePresRow L φ s d * (L.presSegment s).moment true F Y dF d
      = ∫ p in Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc L.box.z₁ L.box.z₂,
          heightIntegrand c (L.box.z₁ + L.box.z₂ - c) F dF p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ 2).eval L.box (p.1, c)) := by
    intro s hs
    obtain ⟨hrad, hlev, hoth, hlo, hhi⟩ := pres_height_facts hL hps he hs
    rw [← hc] at hlev
    rw [hlev] at hoth
    have hseg := grad_seg_height (M := L.degSide) (N := L.degSide + 1) hexp (hL.presSegment_valid s) hrad
      (fun d d' hd hd' => hps.2.2.2.2.2.2 s d d' hd hd') hφ
      (F := F) (dF := dF) (dF' := Y) (by
        rw [hlev, hoth, hmin, hmax]
        exact hint.mono_set (prod_mono (Icc_subset_Icc hlo hhi) subset_rfl))
    rw [hlev, hoth, hmin, hmax] at hseg
    unfold sidePresRow
    simp only [hrad, Bool.false_eq_true, if_false, hlev, hoth, mul_one]
    rw [Fin.sum_univ_eq_sum_range (fun d => edgeSign c (L.box.z₁ + L.box.z₂ - c) *
        (starRingEnd ℂ) (sideTestMoment (L.presSegment s) (fun p => (φ 2).eval L.box p) d) *
          (L.presSegment s).moment true F Y dF d) L.degSide]
    have : ∀ d ∈ Finset.range L.degSide, edgeSign c (L.box.z₁ + L.box.z₂ - c) *
        (starRingEnd ℂ) (sideTestMoment (L.presSegment s) (fun p => (φ 2).eval L.box p) d) *
          (L.presSegment s).moment true F Y dF d =
        (edgeSign c (L.box.z₁ + L.box.z₂ - c)) *
          ((starRingEnd ℂ) (sideTestMoment (L.presSegment s) (fun p => (φ 2).eval L.box p) d) *
          (L.presSegment s).moment true F Y dF d) := fun d _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hseg]
    have h2 := edgeSign_sq c (L.box.z₁ + L.box.z₂ - c)
    linear_combination (∫ p in Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc L.box.z₁ L.box.z₂,
          heightIntegrand c (L.box.z₁ + L.box.z₂ - c) F dF p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ 2).eval L.box (p.1, c))) * h2
  rw [Finset.sum_congr rfl hper]
  have hf : IntegrableOn (fun p => heightIntegrand c (L.box.z₁ + L.box.z₂ - c) F dF p * (p.1 : ℂ) *
      (starRingEnd ℂ) ((φ 2).eval L.box (p.1, c))) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) :=
    hint.mul_continuousOn
      ((Complex.continuous_conj.comp ((bi_contDiff hφ).continuous.comp
        (continuous_fst.prodMk continuous_const))).continuousOn) (rect_compact L.box)
  symm
  refine Breakdown.FracInternal.LayoutRowPressureBoundaryParts.strip_partition_fst (presFiber L.box L e)
    (fun s => (L.presSegment s).lo) (fun s => (L.presSegment s).hi) ?_ ?_ ?_ measurableSet_Icc hf
  · intro u hu
    obtain ⟨s, hrad, hl, h1, h2⟩ := hps.2.2.2.1 u hu.1 hu.2 c hcx
    refine ⟨s, ?_, h1, h2⟩
    simp only [presFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold segSide
    rw [if_neg hrad, hl, hc]
    fin_cases e
    · simp at he
    · simp at he
    · simp
    · simp [hz.ne']
  · intro s hs
    obtain ⟨_, _, _, hlo, hhi⟩ := pres_height_facts hL hps he hs
    exact ⟨hlo, hhi⟩
  · intro s hs s' hs' hne
    obtain ⟨hrad, hlev, _⟩ := pres_height_facts hL hps he hs
    obtain ⟨hrad', hlev', _⟩ := pres_height_facts hL hps he hs'
    exact hps.2.1 s s' hne (by rw [hrad, hrad']) (by rw [hlev, hlev'])

end Layout

theorem radial_bdry {K : CellBox} {c o : ℝ} (hmin : min c o = K.r₁) (hmax : max c o = K.r₂)
    (F dF : Fin 3 → ℝ × ℝ → ℂ) (hint : c ≠ 0 → ∀ a, IntegrableOn (radialIntegrand c o (F a) (dF a)) K.rect)
    (φ : Fin 3 → CellPoly) (hφ : ∀ a, Continuous (fun p => (φ a).eval K p)) :
    ∫ z in Icc K.z₁ K.z₂, (c : ℂ) * cdot3 (fun a => radialStripTrace c o (F a) (dF a) z) (testValue K φ (c, z))
      = (c : ℂ) * edgeSign c o * ∑ a : Fin 3, ∫ p in K.rect,
          radialIntegrand c o (F a) (dF a) p * (starRingEnd ℂ) ((φ a).eval K (c, p.2)) := by
  by_cases hc0 : c = 0
  · simp [hc0]
  have hw : ∀ a, Continuous (fun z : ℝ => (starRingEnd ℂ) ((φ a).eval K (c, z))) := fun a =>
    Complex.continuous_conj.comp ((hφ a).comp (continuous_const.prodMk continuous_id))
  have ht := fun a => trace_radial hmin hmax (hint hc0 a) (hw a)
  unfold cdot3 testValue
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => (ht a).1), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => (ht a).2)

theorem height_bdry {K : CellBox} {c o : ℝ} (hmin : min c o = K.z₁) (hmax : max c o = K.z₂)
    (F dF : Fin 3 → ℝ × ℝ → ℂ)
    (hint : ∀ a, IntegrableOn (fun p => heightIntegrand c o (F a) (dF a) p * (p.1 : ℂ)) K.rect)
    (φ : Fin 3 → CellPoly) (hφ : ∀ a, Continuous (fun p => (φ a).eval K p)) :
    ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * cdot3 (fun a => heightStripTrace c o (F a) (dF a) r) (testValue K φ (r, c))
      = edgeSign c o * ∑ a : Fin 3, ∫ p in K.rect,
          heightIntegrand c o (F a) (dF a) p * (p.1 : ℂ) * (starRingEnd ℂ) ((φ a).eval K (p.1, c)) := by
  have hw : ∀ a, Continuous (fun r : ℝ => (starRingEnd ℂ) ((φ a).eval K (r, c))) := fun a =>
    Complex.continuous_conj.comp ((hφ a).comp (continuous_id.prodMk continuous_const))
  have ht := fun a => trace_height hmin hmax (hint a) (hw a)
  unfold cdot3 testValue
  have e1 : ∀ r : ℝ, (r : ℂ) * ∑ a : Fin 3, heightStripTrace c o (F a) (dF a) r *
      (starRingEnd ℂ) ((φ a).eval K (r, c)) = ∑ a : Fin 3, (r : ℂ) * heightStripTrace c o (F a) (dF a) r *
      (starRingEnd ℂ) ((φ a).eval K (r, c)) := by
    intro r
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  simp_rw [e1]
  rw [integral_finsetSum _ (fun a _ => (ht a).1), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact (ht a).2

section Layout

variable {k N' : ℕ} {c0 : FracCellData k N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

theorem edgeSign_lt {x y : ℝ} (h : x < y) : edgeSign x y = -1 ∧ edgeSign y x = 1 := by
  unfold edgeSign
  exact ⟨by rw [if_neg (not_lt.2 h.le)], by rw [if_pos h]⟩

theorem grad_block (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L) (φ : Fin 3 → CellPoly)
    (hφ : ∀ a, IsBivariatePoly (L.degSide + 1) (L.degSide + 1) (fun p => (φ a).eval K p))
    (FR dFR X FH Y dFH : Fin 3 → ℝ × ℝ → ℂ) (R : RowProfile)
    (hRr : ∀ e z, R.radialSide e z = fun a => radialStripTrace (sideRadius K e) (otherRadius K e) (FR a) (dFR a) z)
    (hRh : ∀ e r, R.heightSide e r = fun a => heightStripTrace (sideHeight K e) (otherHeight K e) (FH a) (dFH a) r)
    (i1 : ∀ a, IntegrableOn (FR a) K.rect) (i2 : ∀ a, IntegrableOn (fun p => (p.1 : ℂ) * dFR a p) K.rect)
    (i3 : ∀ a, IntegrableOn (fun p => (p.1 : ℂ) * FH a p) K.rect)
    (i4 : ∀ a, IntegrableOn (fun p => (p.1 : ℂ) * dFH a p) K.rect) :
    ∑ s : Fin L.segCount, ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1), sideGradRow L φ s a d *
        (if (L.segment s).radial then (L.segment s).moment true (FR a) (dFR a) (X a) d
          else (L.segment s).moment true (FH a) (Y a) (dFH a) d)
      = -rowBoundaryGrad K R φ := by
  have hK := hL.box_valid
  have hr := hK.r_order.2
  have hz := hK.z_order.2
  have hcont : ∀ a, Continuous (fun p => (φ a).eval K p) := fun a => (bi_contDiff (hφ a)).continuous
  rw [← Finset.sum_fiberwise Finset.univ (fun s => segSide K (L.segment s)), Fin.sum_univ_four]
  simp only [segSide_fiber hL]
  have hrad : ∀ e : Fin 4, e.val < 2 → ∀ s ∈ L.sideSegments e, (∑ a : Fin 3, ∑ d : Fin (L.degSide + 1),
      sideGradRow L φ s a d * (if (L.segment s).radial then (L.segment s).moment true (FR a) (dFR a) (X a) d
          else (L.segment s).moment true (FH a) (Y a) (dFH a) d)) =
      ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1), sideGradRow L φ s a d *
        (L.segment s).moment true (FR a) (dFR a) (X a) d := by
    intro e he s hs
    simp only [(seg_radial_facts hL he hs).1, if_true]
  have hhei : ∀ e : Fin 4, 2 ≤ e.val → ∀ s ∈ L.sideSegments e, (∑ a : Fin 3, ∑ d : Fin (L.degSide + 1),
      sideGradRow L φ s a d * (if (L.segment s).radial then (L.segment s).moment true (FR a) (dFR a) (X a) d
          else (L.segment s).moment true (FH a) (Y a) (dFH a) d)) =
      ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1), sideGradRow L φ s a d *
        (L.segment s).moment true (FH a) (Y a) (dFH a) d := by
    intro e he s hs
    simp only [(seg_height_facts hL he hs).1, Bool.false_eq_true, if_false]
  rw [Finset.sum_congr rfl (hrad 0 (by decide)), Finset.sum_congr rfl (hrad 1 (by decide)),
    Finset.sum_congr rfl (hhei 2 (by decide)), Finset.sum_congr rfl (hhei 3 (by decide))]
  have o0 : K.r₁ + K.r₂ - K.r₁ = K.r₂ := by ring
  have o1 : K.r₁ + K.r₂ - K.r₂ = K.r₁ := by ring
  have o2 : K.z₁ + K.z₂ - K.z₁ = K.z₂ := by ring
  have o3 : K.z₁ + K.z₂ - K.z₂ = K.z₁ := by ring
  have hA0 := grad_radial_side hexp hL (e := 0) (by decide) (c := K.r₁) (by simp) φ hφ FR dFR X
    (fun hc0 a => radialIntegrand_int hK (Or.inr (lt_of_le_of_ne hK.r_order.1 (Ne.symm hc0))) (i1 a) (i2 a))
  have hA1 := grad_radial_side hexp hL (e := 1) (by decide) (c := K.r₂) (by simp) φ hφ FR dFR X
    (fun _ a => radialIntegrand_int hK (by
      rw [o1]
      rcases eq_or_lt_of_le hK.r_order.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h) (i1 a) (i2 a))
  have hB2 := grad_height_side hexp hL (e := 2) (by decide) (c := K.z₁) (by simp) φ hφ FH dFH Y
    (fun a => heightIntegrand_w_int (i3 a) (i4 a))
  have hB3 := grad_height_side hexp hL (e := 3) (by decide) (c := K.z₂) (by simp) φ hφ FH dFH Y
    (fun a => heightIntegrand_w_int (i3 a) (i4 a))
  rw [hA0, hA1, hB2, hB3]
  unfold rowBoundaryGrad
  rw [Fin.sum_univ_two]
  simp only [hRr, hRh, sideSign, sideRadius, otherRadius, sideHeight, otherHeight, Fin.isValue, if_true,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
  have m0 := minmax_of hr (Or.inl rfl : K.r₁ = K.r₁ ∨ K.r₁ = K.r₂)
  have m1 := minmax_of hr (Or.inr rfl : K.r₂ = K.r₁ ∨ K.r₂ = K.r₂)
  have m2 := minmax_of hz (Or.inl rfl : K.z₁ = K.z₁ ∨ K.z₁ = K.z₂)
  have m3 := minmax_of hz (Or.inr rfl : K.z₂ = K.z₁ ∨ K.z₂ = K.z₂)
  rw [o0] at m0
  rw [o1] at m1
  rw [o2] at m2
  rw [o3] at m3
  rw [radial_bdry m0.1 m0.2 FR dFR (fun hc0 a => by
      rw [← o0]; exact radialIntegrand_int hK (Or.inr (lt_of_le_of_ne hK.r_order.1 (Ne.symm hc0))) (i1 a) (i2 a))
    φ hcont]
  rw [radial_bdry m1.1 m1.2 FR dFR (fun _ a => by
      rw [← o1]
      exact radialIntegrand_int hK (by
        rw [o1]
        rcases eq_or_lt_of_le hK.r_order.1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h) (i1 a) (i2 a)) φ hcont]
  rw [height_bdry m2.1 m2.2 FH dFH (fun a => heightIntegrand_w_int (i3 a) (i4 a)) φ hcont]
  rw [height_bdry m3.1 m3.2 FH dFH (fun a => heightIntegrand_w_int (i3 a) (i4 a)) φ hcont]
  rw [o0, o1, o2, o3, (edgeSign_lt hr).1, (edgeSign_lt hr).2, (edgeSign_lt hz).1, (edgeSign_lt hz).2]
  ring

end Layout

end Breakdown.CertCell.CellCalculus.RowLow.Internal

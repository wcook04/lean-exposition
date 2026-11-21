import Breakdown.FracCell.CornerIndependenceParts

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

private theorem cornerMoment_eq_term (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz F Fr Fz Frz = edgeSign cr orr * edgeSign cz oz *
      ∫ p in Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz),
        cornerTerm cr orr cz oz F Fr Fz Frz p := rfl

private theorem cornerTerm_integrableOn {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr orr cz oz lo hi zl zh : ℝ} (hlo : 0 ≤ lo) (hpos : 0 < lo ∨ orr = 0) :
    IntegrableOn (cornerTerm cr orr cz oz F Fr Fz Frz) (Set.Icc lo hi ×ˢ Set.Icc zl zh) := by
  set K := Set.Icc lo hi ×ˢ Set.Icc zl zh with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set Z := |zl| + |zh| with hZ
  have hzsub : Set.Icc zl zh ⊆ Set.Icc (-Z) Z := by
    intro t ht
    constructor
    · have := neg_abs_le zl; have := abs_nonneg zh; linarith [ht.1]
    · have := le_abs_self zh; have := abs_nonneg zl; linarith [ht.2]
  have hsub : K ⊆ Set.Icc 0 hi ×ˢ Set.Icc (-Z) Z :=
    Set.prod_mono (Set.Icc_subset_Icc hlo le_rfl) hzsub
  have hF : IntegrableOn F K := (h.1 hi Z).1.mono_set hsub
  have hFz : IntegrableOn Fz K := (h.1 hi Z).2.1.mono_set hsub
  have hg : ContinuousOn (fun p : ℝ × ℝ => (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) K := by
    fun_prop
  have h1 : IntegrableOn (fun p => (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p) K :=
    hF.const_mul _
  have h2 : IntegrableOn (fun p => (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p) K :=
    IntegrableOn.continuousOn_mul hg hFz hK
  have h34 : IntegrableOn (fun p => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p) K ∧
      IntegrableOn (fun p => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p) K := by
    rcases hpos with hlo' | horr
    · have hsub' : K ⊆ Set.Icc lo hi ×ˢ Set.Icc (-Z) Z := Set.prod_mono le_rfl hzsub
      have hFr : IntegrableOn Fr K := (h.2.1 lo hi Z hlo').1.mono_set hsub'
      have hFrz : IntegrableOn Frz K := (h.2.1 lo hi Z hlo').2.mono_set hsub'
      refine ⟨IntegrableOn.continuousOn_mul ?_ hFr hK, IntegrableOn.continuousOn_mul ?_ hFrz hK⟩ <;> fun_prop
    · subst horr
      have hFr : IntegrableOn (fun p => (p.1 : ℂ) * Fr p) K := (h.1 hi Z).2.2.1.mono_set hsub
      have hFrz : IntegrableOn (fun p => (p.1 : ℂ) * Frz p) K := (h.1 hi Z).2.2.2.mono_set hsub
      constructor
      · have e : (fun p : ℝ × ℝ => (((p.1 - 0) / (cr - 0) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p) =
            fun p => ((((1 / cr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ)) * ((p.1 : ℂ) * Fr p) := by
          funext p; push_cast; ring
        rw [e]; exact hFr.const_mul _
      · have e : (fun p : ℝ × ℝ => (((p.1 - 0) / (cr - 0) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p) =
            fun p => ((((1 / cr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) * ((p.1 : ℂ) * Frz p) := by
          funext p; push_cast; ring
        rw [e]
        exact IntegrableOn.continuousOn_mul (by fun_prop) hFrz hK
  exact ((h1.add h2).add h34.1).add h34.2

private theorem cornerMoment_radial_move {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr a b cz oz : ℝ} (ha : 0 ≤ a) (hac : a < cr) (hcb : cr < b) (hz : oz ≠ cz) :
    cornerMoment cr a cz oz F Fr Fz Frz = cornerMoment cr b cz oz F Fr Fz Frz := by
  have hz0 := radial_tent_zero h ha hac hcb hz
  set J := Set.Icc (min cz oz) (max cz oz) with hJ
  have hsplit : Set.Icc a b ×ˢ J = (Set.Icc a cr ×ˢ J) ∪ (Set.Ioc cr b ×ˢ J) := by
    rw [← Set.union_prod, Set.Icc_union_Ioc_eq_Icc hac.le hcb.le]
  have hdisj : Disjoint (Set.Icc a cr ×ˢ J) (Set.Ioc cr b ×ˢ J) :=
    Set.disjoint_left.2 fun p h1 h2 => (not_lt.2 h1.1.2) h2.1.1
  have hm1 : MeasurableSet (Set.Icc a cr ×ˢ J) := measurableSet_Icc.prod measurableSet_Icc
  have hm2 : MeasurableSet (Set.Ioc cr b ×ˢ J) := measurableSet_Ioc.prod measurableSet_Icc
  have eq1 : Set.EqOn (fun p : ℝ × ℝ => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p)
      (cornerTerm cr a cz oz F Fr Fz Frz) (Set.Icc a cr ×ˢ J) := by
    intro p hp
    simp only [if_pos hp.1.2]
  have eq2 : Set.EqOn (fun p : ℝ × ℝ => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p)
      (cornerTerm cr b cz oz F Fr Fz Frz) (Set.Ioc cr b ×ˢ J) := by
    intro p hp
    simp only [if_neg (not_le.2 hp.1.1)]
  have i1 : IntegrableOn (cornerTerm cr a cz oz F Fr Fz Frz) (Set.Icc a cr ×ˢ J) := by
    rcases eq_or_lt_of_le ha with h0 | h0
    · exact cornerTerm_integrableOn h ha (Or.inr h0.symm)
    · exact cornerTerm_integrableOn h ha (Or.inl h0)
  have i2' : IntegrableOn (cornerTerm cr b cz oz F Fr Fz Frz) (Set.Icc cr b ×ˢ J) :=
    cornerTerm_integrableOn h (by linarith) (Or.inl (by linarith))
  have i2 : IntegrableOn (cornerTerm cr b cz oz F Fr Fz Frz) (Set.Ioc cr b ×ˢ J) :=
    i2'.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self le_rfl)
  rw [hsplit, setIntegral_union hdisj hm2 (i1.congr_fun eq1.symm hm1) (i2.congr_fun eq2.symm hm2),
    setIntegral_congr_fun hm1 eq1, setIntegral_congr_fun hm2 eq2] at hz0
  have hset : (Set.Ioc cr b ×ˢ J : Set (ℝ × ℝ)) =ᵐ[volume] (Set.Icc cr b ×ˢ J : Set (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (Filter.EventuallyEq.refl _ _)
  rw [setIntegral_congr_set hset] at hz0
  rw [cornerMoment_eq_term, cornerMoment_eq_term, min_eq_right hac.le, max_eq_left hac.le,
    min_eq_left hcb.le, max_eq_right hcb.le]
  have s1 : edgeSign cr a = 1 := if_pos hac
  have s2 : edgeSign cr b = -1 := if_neg (not_lt.2 hcb.le)
  rw [s1, s2]
  linear_combination edgeSign cz oz * hz0

private theorem cornerMoment_height_move {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr orr cz a b : ℝ} (hcr : 0 < cr) (hr : 0 ≤ min cr orr) (hrc : orr ≠ cr) (hac : a < cz) (hcb : cz < b) :
    cornerMoment cr orr cz a F Fr Fz Frz = cornerMoment cr orr cz b F Fr Fz Frz := by
  have hz0 := height_tent_zero h hcr hr hrc hac hcb
  set R := Set.Icc (min cr orr) (max cr orr) with hR
  have hsplit : R ×ˢ Set.Icc a b = (R ×ˢ Set.Icc a cz) ∪ (R ×ˢ Set.Ioc cz b) := by
    rw [← Set.prod_union, Set.Icc_union_Ioc_eq_Icc hac.le hcb.le]
  have hdisj : Disjoint (R ×ˢ Set.Icc a cz) (R ×ˢ Set.Ioc cz b) :=
    Set.disjoint_left.2 fun p h1 h2 => (not_lt.2 h1.2.2) h2.2.1
  have hm1 : MeasurableSet (R ×ˢ Set.Icc a cz) := measurableSet_Icc.prod measurableSet_Icc
  have hm2 : MeasurableSet (R ×ˢ Set.Ioc cz b) := measurableSet_Icc.prod measurableSet_Ioc
  have eq1 : Set.EqOn (fun p : ℝ × ℝ => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p)
      (cornerTerm cr orr cz a F Fr Fz Frz) (R ×ˢ Set.Icc a cz) := by
    intro p hp
    simp only [if_pos hp.2.2]
  have eq2 : Set.EqOn (fun p : ℝ × ℝ => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p)
      (cornerTerm cr orr cz b F Fr Fz Frz) (R ×ˢ Set.Ioc cz b) := by
    intro p hp
    simp only [if_neg (not_le.2 hp.2.1)]
  have hpos : 0 < min cr orr ∨ orr = 0 := by
    rcases lt_or_gt_of_ne hrc with hlt | hgt
    · rw [min_eq_right hlt.le]
      rcases eq_or_lt_of_le (le_trans hr (min_le_right _ _)) with h0 | h0
      · exact Or.inr h0.symm
      · exact Or.inl h0
    · exact Or.inl (by rw [min_eq_left hgt.le]; exact hcr)
  have i1 : IntegrableOn (cornerTerm cr orr cz a F Fr Fz Frz) (R ×ˢ Set.Icc a cz) :=
    cornerTerm_integrableOn h hr hpos
  have i2' : IntegrableOn (cornerTerm cr orr cz b F Fr Fz Frz) (R ×ˢ Set.Icc cz b) :=
    cornerTerm_integrableOn h hr hpos
  have i2 : IntegrableOn (cornerTerm cr orr cz b F Fr Fz Frz) (R ×ˢ Set.Ioc cz b) :=
    i2'.mono_set (Set.prod_mono le_rfl Set.Ioc_subset_Icc_self)
  rw [hsplit, setIntegral_union hdisj hm2 (i1.congr_fun eq1.symm hm1) (i2.congr_fun eq2.symm hm2),
    setIntegral_congr_fun hm1 eq1, setIntegral_congr_fun hm2 eq2] at hz0
  have hset : (R ×ˢ Set.Ioc cz b : Set (ℝ × ℝ)) =ᵐ[volume] (R ×ˢ Set.Icc cz b : Set (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) Ioc_ae_eq_Icc
  rw [setIntegral_congr_set hset] at hz0
  rw [cornerMoment_eq_term, cornerMoment_eq_term, min_eq_right hac.le, max_eq_left hac.le,
    min_eq_left hcb.le, max_eq_right hcb.le]
  have s1 : edgeSign cz a = 1 := if_pos hac
  have s2 : edgeSign cz b = -1 := if_neg (not_lt.2 hcb.le)
  rw [s1, s2]
  linear_combination edgeSign cr orr * hz0

private theorem corner_normal {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz) {cr cz o oz : ℝ}
    (hcr : 0 < cr) (ho : 0 ≤ min cr o) (hoc : o ≠ cr) (hoz : oz ≠ cz) :
    cornerMoment cr o cz oz F Fr Fz Frz = cornerMoment cr (cr + 1) cz (cz + 1) F Fr Fz Frz := by
  have hr : cornerMoment cr o cz oz F Fr Fz Frz = cornerMoment cr (cr + 1) cz oz F Fr Fz Frz := by
    rcases lt_or_gt_of_ne hoc with hlt | hgt
    · exact cornerMoment_radial_move h (le_trans ho (min_le_right _ _)) hlt (by linarith) hoz
    · rw [← cornerMoment_radial_move h (a := cr / 2) (b := o) (by linarith) (by linarith) hgt hoz]
      exact cornerMoment_radial_move h (by linarith) (by linarith) (by linarith) hoz
  rw [hr]
  have hm : 0 ≤ min cr (cr + 1) := le_min hcr.le (by linarith)
  have hne : cr + 1 ≠ cr := by linarith
  rcases lt_or_gt_of_ne hoz with hlt | hgt
  · exact cornerMoment_height_move h hcr hm hne hlt (by linarith)
  · rw [← cornerMoment_height_move h (a := cz - 1) (b := oz) hcr hm hne (by linarith) hgt]
    exact cornerMoment_height_move h hcr hm hne (by linarith) (by linarith)

theorem cornerIndependence_holds : CornerIndependenceStatement := by
  intro k N c x hx L hL n cr cz orr oz orr' oz' hcr h1 h2 h3 h4 hm hm' a
  have hq := modes_mixedWeak c x hx L hL n a
  have hcr0 : 0 < cr := lt_of_le_of_ne (le_trans hm (min_le_left _ _)) (Ne.symm hcr)
  rw [corner_normal hq hcr0 hm h1 h2, corner_normal hq hcr0 hm' h3 h4]

end Breakdown.CellCert.CellFormula

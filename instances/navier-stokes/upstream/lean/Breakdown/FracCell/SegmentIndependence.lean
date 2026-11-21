import Breakdown.FracCell.SegmentIndependenceParts

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

private theorem indep_of_tent {M : ℝ → ℂ} {Q : ℝ → Prop} {c o o' : ℝ}
    (htent : ∀ l u, Q l → l < c → c < u → M l = M u) (hlow : ∃ l, Q l ∧ l < c)
    (ho : o ≠ c) (ho' : o' ≠ c) (hQo : o < c → Q o) (hQo' : o' < c → Q o') : M o = M o' := by
  rcases lt_or_gt_of_ne ho with h1 | h1 <;> rcases lt_or_gt_of_ne ho' with h2 | h2
  · rw [htent o (c + 1) (hQo h1) h1 (by linarith), htent o' (c + 1) (hQo' h2) h2 (by linarith)]
  · exact htent o o' (hQo h1) h1 h2
  · exact (htent o' o (hQo' h2) h2 h1).symm
  · obtain ⟨l, hl, hlc⟩ := hlow
    rw [← htent l o hl hlc h1, htent l o' hl hlc h2]

private theorem box_sub {a b lo hi R : ℝ} (ha : R ≤ a) :
    Set.Icc a b ×ˢ Set.Icc lo hi ⊆ Set.Icc R b ×ˢ Set.Icc (-(|lo| + |hi|)) (|lo| + |hi|) := by
  intro p hp
  simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
  refine ⟨⟨by linarith [hp.1.1], hp.1.2⟩, ?_, ?_⟩ <;> cases abs_cases lo <;> cases abs_cases hi <;>
    linarith [hp.2.1, hp.2.2]

private theorem radialTerm_integrableOn {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {t : ℝ → ℝ}
    (ht : Continuous t) {c o a b lo hi : ℝ} (ha : 0 ≤ a) (hao : 0 < a ∨ o = 0) :
    IntegrableOn (radialStripTerm c o F dF t) (Set.Icc a b ×ˢ Set.Icc lo hi) := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  have hF : IntegrableOn F (Set.Icc a b ×ˢ Set.Icc lo hi) := ((h.1 b (|lo| + |hi|)).1).mono_set (box_sub ha)
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc a b ×ˢ Set.Icc lo hi) := by
    rcases hao with ha' | ho
    · have h3 : IntegrableOn dF (Set.Icc a b ×ˢ Set.Icc lo hi) :=
        (h.2.1 a b (|lo| + |hi|) ha').mono_set (box_sub le_rfl)
      exact h3.continuousOn_mul (by fun_prop) hK
    · subst ho
      have h2 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Set.Icc a b ×ˢ Set.Icc lo hi) :=
        ((h.1 b (|lo| + |hi|)).2).mono_set (box_sub ha)
      have h3 : IntegrableOn (fun p : ℝ × ℝ => (((1 / c : ℝ)) : ℂ) * ((p.1 : ℂ) * dF p))
          (Set.Icc a b ×ˢ Set.Icc lo hi) := h2.const_mul _
      refine h3.congr_fun ?_ (measurableSet_Icc.prod measurableSet_Icc)
      intro p _
      push_cast
      ring
  have hsum : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc a b ×ˢ Set.Icc lo hi) := (hF.const_mul _).add hdF
  exact hsum.mul_continuousOn (g' := fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) (by fun_prop) hK

private theorem radialStrip_tent {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {lo hi l m u : ℝ}
    {t : ℝ → ℝ} (ht : Continuous t) (hl : 0 ≤ l) (hlm : l < m) (hmu : m < u) :
    radialStripMoment m l lo hi F dF t = radialStripMoment m u lo hi F dF t := by
  have hm : 0 < m := by linarith
  have e1 : radialStripMoment m l lo hi F dF t =
      ∫ p in Set.Icc l m ×ˢ Set.Icc lo hi, radialStripTerm m l F dF t p := by
    simp only [radialStripMoment, edgeSign, if_pos hlm, min_eq_right hlm.le, max_eq_left hlm.le, one_mul]
    rfl
  have e2 : radialStripMoment m u lo hi F dF t =
      -∫ p in Set.Icc m u ×ˢ Set.Icc lo hi, radialStripTerm m u F dF t p := by
    simp only [radialStripMoment, edgeSign, if_neg (not_lt.mpr hmu.le), min_eq_left hmu.le,
      max_eq_right hmu.le, neg_one_mul]
    rfl
  have hI1 : IntegrableOn (radialStripTerm m l F dF t) (Set.Icc l m ×ˢ Set.Icc lo hi) :=
    radialTerm_integrableOn h ht hl (by
      rcases hl.lt_or_eq with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.symm)
  have hI2 : IntegrableOn (radialStripTerm m u F dF t) (Set.Icc m u ×ˢ Set.Icc lo hi) :=
    radialTerm_integrableOn h ht hm.le (Or.inl hm)
  have hset : Set.Icc l u ×ˢ Set.Icc lo hi = Set.Icc l m ×ˢ Set.Icc lo hi ∪ Set.Ioc m u ×ˢ Set.Icc lo hi := by
    rw [← Set.union_prod, Set.Icc_union_Ioc_eq_Icc hlm.le hmu.le]
  have hdisj : Disjoint (Set.Icc l m ×ˢ Set.Icc lo hi) (Set.Ioc m u ×ˢ Set.Icc lo hi) := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨_, h1⟩, _⟩ ⟨⟨h2, _⟩, _⟩
    linarith
  have hae : (Set.Ioc m u ×ˢ Set.Icc lo hi : Set (ℝ × ℝ)) =ᵐ[volume] Set.Icc m u ×ˢ Set.Icc lo hi := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (ae_eq_refl _)
  have eq1 : Set.EqOn (fun p : ℝ × ℝ => if p.1 ≤ m then radialStripTerm m l F dF t p else radialStripTerm m u F dF t p)
      (radialStripTerm m l F dF t) (Set.Icc l m ×ˢ Set.Icc lo hi) := by
    intro p hp
    simp only [if_pos hp.1.2]
  have eq2 : Set.EqOn (fun p : ℝ × ℝ => if p.1 ≤ m then radialStripTerm m l F dF t p else radialStripTerm m u F dF t p)
      (radialStripTerm m u F dF t) (Set.Ioc m u ×ˢ Set.Icc lo hi) := by
    intro p hp
    simp only [if_neg (not_le.mpr hp.1.1)]
  have hmeas1 : MeasurableSet (Set.Icc l m ×ˢ Set.Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  have hmeas2 : MeasurableSet (Set.Ioc m u ×ˢ Set.Icc lo hi) := measurableSet_Ioc.prod measurableSet_Icc
  have hI2' : IntegrableOn (radialStripTerm m u F dF t) (Set.Ioc m u ×ˢ Set.Icc lo hi) :=
    hI2.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self le_rfl)
  have key := radialStrip_tent_zero h ht hl hlm hmu (lo := lo) (hi := hi)
  rw [hset, setIntegral_union hdisj hmeas2 (hI1.congr_fun eq1.symm hmeas1) (hI2'.congr_fun eq2.symm hmeas2),
    setIntegral_congr_fun hmeas1 eq1, setIntegral_congr_fun hmeas2 eq2, setIntegral_congr_set hae] at key
  rw [e1, e2]
  linear_combination key

private theorem heightTerm_integrableOn {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF)
    {t : ℝ → ℝ} (ht : Continuous t) {c o a b lo hi : ℝ} :
    IntegrableOn (heightStripTerm c o wt F dF t) (Set.Icc lo hi ×ˢ Set.Icc a b) := by
  have hK : IsCompact (Set.Icc lo hi ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hsub : Set.Icc lo hi ×ˢ Set.Icc a b ⊆
      Set.Icc (-(|lo| + |hi|)) (|lo| + |hi|) ×ˢ Set.Icc (-(|a| + |b|)) (|a| + |b|) := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> cases abs_cases lo <;> cases abs_cases hi <;> cases abs_cases a <;>
      cases abs_cases b <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hF := ((h.1 (|lo| + |hi|) (|a| + |b|)).1).mono_set hsub
  have hdF := ((h.1 (|lo| + |hi|) (|a| + |b|)).2).mono_set hsub
  have h1 := hF.mul_continuousOn (g' := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * ((t p.1 : ℝ) : ℂ)))
    (by fun_prop) hK
  have h2 := hdF.mul_continuousOn (g' := fun p : ℝ × ℝ => ((((p.2 - o) / (c - o) : ℝ)) : ℂ) * ((t p.1 : ℝ) : ℂ))
    (by fun_prop) hK
  refine (h1.add h2).congr_fun ?_ hK.measurableSet
  intro p _
  simp only [heightStripTerm, Pi.add_apply]
  push_cast
  ring

private theorem heightStrip_tent {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF)
    (hwt : Continuous wt) {lo hi l m u : ℝ} {t : ℝ → ℝ} (ht : Continuous t) (hlm : l < m) (hmu : m < u) :
    heightStripMoment m l lo hi wt F dF t = heightStripMoment m u lo hi wt F dF t := by
  have e1 : heightStripMoment m l lo hi wt F dF t =
      ∫ p in Set.Icc lo hi ×ˢ Set.Icc l m, heightStripTerm m l wt F dF t p := by
    simp only [heightStripMoment, edgeSign, if_pos hlm, min_eq_right hlm.le, max_eq_left hlm.le, one_mul]
    rfl
  have e2 : heightStripMoment m u lo hi wt F dF t =
      -∫ p in Set.Icc lo hi ×ˢ Set.Icc m u, heightStripTerm m u wt F dF t p := by
    simp only [heightStripMoment, edgeSign, if_neg (not_lt.mpr hmu.le), min_eq_left hmu.le,
      max_eq_right hmu.le, neg_one_mul]
    rfl
  have hI1 : IntegrableOn (heightStripTerm m l wt F dF t) (Set.Icc lo hi ×ˢ Set.Icc l m) :=
    heightTerm_integrableOn h ht
  have hI2 : IntegrableOn (heightStripTerm m u wt F dF t) (Set.Icc lo hi ×ˢ Set.Icc m u) :=
    heightTerm_integrableOn h ht
  have hset : Set.Icc lo hi ×ˢ Set.Icc l u = Set.Icc lo hi ×ˢ Set.Icc l m ∪ Set.Icc lo hi ×ˢ Set.Ioc m u := by
    rw [← Set.prod_union, Set.Icc_union_Ioc_eq_Icc hlm.le hmu.le]
  have hdisj : Disjoint (Set.Icc lo hi ×ˢ Set.Icc l m) (Set.Icc lo hi ×ˢ Set.Ioc m u) := by
    rw [Set.disjoint_left]
    rintro p ⟨_, ⟨_, h1⟩⟩ ⟨_, ⟨h2, _⟩⟩
    linarith
  have hae : (Set.Icc lo hi ×ˢ Set.Ioc m u : Set (ℝ × ℝ)) =ᵐ[volume] Set.Icc lo hi ×ˢ Set.Icc m u := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ioc_ae_eq_Icc
  have eq1 : Set.EqOn (fun p : ℝ × ℝ => if p.2 ≤ m then heightStripTerm m l wt F dF t p
      else heightStripTerm m u wt F dF t p) (heightStripTerm m l wt F dF t) (Set.Icc lo hi ×ˢ Set.Icc l m) := by
    intro p hp
    simp only [if_pos hp.2.2]
  have eq2 : Set.EqOn (fun p : ℝ × ℝ => if p.2 ≤ m then heightStripTerm m l wt F dF t p
      else heightStripTerm m u wt F dF t p) (heightStripTerm m u wt F dF t) (Set.Icc lo hi ×ˢ Set.Ioc m u) := by
    intro p hp
    simp only [if_neg (not_le.mpr hp.2.1)]
  have hmeas1 : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc l m) := measurableSet_Icc.prod measurableSet_Icc
  have hmeas2 : MeasurableSet (Set.Icc lo hi ×ˢ Set.Ioc m u) := measurableSet_Icc.prod measurableSet_Ioc
  have hI2' : IntegrableOn (heightStripTerm m u wt F dF t) (Set.Icc lo hi ×ˢ Set.Ioc m u) :=
    hI2.mono_set (Set.prod_mono le_rfl Set.Ioc_subset_Icc_self)
  have key := heightStrip_tent_zero h hwt ht hlm hmu (lo := lo) (hi := hi)
  rw [hset, setIntegral_union hdisj hmeas2 (hI1.congr_fun eq1.symm hmeas1) (hI2'.congr_fun eq2.symm hmeas2),
    setIntegral_congr_fun hmeas1 eq1, setIntegral_congr_fun hmeas2 eq2, setIntegral_congr_set hae] at key
  rw [e1, e2]
  linear_combination key

private theorem test_continuous (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

private theorem moment_other_indep (S S' : FaceSegment) (hr : S.radial = S'.radial) (hl : S.level = S'.level)
    (hlo : S.lo = S'.lo) (hhi : S.hi = S'.hi) (htc : S.testCoef = S'.testCoef)
    (ho : S.other ≠ S.level) (ho' : S'.other ≠ S'.level)
    (hpos : S.radial → S.level ≠ 0 ∧ 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other)
    (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (d : ℕ)
    (hrad : S.radial → IsRadialWeakPair F dFr)
    (hhgt : ¬ S.radial → IsHeightWeakPair (fun r => if weighted then r else 1) F dFz) :
    S.moment weighted F dFr dFz d = S'.moment weighted F dFr dFz d := by
  have htest : S'.test d = S.test d := by
    unfold FaceSegment.test
    rw [htc]
  have ho'' : S'.other ≠ S.level := by rw [hl]; exact ho'
  unfold FaceSegment.moment
  rw [← hr, ← hl, ← hlo, ← hhi, htest]
  by_cases h : S.radial
  · simp only [h, if_true]
    obtain ⟨hne, h0, h0'⟩ := hpos h
    have hc : 0 < S.level := lt_of_le_of_ne (le_min_iff.mp h0).1 (Ne.symm hne)
    refine indep_of_tent (M := fun o => radialStripMoment S.level o S.lo S.hi F dFr (S.test d))
      (Q := fun l => 0 ≤ l) ?_ ⟨0, le_rfl, hc⟩ ho ho'' (fun _ => (le_min_iff.mp h0).2) ?_
    · intro l u hl' hlc hcu
      exact radialStrip_tent (hrad h) (test_continuous S d) hl' hlc hcu
    · intro _
      rw [← hl] at h0'
      exact (le_min_iff.mp h0').2
  · simp only [h]
    have hwt : Continuous (fun r : ℝ => if weighted then r else 1) := by
      cases weighted
      · simpa using continuous_const
      · simpa using continuous_id'
    refine indep_of_tent (M := fun o => heightStripMoment S.level o S.lo S.hi
      (fun r => if weighted then r else 1) F dFz (S.test d))
      (Q := fun _ => True) ?_ ⟨S.level - 1, trivial, by linarith⟩ ho ho'' (fun _ => trivial) (fun _ => trivial)
    intro l u _ hlc hcu
    exact heightStrip_tent (hhgt h) hwt (test_continuous S d) hlc hcu

theorem segmentIndependence_holds : SegmentIndependenceStatement := by
  intro k N c x hx L hL n S S' hS hS' hr hl hlo hhi htc hne hpos a d
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := segment_modes_weak c x hx L hL n a
  have hpos' : S.radial → S.level ≠ 0 ∧ 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other :=
    fun h => ⟨hne h, hpos h⟩
  refine ⟨?_, ?_, ?_⟩
  · exact moment_other_indep S S' hr hl hlo hhi htc hS.other_ne hS'.other_ne hpos' false _ _ _ d
      (fun _ => h1) (fun _ => by simpa using h2)
  · rw [← hr]
    by_cases h : S.radial
    · simp only [h, if_true]
      exact moment_other_indep S S' hr hl hlo hhi htc hS.other_ne hS'.other_ne hpos' true _ _ _ d
        (fun _ => h3) (fun h' => absurd h h')
    · simp only [h]
      exact moment_other_indep S S' hr hl hlo hhi htc hS.other_ne hS'.other_ne hpos' true _ _ _ d
        (fun h' => absurd h' h) (fun _ => by simpa using h4)
  · exact moment_other_indep S S' hr hl hlo hhi htc hS.other_ne hS'.other_ne hpos' true _ _ _ d
      (fun _ => h5) (fun _ => by simpa using h6)

end Breakdown.CellCert.CellFormula

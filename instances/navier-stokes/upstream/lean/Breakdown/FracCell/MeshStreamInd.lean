import Breakdown.FracCell.MeshDefs
import Breakdown.FracCell.SegmentIndependenceParts

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshStreamInd

theorem weightedPair_of_unit {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun _ => 1) F dF) :
    IsHeightWeakPair (fun r => r) F dF := by
  refine ⟨fun R Z => ?_, h.2.1, h.2.2⟩
  have hK : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨h1, h2⟩ := h.1 R Z
  simp only [Complex.ofReal_one, one_mul] at h1 h2
  refine ⟨?_, ?_⟩
  · have := h1.continuousOn_mul (g := fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) (by fun_prop) hK
    exact this
  · have := h2.continuousOn_mul (g := fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) (by fun_prop) hK
    exact this

theorem term_integrableOn {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF)
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

theorem strip_tent {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF)
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
    term_integrableOn h ht
  have hI2 : IntegrableOn (heightStripTerm m u wt F dF t) (Set.Icc lo hi ×ˢ Set.Ioc m u) :=
    (term_integrableOn h ht).mono_set (Set.prod_mono le_rfl Set.Ioc_subset_Icc_self)
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
  have key := heightStrip_tent_zero h hwt ht hlm hmu (lo := lo) (hi := hi)
  rw [hset, setIntegral_union hdisj hmeas2 (hI1.congr_fun eq1.symm hmeas1) (hI2.congr_fun eq2.symm hmeas2),
    setIntegral_congr_fun hmeas1 eq1, setIntegral_congr_fun hmeas2 eq2, setIntegral_congr_set hae] at key
  rw [e1, e2]
  linear_combination key

theorem other_indep {M : ℝ → ℂ} {c o o' : ℝ} (htent : ∀ l u, l < c → c < u → M l = M u)
    (ho : o ≠ c) (ho' : o' ≠ c) : M o = M o' := by
  rcases lt_or_gt_of_ne ho with h1 | h1 <;> rcases lt_or_gt_of_ne ho' with h2 | h2
  · rw [htent o (c + 1) h1 (by linarith), htent o' (c + 1) h2 (by linarith)]
  · exact htent o o' h1 h2
  · exact (htent o' o h2 h1).symm
  · rw [← htent (c - 1) o (by linarith) h1, htent (c - 1) o' (by linarith) h2]

end MeshStreamInd

open MeshStreamInd in
theorem streamIndependence_holds : StreamIndependenceStatement := by
  intro k N c x hx L hL cr cz oz oz' _ hoz hoz'
  have hw : IsHeightWeakPair (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) :=
    weightedPair_of_unit (segment_modes_weak c x hx L hL 0 2).2.1
  refine other_indep (M := fun o => heightStripMoment cz o 0 cr (fun r => r) (L.velMode 0 x 2)
    (L.gradModeOf 0 x 2 2) (fun _ => 1)) ?_ hoz hoz'
  intro l u hl hu
  exact strip_tent hw continuous_id continuous_const hl hu

end Breakdown.CellCert.CellCoordinates

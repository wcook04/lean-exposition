import Breakdown.FracCell.StMesh
import Breakdown.FracCell.SegmentIndependenceParts
import Breakdown.FracCell.MeshStreamInd

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshFluxHeight

private theorem term_integrable {F dF : ℝ × ℝ → ℂ}
    (hF : ∀ R Z : ℝ, IntegrableOn F (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z))
    (hdF : ∀ R Z : ℝ, IntegrableOn dF (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z))
    {wt t : ℝ → ℝ} (hwt : Continuous wt) (ht : Continuous t) (c o lo hi a b : ℝ) :
    IntegrableOn (heightStripTerm c o wt F dF t) (Set.Icc lo hi ×ˢ Set.Icc a b) := by
  have hK : IsCompact (Set.Icc lo hi ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hsub : Set.Icc lo hi ×ˢ Set.Icc a b ⊆
      Set.Icc (-(|lo| + |hi|)) (|lo| + |hi|) ×ˢ Set.Icc (-(|a| + |b|)) (|a| + |b|) := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> cases abs_cases lo <;> cases abs_cases hi <;> cases abs_cases a <;>
      cases abs_cases b <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have h1 := ((hF _ _).mono_set hsub).mul_continuousOn
    (g' := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * ((wt p.1 * t p.1 : ℝ) : ℂ))) (by fun_prop) hK
  have h2 := ((hdF _ _).mono_set hsub).mul_continuousOn
    (g' := fun p : ℝ × ℝ => ((((p.2 - o) / (c - o) : ℝ)) : ℂ) * ((wt p.1 * t p.1 : ℝ) : ℂ)) (by fun_prop) hK
  refine (h1.add h2).congr_fun ?_ hK.measurableSet
  intro p _
  simp only [heightStripTerm, Pi.add_apply]
  ring

private theorem strip_split {c o l m u : ℝ} {wt t : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ}
    (hint : ∀ a b, IntegrableOn (heightStripTerm c o wt F dF t) (Set.Icc a b ×ˢ Set.Icc (min c o) (max c o)))
    (hlm : l ≤ m) (hmu : m ≤ u) :
    heightStripMoment c o l u wt F dF t =
      heightStripMoment c o l m wt F dF t + heightStripMoment c o m u wt F dF t := by
  have e : ∀ a b, heightStripMoment c o a b wt F dF t = edgeSign c o *
      ∫ p in Set.Icc a b ×ˢ Set.Icc (min c o) (max c o), heightStripTerm c o wt F dF t p := fun _ _ => rfl
  rw [e, e, e, ← mul_add]
  congr 1
  have hset : Set.Icc l u ×ˢ Set.Icc (min c o) (max c o) =
      Set.Icc l m ×ˢ Set.Icc (min c o) (max c o) ∪ Set.Ioc m u ×ˢ Set.Icc (min c o) (max c o) := by
    rw [← Set.union_prod, Set.Icc_union_Ioc_eq_Icc hlm hmu]
  have hdisj : Disjoint (Set.Icc l m ×ˢ Set.Icc (min c o) (max c o))
      (Set.Ioc m u ×ˢ Set.Icc (min c o) (max c o)) := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨_, h1⟩, _⟩ ⟨⟨h2, _⟩, _⟩
    linarith
  have hae : (Set.Ioc m u ×ˢ Set.Icc (min c o) (max c o) : Set (ℝ × ℝ)) =ᵐ[volume]
      Set.Icc m u ×ˢ Set.Icc (min c o) (max c o) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (ae_eq_refl _)
  rw [hset, setIntegral_union hdisj (measurableSet_Ioc.prod measurableSet_Icc) (hint l m)
    ((hint m u).mono_set (Set.prod_mono Set.Ioc_subset_Icc_self le_rfl)), setIntegral_congr_set hae]

private theorem strip_point {c o a : ℝ} {wt t : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ}
    (hint : ∀ a b, IntegrableOn (heightStripTerm c o wt F dF t) (Set.Icc a b ×ˢ Set.Icc (min c o) (max c o))) :
    heightStripMoment c o a a wt F dF t = 0 := by
  have h := strip_split (l := a) (m := a) (u := a) hint le_rfl le_rfl
  linear_combination -h

private theorem combine (G : ℂ) (a b r c0 c1 : ℝ) (h : r = c0 * a + c1 * b) :
    (c0 : ℂ) * (G * ((1 * a : ℝ) : ℂ)) + (c1 : ℂ) * (G * ((1 * b : ℝ) : ℂ)) = G * ((r * 1 : ℝ) : ℂ) := by
  subst h
  push_cast
  ring

theorem fluxHeight_of (hSI : StreamIndependenceStatement) : FluxHeightStatement := by
  intro k N c x hx L hL S hS o o' hrad hlo ho ho' c0 c1 hc
  have hw := (segment_modes_weak c x hx L hL 0 2).2.1
  have hF : ∀ R Z : ℝ, IntegrableOn (L.velMode 0 x 2) (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z) :=
    fun R Z => by simpa using (hw.1 R Z).1
  have hdF : ∀ R Z : ℝ, IntegrableOn (L.gradModeOf 0 x 2 2) (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z) :=
    fun R Z => by simpa using (hw.1 R Z).2
  have hint : ∀ {wt t : ℝ → ℝ}, Continuous wt → Continuous t → ∀ a b,
      IntegrableOn (heightStripTerm S.level S.other wt (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) t)
        (Set.Icc a b ×ˢ Set.Icc (min S.level S.other) (max S.level S.other)) :=
    fun hwt ht a b => term_integrable hF hdF hwt ht _ _ _ _ _ _
  have hint1 := hint (wt := fun r => r) (t := fun _ => 1) continuous_id continuous_const
  have hhi : 0 < S.hi := lt_of_le_of_lt hlo hS.lo_lt_hi
  have eHi : streamValue L x S.hi S.level o = heightStripMoment S.level S.other 0 S.hi (fun r => r)
      (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1) := hSI c x hx L hL S.hi S.level o S.other hhi ho hS.other_ne
  have eLo : streamValue L x S.lo S.level o' = heightStripMoment S.level S.other 0 S.lo (fun r => r)
      (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1) := by
    rcases hlo.lt_or_eq with h | h
    · exact hSI c x hx L hL S.lo S.level o' S.other h ho' hS.other_ne
    · rw [← h]
      have hint2 := fun a b => term_integrable (c := S.level) (o := o') (lo := a) (hi := b)
        (a := min S.level o') (b := max S.level o') hF hdF (wt := fun r => r) (t := fun _ => 1)
        continuous_id continuous_const
      exact (strip_point hint2).trans (strip_point hint1).symm
  rw [eHi, eLo, strip_split hint1 hlo hS.lo_lt_hi.le, add_sub_cancel_left]
  simp only [FaceSegment.moment, hrad, Bool.false_eq_true, if_false]
  have e : ∀ (wt t : ℝ → ℝ), heightStripMoment S.level S.other S.lo S.hi wt (L.velMode 0 x 2)
      (L.gradModeOf 0 x 2 2) t = edgeSign S.level S.other *
      ∫ p in Set.Icc S.lo S.hi ×ˢ Set.Icc (min S.level S.other) (max S.level S.other),
        heightStripTerm S.level S.other wt (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) t p := fun _ _ => rfl
  have htc : ∀ d, Continuous (S.test d) := fun d => by
    unfold FaceSegment.test
    fun_prop
  have I0 := hint (wt := fun _ => 1) (t := S.test 0) continuous_const (htc 0) S.lo S.hi
  have I1 := hint (wt := fun _ => 1) (t := S.test 1) continuous_const (htc 1) S.lo S.hi
  have key : (c0 : ℂ) * (∫ p in Set.Icc S.lo S.hi ×ˢ Set.Icc (min S.level S.other) (max S.level S.other),
        heightStripTerm S.level S.other (fun _ => 1) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (S.test 0) p)
      + (c1 : ℂ) * (∫ p in Set.Icc S.lo S.hi ×ˢ Set.Icc (min S.level S.other) (max S.level S.other),
        heightStripTerm S.level S.other (fun _ => 1) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (S.test 1) p)
      = ∫ p in Set.Icc S.lo S.hi ×ˢ Set.Icc (min S.level S.other) (max S.level S.other),
        heightStripTerm S.level S.other (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1) p := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (I0.const_mul _) (I1.const_mul _)]
    refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) ?_
    intro p hp
    simp only [heightStripTerm]
    exact combine _ _ _ _ _ _ (hc p.1 hp.1)
  rw [e, e, e, ← key]
  ring

end MeshFluxHeight

theorem fluxHeight : FluxHeightStatement := MeshFluxHeight.fluxHeight_of streamIndependence_holds

end Breakdown.CellCert.CellCoordinates

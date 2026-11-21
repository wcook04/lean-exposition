import Breakdown.CertCell.RowsMatchFlux
import Breakdown.CertCell.GaugePlaneFlipFacts
import Breakdown.CertCell.LocalRelations
import Breakdown.FracCell.SegmentModesHeight
import Breakdown.FracCell.MeshStreamInd
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates LocalField

variable {k : ℕ} {C : Type} {nE nM : ℕ}

namespace Internal.KeyFlux

variable {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem rect_integrable (hv : IsLocalSecondOrderField v G H) (m : ℕ) (r₁ r₂ z₁ z₂ : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) ∧
      IntegrableOn (gradMode m 0 G 2 2) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
  ⟨FracInternal.MeshDataAffineModes.int_rect (f := fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2)
      (fun p => FracInternal.SegmentHeight.vel_refl m 0 v 2 p)
      (fun R => (localModeStripIntegrable m v G H hv 0 R (-R) R).1 2) r₁ r₂ z₁ z₂,
    FracInternal.MeshDataAffineModes.int_rect (f := gradMode m 0 G 2 2)
      (fun p => FracInternal.SegmentHeight.grad_refl2 m 0 G 2 p)
      (fun R => (localModeStripIntegrable m v G H hv 0 R (-R) R).2 2 2) r₁ r₂ z₁ z₂⟩

theorem height_pair (hv : IsLocalSecondOrderField v G H) (m : ℕ) :
    IsHeightWeakPair (fun _ => 1) (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2) := by
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
        IntegrableOn (gradMode m 0 G 2 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z _ => ⟨(rect_integrable hv m (-R) R (-Z) Z).1.mono_set (FracInternal.SegmentHeight.box_sub δ R Z),
      (rect_integrable hv m (-R) R (-Z) Z).2.mono_set (FracInternal.SegmentHeight.box_sub δ R Z)⟩
  refine ⟨fun R Z => ⟨?_, ?_⟩, hoff,
    FracInternal.SegmentRefl.height_ident_refl (F := fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2)
      (dF := gradMode m 0 G 2 2)
      (mul_ne_zero (FracInternal.SegmentHeight.halfTurn_ne m 0) (FracInternal.SegmentHeight.sign_ne 2))
      (fun p => FracInternal.SegmentHeight.vel_refl m 0 v 2 p)
      (fun p => FracInternal.SegmentHeight.grad_refl2 m 0 G 2 p) hoff
      (fun ψ hψ hc hpos => (localModeWeakIdentity m v G H hv 0 2 ψ hψ hc hpos).2.1)⟩
  · simpa using (rect_integrable hv m (-R) R (-Z) Z).1
  · simpa using (rect_integrable hv m (-R) R (-Z) Z).2

theorem trace_indep (hv : IsLocalSecondOrderField v G H) (m : ℕ) {c o o' R : ℝ} (ho : o ≠ c) (ho' : o' ≠ c) :
    heightStripMoment c o 0 R (fun r => r) (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2)
        (fun _ => 1)
      = heightStripMoment c o' 0 R (fun r => r) (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2)
        (fun _ => 1) :=
  MeshStreamInd.other_indep (M := fun o => heightStripMoment c o 0 R (fun r => r)
      (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2) (fun _ => 1))
    (fun _ _ hl hu => MeshStreamInd.strip_tent (MeshStreamInd.weightedPair_of_unit (height_pair hv m))
      continuous_id continuous_const hl hu) ho ho'

theorem radial_const (c o lo hi a : ℝ) (F dF : ℝ × ℝ → ℂ) :
    radialStripMoment c o lo hi F dF (fun _ => a) = (a : ℂ) * radialStripMoment c o lo hi F dF (fun _ => 1) := by
  simp only [radialStripMoment, Complex.ofReal_one, mul_one]
  rw [integral_mul_const]
  ring

theorem radial_key {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (hx : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1)
    (L : CellLayout) {lev lo hi : ℝ} (t : ℕ → ℕ → ℝ) (hlev : 0 < lev) (hlh : lo < hi) :
    keyValue L x (SkeletonKey.velocity 0 true lev lo hi t 0 0)
      = -((t 0 0 / lev : ℝ) : ℂ) *
          (keyValue L x (SkeletonKey.stream (lev, hi)) - keyValue L x (SkeletonKey.stream (lev, lo))) := by
  have hf := localCylinderFlux L.order x.1 x.2.1 x.2.2.1 hx lev (lev + 1) lo hi hlev (by linarith) (by linarith) hlh
  have e1 := trace_indep hx L.order (c := hi) (o := lo) (o' := hi + 1) (R := lev) hlh.ne (by linarith)
  have e2 := trace_indep hx L.order (c := lo) (o := hi) (o' := lo + 1) (R := lev) hlh.ne' (by linarith)
  have et : (fun s : ℝ => ∑ i ∈ Finset.range (0 + 1), t 0 i * s ^ i) = fun _ => t 0 0 := by
    funext s
    simp
  show radialStripMoment lev (lev + 1) lo hi (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 0)
      (gradMode L.order 0 x.2.1 0 0) (fun s : ℝ => ∑ i ∈ Finset.range (0 + 1), t 0 i * s ^ i)
    = -((t 0 0 / lev : ℝ) : ℂ) *
      (heightStripMoment hi (hi + 1) 0 lev (fun r => r) (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2)
          (gradMode L.order 0 x.2.1 2 2) (fun _ => 1)
        - heightStripMoment lo (lo + 1) 0 lev (fun r => r) (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2)
          (gradMode L.order 0 x.2.1 2 2) (fun _ => 1))
  rw [et, radial_const, ← e1, ← e2]
  have hl : (lev : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlev.ne'
  push_cast
  field_simp
  linear_combination (t 0 0 : ℂ) * hf

theorem strip_term_eq (c o : ℝ) (wt tt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    heightStripTerm c o wt F dF tt p
      = ((wt p.1 * tt p.1 : ℝ) : ℂ) * heightStripTerm c o (fun _ => 1) F dF (fun _ => 1) p := by
  simp only [heightStripTerm]
  push_cast
  ring

theorem strip_split {c o l m u : ℝ} {wt t : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ}
    (hint : IntegrableOn (heightStripTerm c o wt F dF t) (Set.Icc l u ×ˢ Set.Icc (min c o) (max c o)))
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
  have h1 : IntegrableOn (heightStripTerm c o wt F dF t) (Set.Icc l m ×ˢ Set.Icc (min c o) (max c o)) :=
    hint.mono_set (Set.prod_mono (Set.Icc_subset_Icc le_rfl hmu) le_rfl)
  have h2 : IntegrableOn (heightStripTerm c o wt F dF t) (Set.Ioc m u ×ˢ Set.Icc (min c o) (max c o)) :=
    hint.mono_set (Set.prod_mono (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hlm le_rfl)) le_rfl)
  rw [hset, setIntegral_union hdisj (measurableSet_Ioc.prod measurableSet_Icc) h1 h2, setIntegral_congr_set hae]

theorem height_key {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (hx : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1)
    (L : CellLayout) {lev lo hi : ℝ} (t : ℕ → ℕ → ℝ) (hlo : 0 ≤ lo) (hlh : lo < hi) (h10 : t 1 0 ≠ 0) :
    keyValue L x (SkeletonKey.velocity 0 false lev lo hi t 2 0)
      = ((t 0 0 / t 1 0 : ℝ) : ℂ) * (keyValue L x (SkeletonKey.velocity 0 false lev lo hi t 2 1)
          - (t 1 1 : ℂ) * (keyValue L x (SkeletonKey.stream (hi, lev)) - keyValue L x (SkeletonKey.stream (lo, lev)))) := by
  have hp1 : IsHeightWeakPair (fun _ => 1) (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2)
      (gradMode L.order 0 x.2.1 2 2) := height_pair hx L.order
  have hpr := MeshStreamInd.weightedPair_of_unit hp1
  have ig : ∀ a b, IntegrableOn (heightStripTerm lev (lev + 1) (fun _ => 1)
      (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1))
      (Set.Icc a b ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1))) := fun a b =>
    MeshStreamInd.term_integrableOn (c := lev) (o := lev + 1) (lo := a) (hi := b) (a := min lev (lev + 1))
      (b := max lev (lev + 1)) hp1 continuous_const
  have igr : ∀ a b, IntegrableOn (heightStripTerm lev (lev + 1) (fun r => r)
      (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1))
      (Set.Icc a b ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1))) := fun a b =>
    MeshStreamInd.term_integrableOn (c := lev) (o := lev + 1) (lo := a) (hi := b) (a := min lev (lev + 1))
      (b := max lev (lev + 1)) hpr continuous_const
  have igr' : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) * heightStripTerm lev (lev + 1) (fun _ => 1)
      (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1) p)
      (Set.Icc a b ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1))) := by
    intro a b
    refine (igr a b).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    rw [strip_term_eq]
    simp
  have hm : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1))) :=
    measurableSet_Icc.prod measurableSet_Icc
  have I0 : ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
      heightStripTerm lev (lev + 1) (fun r => if false = true then r else 1)
        (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2)
        (fun s => ∑ i ∈ Finset.range (0 + 1), t 0 i * s ^ i) p
      = (t 0 0 : ℂ) * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
        heightStripTerm lev (lev + 1) (fun _ => 1)
          (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1) p := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hm (fun p _ => ?_)
    rw [strip_term_eq]
    simp
  have I1 : ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
      heightStripTerm lev (lev + 1) (fun r => if false = true then r else 1)
        (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2)
        (fun s => ∑ i ∈ Finset.range (1 + 1), t 1 i * s ^ i) p
      = (t 1 0 : ℂ) * (∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
          heightStripTerm lev (lev + 1) (fun _ => 1)
            (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1) p)
        + (t 1 1 : ℂ) * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
          ((p.1 : ℝ) : ℂ) * heightStripTerm lev (lev + 1) (fun _ => 1)
            (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1) p := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((ig lo hi).const_mul _) ((igr' lo hi).const_mul _)]
    refine setIntegral_congr_fun hm (fun p _ => ?_)
    rw [strip_term_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, mul_one]
    push_cast
    ring
  have IS : heightStripMoment lev (lev + 1) 0 hi (fun r => r)
        (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1)
      - heightStripMoment lev (lev + 1) 0 lo (fun r => r)
        (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1)
      = edgeSign lev (lev + 1) * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
          ((p.1 : ℝ) : ℂ) * heightStripTerm lev (lev + 1) (fun _ => 1)
            (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1) p := by
    rw [strip_split (igr 0 hi) hlo hlh.le, add_sub_cancel_left]
    show edgeSign lev (lev + 1) * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
      heightStripTerm lev (lev + 1) (fun r => r) (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2)
        (gradMode L.order 0 x.2.1 2 2) (fun _ => 1) p = _
    congr 1
    refine setIntegral_congr_fun hm (fun p _ => ?_)
    rw [strip_term_eq]
    simp
  show edgeSign lev (lev + 1) * (∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
      heightStripTerm lev (lev + 1) (fun r => if false = true then r else 1)
        (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2)
        (fun s => ∑ i ∈ Finset.range (0 + 1), t 0 i * s ^ i) p)
    = ((t 0 0 / t 1 0 : ℝ) : ℂ) * (edgeSign lev (lev + 1) *
        (∫ p in Set.Icc lo hi ×ˢ Set.Icc (min lev (lev + 1)) (max lev (lev + 1)),
          heightStripTerm lev (lev + 1) (fun r => if false = true then r else 1)
            (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2)
            (fun s => ∑ i ∈ Finset.range (1 + 1), t 1 i * s ^ i) p)
        - (t 1 1 : ℂ) * (heightStripMoment lev (lev + 1) 0 hi (fun r => r)
            (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1)
          - heightStripMoment lev (lev + 1) 0 lo (fun r => r)
            (fun p : ℝ × ℝ => modeVec L.order 0 x.1 p.1 p.2 2) (gradMode L.order 0 x.2.1 2 2) (fun _ => 1)))
  rw [I0, I1, IS]
  have h10' : (t 1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h10
  push_cast
  field_simp
  ring

theorem keyFlux_local {j : ℕ} (x : CellCert.Assembly.FieldTuple j)
    (hx : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1) (L : CellLayout) :
    (∀ (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ), 0 < lev → 0 ≤ lo → lo < hi →
        keyValue L x (SkeletonKey.velocity 0 true lev lo hi t 0 0)
          = -((t 0 0 / lev : ℝ) : ℂ) *
            (keyValue L x (SkeletonKey.stream (lev, hi)) - keyValue L x (SkeletonKey.stream (lev, lo)))) ∧
      (∀ (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ), 0 ≤ lo → lo < hi → t 1 0 ≠ 0 →
        keyValue L x (SkeletonKey.velocity 0 false lev lo hi t 2 0)
          = ((t 0 0 / t 1 0 : ℝ) : ℂ) * (keyValue L x (SkeletonKey.velocity 0 false lev lo hi t 2 1)
              - (t 1 1 : ℂ) * (keyValue L x (SkeletonKey.stream (hi, lev))
                - keyValue L x (SkeletonKey.stream (lo, lev))))) :=
  ⟨fun _ _ _ t hlev _ hlh => radial_key x hx L t hlev hlh,
    fun _ _ _ t hlo hlh h10 => height_key x hx L t hlo hlh h10⟩

end Internal.KeyFlux

theorem keyFluxHolds_of_lift (hP : PlaneFlipFacts.PeriodicSecondOrderHolds) (hL : HarmonicLiftStatement)
    (D : CellLayerData k C nE nM) : KeyFluxHolds D := by
  intro q v G H g Pg hfh L _ ν x hx
  obtain ⟨hc, hs, -⟩ := hL 0 v G H (hP _ _ v G H g hfh.2.2.1) ν
  rcases hx with rfl | rfl
  · exact Internal.KeyFlux.keyFlux_local _ hc L
  · exact Internal.KeyFlux.keyFlux_local _ hs L

end Assembly

end CertCell

end Breakdown

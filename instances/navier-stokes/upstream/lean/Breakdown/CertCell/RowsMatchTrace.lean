import Breakdown.CertCell.RowsMatchTracePairs
import Breakdown.FracCell.SegmentIndependenceParts
import Breakdown.FracCell.CornerIndependenceParts
import Breakdown.FracCell.MeshStreamInd

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.TraceLocal

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.CellCert.CellFormula
open Breakdown.CertCell.LocalField

theorem tent_move {M : ℝ → ℂ} {Q : ℝ → Prop} {c o o' : ℝ}
    (htent : ∀ l u, Q l → l < c → c < u → M l = M u) (hlow : ∃ l, Q l ∧ l < c)
    (ho : o ≠ c) (ho' : o' ≠ c) (hQo : o < c → Q o) (hQo' : o' < c → Q o') : M o = M o' := by
  obtain ⟨l, hl, hlc⟩ := hlow
  have key : ∀ w, w ≠ c → (w < c → Q w) → M w = M (c + 1) := by
    intro w hw hQw
    rcases lt_or_gt_of_ne hw with h | h
    · exact htent w (c + 1) (hQw h) h (by linarith)
    · rw [← htent l w hl hlc h, htent l (c + 1) hl hlc (by linarith)]
  rw [key o ho hQo, key o' ho' hQo']

theorem split_fst {f g : ℝ × ℝ → ℂ} {l m u : ℝ} {J : Set ℝ} (hJ : MeasurableSet J) (hlm : l ≤ m) (hmu : m ≤ u)
    (hf : IntegrableOn f (Icc l m ×ˢ J)) (hg : IntegrableOn g (Icc m u ×ˢ J)) :
    ∫ p in Icc l u ×ˢ J, (if p.1 ≤ m then f p else g p) =
      (∫ p in Icc l m ×ˢ J, f p) + ∫ p in Icc m u ×ˢ J, g p := by
  have hset : Icc l u ×ˢ J = Icc l m ×ˢ J ∪ Ioc m u ×ˢ J := by
    rw [← union_prod, Icc_union_Ioc_eq_Icc hlm hmu]
  have hdisj : Disjoint (Icc l m ×ˢ J) (Ioc m u ×ˢ J) :=
    disjoint_left.2 fun p h1 h2 => (not_lt.2 h1.1.2) h2.1.1
  have hm1 : MeasurableSet (Icc l m ×ˢ J) := measurableSet_Icc.prod hJ
  have hm2 : MeasurableSet (Ioc m u ×ˢ J) := measurableSet_Ioc.prod hJ
  have e1 : EqOn (fun p : ℝ × ℝ => if p.1 ≤ m then f p else g p) f (Icc l m ×ˢ J) := by
    intro p hp
    simp only [if_pos hp.1.2]
  have e2 : EqOn (fun p : ℝ × ℝ => if p.1 ≤ m then f p else g p) g (Ioc m u ×ˢ J) := by
    intro p hp
    simp only [if_neg (not_le.2 hp.1.1)]
  have hg' : IntegrableOn g (Ioc m u ×ˢ J) := hg.mono_set (prod_mono Ioc_subset_Icc_self le_rfl)
  have hae : (Ioc m u ×ˢ J : Set (ℝ × ℝ)) =ᵐ[volume] Icc m u ×ˢ J := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (ae_eq_refl _)
  rw [hset, setIntegral_union hdisj hm2 (hf.congr_fun e1.symm hm1) (hg'.congr_fun e2.symm hm2),
    setIntegral_congr_fun hm1 e1, setIntegral_congr_fun hm2 e2, setIntegral_congr_set hae]

theorem split_snd {f g : ℝ × ℝ → ℂ} {l m u : ℝ} {I : Set ℝ} (hI : MeasurableSet I) (hlm : l ≤ m) (hmu : m ≤ u)
    (hf : IntegrableOn f (I ×ˢ Icc l m)) (hg : IntegrableOn g (I ×ˢ Icc m u)) :
    ∫ p in I ×ˢ Icc l u, (if p.2 ≤ m then f p else g p) =
      (∫ p in I ×ˢ Icc l m, f p) + ∫ p in I ×ˢ Icc m u, g p := by
  have hset : I ×ˢ Icc l u = I ×ˢ Icc l m ∪ I ×ˢ Ioc m u := by
    rw [← prod_union, Icc_union_Ioc_eq_Icc hlm hmu]
  have hdisj : Disjoint (I ×ˢ Icc l m) (I ×ˢ Ioc m u) :=
    disjoint_left.2 fun p h1 h2 => (not_lt.2 h1.2.2) h2.2.1
  have hm1 : MeasurableSet (I ×ˢ Icc l m) := hI.prod measurableSet_Icc
  have hm2 : MeasurableSet (I ×ˢ Ioc m u) := hI.prod measurableSet_Ioc
  have e1 : EqOn (fun p : ℝ × ℝ => if p.2 ≤ m then f p else g p) f (I ×ˢ Icc l m) := by
    intro p hp
    simp only [if_pos hp.2.2]
  have e2 : EqOn (fun p : ℝ × ℝ => if p.2 ≤ m then f p else g p) g (I ×ˢ Ioc m u) := by
    intro p hp
    simp only [if_neg (not_le.2 hp.2.1)]
  have hg' : IntegrableOn g (I ×ˢ Ioc m u) := hg.mono_set (prod_mono le_rfl Ioc_subset_Icc_self)
  have hae : (I ×ˢ Ioc m u : Set (ℝ × ℝ)) =ᵐ[volume] I ×ˢ Icc m u := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ioc_ae_eq_Icc
  rw [hset, setIntegral_union hdisj hm2 (hf.congr_fun e1.symm hm1) (hg'.congr_fun e2.symm hm2),
    setIntegral_congr_fun hm1 e1, setIntegral_congr_fun hm2 e2, setIntegral_congr_set hae]

theorem big_box {a b lo hi : ℝ} (ha : 0 ≤ a) :
    Icc a b ×ˢ Icc lo hi ⊆ Icc 0 b ×ˢ Icc (-(|lo| + |hi|)) (|lo| + |hi|) := by
  intro p hp
  simp only [mem_prod, mem_Icc] at hp ⊢
  refine ⟨⟨by linarith [hp.1.1], hp.1.2⟩, ?_, ?_⟩ <;> cases abs_cases lo <;> cases abs_cases hi <;>
    linarith [hp.2.1, hp.2.2]

theorem off_box {a b lo hi : ℝ} : Icc a b ×ˢ Icc lo hi ⊆ Icc a b ×ˢ Icc (-(|lo| + |hi|)) (|lo| + |hi|) := by
  intro p hp
  simp only [mem_prod, mem_Icc] at hp ⊢
  refine ⟨hp.1, ?_, ?_⟩ <;> cases abs_cases lo <;> cases abs_cases hi <;> linarith [hp.2.1, hp.2.2]

theorem radial_term_int {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {t : ℝ → ℝ} (ht : Continuous t)
    {c o a b lo hi : ℝ} (ha : 0 ≤ a) (hao : 0 < a ∨ o = 0) :
    IntegrableOn (radialStripTerm c o F dF t) (Icc a b ×ˢ Icc lo hi) := by
  have hK : IsCompact (Icc a b ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  have hF : IntegrableOn F (Icc a b ×ˢ Icc lo hi) := ((h.1 b (|lo| + |hi|)).1).mono_set (big_box ha)
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) (Icc a b ×ˢ Icc lo hi) := by
    rcases hao with ha' | ho
    · exact ((h.2.1 a b (|lo| + |hi|) ha').mono_set off_box).continuousOn_mul (by fun_prop) hK
    · subst ho
      have h1 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc a b ×ˢ Icc lo hi) :=
        ((h.1 b (|lo| + |hi|)).2).mono_set (big_box ha)
      have h2 : IntegrableOn (fun p : ℝ × ℝ => (((1 / c : ℝ)) : ℂ) * ((p.1 : ℂ) * dF p)) (Icc a b ×ˢ Icc lo hi) :=
        h1.const_mul _
      refine h2.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      push_cast
      ring
  have hsum : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Icc a b ×ˢ Icc lo hi) := (hF.const_mul _).add hdF
  exact hsum.mul_continuousOn (g' := fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) (by fun_prop) hK

theorem radial_tent {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {lo hi l m u : ℝ} {t : ℝ → ℝ}
    (ht : Continuous t) (hl : 0 ≤ l) (hlm : l < m) (hmu : m < u) :
    radialStripMoment m l lo hi F dF t = radialStripMoment m u lo hi F dF t := by
  have hm : 0 < m := by linarith
  have key := radialStrip_tent_zero h ht hl hlm hmu (lo := lo) (hi := hi)
  rw [split_fst measurableSet_Icc hlm.le hmu.le (radial_term_int h ht hl (hl.lt_or_eq.imp id Eq.symm))
    (radial_term_int h ht hm.le (Or.inl hm))] at key
  have e : ∀ o, radialStripMoment m o lo hi F dF t =
      edgeSign m o * ∫ p in Icc (min m o) (max m o) ×ˢ Icc lo hi, radialStripTerm m o F dF t p := fun _ => rfl
  rw [e, e, min_eq_right hlm.le, max_eq_left hlm.le, min_eq_left hmu.le, max_eq_right hmu.le]
  simp only [edgeSign, if_pos hlm, if_neg (not_lt.2 hmu.le)]
  linear_combination key

theorem seg_indep (S S' : FaceSegment) (hr : S.radial = S'.radial) (hl : S.level = S'.level)
    (hlo : S.lo = S'.lo) (hhi : S.hi = S'.hi) (htc : S.testCoef = S'.testCoef)
    (ho : S.other ≠ S.level) (ho' : S'.other ≠ S'.level)
    (hpos : S.radial → S.level ≠ 0 ∧ 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other)
    (weighted : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (d : ℕ)
    (hrad : S.radial → IsRadialWeakPair F dFr)
    (hhgt : ¬ S.radial → IsHeightWeakPair (fun r => if weighted then r else 1) F dFz) :
    S.moment weighted F dFr dFz d = S'.moment weighted F dFr dFz d := by
  obtain ⟨r, l, o, lo, hi, tc⟩ := S
  obtain ⟨r', l', o', lo', hi', tc'⟩ := S'
  simp only at hr hl hlo hhi htc ho ho' hpos hrad hhgt
  subst hr hl hlo hhi htc
  have ht : Continuous (fun s : ℝ => ∑ i ∈ Finset.range (d + 1), tc d i * s ^ i) := by fun_prop
  cases r
  · simp only [FaceSegment.moment, FaceSegment.test, Bool.false_eq_true, if_false]
    have hwt : Continuous (fun r : ℝ => if weighted then r else 1) := by
      cases weighted
      · simpa using continuous_const
      · simpa using continuous_id'
    exact Breakdown.CellCert.CellCoordinates.MeshStreamInd.other_indep
      (M := fun w => heightStripMoment l w lo hi (fun r => if weighted then r else 1) F dFz
        (fun s => ∑ i ∈ Finset.range (d + 1), tc d i * s ^ i))
      (fun _ _ hlw hwu => Breakdown.CellCert.CellCoordinates.MeshStreamInd.strip_tent (hhgt (by simp)) hwt ht hlw hwu)
      ho ho'
  · simp only [FaceSegment.moment, FaceSegment.test, if_true]
    obtain ⟨hne, h0, h0'⟩ := hpos rfl
    have hc : 0 < l := lt_of_le_of_ne (le_min_iff.mp h0).1 (Ne.symm hne)
    exact tent_move (M := fun w => radialStripMoment l w lo hi F dFr
        (fun s => ∑ i ∈ Finset.range (d + 1), tc d i * s ^ i)) (Q := fun w => 0 ≤ w)
      (fun _ _ hw hwl hlu => radial_tent (hrad rfl) ht hw hwl hlu) ⟨0, le_rfl, hc⟩ ho ho'
      (fun _ => (le_min_iff.mp h0).2) (fun _ => (le_min_iff.mp h0').2)

theorem corner_term_int {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr orr cz oz lo hi zl zh : ℝ} (hlo : 0 ≤ lo) (hpos : 0 < lo ∨ orr = 0) :
    IntegrableOn (cornerTerm cr orr cz oz F Fr Fz Frz) (Icc lo hi ×ˢ Icc zl zh) := by
  have hK : IsCompact (Icc lo hi ×ˢ Icc zl zh) := isCompact_Icc.prod isCompact_Icc
  set Z := |zl| + |zh| with hZ
  have hF : IntegrableOn F (Icc lo hi ×ˢ Icc zl zh) := (h.1 hi Z).1.mono_set (big_box hlo)
  have hFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc zl zh) := (h.1 hi Z).2.1.mono_set (big_box hlo)
  have h1 : IntegrableOn (fun p => (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p)
      (Icc lo hi ×ˢ Icc zl zh) := hF.const_mul _
  have h2 : IntegrableOn (fun p => (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p)
      (Icc lo hi ×ˢ Icc zl zh) := IntegrableOn.continuousOn_mul (by fun_prop) hFz hK
  have h34 : IntegrableOn (fun p => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p)
        (Icc lo hi ×ˢ Icc zl zh) ∧
      IntegrableOn (fun p => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p)
        (Icc lo hi ×ˢ Icc zl zh) := by
    rcases hpos with hlo' | horr
    · have hFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc zl zh) := (h.2.1 lo hi Z hlo').1.mono_set off_box
      have hFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc zl zh) := (h.2.1 lo hi Z hlo').2.mono_set off_box
      exact ⟨IntegrableOn.continuousOn_mul (by fun_prop) hFr hK, IntegrableOn.continuousOn_mul (by fun_prop) hFrz hK⟩
    · subst horr
      have hFr : IntegrableOn (fun p => (p.1 : ℂ) * Fr p) (Icc lo hi ×ˢ Icc zl zh) :=
        (h.1 hi Z).2.2.1.mono_set (big_box hlo)
      have hFrz : IntegrableOn (fun p => (p.1 : ℂ) * Frz p) (Icc lo hi ×ˢ Icc zl zh) :=
        (h.1 hi Z).2.2.2.mono_set (big_box hlo)
      have g1 : IntegrableOn (fun p => ((((1 / cr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ)) * ((p.1 : ℂ) * Fr p))
          (Icc lo hi ×ˢ Icc zl zh) := hFr.const_mul _
      have g2 : IntegrableOn (fun p => ((((1 / cr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) *
          ((p.1 : ℂ) * Frz p)) (Icc lo hi ×ˢ Icc zl zh) := IntegrableOn.continuousOn_mul (by fun_prop) hFrz hK
      refine ⟨g1.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc),
        g2.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)⟩ <;> push_cast <;> ring
  exact ((h1.add h2).add h34.1).add h34.2

theorem corner_eq (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz F Fr Fz Frz = edgeSign cr orr * edgeSign cz oz *
      ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz), cornerTerm cr orr cz oz F Fr Fz Frz p :=
  rfl

theorem corner_radial {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr a b cz oz : ℝ} (ha : 0 ≤ a) (hac : a < cr) (hcb : cr < b) (hz : oz ≠ cz) :
    cornerMoment cr a cz oz F Fr Fz Frz = cornerMoment cr b cz oz F Fr Fz Frz := by
  have key := radial_tent_zero h ha hac hcb hz
  have hfun : (fun p : ℝ × ℝ => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p) =
      fun p => if p.1 ≤ cr then cornerTerm cr a cz oz F Fr Fz Frz p else cornerTerm cr b cz oz F Fr Fz Frz p := by
    funext p
    split_ifs <;> rfl
  rw [hfun, split_fst measurableSet_Icc hac.le hcb.le
    (corner_term_int h ha (ha.lt_or_eq.imp id Eq.symm)) (corner_term_int h (by linarith) (Or.inl (by linarith)))]
    at key
  rw [corner_eq, corner_eq, min_eq_right hac.le, max_eq_left hac.le, min_eq_left hcb.le, max_eq_right hcb.le]
  rw [show edgeSign cr a = 1 from if_pos hac, show edgeSign cr b = -1 from if_neg (not_lt.2 hcb.le)]
  linear_combination edgeSign cz oz * key

theorem corner_height {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr orr cz a b : ℝ} (hcr : 0 < cr) (hr : 0 ≤ min cr orr) (hrc : orr ≠ cr) (hac : a < cz) (hcb : cz < b) :
    cornerMoment cr orr cz a F Fr Fz Frz = cornerMoment cr orr cz b F Fr Fz Frz := by
  have key := height_tent_zero h hcr hr hrc hac hcb
  have hpos : 0 < min cr orr ∨ orr = 0 := by
    rcases lt_or_gt_of_ne hrc with hlt | hgt
    · rw [min_eq_right hlt.le]
      rcases eq_or_lt_of_le (le_trans hr (min_le_right _ _)) with h0 | h0
      · exact Or.inr h0.symm
      · exact Or.inl h0
    · exact Or.inl (by rw [min_eq_left hgt.le]; exact hcr)
  have hfun : (fun p : ℝ × ℝ => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p) =
      fun p => if p.2 ≤ cz then cornerTerm cr orr cz a F Fr Fz Frz p else cornerTerm cr orr cz b F Fr Fz Frz p := by
    funext p
    split_ifs <;> rfl
  rw [hfun, split_snd measurableSet_Icc hac.le hcb.le (corner_term_int h hr hpos) (corner_term_int h hr hpos)]
    at key
  rw [corner_eq, corner_eq, min_eq_right hac.le, max_eq_left hac.le, min_eq_left hcb.le, max_eq_right hcb.le]
  rw [show edgeSign cz a = 1 from if_pos hac, show edgeSign cz b = -1 from if_neg (not_lt.2 hcb.le)]
  linear_combination edgeSign cr orr * key

theorem corner_normal {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz) {cr cz o oz : ℝ}
    (hcr : 0 < cr) (ho : 0 ≤ min cr o) (hoc : o ≠ cr) (hoz : oz ≠ cz) :
    cornerMoment cr o cz oz F Fr Fz Frz = cornerMoment cr (cr + 1) cz (cz + 1) F Fr Fz Frz := by
  have step1 : cornerMoment cr o cz oz F Fr Fz Frz = cornerMoment cr (cr + 1) cz oz F Fr Fz Frz := by
    rcases lt_or_gt_of_ne hoc with hlt | hgt
    · exact corner_radial h (le_trans ho (min_le_right _ _)) hlt (by linarith) hoz
    · rw [← corner_radial h (a := cr / 2) (b := o) (by linarith) (by linarith) hgt hoz]
      exact corner_radial h (by linarith) (by linarith) (by linarith) hoz
  rw [step1]
  have hm : 0 ≤ min cr (cr + 1) := le_min hcr.le (by linarith)
  have hne : cr + 1 ≠ cr := by linarith
  rcases lt_or_gt_of_ne hoz with hlt | hgt
  · exact corner_height h hcr hm hne hlt (by linarith)
  · rw [← corner_height h (a := cz - 1) (b := oz) hcr hm hne (by linarith) hgt]
    exact corner_height h hcr hm hne (by linarith) (by linarith)

end Breakdown.CertCell.Assembly.Internal.TraceLocal

namespace Breakdown.CertCell.Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates LocalField

variable {k : ℕ} {C : Type} {nE nM : ℕ}

namespace Internal.TraceLocal

theorem wt_true {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) :
    IsHeightWeakPair (fun r => if true then r else 1) F dF := by
  simpa using h

theorem wt_false {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun _ => 1) F dF) :
    IsHeightWeakPair (fun r => if false then r else 1) F dF := by
  simpa using h

theorem head_radial {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (hQ : SteadyCert.IsGradientField x.2.2.2.2)
    (L : CellLayout) (n : ℤ) : IsRadialWeakPair (headPressure L n x) (L.pressureGradMode n x 0) :=
  pres_radial hQ L.order n _

theorem head_height {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (hQ : SteadyCert.IsGradientField x.2.2.2.2)
    (L : CellLayout) (n : ℤ) :
    IsHeightWeakPair (fun r => if true then r else 1) (headPressure L n x) (L.pressureGradMode n x 2) :=
  wt_true (pres_height hQ L.order n _ : IsHeightWeakPair (fun r => r) (headPressure L n x) (L.pressureGradMode n x 2))

theorem trace_local {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1)
    (hQ : SteadyCert.IsGradientField x.2.2.2.2) (L : CellLayout) :
    (∀ (n : ℤ) (S S' : FaceSegment), IsFaceSegment S → IsFaceSegment S' → S.radial = S'.radial →
        S.level = S'.level → S.lo = S'.lo → S.hi = S'.hi → S.testCoef = S'.testCoef → (S.radial → S.level ≠ 0) →
        (S.radial → 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other) → ∀ (a : Fin 3) (d : ℕ),
          S.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d =
            S'.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d ∧
          (if S.radial then S.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
              (L.secondModeOf n x a 0 2) d
            else S.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) =
          (if S'.radial then S'.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
              (L.secondModeOf n x a 0 2) d
            else S'.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) ∧
          S.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d =
            S'.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d) ∧
    (∀ (n : ℤ) (cr cz orr oz orr' oz' : ℝ), cr ≠ 0 → orr ≠ cr → oz ≠ cz → orr' ≠ cr → oz' ≠ cz →
        0 ≤ min cr orr → 0 ≤ min cr orr' → ∀ a : Fin 3,
          cornerMoment cr orr cz oz (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
              (L.secondModeOf n x a 0 2) =
            cornerMoment cr orr' cz oz' (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
              (L.secondModeOf n x a 0 2)) ∧
    (∀ (cr cz oz oz' : ℝ), 0 < cr → oz ≠ cz → oz' ≠ cz →
        heightStripMoment cz oz 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)
          = heightStripMoment cz oz' 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)) := by
  refine ⟨fun n S S' hS hS' hr hl hlo hhi htc hne hpos a d => ?_,
    fun n cr cz orr oz orr' oz' hcr h1 h2 h3 h4 hm hm' a => ?_, fun cr cz oz oz' _ hoz hoz' => ?_⟩
  · have hpos' : S.radial → S.level ≠ 0 ∧ 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other :=
      fun h => ⟨hne h, hpos h⟩
    have I := seg_indep S S' hr hl hlo hhi htc hS.other_ne hS'.other_ne hpos'
    have vr : IsRadialWeakPair (L.velMode n x a) (L.gradModeOf n x a 0) := vel_radial hs L.order n a
    have vh : IsHeightWeakPair (fun r => if false then r else 1) (L.velMode n x a) (L.gradModeOf n x a 2) :=
      wt_false (vel_height hs L.order n a : IsHeightWeakPair (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2))
    have gr : IsRadialWeakPair (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) := grad_radial hs L.order n a
    have gh : IsHeightWeakPair (fun r => if true then r else 1) (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2) :=
      wt_true (grad_height hs L.order n a :
        IsHeightWeakPair (fun r => r) (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2))
    refine ⟨I false _ _ _ d (fun _ => vr) (fun _ => vh), ?_,
      I true _ _ _ d (fun _ => head_radial x hQ L n) (fun _ => head_height x hQ L n)⟩
    rw [← hr]
    by_cases h : S.radial
    · simp only [h, if_true]
      exact I true _ _ _ d (fun _ => gr) (fun h' => absurd h h')
    · simp only [h]
      exact I true _ _ _ d (fun h' => absurd h' h) (fun _ => gh)
  · have hq : IsMixedWeakQuad (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
        (L.secondModeOf n x a 0 2) := corner_quad hs L.order n a
    have hcr0 : 0 < cr := lt_of_le_of_ne (le_trans hm (min_le_left _ _)) (Ne.symm hcr)
    rw [corner_normal hq hcr0 hm h1 h2, corner_normal hq hcr0 hm' h3 h4]
  · have hw : IsHeightWeakPair (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) :=
      CellCert.CellCoordinates.MeshStreamInd.weightedPair_of_unit (vel_height hs L.order 0 2)
    exact CellCert.CellCoordinates.MeshStreamInd.other_indep
      (M := fun o => heightStripMoment cz o 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1))
      (fun _ _ hl hu => CellCert.CellCoordinates.MeshStreamInd.strip_tent hw continuous_id continuous_const hl hu)
      hoz hoz'

end Internal.TraceLocal

theorem harmonicTraceIndependence_of_lift (hP : PlaneFlipFacts.PeriodicSecondOrderHolds) (hL : HarmonicLiftStatement)
    (D : CellLayerData k C nE nM) : HarmonicTraceIndependence D := by
  intro q v G H g Pg hfh ν x hx L _
  obtain ⟨hc, hs, -⟩ := hL 0 v G H (hP _ _ v G H g hfh.2.2.1) ν
  have hPg : CellCalculus.IsPeriodicPressure Pg := hfh.2.2.2.1
  have hgc : SteadyCert.IsGradientField (harmonicCos ν Pg) := (hPg.harmonic_gradient ν).1
  have hgs : SteadyCert.IsGradientField (harmonicSin ν Pg) := (hPg.harmonic_gradient ν).2
  rcases hx with rfl | rfl
  · exact Internal.TraceLocal.trace_local (cosTuple ν v G H Pg) hc hgc L
  · exact Internal.TraceLocal.trace_local (sinTuple ν v G H Pg) hs hgs L

end Breakdown.CertCell.Assembly

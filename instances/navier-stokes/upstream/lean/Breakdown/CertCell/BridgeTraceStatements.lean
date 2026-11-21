import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.CellCalculusStatements

open scoped ContDiff ENNReal ComplexOrder
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula CellCert.CellAnalysis Bridge

def IsAxisAdmissibleTest (lo : ℝ) (t : ℝ → ℝ) : Prop :=
  0 < lo ∨ (lo = 0 ∧ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ r, t r = r * t₀ r)

def sideTrace (f fd : ℝ → ℂ) (c o : ℝ) : ℂ :=
  edgeSign c o * ∫ r in Set.Icc (min c o) (max c o),
    ((((1 / (c - o)) : ℝ) : ℂ) * f r + (((r - o) / (c - o) : ℝ) : ℂ) * fd r)

def SideTraceMatchHolds : Prop :=
  ∀ (f fd : ℝ → ℂ) (c o o' a b : ℝ), c ≠ o → c ≠ o' → a < min c (min o o') → max c (max o o') < b →
    HasWeakDerivOn f fd a b → sideTrace f fd c o = sideTrace f fd c o'

def AxisSideTraceHolds : Prop :=
  ∀ (f fd : ℝ → ℂ) (c o' b : ℝ), 0 < c → 0 ≤ o' → c ≠ o' → max c o' < b →
    (∀ lo, 0 < lo → HasWeakDerivOn f fd lo b) → MeasureTheory.IntegrableOn f (Set.Ioo 0 b) →
    MeasureTheory.IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ) * fd r) (Set.Ioo 0 b) →
    sideTrace f fd c 0 = sideTrace f fd c o'

def RadialStripTraceHolds : Prop :=
  ∀ (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ), c ≠ o → lo < hi → Continuous t →
    MeasureTheory.IntegrableOn (fun p => ((t p.2 : ℝ) : ℂ) * F p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) →
    MeasureTheory.IntegrableOn (fun p => (((p.1 - o) * t p.2 : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) →
    radialStripMoment c o lo hi F dF t
      = ∫ z in Set.Icc lo hi, ((t z : ℝ) : ℂ) * sideTrace (fun r => F (r, z)) (fun r => dF (r, z)) c o

def HeightStripTraceHolds : Prop :=
  ∀ (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ), c ≠ o → lo < hi → Continuous wt → Continuous t →
    MeasureTheory.IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * F p)
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) →
    MeasureTheory.IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * dF p)
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) →
    heightStripMoment c o lo hi wt F dF t
      = ∫ r in Set.Icc lo hi, ((wt r * t r : ℝ) : ℂ) * sideTrace (fun z => F (r, z)) (fun z => dF (r, z)) c o

def CornerPointTraceHolds : Prop :=
  ∀ (F Fr Fz Frz : ℝ × ℝ → ℂ) (cr orr orr' cz oz oz' lo hi zlo zhi : ℝ),
    cr ≠ orr → cr ≠ orr' → cz ≠ oz → cz ≠ oz' →
    lo < min cr (min orr orr') → max cr (max orr orr') < hi →
    zlo < min cz (min oz oz') → max cz (max oz oz') < zhi →
    HasWeakPlaneDerivsOn F Fr Fz Frz (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) →
    cornerMoment cr orr cz oz F Fr Fz Frz = cornerMoment cr orr' cz oz' F Fr Fz Frz

def CornerAxisTraceHolds : Prop :=
  ∀ (F Fr Fz Frz : ℝ × ℝ → ℂ) (cr orr' cz oz oz' hi zlo zhi : ℝ),
    0 < cr → 0 ≤ orr' → cr ≠ orr' → cz ≠ oz → cz ≠ oz' → max cr orr' < hi →
    zlo < min cz (min oz oz') → max cz (max oz oz') < zhi →
    (∀ lo, 0 < lo → HasWeakPlaneDerivsOn F Fr Fz Frz (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)) →
    MeasureTheory.IntegrableOn F (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) →
    MeasureTheory.IntegrableOn Fz (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) →
    MeasureTheory.IntegrableOn (fun p => (p.1 : ℂ) * Fr p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) →
    MeasureTheory.IntegrableOn (fun p => (p.1 : ℂ) * Frz p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) →
    cornerMoment cr 0 cz oz F Fr Fz Frz = cornerMoment cr orr' cz oz' F Fr Fz Frz

def planeGrad (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeGrad ξ G 0 (planePoint p) (a, b)

def planeSlope (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, c, b)

def planeVelocity (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) : ℝ × ℝ → ℂ :=
  fun p => modeVel ξ v 0 (planePoint p) a

def ModeRadialDerivHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a b : Fin 3),
    ∀ᵐ z : ℝ, ∀ lo hi : ℝ, 0 < lo → lo < hi →
      HasWeakDerivOn (fun r => planeVelocity ξ v a (r, z)) (fun r => planeGrad ξ G a 0 (r, z)) lo hi ∧
      HasWeakDerivOn (fun r => planeGrad ξ G a b (r, z)) (fun r => planeSlope ξ H a b 0 (r, z)) lo hi

def ModePlaneDerivsHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a : Fin 3) (lo hi zlo zhi : ℝ), 0 < lo → lo < hi → zlo < zhi →
      HasWeakPlaneDerivsOn (planeVelocity ξ v a) (planeGrad ξ G a 0) (planeGrad ξ G a 2) (planeSlope ξ H a 0 2)
        (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) ∧
      ∀ b c : Fin 3, MeasureTheory.IntegrableOn (planeGrad ξ G a b) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) ∧
        MeasureTheory.IntegrableOn (planeSlope ξ H a b c) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)

def ModeAxisIntegrableHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a b c : Fin 3) (hi zlo zhi : ℝ), 0 < hi → zlo < zhi →
      MeasureTheory.IntegrableOn (fun p => (p.1 : ℂ) * planeVelocity ξ v a p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) ∧
      MeasureTheory.IntegrableOn (fun p => (p.1 : ℂ) * planeGrad ξ G a b p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) ∧
      MeasureTheory.IntegrableOn (fun p => (p.1 : ℂ) * planeSlope ξ H a b c p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)

def ModeAxisPlainIntegrableHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a b : Fin 3) (hi zlo zhi : ℝ), 0 < hi → zlo < zhi →
      MeasureTheory.IntegrableOn (planeVelocity ξ v a) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) ∧
      MeasureTheory.IntegrableOn (planeGrad ξ G a b) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)

def RadialDataMatchHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a : Fin 3) (c o o' lo hi : ℝ) (t : ℝ → ℝ),
      0 < c → 0 ≤ o → 0 ≤ o' → c ≠ o → c ≠ o' → lo < hi → Continuous t →
      radialStripMoment c o lo hi (planeVelocity ξ v a) (planeGrad ξ G a 0) t
          = radialStripMoment c o' lo hi (planeVelocity ξ v a) (planeGrad ξ G a 0) t ∧
      radialStripMoment c o lo hi (planeGrad ξ G a 0) (planeSlope ξ H a 0 0) t
          = radialStripMoment c o' lo hi (planeGrad ξ G a 0) (planeSlope ξ H a 0 0) t

def HeightDataMatchHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a : Fin 3) (c o o' lo hi : ℝ) (wt t : ℝ → ℝ),
      c ≠ o → c ≠ o' → 0 ≤ lo → lo < hi → Continuous wt → Continuous t →
      heightStripMoment c o lo hi wt (planeVelocity ξ v a) (planeGrad ξ G a 2) t
          = heightStripMoment c o' lo hi wt (planeVelocity ξ v a) (planeGrad ξ G a 2) t ∧
      (IsAxisAdmissibleTest lo (fun r => wt r * t r) →
        heightStripMoment c o lo hi wt (planeGrad ξ G a 2) (planeSlope ξ H a 2 2) t
          = heightStripMoment c o' lo hi wt (planeGrad ξ G a 2) (planeSlope ξ H a 2 2) t)

def CornerDataMatchHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → ∀ (ξ : ℤ × ℤ) (a : Fin 3) (cr orr orr' cz oz oz' : ℝ),
      0 < cr → 0 ≤ orr → 0 ≤ orr' → cr ≠ orr → cr ≠ orr' → cz ≠ oz → cz ≠ oz' →
      cornerMoment cr orr cz oz (planeVelocity ξ v a) (planeGrad ξ G a 0) (planeGrad ξ G a 2) (planeSlope ξ H a 0 2)
        = cornerMoment cr orr' cz oz' (planeVelocity ξ v a) (planeGrad ξ G a 0) (planeGrad ξ G a 2)
          (planeSlope ξ H a 0 2)

theorem radialDataMatch_of_parts (hD : ModeRadialDerivHolds) (hP : ModePlaneDerivsHolds)
    (hR : RadialStripTraceHolds) (hM : SideTraceMatchHolds) (hA : AxisSideTraceHolds)
    (hW : ModeAxisIntegrableHolds) (hU : ModeAxisPlainIntegrableHolds) : RadialDataMatchHolds := by
  have weakDerivOn_of_le : ∀ (f fd : ℝ → ℂ) {lo b : ℝ} (h : b ≤ lo), HasWeakDerivOn f fd lo b := by
    intro f fd lo b h
    have he : Set.Ioo lo b = ∅ := Set.Ioo_eq_empty (not_lt.mpr h)
    refine ⟨?_, ?_, fun ψ _ _ _ => ?_⟩
    · rw [he]; exact integrableOn_empty
    · rw [he]; exact integrableOn_empty
    · rw [he]; simp
  have lineIntegrable_of_box : ∀ {F : ℝ × ℝ → ℂ} {b lo hi : ℝ} (hF : IntegrableOn F (Set.Icc 0 b ×ˢ Set.Icc lo hi)), ∀ᵐ z ∂(volume.restrict (Set.Icc lo hi)), IntegrableOn (fun r => F (r, z)) (Set.Ioo 0 b) := by
    intro F b lo hi hF
    have h1 : Integrable F ((volume.restrict (Set.Icc (0 : ℝ) b)).prod (volume.restrict (Set.Icc lo hi))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hF
    filter_upwards [h1.prod_left_ae] with z hz
    exact (show IntegrableOn (fun r => F (r, z)) (Set.Icc 0 b) volume from hz).mono_set Set.Ioo_subset_Icc_self
  have stripIntegrable_value : ∀ {F : ℝ × ℝ → ℂ} {t : ℝ → ℝ} {c o lo hi : ℝ} (hU : ∀ hi zlo zhi : ℝ, 0 < hi → zlo < zhi → IntegrableOn F (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)) (hc : 0 < c) (ho : 0 ≤ o) (hlh : lo < hi) (ht : Continuous t), IntegrableOn (fun p => ((t p.2 : ℝ) : ℂ) * F p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
    intro F t c o lo hi hU hc ho hlh ht
    have hsub : Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi ⊆ Set.Icc 0 (max c o) ×ˢ Set.Icc lo hi :=
      Set.prod_mono (Set.Icc_subset_Icc_left (le_min hc.le ho)) le_rfl
    have hF := (hU (max c o) lo hi (lt_max_of_lt_left hc) hlh).mono_set hsub
    exact IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).continuousOn
      hF (isCompact_Icc.prod isCompact_Icc)
  have stripIntegrable_slope : ∀ {dF : ℝ × ℝ → ℂ} {t : ℝ → ℝ} {c o lo hi : ℝ} (hP : ∀ lo hi zlo zhi : ℝ, 0 < lo → lo < hi → zlo < zhi → IntegrableOn dF (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)) (hW : ∀ hi zlo zhi : ℝ, 0 < hi → zlo < zhi → IntegrableOn (fun p => (p.1 : ℂ) * dF p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)) (hc : 0 < c) (ho : 0 ≤ o) (hco : c ≠ o) (hlh : lo < hi) (ht : Continuous t), IntegrableOn (fun p => (((p.1 - o) * t p.2 : ℝ) : ℂ) * dF p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
    intro dF t c o lo hi hP hW hc ho hco hlh ht
    have hK : IsCompact (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := isCompact_Icc.prod isCompact_Icc
    rcases ho.lt_or_eq with ho' | ho'
    · have hF := hP (min c o) (max c o) lo hi (lt_min hc ho') (min_lt_max.mpr hco) hlh
      exact IntegrableOn.continuousOn_mul
        (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).mul
          (ht.comp continuous_snd))).continuousOn hF hK
    · subst ho'
      have hsub : Set.Icc (min c 0) (max c 0) ×ˢ Set.Icc lo hi ⊆ Set.Icc 0 (max c 0) ×ˢ Set.Icc lo hi :=
        Set.prod_mono (Set.Icc_subset_Icc_left (le_min hc.le le_rfl)) le_rfl
      have hF := (hW (max c 0) lo hi (lt_max_of_lt_left hc) hlh).mono_set hsub
      have hG := IntegrableOn.continuousOn_mul
        (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).continuousOn hF hK
      refine hG.congr_fun (fun p _ => ?_) hK.measurableSet
      simp only [Function.comp_apply]
      push_cast
      ring
  have sideTrace_eq_of_line : ∀ {f fd : ℝ → ℂ} {c o o' b : ℝ} (hM : SideTraceMatchHolds) (hA : AxisSideTraceHolds) (hc : 0 < c) (ho : 0 ≤ o) (ho' : 0 ≤ o') (hco : c ≠ o) (hco' : c ≠ o') (hb : max c (max o o') < b) (hd : ∀ lo hi : ℝ, 0 < lo → lo < hi → HasWeakDerivOn f fd lo hi) (hf : IntegrableOn f (Set.Ioo 0 b)) (hfd : IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ) * fd r) (Set.Ioo 0 b)), sideTrace f fd c o = sideTrace f fd c o' := by
    intro f fd c o o' b hM hA hc ho ho' hco hco' hb hd hf hfd
    have hall : ∀ lo, 0 < lo → HasWeakDerivOn f fd lo b := fun lo hlo => by
      rcases lt_or_ge lo b with h | h
      · exact hd lo b hlo h
      · exact weakDerivOn_of_le f fd h
    rcases ho.lt_or_eq with ho0 | ho0
    · rcases ho'.lt_or_eq with ho0' | ho0'
      · have hm : 0 < min c (min o o') := lt_min hc (lt_min ho0 ho0')
        refine hM f fd c o o' (min c (min o o') / 2) b hco hco' (half_lt_self hm) hb ?_
        exact hd _ _ (half_pos hm)
          (lt_trans (half_lt_self hm) (lt_of_le_of_lt ((min_le_left _ _).trans (le_max_left _ _)) hb))
      · subst ho0'
        exact (hA f fd c o b hc ho hco
          (lt_of_le_of_lt (max_le_max le_rfl (le_max_left _ _)) hb) hall hf hfd).symm
    · subst ho0
      exact hA f fd c o' b hc ho' hco' (lt_of_le_of_lt (max_le_max le_rfl (le_max_right _ _)) hb) hall hf hfd
  have radialStripMoment_eq_of_lines : ∀ (hR : RadialStripTraceHolds) (hM : SideTraceMatchHolds) (hA : AxisSideTraceHolds) {F dF : ℝ × ℝ → ℂ} (hD : ∀ᵐ z : ℝ, ∀ lo hi : ℝ, 0 < lo → lo < hi → HasWeakDerivOn (fun r => F (r, z)) (fun r => dF (r, z)) lo hi) (hP : ∀ lo hi zlo zhi : ℝ, 0 < lo → lo < hi → zlo < zhi → IntegrableOn dF (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)) (hU : ∀ hi zlo zhi : ℝ, 0 < hi → zlo < zhi → IntegrableOn F (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)) (hW : ∀ hi zlo zhi : ℝ, 0 < hi → zlo < zhi → IntegrableOn (fun p => (p.1 : ℂ) * dF p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)) {c o o' lo hi : ℝ} {t : ℝ → ℝ} (hc : 0 < c) (ho : 0 ≤ o) (ho' : 0 ≤ o') (hco : c ≠ o) (hco' : c ≠ o') (hlh : lo < hi) (ht : Continuous t), radialStripMoment c o lo hi F dF t = radialStripMoment c o' lo hi F dF t := by
    intro hR hM hA F dF hD hP hU hW c o o' lo hi t hc ho ho' hco hco' hlh ht
    rw [hR c o lo hi F dF t hco hlh ht (stripIntegrable_value hU hc ho hlh ht)
        (stripIntegrable_slope hP hW hc ho hco hlh ht),
      hR c o' lo hi F dF t hco' hlh ht (stripIntegrable_value hU hc ho' hlh ht)
        (stripIntegrable_slope hP hW hc ho' hco' hlh ht)]
    obtain ⟨b, hb0, hbl⟩ : ∃ b : ℝ, 0 < b ∧ max c (max o o') < b :=
      ⟨max c (max o o') + 1, by have := le_max_left c (max o o'); linarith, lt_add_one _⟩
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hD, lineIntegrable_of_box (hU b lo hi hb0 hlh),
      lineIntegrable_of_box (hW b lo hi hb0 hlh)] with z hz hfz hfdz
    rw [sideTrace_eq_of_line hM hA hc ho ho' hco hco' hbl hz hfz hfdz]
  intro Γ P v G H g hpert ξ a c o o' lo hi t hc ho ho' hco hco' hlh ht
  have hDl := hD Γ P v G H g hpert ξ a 0
  refine ⟨?_, ?_⟩
  · refine radialStripMoment_eq_of_lines hR hM hA ?_ ?_ ?_ ?_ hc ho ho' hco hco' hlh ht
    · filter_upwards [hDl] with z hz lo' hi' h1 h2
      exact (hz lo' hi' h1 h2).1
    · intro lo' hi' zlo zhi h1 h2 h3
      exact (hP Γ P v G H g hpert ξ a lo' hi' zlo zhi h1 h2 h3).1.2.1
    · intro hi' zlo zhi h1 h2
      exact (hU Γ P v G H g hpert ξ a 0 hi' zlo zhi h1 h2).1
    · intro hi' zlo zhi h1 h2
      exact (hW Γ P v G H g hpert ξ a 0 0 hi' zlo zhi h1 h2).2.1
  · refine radialStripMoment_eq_of_lines hR hM hA ?_ ?_ ?_ ?_ hc ho ho' hco hco' hlh ht
    · filter_upwards [hDl] with z hz lo' hi' h1 h2
      exact (hz lo' hi' h1 h2).2
    · intro lo' hi' zlo zhi h1 h2 h3
      exact ((hP Γ P v G H g hpert ξ a lo' hi' zlo zhi h1 h2 h3).2 0 0).2
    · intro hi' zlo zhi h1 h2
      exact (hU Γ P v G H g hpert ξ a 0 hi' zlo zhi h1 h2).2
    · intro hi' zlo zhi h1 h2
      exact (hW Γ P v G H g hpert ξ a 0 0 hi' zlo zhi h1 h2).2.2

theorem heightDataMatch_of_parts (hD : ModeHeightDerivHolds) (hP : ModePlaneDerivsHolds)
    (hS : HeightStripTraceHolds) (hM : SideTraceMatchHolds) (hW : ModeAxisIntegrableHolds)
    (hU : ModeAxisPlainIntegrableHolds) : HeightDataMatchHolds := by
  have sideWindow : ∀ (c o o' : ℝ), -(|c| + |o| + |o'| + 1) < min c (min o o') ∧ max c (max o o') < |c| + |o| + |o'| + 1 := by
    intro c o o'
    refine ⟨lt_min_iff.2 ⟨?_, lt_min_iff.2 ⟨?_, ?_⟩⟩, max_lt_iff.2 ⟨?_, max_lt_iff.2 ⟨?_, ?_⟩⟩⟩ <;>
      linarith [neg_abs_le c, neg_abs_le o, neg_abs_le o', le_abs_self c, le_abs_self o, le_abs_self o',
        abs_nonneg c, abs_nonneg o, abs_nonneg o']
  have weightedOn : ∀ {u : ℝ → ℝ} (hu : Continuous u) {f : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ} (hf : IntegrableOn f (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)), IntegrableOn (fun p => ((u p.1 : ℝ) : ℂ) * f p) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) := by
    intro u hu f lo hi zlo zhi hf
    exact hf.continuousOn_mul (Complex.continuous_ofReal.comp (hu.comp continuous_fst)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)
  have stripMomentMatch : ∀ (hS : HeightStripTraceHolds) (hM : SideTraceMatchHolds) {F dF : ℝ × ℝ → ℂ} {c o o' lo hi : ℝ} {wt t : ℝ → ℝ} (hco : c ≠ o) (hco' : c ≠ o') (hlo : 0 ≤ lo) (hlohi : lo < hi) (hwt : Continuous wt) (ht : Continuous t) (hF : ∀ zlo zhi : ℝ, zlo < zhi → IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * F p) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)) (hdF : ∀ zlo zhi : ℝ, zlo < zhi → IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * dF p) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)) (hline : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h → HasWeakDerivOn (fun z => F (r, z)) (fun z => dF (r, z)) (-h) h), heightStripMoment c o lo hi wt F dF t = heightStripMoment c o' lo hi wt F dF t := by
    intro hS hM F dF c o o' lo hi wt t hco hco' hlo hlohi hwt ht hF hdF hline
    rw [hS c o lo hi wt F dF t hco hlohi hwt ht (hF _ _ (min_lt_max.2 hco)) (hdF _ _ (min_lt_max.2 hco)),
      hS c o' lo hi wt F dF t hco' hlohi hwt ht (hF _ _ (min_lt_max.2 hco'))
        (hdF _ _ (min_lt_max.2 hco'))]
    refine (setIntegral_congr_set Ioc_ae_eq_Icc).symm.trans
      ((integral_congr_ae ?_).trans (setIntegral_congr_set Ioc_ae_eq_Icc))
    have hsub : Set.Ioc lo hi ⊆ Set.Ioi (0 : ℝ) := fun r hr => lt_of_le_of_lt hlo hr.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hline] with r hr
    have hw := sideWindow c o o'
    have hpos : (0 : ℝ) < |c| + |o| + |o'| + 1 := by positivity
    rw [hM (fun z => F (r, z)) (fun z => dF (r, z)) c o o' _ _ hco hco' hw.1 hw.2 (hr _ hpos)]
  intro Γ P v G H g hpert ξ a c o o' lo hi wt t hco hco' hlo hlohi hwt ht
  have hhi : 0 < hi := lt_of_le_of_lt hlo hlohi
  have hwtt : Continuous (fun r => wt r * t r) := hwt.mul ht
  have hsub : ∀ zlo zhi : ℝ, Set.Icc lo hi ×ˢ Set.Icc zlo zhi ⊆ Set.Icc 0 hi ×ˢ Set.Icc zlo zhi :=
    fun zlo zhi => Set.prod_mono (Set.Icc_subset_Icc_left hlo) le_rfl
  have hlineAll := hD Γ P v G H g hpert ξ a
  have hvel : ∀ zlo zhi : ℝ, zlo < zhi →
      IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * planeVelocity ξ v a p)
        (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) := fun zlo zhi hz =>
    weightedOn (u := fun r => wt r * t r) hwtt
      ((hU Γ P v G H g hpert ξ a 2 hi zlo zhi hhi hz).1.mono_set (hsub zlo zhi))
  have hgrad : ∀ zlo zhi : ℝ, zlo < zhi →
      IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * planeGrad ξ G a 2 p)
        (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) := fun zlo zhi hz =>
    weightedOn (u := fun r => wt r * t r) hwtt
      ((hU Γ P v G H g hpert ξ a 2 hi zlo zhi hhi hz).2.mono_set (hsub zlo zhi))
  refine ⟨stripMomentMatch hS hM hco hco' hlo hlohi hwt ht hvel hgrad ?_,
    fun hadm => stripMomentMatch hS hM hco hco' hlo hlohi hwt ht hgrad ?_ ?_⟩
  · filter_upwards [hlineAll] with r hr h hh using (hr h hh).1
  · rcases hadm with hlo' | ⟨rfl, t₀, ht₀, hfac⟩
    · intro zlo zhi hz
      exact weightedOn (u := fun r => wt r * t r) hwtt
        ((hP Γ P v G H g hpert ξ a lo hi zlo zhi hlo' hlohi hz).2 2 2).2
    · intro zlo zhi hz
      have heq : (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * planeSlope ξ H a 2 2 p)
          = fun p => ((t₀ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) * planeSlope ξ H a 2 2 p) := by
        funext p
        rw [show wt p.1 * t p.1 = p.1 * t₀ p.1 from hfac p.1]
        push_cast
        ring
      rw [heq]
      exact weightedOn ht₀ (hW Γ P v G H g hpert ξ a 2 2 hi zlo zhi hhi hz).2.2
  · filter_upwards [hlineAll] with r hr h hh using (hr h hh).2.1

theorem cornerDataMatch_of_parts (hP : ModePlaneDerivsHolds) (hC : CornerPointTraceHolds)
    (hA : CornerAxisTraceHolds) (hW : ModeAxisIntegrableHolds) (hU : ModeAxisPlainIntegrableHolds) :
    CornerDataMatchHolds := by
  have weakPlaneDerivs_of_null_box : ∀ (F Fr Fz Frz : ℝ × ℝ → ℂ) (lo hi zlo zhi : ℝ) (hlh : hi ≤ lo), HasWeakPlaneDerivsOn F Fr Fz Frz (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) := by
    intro F Fr Fz Frz lo hi zlo zhi hlh
    have hvol : (volume : Measure (ℝ × ℝ)) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
        ENNReal.ofReal_eq_zero.mpr (by linarith), zero_mul]
    have h0 : (volume : Measure (ℝ × ℝ)).restrict (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) = 0 :=
      Measure.restrict_eq_zero.mpr hvol
    refine ⟨?_, ?_, ?_, ?_, fun ψ _ _ _ => ?_⟩
    · unfold IntegrableOn
      rw [h0]
      exact integrable_zero_measure
    · unfold IntegrableOn
      rw [h0]
      exact integrable_zero_measure
    · unfold IntegrableOn
      rw [h0]
      exact integrable_zero_measure
    · unfold IntegrableOn
      rw [h0]
      exact integrable_zero_measure
    · simp only [h0, integral_zero_measure, neg_zero, and_self]
  intro Γ P v G H g hpert ξ a cr orr orr' cz oz oz' hcr horr horr' hne hne' hz hz'
  have step : ∀ o2 w w' : ℝ, 0 ≤ o2 → cr ≠ o2 → cz ≠ w → cz ≠ w' →
      cornerMoment cr 0 cz w (planeVelocity ξ v a) (planeGrad ξ G a 0) (planeGrad ξ G a 2)
          (planeSlope ξ H a 0 2)
        = cornerMoment cr o2 cz w' (planeVelocity ξ v a) (planeGrad ξ G a 0) (planeGrad ξ G a 2)
          (planeSlope ξ H a 0 2) := by
    intro o2 w w' ho2 hne2 hw hw'
    have hhi : 0 < max cr o2 + 1 := by
      have := le_max_left cr o2
      linarith
    have hzz : min cz (min w w') - 1 < max cz (max w w') + 1 := by
      have h1 := min_le_left cz (min w w')
      have h2 := le_max_left cz (max w w')
      linarith
    refine hA (planeVelocity ξ v a) (planeGrad ξ G a 0) (planeGrad ξ G a 2) (planeSlope ξ H a 0 2)
      cr o2 cz w w' (max cr o2 + 1) (min cz (min w w') - 1) (max cz (max w w') + 1)
      hcr ho2 hne2 hw hw' (by linarith) (by linarith) (by linarith) ?_
      (hU Γ P v G H g hpert ξ a 0 _ _ _ hhi hzz).1
      (hU Γ P v G H g hpert ξ a 2 _ _ _ hhi hzz).2
      (hW Γ P v G H g hpert ξ a 0 0 _ _ _ hhi hzz).2.1
      (hW Γ P v G H g hpert ξ a 0 2 _ _ _ hhi hzz).2.2
    intro lo hlo
    by_cases hlh : lo < max cr o2 + 1
    · exact (hP Γ P v G H g hpert ξ a lo _ _ _ hlo hlh hzz).1
    · exact weakPlaneDerivs_of_null_box _ _ _ _ _ _ _ _ (not_lt.mp hlh)
  exact (step orr oz oz horr hne hz hz).symm.trans (step orr' oz oz' horr' hne' hz hz')

def IsSquareIntegrableNear (Q : Space → Space) : Prop :=
  AEStronglyMeasurable Q volume ∧ ∀ R : ℝ, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖Q y‖ ^ 2) < ⊤

def PressureModeDerivHolds : Prop :=
  ∀ (m : ℕ) (Q : Space → Space) (q : Space → ℝ), 1 ≤ m → IsPotentialOf Q q → IsSquareIntegrableNear Q → ∀ n : ℤ,
    (∀ᵐ z : ℝ, ∀ lo hi : ℝ, 0 < lo → lo < hi →
      HasWeakDerivOn (fun r => presMode m n q r z) (fun r => modeVec m n Q r z 0) lo hi) ∧
    (∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ zlo zhi : ℝ, zlo < zhi →
      HasWeakDerivOn (fun z => presMode m n q r z) (fun z => modeVec m n Q r z 2) zlo zhi)

def PressureModeIntegrableHolds : Prop :=
  ∀ (m : ℕ) (Q : Space → Space) (q : Space → ℝ), 1 ≤ m → IsPotentialOf Q q → IsSquareIntegrableNear Q →
    ∀ (n : ℤ) (b : Fin 3) (hi zlo zhi : ℝ), 0 < hi → zlo < zhi →
      MeasureTheory.IntegrableOn (fun p => presMode m n q p.1 p.2) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) ∧
      MeasureTheory.IntegrableOn (fun p => (p.1 : ℂ) * modeVec m n Q p.1 p.2 b) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi) ∧
      ∀ lo, 0 < lo → lo < hi →
        MeasureTheory.IntegrableOn (fun p => modeVec m n Q p.1 p.2 b) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)

def PressurePlaneFlipHolds : Prop :=
  ∀ (m : ℕ) (Q : Space → Space) (q : Space → ℝ), 1 ≤ m → IsPotentialOf Q q → IsSquareIntegrableNear Q →
    (∀ᵐ y, Q (flipPoint y) = flipPoint (Q y)) → ∀ n : ℤ,
      ∀ᵐ p ∂(volume.restrict halfPlane), presMode m (-n) q p.1 (-p.2) = presMode m n q p.1 p.2

def PressureStripFlipHolds : Prop :=
  ∀ (m : ℕ) (Q : Space → Space) (q : Space → ℝ), 1 ≤ m → IsPotentialOf Q q → IsSquareIntegrableNear Q →
    (∀ᵐ y, Q (flipPoint y) = flipPoint (Q y)) → ∀ n : ℤ,
    ∀ (lo hi h h' : ℝ) (wt t : ℝ → ℝ), IsAxisAdmissibleTest lo (fun r => wt r * t r) → lo < hi → 0 < h → 0 < h' →
      Continuous wt → Continuous t →
      heightStripMoment 0 h lo hi wt (fun p => presMode m (-n) q p.1 p.2) (fun p => modeVec m (-n) Q p.1 p.2 2) t
        = heightStripMoment 0 h' lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t

def PressureDataMatchHolds : Prop :=
  ∀ (m : ℕ) (Q : Space → Space) (q : Space → ℝ), 1 ≤ m → IsPotentialOf Q q → IsSquareIntegrableNear Q → ∀ n : ℤ,
    (∀ (c o o' lo hi : ℝ) (t : ℝ → ℝ), 0 < c → 0 ≤ o → 0 ≤ o' → c ≠ o → c ≠ o' → lo < hi → Continuous t →
      radialStripMoment c o lo hi (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 0) t
        = radialStripMoment c o' lo hi (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 0) t) ∧
    ∀ (c o o' lo hi : ℝ) (wt t : ℝ → ℝ), c ≠ o → c ≠ o' → IsAxisAdmissibleTest lo (fun r => wt r * t r) → lo < hi →
      Continuous wt → Continuous t →
      heightStripMoment c o lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t
        = heightStripMoment c o' lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t

def PotentialConstantHolds : Prop :=
  ∀ (Q : Space → Space) (q q' : Space → ℝ), IsPotentialOf Q q → IsPotentialOf Q q' → ∃ C : ℝ, ∀ᵐ y, q' y = q y + C

def PotentialNegationHolds : Prop :=
  ∀ (Q : Space → Space) (q : Space → ℝ), IsPotentialOf Q q → IsPotentialOf (fun y => -Q y) (fun y => -q y)

def PotentialShiftHolds : Prop :=
  ∀ (Q : Space → Space) (q : Space → ℝ) (C : ℝ), IsPotentialOf Q q → IsPotentialOf Q (fun y => q y - C)

def PotentialOfGradientHolds : Prop :=
  ∀ Q : Space → Space, SteadyCert.IsGradientField Q → IsPotentialOf Q (potentialOf Q)

def HarmonicPressureSquareHolds : Prop :=
  ∀ Pg : ℝ → Space → Space, CellCalculus.IsPeriodicPressure Pg → ∀ ν : ℤ,
    IsSquareIntegrableNear (CellCalculus.harmonicCos ν Pg) ∧ IsSquareIntegrableNear (CellCalculus.harmonicSin ν Pg)

def HarmonicPressureFlipHolds : Prop :=
  ∀ Pg : ℝ → Space → Space, CellCalculus.IsPeriodicPressure Pg →
    (∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) → ∀ ν : ℤ,
      (∀ᵐ y, CellCalculus.harmonicCos ν Pg (flipPoint y) = flipPoint (CellCalculus.harmonicCos ν Pg y)) ∧
      (∀ᵐ y, CellCalculus.harmonicSin ν Pg (flipPoint y) = flipPoint (CellCalculus.harmonicSin ν Pg y))

def StripDataFlipAxisHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3) (lo hi h h' : ℝ) (wt t : ℝ → ℝ),
      0 ≤ lo → lo < hi → 0 < h → 0 < h' → Continuous wt → Continuous t →
      heightStripMoment 0 h lo hi wt (planeVelocity (flipLabel ξ) v a) (planeGrad (flipLabel ξ) G a 2) t
        = (frameSign a : ℂ) * heightStripMoment 0 h' lo hi wt (planeVelocity ξ v a) (planeGrad ξ G a 2) t ∧
      (IsAxisAdmissibleTest lo (fun r => wt r * t r) →
        heightStripMoment 0 h lo hi wt (planeGrad (flipLabel ξ) G a 2) (planeSlope (flipLabel ξ) H a 2 2) t
          = -((frameSign a : ℂ) * heightStripMoment 0 h' lo hi wt (planeGrad ξ G a 2) (planeSlope ξ H a 2 2) t))

def CornerDataFlipAxisHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g → (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) →
    ∀ (ξ : ℤ × ℤ) (a : Fin 3) (cr orr h h' : ℝ), 0 < cr → 0 ≤ orr → cr ≠ orr → 0 < h → 0 < h' →
      cornerMoment cr orr 0 h (planeVelocity (flipLabel ξ) v a) (planeGrad (flipLabel ξ) G a 0)
          (planeGrad (flipLabel ξ) G a 2) (planeSlope (flipLabel ξ) H a 0 2)
        = (frameSign a : ℂ) * cornerMoment cr orr 0 h' (planeVelocity ξ v a) (planeGrad ξ G a 0)
          (planeGrad ξ G a 2) (planeSlope ξ H a 0 2)

structure RadialTraceParts : Prop where
  side_match : SideTraceMatchHolds
  axis_side : AxisSideTraceHolds
  radial_strip : RadialStripTraceHolds
  height_strip : HeightStripTraceHolds
  radial_deriv : ModeRadialDerivHolds

structure CornerPointTraceParts : Prop where
  corner_point : CornerPointTraceHolds
  corner_axis : CornerAxisTraceHolds
  plane_derivs : ModePlaneDerivsHolds

structure PressurePotentialTraceParts : Prop where
  pressure_deriv : PressureModeDerivHolds
  pressure_integrable : PressureModeIntegrableHolds
  pressure_flip : PressurePlaneFlipHolds
  potential_constant : PotentialConstantHolds
  potential_negation : PotentialNegationHolds
  potential_shift : PotentialShiftHolds
  potential_of_gradient : PotentialOfGradientHolds
  harmonic_square : HarmonicPressureSquareHolds
  harmonic_flip : HarmonicPressureFlipHolds

structure AxisPlaneFlipParts : Prop where
  strip_axis : StripDataFlipAxisHolds
  corner_axis : CornerDataFlipAxisHolds

structure StripIntegrabilityParts : Prop where
  plane_derivs : ModePlaneDerivsHolds
  axis_weighted : ModeAxisIntegrableHolds
  axis_plain : ModeAxisPlainIntegrableHolds

theorem pressureStripFlip_of_parts (hD : PressureModeDerivHolds) (hI : PressureModeIntegrableHolds)
    (hF : PressurePlaneFlipHolds) (hS : HeightStripTraceHolds) (hM : SideTraceMatchHolds) :
    PressureStripFlipHolds := by
  have weak_integrableOn_Icc : ∀ {f fd : ℝ → ℂ} (hw : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f fd zlo zhi) (a b : ℝ), IntegrableOn f (Set.Icc a b) ∧ IntegrableOn fd (Set.Icc a b) := by
    intro f fd hw a b
    have h := hw (min a b - 1) (max a b + 1) (by linarith [min_le_max (a := a) (b := b)])
    have hsub : Set.Icc a b ⊆ Set.Ioo (min a b - 1) (max a b + 1) := fun x hx =>
      ⟨by linarith [hx.1, min_le_left a b], by linarith [hx.2, le_max_right a b]⟩
    exact ⟨h.1.mono_set hsub, h.2.1.mono_set hsub⟩
  have weak_intervalIntegrable : ∀ {f fd : ℝ → ℂ} (hw : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f fd zlo zhi) (a b : ℝ), IntervalIntegrable fd volume a b := by
    intro f fd hw a b
    exact ⟨(weak_integrableOn_Icc hw a b).2.mono_set Set.Ioc_subset_Icc_self,
      (weak_integrableOn_Icc hw b a).2.mono_set Set.Ioc_subset_Icc_self⟩
  have sideTrace_split : ∀ (f fd : ℝ → ℂ) (c o : ℝ) (hf : IntegrableOn f (Set.Icc (min c o) (max c o))) (hfd : IntegrableOn fd (Set.Icc (min c o) (max c o))), sideTrace f fd c o = edgeSign c o * ((((1 / (c - o)) : ℝ) : ℂ) * ∫ r in Set.Icc (min c o) (max c o), f r) + edgeSign c o * ∫ r in Set.Icc (min c o) (max c o), (((r - o) / (c - o) : ℝ) : ℂ) * fd r := by
    intro f fd c o hf hfd
    unfold sideTrace
    rw [integral_add (hf.const_mul _), integral_const_mul, mul_add]
    exact hfd.continuousOn_mul (by fun_prop) isCompact_Icc
  have weighted_norm_le : ∀ (fd : ℝ → ℂ) (a b c o : ℝ) (hab : a ≤ b) (hfd : IntegrableOn fd (Set.Icc a b)) (hw : ∀ r ∈ Set.Icc a b, |(r - o) / (c - o)| ≤ 1), ‖∫ r in Set.Icc a b, (((r - o) / (c - o) : ℝ) : ℂ) * fd r‖ ≤ ∫ r in a..b, ‖fd r‖ := by
    intro fd a b c o hab hfd hw
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    refine norm_integral_le_of_norm_le hfd.norm ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw r hr)
  have line_flip : ∀ (f1 fd1 f2 fd2 : ℝ → ℂ) (h h' : ℝ) (hh : 0 < h) (hh' : 0 < h') (hM : SideTraceMatchHolds) (hw1 : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f1 fd1 zlo zhi) (hw2 : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f2 fd2 zlo zhi) (hfl : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), f1 z = f2 (-z)), sideTrace f1 fd1 0 h = sideTrace f2 fd2 0 h' := by
    intro f1 fd1 f2 fd2 h h' hh hh' hM hw1 hw2 hfl
    set k : ℝ → ℝ := fun x => (∫ r in (0 : ℝ)..x, ‖fd1 r‖) - ∫ r in (0 : ℝ)..(-x), ‖fd2 r‖ with hk
    have hkc : Continuous k := by
      have c1 := intervalIntegral.continuous_primitive (fun a b => (weak_intervalIntegrable hw1 a b).norm) 0
      have c2 := intervalIntegral.continuous_primitive (fun a b => (weak_intervalIntegrable hw2 a b).norm) 0
      exact c1.sub (c2.comp continuous_neg)
    have hk0 : k 0 = 0 := by simp [hk]
    have hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
        ‖sideTrace f1 fd1 0 h - sideTrace f2 fd2 0 h'‖ ≤ k ε := by
      intro ε hε hε1
      have e1 : sideTrace f1 fd1 0 h = sideTrace f1 fd1 0 ε :=
        hM f1 fd1 0 h ε (-1) (h + 2) hh.ne hε.ne
          (lt_min (by norm_num) (lt_min (by linarith) (by linarith)))
          (max_lt (by linarith) (max_lt (by linarith) (by linarith))) (hw1 _ _ (by linarith))
      have e2 : sideTrace f2 fd2 0 h' = sideTrace f2 fd2 0 (-ε) :=
        hM f2 fd2 0 h' (-ε) (-2) (h' + 1) hh'.ne (ne_of_gt (by linarith))
          (lt_min (by norm_num) (lt_min (by linarith) (by linarith)))
          (max_lt (by linarith) (max_lt (by linarith) (by linarith))) (hw2 _ _ (by linarith))
      have m1 : min (0 : ℝ) ε = 0 := min_eq_left hε.le
      have M1 : max (0 : ℝ) ε = ε := max_eq_right hε.le
      have m2 : min (0 : ℝ) (-ε) = -ε := min_eq_right (by linarith)
      have M2 : max (0 : ℝ) (-ε) = 0 := max_eq_left (by linarith)
      have s1 := sideTrace_split f1 fd1 0 ε (by rw [m1, M1]; exact (weak_integrableOn_Icc hw1 0 ε).1)
        (by rw [m1, M1]; exact (weak_integrableOn_Icc hw1 0 ε).2)
      have s2 := sideTrace_split f2 fd2 0 (-ε) (by rw [m2, M2]; exact (weak_integrableOn_Icc hw2 (-ε) 0).1)
        (by rw [m2, M2]; exact (weak_integrableOn_Icc hw2 (-ε) 0).2)
      rw [m1, M1] at s1
      rw [m2, M2] at s2
      have es1 : edgeSign 0 ε = -1 := by simp [edgeSign, not_lt.mpr hε.le]
      have es2 : edgeSign 0 (-ε) = 1 := by simp [edgeSign, hε]
      have hS : ∫ r in Set.Icc (-ε) 0, f2 r = ∫ r in Set.Icc 0 ε, f1 r := by
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hε.le]
        have hc := intervalIntegral.integral_comp_neg (a := 0) (b := ε) f2
        rw [neg_zero] at hc
        rw [← hc]
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hfl] with x hx hmem
        rw [Set.uIoc_of_le hε.le] at hmem
        exact (hx hmem.1).symm
      have b1 := weighted_norm_le fd1 0 ε 0 ε hε.le (weak_integrableOn_Icc hw1 0 ε).2 (fun r hr => by
        rw [abs_div, div_le_one (abs_pos.mpr (sub_ne_zero.mpr hε.ne)), abs_of_nonpos (by linarith [hr.2]),
          abs_of_neg (by linarith)]
        linarith [hr.1])
      have b2 := weighted_norm_le fd2 (-ε) 0 0 (-ε) (by linarith) (weak_integrableOn_Icc hw2 (-ε) 0).2
        (fun r hr => by
          rw [abs_div, div_le_one (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (by linarith)))),
            abs_of_nonneg (by linarith [hr.1]), abs_of_pos (by linarith)]
          linarith [hr.2])
      have hsym : ∫ r in (-ε)..0, ‖fd2 r‖ = -∫ r in (0 : ℝ)..(-ε), ‖fd2 r‖ := intervalIntegral.integral_symm _ _
      rw [e1, e2, s1, s2, es1, es2, hS]
      have hc : ((1 / (0 - ε) : ℝ) : ℂ) = -((1 / (0 - -ε) : ℝ) : ℂ) := by push_cast; ring
      rw [hc]
      set T1 := ∫ r in Set.Icc 0 ε, (((r - ε) / (0 - ε) : ℝ) : ℂ) * fd1 r
      set T2 := ∫ r in Set.Icc (-ε) 0, (((r - -ε) / (0 - -ε) : ℝ) : ℂ) * fd2 r
      have halg : -1 * (-((1 / (0 - -ε) : ℝ) : ℂ) * ∫ r in Set.Icc 0 ε, f1 r) + -1 * T1
          - (1 * (((1 / (0 - -ε) : ℝ) : ℂ) * ∫ r in Set.Icc 0 ε, f1 r) + 1 * T2) = -(T1 + T2) := by ring
      rw [halg, norm_neg]
      refine (norm_add_le _ _).trans ?_
      simp only [hk]
      linarith
    have htk : Filter.Tendsto k (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (hkc.continuousAt (x := 0)).tendsto
      rw [hk0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖sideTrace f1 fd1 0 h - sideTrace f2 fd2 0 h'‖ ≤ k ε := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε using hbound ε hε.1 hε.2
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto htk hev))
  have weighted_strip_integrable : ∀ (G : ℝ × ℝ → ℂ) (lo hi zlo zhi : ℝ) (wt t : ℝ → ℝ) (hadm : IsAxisAdmissibleTest lo (fun r => wt r * t r)) (hwt : Continuous wt) (ht : Continuous t) (hplain : 0 < lo → IntegrableOn G (Set.Icc lo hi ×ˢ Set.Icc zlo zhi)) (hweighted : IntegrableOn (fun p => (p.1 : ℂ) * G p) (Set.Icc 0 hi ×ˢ Set.Icc zlo zhi)), IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * G p) (Set.Icc lo hi ×ˢ Set.Icc zlo zhi) := by
    intro G lo hi zlo zhi wt t hadm hwt ht hplain hweighted
    rcases hadm with hlo | ⟨rfl, t₀, ht₀, hrt⟩
    · exact (hplain hlo).continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
    · have he : (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * G p)
          = fun p => ((t₀ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) * G p) := by
        funext p
        have hp := hrt p.1
        simp only at hp
        rw [hp]
        push_cast
        ring
      rw [he]
      exact hweighted.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  intro m Q q hm hQ hsq hflipQ n lo hi h h' wt t hadm hlohi hh hh' hwt ht
  have hlo : 0 ≤ lo := by
    rcases hadm with h0 | ⟨h0, _⟩
    · exact h0.le
    · exact h0.ge
  have hhi : 0 < hi := lt_of_le_of_lt hlo hlohi
  have intF : ∀ (k : ℤ) (c : ℝ), 0 < c →
      IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * presMode m k q p.1 p.2)
        (Set.Icc lo hi ×ˢ Set.Icc (min 0 c) (max 0 c)) := by
    intro k c hc
    rw [min_eq_left hc.le, max_eq_right hc.le]
    have hk := ((hI m Q q hm hQ hsq k 2 hi 0 c hhi hc).1).mono_set
      (Set.prod_mono (Set.Icc_subset_Icc_left hlo) le_rfl)
    exact hk.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  have intD : ∀ (k : ℤ) (c : ℝ), 0 < c →
      IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * modeVec m k Q p.1 p.2 2)
        (Set.Icc lo hi ×ˢ Set.Icc (min 0 c) (max 0 c)) := by
    intro k c hc
    rw [min_eq_left hc.le, max_eq_right hc.le]
    have hk := hI m Q q hm hQ hsq k 2 hi 0 c hhi hc
    exact weighted_strip_integrable (fun p => modeVec m k Q p.1 p.2 2) lo hi 0 c wt t hadm hwt ht
      (fun hl => hk.2.2 lo hl hlohi) hk.2.1
  rw [hS 0 h lo hi wt (fun p => presMode m (-n) q p.1 p.2) (fun p => modeVec m (-n) Q p.1 p.2 2) t
      hh.ne hlohi hwt ht (intF (-n) h hh) (intD (-n) h hh),
    hS 0 h' lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t
      hh'.ne hlohi hwt ht (intF n h' hh') (intD n h' hh')]
  have hDm := (hD m Q q hm hQ hsq (-n)).2
  have hDp := (hD m Q q hm hQ hsq n).2
  have hFl := hF m Q q hm hQ hsq hflipQ (-n)
  simp only [neg_neg] at hFl
  have hFl2 : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      presMode m n q r (-z) = presMode m (-n) q r z := by
    have e : volume.restrict Breakdown.CertCell.halfPlane
        = (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      rfl
    rw [e] at hFl
    exact Measure.ae_ae_of_ae_prod hFl
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hDm, (ae_restrict_iff' measurableSet_Ioi).1 hDp,
    (ae_restrict_iff' measurableSet_Ioi).1 hFl2] with r h1 h2 h3 hmem
  have hr : (0 : ℝ) < r := lt_of_le_of_lt hlo hmem.1
  congr 1
  exact line_flip _ _ _ _ h h' hh hh' hM (h1 hr) (h2 hr)
    (by filter_upwards [h3 hr] with z hz using hz.symm)

theorem pressureDataMatch_of_parts (hD : PressureModeDerivHolds) (hI : PressureModeIntegrableHolds)
    (hR : RadialStripTraceHolds) (hS : HeightStripTraceHolds) (hM : SideTraceMatchHolds) (hA : AxisSideTraceHolds) :
    PressureDataMatchHolds := by
  have weakDerivOn_of_le : ∀ (f fd : ℝ → ℂ) {a b : ℝ} (hab : b ≤ a), HasWeakDerivOn f fd a b := by
    intro f fd a b hab
    have he : Set.Ioo a b = ∅ := Set.Ioo_eq_empty (not_lt.mpr hab)
    refine ⟨?_, ?_, ?_⟩
    · rw [he]; exact integrableOn_empty
    · rw [he]; exact integrableOn_empty
    · intro ψ _ _ _
      rw [he]; simp
  have sectionIntegrable : ∀ {f : ℝ × ℝ → ℂ} {s u : Set ℝ} (hf : IntegrableOn f (s ×ˢ u)), ∀ᵐ z ∂(volume.restrict u), IntegrableOn (fun r => f (r, z)) s := by
    intro f s u hf
    have h : Integrable f ((volume.restrict s).prod (volume.restrict u)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hf
    exact h.prod_left_ae
  have radialSideTraceEq : ∀ (hA : AxisSideTraceHolds) (hM : SideTraceMatchHolds) (f fd : ℝ → ℂ) {c o o' : ℝ} (hc : 0 < c) (ho : 0 ≤ o) (ho' : 0 ≤ o') (hco : c ≠ o) (hco' : c ≠ o') (hd : ∀ lo hi : ℝ, 0 < lo → lo < hi → HasWeakDerivOn f fd lo hi) (hf : IntegrableOn f (Set.Ioo 0 (max c (max o o') + 1))) (hfd : IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ) * fd r) (Set.Ioo 0 (max c (max o o') + 1))), sideTrace f fd c o = sideTrace f fd c o' := by
    intro hA hM f fd c o o' hc ho ho' hco hco' hd hf hfd
    have hdb : ∀ lo, 0 < lo → HasWeakDerivOn f fd lo (max c (max o o') + 1) := by
      intro lo hlo
      rcases lt_or_ge lo (max c (max o o') + 1) with h | h
      · exact hd lo _ hlo h
      · exact weakDerivOn_of_le f fd h
    have hcb : max c o < max c (max o o') + 1 :=
      lt_of_le_of_lt (max_le_max le_rfl (le_max_left _ _)) (lt_add_one _)
    have hcb' : max c o' < max c (max o o') + 1 :=
      lt_of_le_of_lt (max_le_max le_rfl (le_max_right _ _)) (lt_add_one _)
    rcases eq_or_lt_of_le ho with h0 | hpos
    · rw [← h0]
      exact hA f fd c o' _ hc ho' hco' hcb' hdb hf hfd
    · rcases eq_or_lt_of_le ho' with h0' | hpos'
      · rw [← h0']
        exact (hA f fd c o _ hc ho hco hcb hdb hf hfd).symm
      · have hmin : 0 < min c (min o o') := lt_min hc (lt_min hpos hpos')
        have ha : min c (min o o') / 2 < min c (min o o') := half_lt_self hmin
        have hab : min c (min o o') / 2 < max c (max o o') + 1 :=
          lt_trans ha (lt_of_le_of_lt (le_trans (min_le_left _ _) (le_max_left _ _)) (lt_add_one _))
        exact hM f fd c o o' _ _ hco hco' ha (lt_add_one _) (hd _ _ (half_pos hmin) hab)
  have heightSideTraceEq : ∀ (hM : SideTraceMatchHolds) (f fd : ℝ → ℂ) {c o o' : ℝ} (hco : c ≠ o) (hco' : c ≠ o') (hd : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f fd zlo zhi), sideTrace f fd c o = sideTrace f fd c o' := by
    intro hM f fd c o o' hco hco' hd
    have ha : min c (min o o') - 1 < min c (min o o') := sub_one_lt _
    have hb : max c (max o o') < max c (max o o') + 1 := lt_add_one _
    have hab : min c (min o o') - 1 < max c (max o o') + 1 :=
      lt_trans ha (lt_of_le_of_lt (le_trans (min_le_left _ _) (le_max_left _ _)) hb)
    exact hM f fd c o o' _ _ hco hco' ha hb (hd _ _ hab)
  have continuousOn_ofReal_comp : ∀ {K : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℝ} (hg : Continuous g), ContinuousOn (fun p => ((g p : ℝ) : ℂ)) K := by
    intro K g hg
    exact (Complex.continuous_ofReal.comp hg).continuousOn
  have presRadialMatch : ∀ (hD : PressureModeDerivHolds) (hI : PressureModeIntegrableHolds) (hR : RadialStripTraceHolds) (hM : SideTraceMatchHolds) (hA : AxisSideTraceHolds) {m : ℕ} {Q : Space → Space} {q : Space → ℝ} (hm : 1 ≤ m) (hq : IsPotentialOf Q q) (hQ : IsSquareIntegrableNear Q) (n : ℤ) {c o o' lo hi : ℝ} {t : ℝ → ℝ} (hc : 0 < c) (ho : 0 ≤ o) (ho' : 0 ≤ o') (hco : c ≠ o) (hco' : c ≠ o') (hlo : lo < hi) (ht : Continuous t), radialStripMoment c o lo hi (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 0) t = radialStripMoment c o' lo hi (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 0) t := by
    intro hD hI hR hM hA m Q q hm hq hQ n c o o' lo hi t hc ho ho' hco hco' hlo ht
    have hK : ∀ e : ℝ, IsCompact (Set.Icc (min c e) (max c e) ×ˢ Set.Icc lo hi) :=
      fun e => isCompact_Icc.prod isCompact_Icc
    have hvalue : ∀ e : ℝ, 0 ≤ e → c ≠ e →
        IntegrableOn (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ) * presMode m n q p.1 p.2)
          (Set.Icc (min c e) (max c e) ×ˢ Set.Icc lo hi) := by
      intro e he _
      have hmax : 0 < max c e := lt_of_lt_of_le hc (le_max_left _ _)
      have h1 := (hI m Q q hm hq hQ n 0 (max c e) lo hi hmax hlo).1
      have h2 := h1.mono_set (Set.prod_mono (Set.Icc_subset_Icc (le_min hc.le he) le_rfl) subset_rfl)
      exact IntegrableOn.continuousOn_mul (g := fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ))
        (continuousOn_ofReal_comp (ht.comp continuous_snd)) h2 (hK e)
    have hslope : ∀ e : ℝ, 0 ≤ e → c ≠ e →
        IntegrableOn (fun p : ℝ × ℝ => (((p.1 - e) * t p.2 : ℝ) : ℂ) * modeVec m n Q p.1 p.2 0)
          (Set.Icc (min c e) (max c e) ×ˢ Set.Icc lo hi) := by
      intro e he hce
      have hmax : 0 < max c e := lt_of_lt_of_le hc (le_max_left _ _)
      rcases eq_or_lt_of_le he with h0 | hpos
      · subst h0
        have h1 := (hI m Q q hm hq hQ n 0 (max c 0) lo hi hmax hlo).2.1
        have h2 := h1.mono_set (Set.prod_mono (Set.Icc_subset_Icc (le_min hc.le le_rfl) le_rfl) subset_rfl)
        have h3 := IntegrableOn.mul_continuousOn (g := fun p : ℝ × ℝ => ((p.1 : ℂ) * modeVec m n Q p.1 p.2 0))
          (g' := fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) h2 (continuousOn_ofReal_comp (ht.comp continuous_snd)) (hK 0)
        refine h3.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        push_cast
        ring
      · have hmin : 0 < min c e := lt_min hc hpos
        have h1 := (hI m Q q hm hq hQ n 0 (max c e) lo hi hmax hlo).2.2 (min c e) hmin (min_lt_max.mpr hce)
        exact IntegrableOn.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.1 - e) * t p.2 : ℝ) : ℂ))
          (continuousOn_ofReal_comp (((continuous_fst.sub continuous_const).mul (ht.comp continuous_snd)))) h1 (hK e)
    rw [hR c o lo hi _ _ t hco hlo ht (hvalue o ho hco) (hslope o ho hco),
      hR c o' lo hi _ _ t hco' hlo ht (hvalue o' ho' hco') (hslope o' ho' hco')]
    refine integral_congr_ae ?_
    have hb : 0 < max c (max o o') + 1 :=
      lt_of_lt_of_le hc (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one))
    have hJ := hI m Q q hm hq hQ n 0 (max c (max o o') + 1) lo hi hb hlo
    have s1 := sectionIntegrable hJ.1
    have s2 := sectionIntegrable hJ.2.1
    have hd := ae_restrict_of_ae (μ := volume) (s := Set.Icc lo hi) (hD m Q q hm hq hQ n).1
    filter_upwards [s1, s2, hd] with z h1 h2 h3
    have key := radialSideTraceEq hA hM (fun r => presMode m n q r z) (fun r => modeVec m n Q r z 0) hc ho ho'
      hco hco' h3 (h1.mono_set Set.Ioo_subset_Icc_self) (h2.mono_set Set.Ioo_subset_Icc_self)
    exact congrArg (fun s => ((t z : ℝ) : ℂ) * s) key
  have presHeightMatch : ∀ (hD : PressureModeDerivHolds) (hI : PressureModeIntegrableHolds) (hS : HeightStripTraceHolds) (hM : SideTraceMatchHolds) {m : ℕ} {Q : Space → Space} {q : Space → ℝ} (hm : 1 ≤ m) (hq : IsPotentialOf Q q) (hQ : IsSquareIntegrableNear Q) (n : ℤ) {c o o' lo hi : ℝ} {wt t : ℝ → ℝ} (hco : c ≠ o) (hco' : c ≠ o') (hadm : IsAxisAdmissibleTest lo (fun r => wt r * t r)) (hlo : lo < hi) (hwt : Continuous wt) (ht : Continuous t), heightStripMoment c o lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t = heightStripMoment c o' lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t := by
    intro hD hI hS hM m Q q hm hq hQ n c o o' lo hi wt t hco hco' hadm hlo hwt ht
    have h0lo : 0 ≤ lo := by
      rcases hadm with h | h
      · exact h.le
      · exact h.1.ge
    have hhi : 0 < hi := lt_of_le_of_lt h0lo hlo
    have hK : ∀ e : ℝ, IsCompact (Set.Icc lo hi ×ˢ Set.Icc (min c e) (max c e)) :=
      fun e => isCompact_Icc.prod isCompact_Icc
    have hwc : ContinuousOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ)) (Set.univ) :=
      continuousOn_ofReal_comp ((hwt.comp continuous_fst).mul (ht.comp continuous_fst))
    have hvalue : ∀ e : ℝ, c ≠ e →
        IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * presMode m n q p.1 p.2)
          (Set.Icc lo hi ×ˢ Set.Icc (min c e) (max c e)) := by
      intro e hce
      have h1 := (hI m Q q hm hq hQ n 2 hi (min c e) (max c e) hhi (min_lt_max.mpr hce)).1
      have h2 := h1.mono_set (Set.prod_mono (Set.Icc_subset_Icc h0lo le_rfl) subset_rfl)
      exact IntegrableOn.continuousOn_mul (g := fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ))
        (hwc.mono (Set.subset_univ _)) h2 (hK e)
    have hslope : ∀ e : ℝ, c ≠ e →
        IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * modeVec m n Q p.1 p.2 2)
          (Set.Icc lo hi ×ˢ Set.Icc (min c e) (max c e)) := by
      intro e hce
      have hJ := hI m Q q hm hq hQ n 2 hi (min c e) (max c e) hhi (min_lt_max.mpr hce)
      rcases hadm with hpos | ⟨h0, t₀, ht₀, hfac⟩
      · exact IntegrableOn.continuousOn_mul (g := fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ))
          (hwc.mono (Set.subset_univ _)) (hJ.2.2 lo hpos hlo) (hK e)
      · subst h0
        have h3 := IntegrableOn.mul_continuousOn (g := fun p : ℝ × ℝ => ((p.1 : ℂ) * modeVec m n Q p.1 p.2 2))
          (g' := fun p : ℝ × ℝ => ((t₀ p.1 : ℝ) : ℂ)) hJ.2.1 (continuousOn_ofReal_comp (ht₀.comp continuous_fst))
          (hK e)
        refine h3.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        have hp := hfac p.1
        simp only at hp
        rw [hp]
        push_cast
        ring
    rw [hS c o lo hi wt _ _ t hco hlo hwt ht (hvalue o hco) (hslope o hco),
      hS c o' lo hi wt _ _ t hco' hlo hwt ht (hvalue o' hco') (hslope o' hco')]
    refine integral_congr_ae ?_
    have hd := (ae_restrict_iff' measurableSet_Ioi).mp (hD m Q q hm hq hQ n).2
    have hne : ∀ᵐ r : ℝ, r ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (s := Set.Icc lo hi) hd,
      ae_restrict_of_ae (s := Set.Icc lo hi) hne] with r hr h3 h4
    have hrpos : (0 : ℝ) < r := lt_of_le_of_ne (le_trans h0lo hr.1) (Ne.symm h4)
    have key := heightSideTraceEq hM (fun z => presMode m n q r z) (fun z => modeVec m n Q r z 2) hco hco'
      (h3 hrpos)
    exact congrArg (fun s => ((wt r * t r : ℝ) : ℂ) * s) key
  intro m Q q hm hq hQ n
  refine ⟨?_, ?_⟩
  · intro c o o' lo hi t hc ho ho' hco hco' hlo ht
    exact presRadialMatch hD hI hR hM hA hm hq hQ n hc ho ho' hco hco' hlo ht
  · intro c o o' lo hi wt t hco hco' hadm hlo hwt ht
    exact presHeightMatch hD hI hS hM hm hq hQ n hco hco' hadm hlo hwt ht

end SideTrace

end CertCell

end Breakdown

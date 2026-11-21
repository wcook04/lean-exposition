import Breakdown.CertCell.AssemblyTiedParts
import Breakdown.CertCell.HarmonicSideData
import Breakdown.CertCell.HarmonicProfiles

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField
  CellCalculus

namespace Internal.HarmonicCorner

open CellCalculus.Internal.HarmonicSide

theorem corner_split (cr orr cz oz : ℝ)
    {F Fr Fz Frz F₁ Fr₁ Fz₁ Frz₁ F₂ Fr₂ Fz₂ Frz₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn (fun p : ℝ × ℝ => ((1 / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ) * F₁ p
        + ((1 / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz₁ p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ) * Fr₁ p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz₁ p)
      (Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz)))
    (h₂ : IntegrableOn (fun p : ℝ × ℝ => ((1 / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ) * F₂ p
        + ((1 / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz₂ p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ) * Fr₂ p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz₂ p)
      (Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz)))
    (he : ∀ᵐ p ∂(volume.restrict (Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz))),
      F p = F₁ p + Complex.I * F₂ p ∧ Fr p = Fr₁ p + Complex.I * Fr₂ p ∧
        Fz p = Fz₁ p + Complex.I * Fz₂ p ∧ Frz p = Frz₁ p + Complex.I * Frz₂ p) :
    cornerMoment cr orr cz oz F Fr Fz Frz =
      cornerMoment cr orr cz oz F₁ Fr₁ Fz₁ Frz₁ + Complex.I * cornerMoment cr orr cz oz F₂ Fr₂ Fz₂ Frz₂ := by
  unfold cornerMoment
  rw [integral_split h₁ h₂]
  · ring
  · filter_upwards [he] with p hp
    rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    ring

theorem one_term {s : Set (ℝ × ℝ)} (hs : IsCompact s) {A : ℝ × ℝ → ℂ} (h : IntegrableOn A s)
    (g : ℝ × ℝ → ℂ) (hg : Continuous g) : IntegrableOn (fun p => g p * A p) s :=
  h.continuousOn_mul hg.continuousOn hs

theorem corner_int {K : CellBox} {V Dr Dz T : ℝ × ℝ → ℂ} (hV : IntegrableOn V K.rect)
    (hr : IntegrableOn Dr K.rect) (hz : IntegrableOn Dz K.rect)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * T p) K.rect) (cr orr cz oz : ℝ) (hne : cr ≠ orr)
    (hcase : orr = 0 ∨ 0 < K.r₁) :
    IntegrableOn (fun p : ℝ × ℝ => ((1 / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ) * V p
        + ((1 / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Dz p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ) * Dr p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * T p) K.rect := by
  have hs := rect_compact K
  have hm := rect_measurable K
  have cz' : Continuous (fun p : ℝ × ℝ => (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)
  have cr' : Continuous (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)
  have i1 := one_term hs hV (fun _ => ((1 / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ)) continuous_const
  have i2 := one_term hs hz (fun p => ((1 / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ))
    (continuous_const.mul cz')
  have i3 := one_term hs hr (fun p => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * ((1 / (cz - oz) : ℝ) : ℂ))
    (cr'.mul continuous_const)
  have i4 : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ)
      * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * T p) K.rect := by
    rcases hcase with rfl | hpos
    · refine (one_term hs hT (fun p => ((1 / (cr - 0) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ))
        (continuous_const.mul ?_)).congr_fun (fun p _ => ?_) hm
      · exact Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)
      · simp only
        push_cast
        ring
    · have hne0 : ∀ p ∈ K.rect, p.1 ≠ 0 := fun p hp => ne_of_gt (lt_of_lt_of_le hpos hp.1.1)
      have hlo' : cr - orr ≠ 0 := sub_ne_zero.2 hne
      refine (hT.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.1 - orr) / ((cr - orr) * p.1) : ℝ) : ℂ)
          * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) ?_ hs).congr_fun (fun p hp => ?_) hm
      · exact (Complex.continuous_ofReal.comp_continuousOn
          ((continuous_fst.sub continuous_const).continuousOn.div (continuous_const.mul continuous_fst).continuousOn
            (fun p hp => mul_ne_zero hlo' (hne0 p hp)))).mul cz'.continuousOn
      · have h1 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hne0 p hp
        have h2 : (cr : ℂ) - (orr : ℂ) ≠ 0 := by exact_mod_cast hlo'
        push_cast
        field_simp
  refine (((i1.add i2).add i3).add i4).congr_fun (fun p _ => ?_) hm
  simp only [Pi.add_apply]

theorem stream_int {V D : ℝ × ℝ → ℂ} {R a b : ℝ} (hV : IntegrableOn V (Icc 0 R ×ˢ Icc a b))
    (hD : IntegrableOn D (Icc 0 R ×ˢ Icc a b)) (l o : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (((1 / (l - o) : ℝ) : ℂ) * V p + (((p.2 - o) / (l - o) : ℝ) : ℂ) * D p)
      * (((fun r : ℝ => r) p.1 : ℝ) : ℂ)) (Icc 0 R ×ˢ Icc a b) :=
  two_term (isCompact_Icc.prod isCompact_Icc) (measurableSet_Icc.prod measurableSet_Icc) hV hD
    (g₁ := fun p => ((1 / (l - o) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ))
    (g₂ := fun p => (((p.2 - o) / (l - o) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ))
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).continuousOn
    ((Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).mul
      (Complex.continuous_ofReal.comp continuous_fst)).continuousOn
    (fun _ _ => by ring)

theorem corner_rect {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hLay : IsCellLayout c K S B L) (i : Fin L.cornerCount) :
    Icc (min (L.corner i).1 (L.cornerOther i).1) (max (L.corner i).1 (L.cornerOther i).1) ×ˢ
      Icc (min (L.corner i).2 (L.cornerOther i).2) (max (L.corner i).2 (L.cornerOther i).2) = K.rect := by
  have hcc := hLay.corner_is_corner i
  have hco := hLay.corner_other i
  rw [hco.1, hco.2, pair_Icc hLay.box_valid.r_order.2 hcc.1, pair_Icc hLay.box_valid.z_order.2 hcc.2.1]
  rfl

theorem corner_ne {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hLay : IsCellLayout c K S B L) (i : Fin L.cornerCount) :
    (L.corner i).1 ≠ (L.cornerOther i).1 := by
  have hK := hLay.box_valid.r_order.2
  rw [(hLay.corner_other i).1]
  rcases (hLay.corner_is_corner i).1 with h | h <;> rw [h] <;> intro h' <;> linarith

theorem corner_case {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hLay : IsCellLayout c K S B L) (i : Fin L.cornerCount) :
    (L.cornerOther i).1 = 0 ∨ 0 < K.r₁ := by
  obtain ⟨hlev, -, hl0⟩ := hLay.corner_is_corner i
  rcases eq_or_lt_of_le hLay.box_valid.r_order.1 with h0 | h0
  · left
    rw [(hLay.corner_other i).1]
    rcases hlev with h | h
    · exact absurd (h.trans h0.symm) hl0
    · rw [h, ← h0]
      ring
  · exact Or.inr h0

end Internal.HarmonicCorner

open CellCalculus.Internal.HarmonicSide Internal.HarmonicCorner in
theorem harmonicCornerData_of (h1 : HarmonicLiftStatement) : HarmonicCornerDataStatement := by
  intro m K B L hL v G H Pg hvGH _ ν
  obtain ⟨c, S, hco, -, hLay⟩ := hL
  have hord : L.order = m := hLay.order_eq.trans hco
  have hK : IsCellBox K := hLay.box_valid
  obtain ⟨hcos, hsin, hae⟩ := h1 m v G H hvGH ν
  have eV : ∀ (n : ℤ) a, L.velMode n (cosTuple ν v G H Pg) a
        = (fun p : ℝ × ℝ => modeVec m n (harmonicCos ν v) p.1 p.2 a) ∧
      L.velMode n (sinTuple ν v G H Pg) a = (fun p : ℝ × ℝ => modeVec m n (harmonicSin ν v) p.1 p.2 a) :=
    fun _ _ => ⟨by rw [← hord]; rfl, by rw [← hord]; rfl⟩
  have eG : ∀ (n : ℤ) a b, L.gradModeOf n (cosTuple ν v G H Pg) a b = gradMode m n (harmonicCos ν G) a b ∧
      L.gradModeOf n (sinTuple ν v G H Pg) a b = gradMode m n (harmonicSin ν G) a b :=
    fun _ _ _ => ⟨by rw [← hord]; rfl, by rw [← hord]; rfl⟩
  have eT : ∀ (n : ℤ) a b c, L.secondModeOf n (cosTuple ν v G H Pg) a b c = modeThird m n (harmonicCos ν H) a b c ∧
      L.secondModeOf n (sinTuple ν v G H Pg) a b c = modeThird m n (harmonicSin ν H) a b c :=
    fun _ _ _ _ => ⟨by rw [← hord]; rfl, by rw [← hord]; rfl⟩
  refine ⟨fun n hn i a => ?_, fun hν i => ?_⟩
  · have hprof := hae n hn
    obtain ⟨cV, cG, cT⟩ := field_integrable hcos hK m n
    obtain ⟨sV, sG, sT⟩ := field_integrable hsin hK m n
    simp only [harmonicData, CellLayout.trueData, CellDatum.cornerVelocity, Sum.elim_inr, Sum.elim_inl]
    rw [(eV n a).1, (eV n a).2, (eG n a 0).1, (eG n a 0).2, (eG n a 2).1, (eG n a 2).2, (eT n a 0 2).1,
      (eT n a 0 2).2]
    symm
    have hrect := corner_rect hLay i
    have hne := corner_ne hLay i
    have hcase := corner_case hLay i
    refine corner_split _ _ _ _ ?_ ?_ ?_
    · rw [hrect]
      exact corner_int (cV a) (cG a 0) (cG a 2) (cT a 0 2) _ _ _ _ hne hcase
    · rw [hrect]
      exact corner_int (sV a) (sG a 0) (sG a 2) (sT a 0 2) _ _ _ _ hne hcase
    · rw [hrect]
      exact ae_on_nonneg (rect_measurable K) (rect_nonneg hK subset_rfl)
        (hprof.mono fun p hp hpos => ⟨(hp hpos).1 a, (hp hpos).2.1 a 0, (hp hpos).2.1 a 2, (hp hpos).2.2 a 0 2⟩)
  · have hprof := hae 0 (by simpa using hν)
    have hcS := localModeStripIntegrable m _ _ _ hcos 0 (L.corner i).1
      (min (L.corner i).2 (L.cornerOther i).2) (max (L.corner i).2 (L.cornerOther i).2)
    have hsS := localModeStripIntegrable m _ _ _ hsin 0 (L.corner i).1
      (min (L.corner i).2 (L.cornerOther i).2) (max (L.corner i).2 (L.cornerOther i).2)
    simp only [harmonicData, CellLayout.trueData, CellDatum.cornerStream, Sum.elim_inr, Sum.elim_inl]
    rw [(eV 0 2).1, (eV 0 2).2, (eG 0 2 2).1, (eG 0 2 2).2]
    symm
    exact height_split _ _ _ _ (fun r => r) _ continuous_const
      (stream_int (hcS.1 2) (hcS.2 2 2) _ _) (stream_int (hsS.1 2) (hsS.2 2 2) _ _)
      (ae_on_nonneg (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => hp.1.1)
        (hprof.mono fun p hp hpos => ⟨(hp hpos).1 2, (hp hpos).2.1 2 2⟩))

theorem harmonicCornerData_holds : HarmonicCornerDataStatement :=
  harmonicCornerData_of harmonicLift_holds

end Assembly

end CertCell

end Breakdown

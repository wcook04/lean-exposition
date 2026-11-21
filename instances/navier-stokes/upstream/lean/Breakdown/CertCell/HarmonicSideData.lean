import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.CertCell.LocalResolvedEnergy

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.HarmonicSide

theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : (volume : Measure (ℝ × ℝ)) ({0} ×ˢ univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with p hp h0
  exact hp ⟨h0, trivial⟩

theorem ae_on_nonneg {P : ℝ × ℝ → Prop} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (h0 : ∀ p ∈ s, 0 ≤ p.1)
    (h : ∀ᵐ p ∂volume, 0 < p.1 → P p) : ∀ᵐ p ∂(volume.restrict s), P p := by
  rw [ae_restrict_iff' hs]
  filter_upwards [h, ae_fst_ne_zero] with p hp hne hmem
  exact hp (lt_of_le_of_ne (h0 p hmem) (Ne.symm hne))

theorem integral_split {s : Set (ℝ × ℝ)} {f f₁ f₂ : ℝ × ℝ → ℂ} (h₁ : IntegrableOn f₁ s)
    (h₂ : IntegrableOn f₂ s) (he : ∀ᵐ p ∂(volume.restrict s), f p = f₁ p + Complex.I * f₂ p) :
    ∫ p in s, f p = (∫ p in s, f₁ p) + Complex.I * ∫ p in s, f₂ p := by
  rw [integral_congr_ae he, integral_add h₁ (h₂.const_mul Complex.I), integral_const_mul]

theorem radial_split (c o lo hi : ℝ) (t : ℝ → ℝ) (ht : Continuous t) {F dF F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * F₁ p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF₁ p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (h₂ : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * F₂ p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF₂ p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (he : ∀ᵐ p ∂(volume.restrict (Icc (min c o) (max c o) ×ˢ Icc lo hi)),
      F p = F₁ p + Complex.I * F₂ p ∧ dF p = dF₁ p + Complex.I * dF₂ p) :
    radialStripMoment c o lo hi F dF t =
      radialStripMoment c o lo hi F₁ dF₁ t + Complex.I * radialStripMoment c o lo hi F₂ dF₂ t := by
  have hc : IsCompact (Icc (min c o) (max c o) ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  have htc : ContinuousOn (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) (Icc (min c o) (max c o) ×ˢ Icc lo hi) :=
    (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).continuousOn
  unfold radialStripMoment
  rw [integral_split (h₁.mul_continuousOn htc hc) (h₂.mul_continuousOn htc hc)]
  · ring
  · filter_upwards [he] with p hp
    rw [hp.1, hp.2]
    ring

theorem height_split (c o lo hi : ℝ) (wt t : ℝ → ℝ) (ht : Continuous t) {F dF F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * F₁ p
        + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF₁ p) * ((wt p.1 : ℝ) : ℂ))
      (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (h₂ : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * F₂ p
        + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF₂ p) * ((wt p.1 : ℝ) : ℂ))
      (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (he : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc (min c o) (max c o))),
      F p = F₁ p + Complex.I * F₂ p ∧ dF p = dF₁ p + Complex.I * dF₂ p) :
    heightStripMoment c o lo hi wt F dF t =
      heightStripMoment c o lo hi wt F₁ dF₁ t + Complex.I * heightStripMoment c o lo hi wt F₂ dF₂ t := by
  have hc : IsCompact (Icc lo hi ×ˢ Icc (min c o) (max c o)) := isCompact_Icc.prod isCompact_Icc
  have hm : MeasurableSet (Icc lo hi ×ˢ Icc (min c o) (max c o)) := measurableSet_Icc.prod measurableSet_Icc
  have htc : ContinuousOn (fun p : ℝ × ℝ => ((t p.1 : ℝ) : ℂ)) (Icc lo hi ×ˢ Icc (min c o) (max c o)) :=
    (Complex.continuous_ofReal.comp (ht.comp continuous_fst)).continuousOn
  have k₁ : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * F₁ p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF₁ p) * ((wt p.1 * t p.1 : ℝ) : ℂ))
      (Icc lo hi ×ˢ Icc (min c o) (max c o)) :=
    (h₁.mul_continuousOn htc hc).congr_fun (fun p _ => by push_cast; ring) hm
  have k₂ : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * F₂ p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF₂ p) * ((wt p.1 * t p.1 : ℝ) : ℂ))
      (Icc lo hi ×ˢ Icc (min c o) (max c o)) :=
    (h₂.mul_continuousOn htc hc).congr_fun (fun p _ => by push_cast; ring) hm
  unfold heightStripMoment
  rw [integral_split k₁ k₂]
  · ring
  · filter_upwards [he] with p hp
    rw [hp.1, hp.2]
    ring

theorem test_continuous (Sg : FaceSegment) (d : ℕ) : Continuous (Sg.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem moment_split (Sg : FaceSegment) (w : Bool) (d : ℕ) {F Fr Fz F₁ Fr₁ Fz₁ F₂ Fr₂ Fz₂ : ℝ × ℝ → ℂ}
    (hrad : Sg.radial = true →
      IntegrableOn (fun p : ℝ × ℝ => ((1 / (Sg.level - Sg.other) : ℝ) : ℂ) * F₁ p
        + (((p.1 - Sg.other) / (Sg.level - Sg.other) : ℝ) : ℂ) * Fr₁ p)
        (Icc (min Sg.level Sg.other) (max Sg.level Sg.other) ×ˢ Icc Sg.lo Sg.hi) ∧
      IntegrableOn (fun p : ℝ × ℝ => ((1 / (Sg.level - Sg.other) : ℝ) : ℂ) * F₂ p
        + (((p.1 - Sg.other) / (Sg.level - Sg.other) : ℝ) : ℂ) * Fr₂ p)
        (Icc (min Sg.level Sg.other) (max Sg.level Sg.other) ×ˢ Icc Sg.lo Sg.hi) ∧
      ∀ᵐ p ∂(volume.restrict (Icc (min Sg.level Sg.other) (max Sg.level Sg.other) ×ˢ Icc Sg.lo Sg.hi)),
        F p = F₁ p + Complex.I * F₂ p ∧ Fr p = Fr₁ p + Complex.I * Fr₂ p)
    (hhei : ¬ Sg.radial = true →
      IntegrableOn (fun p : ℝ × ℝ => (((1 / (Sg.level - Sg.other) : ℝ) : ℂ) * F₁ p
        + (((p.2 - Sg.other) / (Sg.level - Sg.other) : ℝ) : ℂ) * Fz₁ p) * (((if w then p.1 else 1 : ℝ)) : ℂ))
        (Icc Sg.lo Sg.hi ×ˢ Icc (min Sg.level Sg.other) (max Sg.level Sg.other)) ∧
      IntegrableOn (fun p : ℝ × ℝ => (((1 / (Sg.level - Sg.other) : ℝ) : ℂ) * F₂ p
        + (((p.2 - Sg.other) / (Sg.level - Sg.other) : ℝ) : ℂ) * Fz₂ p) * (((if w then p.1 else 1 : ℝ)) : ℂ))
        (Icc Sg.lo Sg.hi ×ˢ Icc (min Sg.level Sg.other) (max Sg.level Sg.other)) ∧
      ∀ᵐ p ∂(volume.restrict (Icc Sg.lo Sg.hi ×ˢ Icc (min Sg.level Sg.other) (max Sg.level Sg.other))),
        F p = F₁ p + Complex.I * F₂ p ∧ Fz p = Fz₁ p + Complex.I * Fz₂ p) :
    Sg.moment w F Fr Fz d = Sg.moment w F₁ Fr₁ Fz₁ d + Complex.I * Sg.moment w F₂ Fr₂ Fz₂ d := by
  have ht := test_continuous Sg d
  unfold FaceSegment.moment
  by_cases hr : Sg.radial = true
  · simp only [if_pos hr]
    obtain ⟨h₁, h₂, he⟩ := hrad hr
    exact radial_split _ _ _ _ _ ht h₁ h₂ he
  · simp only [if_neg hr]
    obtain ⟨h₁, h₂, he⟩ := hhei hr
    exact height_split _ _ _ _ (fun r => if w then r else 1) _ ht h₁ h₂ he

theorem two_term {s : Set (ℝ × ℝ)} (hs : IsCompact s) (hsm : MeasurableSet s) {A B f g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn A s) (h₂ : IntegrableOn B s) (c₁ : ContinuousOn g₁ s) (c₂ : ContinuousOn g₂ s)
    (he : ∀ p ∈ s, g₁ p * A p + g₂ p * B p = f p) : IntegrableOn f s :=
  ((h₁.continuousOn_mul c₁ hs).add (h₂.continuousOn_mul c₂ hs)).congr_fun he hsm

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_measurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem third_oneHot (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) :
    comboThird (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m n H c = modeThird m n H a b c := by
  funext p
  fin_cases a <;> fin_cases b <;> simp [comboThird, Fin.sum_univ_three]

theorem field_integrable {v G : _} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsLocalSecondOrderField v G H) {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) :
    (∀ a, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect) ∧
    (∀ a b, IntegrableOn (gradMode m n G a b) K.rect) ∧
    (∀ a b c, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b c p) K.rect) := by
  have hsub : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc K.z₁ K.z₂ :=
    prod_mono (Icc_subset_Icc_left hK.r_order.1) subset_rfl
  have hS := localModeStripIntegrable m v G H hs n K.r₂ K.z₁ K.z₂
  refine ⟨fun a => (hS.1 a).mono_set hsub, fun a b => (hS.2 a b).mono_set hsub, fun a b c => ?_⟩
  obtain ⟨-, -, hc⟩ := localModeSquareIntegrable K hK m v G H hs n
    (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0)
  obtain ⟨hm, hi⟩ := hc c
  rw [third_oneHot] at hm hi
  have hr : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect :=
    continuous_fst.continuousOn.integrableOn_compact (rect_compact K)
  refine Integrable.mono' ((hr.add hi).div_const 2)
    ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hm) ?_
  filter_upwards [ae_restrict_mem (rect_measurable K)] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have hq : ‖modeThird m n H a b c p‖ ≤ (1 + ‖modeThird m n H a b c p‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖modeThird m n H a b c p‖ - 1)]
  calc p.1 * ‖modeThird m n H a b c p‖ ≤ p.1 * ((1 + ‖modeThird m n H a b c p‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hq h0
    _ = (p.1 + p.1 * ‖modeThird m n H a b c p‖ ^ 2) / 2 := by ring

theorem radial_plain_int {K : CellBox} {V D : ℝ × ℝ → ℂ} (hV : IntegrableOn V K.rect) (hD : IntegrableOn D K.rect)
    (l o : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => ((1 / (l - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (l - o) : ℝ) : ℂ) * D p) K.rect :=
  two_term (rect_compact K) (rect_measurable K) hV hD (g₁ := fun _ => ((1 / (l - o) : ℝ) : ℂ))
    (g₂ := fun p => (((p.1 - o) / (l - o) : ℝ) : ℂ)) continuousOn_const
    (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)).continuousOn
    (fun _ _ => rfl)

theorem radial_weighted_int {K : CellBox} {G0 T : ℝ × ℝ → ℂ} (hG : IntegrableOn G0 K.rect)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * T p) K.rect) (l o : ℝ) (hlo : l ≠ o)
    (hcase : o = 0 ∨ 0 < K.r₁) :
    IntegrableOn (fun p : ℝ × ℝ => ((1 / (l - o) : ℝ) : ℂ) * G0 p + (((p.1 - o) / (l - o) : ℝ) : ℂ) * T p) K.rect := by
  rcases hcase with rfl | hpos
  · exact two_term (rect_compact K) (rect_measurable K) hG hT (g₁ := fun _ => ((1 / (l - 0) : ℝ) : ℂ))
      (g₂ := fun _ => ((1 / (l - 0) : ℝ) : ℂ)) continuousOn_const continuousOn_const
      (fun p _ => by push_cast; ring)
  · have hne : ∀ p ∈ K.rect, p.1 ≠ 0 := fun p hp => ne_of_gt (lt_of_lt_of_le hpos hp.1.1)
    have hlo' : l - o ≠ 0 := sub_ne_zero.2 hlo
    refine two_term (rect_compact K) (rect_measurable K) hG hT (g₁ := fun _ => ((1 / (l - o) : ℝ) : ℂ))
      (g₂ := fun p => (((p.1 - o) / ((l - o) * p.1) : ℝ) : ℂ)) continuousOn_const ?_ (fun p hp => ?_)
    · exact Complex.continuous_ofReal.comp_continuousOn
        ((continuous_fst.sub continuous_const).continuousOn.div (continuous_const.mul continuous_fst).continuousOn
          (fun p hp => mul_ne_zero hlo' (hne p hp)))
    · have h1 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hne p hp
      have h2 : (l : ℂ) - (o : ℂ) ≠ 0 := by exact_mod_cast hlo'
      push_cast
      field_simp

theorem height_plain_int {K : CellBox} {V D : ℝ × ℝ → ℂ} (hV : IntegrableOn V K.rect) (hD : IntegrableOn D K.rect)
    (l o : ℝ) (wt : ℝ → ℝ) (hw : Continuous wt) :
    IntegrableOn (fun p : ℝ × ℝ => (((1 / (l - o) : ℝ) : ℂ) * V p + (((p.2 - o) / (l - o) : ℝ) : ℂ) * D p)
      * ((wt p.1 : ℝ) : ℂ)) K.rect :=
  two_term (rect_compact K) (rect_measurable K) hV hD
    (g₁ := fun p => ((1 / (l - o) : ℝ) : ℂ) * ((wt p.1 : ℝ) : ℂ))
    (g₂ := fun p => (((p.2 - o) / (l - o) : ℝ) : ℂ) * ((wt p.1 : ℝ) : ℂ))
    (continuous_const.mul (Complex.continuous_ofReal.comp (hw.comp continuous_fst))).continuousOn
    ((Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).mul
      (Complex.continuous_ofReal.comp (hw.comp continuous_fst))).continuousOn
    (fun _ _ => by ring)

theorem height_weighted_int {K : CellBox} {G2 T : ℝ × ℝ → ℂ} (hG : IntegrableOn G2 K.rect)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * T p) K.rect) (l o : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (((1 / (l - o) : ℝ) : ℂ) * G2 p + (((p.2 - o) / (l - o) : ℝ) : ℂ) * T p)
      * ((p.1 : ℝ) : ℂ)) K.rect :=
  two_term (rect_compact K) (rect_measurable K) hG hT
    (g₁ := fun p => ((1 / (l - o) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ))
    (g₂ := fun p => (((p.2 - o) / (l - o) : ℝ) : ℂ))
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).continuousOn
    (Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).continuousOn
    (fun _ _ => by ring)

theorem pair_Icc {u w l : ℝ} (huw : u < w) (hl : l = u ∨ l = w) :
    Icc (min l (u + w - l)) (max l (u + w - l)) = Icc u w := by
  rcases hl with rfl | rfl
  · rw [add_sub_cancel_left, min_eq_left huw.le, max_eq_right huw.le]
  · rw [add_sub_cancel_right, min_eq_right huw.le, max_eq_left huw.le]

theorem radial_strip_sub {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hLay : IsCellLayout c K S B L) (s : Fin L.segCount) (hr : (L.segment s).radial = true) :
    Icc (min (L.segment s).level (L.segment s).other) (max (L.segment s).level (L.segment s).other) ×ˢ
      Icc (L.segment s).lo (L.segment s).hi ⊆ K.rect := by
  obtain ⟨-, hlev, hlo, hhi, -⟩ := (hLay.segment_on_side s).resolve_right (fun h => h.1 hr)
  rw [(hLay.segment_other_in_box s).1 hr, pair_Icc hLay.box_valid.r_order.2 hlev]
  exact prod_mono subset_rfl (Icc_subset_Icc hlo hhi)

theorem height_strip_sub {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hLay : IsCellLayout c K S B L) (s : Fin L.segCount) (hr : ¬ (L.segment s).radial = true) :
    Icc (L.segment s).lo (L.segment s).hi ×ˢ
      Icc (min (L.segment s).level (L.segment s).other) (max (L.segment s).level (L.segment s).other) ⊆ K.rect := by
  obtain ⟨-, hlev, hlo, hhi⟩ := (hLay.segment_on_side s).resolve_left (fun h => hr h.1)
  rw [(hLay.segment_other_in_box s).2 hr, pair_Icc hLay.box_valid.z_order.2 hlev]
  exact prod_mono (Icc_subset_Icc hlo hhi) subset_rfl

theorem radial_other_case {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hLay : IsCellLayout c K S B L) (s : Fin L.segCount) (hr : (L.segment s).radial = true) :
    (L.segment s).other = 0 ∨ 0 < K.r₁ := by
  obtain ⟨-, hlev, -, -, hl0⟩ := (hLay.segment_on_side s).resolve_right (fun h => h.1 hr)
  rcases eq_or_lt_of_le hLay.box_valid.r_order.1 with h0 | h0
  · left
    rw [(hLay.segment_other_in_box s).1 hr]
    rcases hlev with h | h
    · exact absurd (h.trans h0.symm) hl0
    · rw [h, ← h0]
      ring
  · exact Or.inr h0

theorem rect_nonneg {K : CellBox} (hK : IsCellBox K) {s : Set (ℝ × ℝ)} (hs : s ⊆ K.rect) :
    ∀ p ∈ s, 0 ≤ p.1 :=
  fun _ hp => hK.r_order.1.trans (hs hp).1.1

end Internal.HarmonicSide

open Internal.HarmonicSide in
theorem harmonicSideData_holds (h1 : HarmonicLiftStatement) : HarmonicSideDataStatement := by
  intro m K B L hL v G H Pg hvGH _ ν n hn
  obtain ⟨c, S, hco, -, hLay⟩ := hL
  have hord : L.order = m := hLay.order_eq.trans hco
  have hK : IsCellBox K := hLay.box_valid
  obtain ⟨hcos, hsin, hae⟩ := h1 m v G H hvGH ν
  have hprof := hae n hn
  obtain ⟨cV, cG, cT⟩ := field_integrable hcos hK m n
  obtain ⟨sV, sG, sT⟩ := field_integrable hsin hK m n
  have eV : ∀ a, L.velMode n (cosTuple ν v G H Pg) a
        = (fun p : ℝ × ℝ => modeVec m n (harmonicCos ν v) p.1 p.2 a) ∧
      L.velMode n (sinTuple ν v G H Pg) a = (fun p : ℝ × ℝ => modeVec m n (harmonicSin ν v) p.1 p.2 a) :=
    fun a => ⟨by rw [← hord]; rfl, by rw [← hord]; rfl⟩
  have eG : ∀ a b, L.gradModeOf n (cosTuple ν v G H Pg) a b = gradMode m n (harmonicCos ν G) a b ∧
      L.gradModeOf n (sinTuple ν v G H Pg) a b = gradMode m n (harmonicSin ν G) a b :=
    fun a b => ⟨by rw [← hord]; rfl, by rw [← hord]; rfl⟩
  have eT : ∀ a b c, L.secondModeOf n (cosTuple ν v G H Pg) a b c = modeThird m n (harmonicCos ν H) a b c ∧
      L.secondModeOf n (sinTuple ν v G H Pg) a b c = modeThird m n (harmonicSin ν H) a b c :=
    fun a b c => ⟨by rw [← hord]; rfl, by rw [← hord]; rfl⟩
  refine ⟨fun s a d => ?_, fun s a d => ?_⟩
  · simp only [harmonicData, CellLayout.trueData, CellDatum.sideVelocity, Sum.elim_inr, Sum.elim_inl]
    rw [(eV a).1, (eV a).2, (eG a 0).1, (eG a 0).2, (eG a 2).1, (eG a 2).2]
    symm
    refine moment_split _ false d (fun hr => ?_) (fun hr => ?_)
    · have hsub := radial_strip_sub hLay s hr
      exact ⟨(radial_plain_int (cV a) (cG a 0) (L.segment s).level (L.segment s).other).mono_set hsub,
        (radial_plain_int (sV a) (sG a 0) (L.segment s).level (L.segment s).other).mono_set hsub,
        ae_on_nonneg ((measurableSet_Icc.prod measurableSet_Icc)) (rect_nonneg hK hsub)
          (hprof.mono fun p hp hpos => ⟨(hp hpos).1 a, (hp hpos).2.1 a 0⟩)⟩
    · have hsub := height_strip_sub hLay s hr
      exact ⟨((height_plain_int (cV a) (cG a 2) (L.segment s).level (L.segment s).other (fun _ => 1) continuous_const).mono_set hsub).congr_fun
          (fun p _ => by simp) (measurableSet_Icc.prod measurableSet_Icc),
        ((height_plain_int (sV a) (sG a 2) (L.segment s).level (L.segment s).other (fun _ => 1) continuous_const).mono_set hsub).congr_fun
          (fun p _ => by simp) (measurableSet_Icc.prod measurableSet_Icc),
        ae_on_nonneg (measurableSet_Icc.prod measurableSet_Icc) (rect_nonneg hK hsub)
          (hprof.mono fun p hp hpos => ⟨(hp hpos).1 a, (hp hpos).2.1 a 2⟩)⟩
  · simp only [harmonicData, CellLayout.trueData, CellDatum.sideGradient, Sum.elim_inr, Sum.elim_inl]
    by_cases hr : (L.segment s).radial = true
    · simp only [if_pos hr]
      rw [(eG a 0).1, (eG a 0).2, (eT a 0 0).1, (eT a 0 0).2, (eT a 0 2).1, (eT a 0 2).2]
      symm
      refine moment_split _ true d (fun _ => ?_) (fun h => absurd hr h)
      have hsub := radial_strip_sub hLay s hr
      have hlo := (hLay.segment_valid s).other_ne.symm
      have hcase := radial_other_case hLay s hr
      exact ⟨(radial_weighted_int (cG a 0) (cT a 0 0) (L.segment s).level (L.segment s).other hlo hcase).mono_set hsub,
        (radial_weighted_int (sG a 0) (sT a 0 0) (L.segment s).level (L.segment s).other hlo hcase).mono_set hsub,
        ae_on_nonneg ((measurableSet_Icc.prod measurableSet_Icc)) (rect_nonneg hK hsub)
          (hprof.mono fun p hp hpos => ⟨(hp hpos).2.1 a 0, (hp hpos).2.2 a 0 0⟩)⟩
    · simp only [if_neg hr]
      rw [(eG a 2).1, (eG a 2).2, (eT a 2 0).1, (eT a 2 0).2, (eT a 2 2).1, (eT a 2 2).2]
      symm
      refine moment_split _ true d (fun h => absurd h hr) (fun _ => ?_)
      have hsub := height_strip_sub hLay s hr
      exact ⟨((height_weighted_int (cG a 2) (cT a 2 2) (L.segment s).level (L.segment s).other).mono_set hsub).congr_fun (fun p _ => by simp) (measurableSet_Icc.prod measurableSet_Icc),
        ((height_weighted_int (sG a 2) (sT a 2 2) (L.segment s).level (L.segment s).other).mono_set hsub).congr_fun (fun p _ => by simp) (measurableSet_Icc.prod measurableSet_Icc),
        ae_on_nonneg (measurableSet_Icc.prod measurableSet_Icc) (rect_nonneg hK hsub)
          (hprof.mono fun p hp hpos => ⟨(hp hpos).2.1 a 2, (hp hpos).2.2 a 2 2⟩)⟩

end CellCalculus

end CertCell

end Breakdown

import Breakdown.CertCell.AssemblyStatements
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus SteadyCert

private theorem rect_compact' (a b c d : ℝ) : IsCompact (Icc a b ×ˢ Icc c d) :=
  isCompact_Icc.prod isCompact_Icc

private theorem cont_mul_int {s : Set (ℝ × ℝ)} (hs : IsCompact s) {B : ℝ × ℝ → ℝ} (hB : Continuous B)
    {F : ℝ × ℝ → ℂ} (h : IntegrableOn F s) : IntegrableOn (fun p => ((B p : ℝ) : ℂ) * F p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp hB).continuousOn h hs

private theorem presMode_one_const (m : ℕ) (n : ℤ) :
    (fun p : ℝ × ℝ => presMode m n (fun _ => 1) p.1 p.2) = fun _ => presMode m n (fun _ => 1) 0 0 := by
  funext p
  simp only [presMode]

private theorem presMode_one_int (m : ℕ) (n : ℤ) {s : Set (ℝ × ℝ)} (hs : IsCompact s) :
    IntegrableOn (fun p : ℝ × ℝ => presMode m n (fun _ => 1) p.1 p.2) s := by
  rw [presMode_one_const]
  exact continuousOn_const.integrableOn_compact hs

private theorem int_of_weighted {r₁ r₂ z₁ z₂ : ℝ} (h0 : 0 < r₁) {F : ℝ × ℝ → ℂ}
    (h : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc r₁ r₂ ×ˢ Icc z₁ z₂)) :
    IntegrableOn F (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  have hs := rect_compact' r₁ r₂ z₁ z₂
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.1⁻¹ : ℝ) : ℂ)) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_fst.continuousOn.inv₀ (fun p hp => (h0.trans_le hp.1.1).ne'))
  refine (IntegrableOn.continuousOn_mul hc h hs).congr_fun (fun p hp => ?_) hs.measurableSet
  have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (h0.trans_le hp.1.1).ne'
  push_cast
  field_simp

private theorem radial_grad_int {c o lo hi : ℝ} {t : ℝ → ℝ} (ht : Continuous t) {dF : ℝ × ℝ → ℂ}
    (hc : c ≠ 0) (hmin : 0 ≤ min c o)
    (hw : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc (min c o) (max c o) ×ˢ Icc lo hi)) :
    IntegrableOn (fun p : ℝ × ℝ => ((((p.1 - o) / (c - o)) * t p.2 : ℝ) : ℂ) * dF p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi) := by
  have hs := rect_compact' (min c o) (max c o) lo hi
  by_cases ho : o = 0
  · subst ho
    refine (cont_mul_int hs (B := fun p => t p.2 / c) (by fun_prop) hw).congr_fun (fun p _ => ?_)
      hs.measurableSet
    push_cast
    ring
  · have hne : min c o ≠ 0 := by
      rcases min_choice c o with h | h <;> rw [h]
      · exact hc
      · exact ho
    exact cont_mul_int hs (by fun_prop) (int_of_weighted (lt_of_le_of_ne hmin (Ne.symm hne)) hw)

private theorem integral_shift {s : Set (ℝ × ℝ)} {I1 I2 IU : ℝ × ℝ → ℂ} (k : ℂ)
    (h : ∀ᵐ p ∂(volume.restrict s), I1 p = I2 p + k * IU p) (h2 : IntegrableOn I2 s) (hU : IntegrableOn IU s) :
    ∫ p in s, I1 p = (∫ p in s, I2 p) + k * ∫ p in s, IU p := by
  rw [integral_congr_ae h, integral_add h2 (hU.const_mul k), integral_const_mul]

private theorem radial_shift (c o lo hi : ℝ) (t : ℝ → ℝ) {F1 F2 U dF : ℝ × ℝ → ℂ} (k : ℂ)
    (hF : ∀ᵐ p ∂volume, F1 p = F2 p + k * U p)
    (iF : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * t p.2 : ℝ) : ℂ) * F2 p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (iG : IntegrableOn (fun p : ℝ × ℝ => ((((p.1 - o) / (c - o)) * t p.2 : ℝ) : ℂ) * dF p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (iU : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * t p.2 : ℝ) : ℂ) * U p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi)) :
    radialStripMoment c o lo hi F1 dF t =
      radialStripMoment c o lo hi F2 dF t + k * radialStripMoment c o lo hi U (fun _ => 0) t := by
  unfold radialStripMoment
  have e1 := integral_shift (s := Icc (min c o) (max c o) ×ˢ Icc lo hi)
    (I1 := fun p => ((((1 / (c - o) : ℝ)) : ℂ) * F1 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ))
    (I2 := fun p => ((((1 / (c - o) : ℝ)) : ℂ) * F2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ))
    (IU := fun p => ((((1 / (c - o) : ℝ)) : ℂ) * U p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * 0) * ((t p.2 : ℝ) : ℂ)) k
    (by filter_upwards [ae_restrict_of_ae hF] with p hp; rw [hp]; ring)
    ((iF.add iG).congr_fun (fun p _ => by simp only [Pi.add_apply]; push_cast; ring)
      (measurableSet_Icc.prod measurableSet_Icc))
    (iU.congr_fun (fun p _ => by push_cast; ring) (measurableSet_Icc.prod measurableSet_Icc))
  simp only [mul_zero, add_zero] at e1 ⊢
  rw [e1]
  ring

private theorem height_shift (c o lo hi : ℝ) (wt t : ℝ → ℝ) {F1 F2 U dF : ℝ × ℝ → ℂ} (k : ℂ)
    (hF : ∀ᵐ p ∂volume, F1 p = F2 p + k * U p)
    (iF : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * (wt p.1 * t p.1) : ℝ) : ℂ) * F2 p)
      (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (iG : IntegrableOn (fun p : ℝ × ℝ => ((((p.2 - o) / (c - o)) * (wt p.1 * t p.1) : ℝ) : ℂ) * dF p)
      (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (iU : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * (wt p.1 * t p.1) : ℝ) : ℂ) * U p)
      (Icc lo hi ×ˢ Icc (min c o) (max c o))) :
    heightStripMoment c o lo hi wt F1 dF t =
      heightStripMoment c o lo hi wt F2 dF t + k * heightStripMoment c o lo hi wt U (fun _ => 0) t := by
  unfold heightStripMoment
  have e1 := integral_shift (s := Icc lo hi ×ˢ Icc (min c o) (max c o))
    (I1 := fun p => ((((1 / (c - o) : ℝ)) : ℂ) * F1 p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
      ((wt p.1 * t p.1 : ℝ) : ℂ))
    (I2 := fun p => ((((1 / (c - o) : ℝ)) : ℂ) * F2 p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
      ((wt p.1 * t p.1 : ℝ) : ℂ))
    (IU := fun p => ((((1 / (c - o) : ℝ)) : ℂ) * U p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * 0) *
      ((wt p.1 * t p.1 : ℝ) : ℂ)) k
    (by filter_upwards [ae_restrict_of_ae hF] with p hp; rw [hp]; ring)
    ((iF.add iG).congr_fun (fun p _ => by simp only [Pi.add_apply]; push_cast; ring)
      (measurableSet_Icc.prod measurableSet_Icc))
    (iU.congr_fun (fun p _ => by push_cast; ring) (measurableSet_Icc.prod measurableSet_Icc))
  simp only [mul_zero, add_zero] at e1 ⊢
  rw [e1]
  ring

private theorem potential_shift_ae {m : ℕ} {Q : Space → Space} (hQ : IsGradientField Q) (n : ℤ) (e e' : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, presMode m n (fun y => potentialOf Q y - e) p.1 p.2 =
      presMode m n (fun y => potentialOf Q y - e') p.1 p.2 +
        ((e' - e : ℝ) : ℂ) * presMode m n (fun _ => 1) p.1 p.2 := by
  have hQQ : (1 : ℝ) • Q + (0 : ℝ) • Q = Q := by simp
  have hC : potentialOf ((1 : ℝ) • Q + (0 : ℝ) • Q) =ᵐ[volume]
      fun y => 1 * potentialOf Q y + 0 * potentialOf Q y + 0 :=
    Filter.Eventually.of_forall fun y => by simp
  have h := MeshDataAffineModes.gradient_modes_affine m Q Q hQ hQ 1 0 0 e' 0 e hC n
  rw [hQQ] at h
  filter_upwards [h] with p hp
  rw [hp.1]
  push_cast
  ring

private theorem moment_shift (S : FaceSegment)
    (hS : S.radial = true → S.level ≠ 0 ∧ 0 ≤ min S.level S.other)
    (m : ℕ) {Q : Space → Space} (hQ : IsGradientField Q) (n : ℤ) (e e' : ℝ) (d : ℕ) :
    S.moment true (fun p => presMode m n (fun y => potentialOf Q y - e) p.1 p.2)
        (fun p => modeVec m n Q p.1 p.2 0) (fun p => modeVec m n Q p.1 p.2 2) d =
      S.moment true (fun p => presMode m n (fun y => potentialOf Q y - e') p.1 p.2)
          (fun p => modeVec m n Q p.1 p.2 0) (fun p => modeVec m n Q p.1 p.2 2) d +
        ((e' - e : ℝ) : ℂ) * S.moment true (fun p => presMode m n (fun _ => 1) p.1 p.2)
          (fun _ => 0) (fun _ => 0) d := by
  have hae := potential_shift_ae (m := m) hQ n e e'
  have htc : Continuous (S.test d) := by unfold FaceSegment.test; fun_prop
  unfold FaceSegment.moment
  by_cases hr : S.radial = true
  · simp only [hr, if_true]
    obtain ⟨hl, hmin⟩ := hS hr
    have hs := rect_compact' (min S.level S.other) (max S.level S.other) S.lo S.hi
    have hint := MeshDataAffineModes.gradient_modes_integrable m Q hQ n e'
      (min S.level S.other) (max S.level S.other) S.lo S.hi
    exact radial_shift _ _ _ _ _ _ hae (cont_mul_int hs (by fun_prop) hint.1)
      (radial_grad_int htc hl hmin (hint.2 0)) (cont_mul_int hs (by fun_prop) (presMode_one_int m n hs))
  · simp only [hr, if_false, Bool.false_eq_true, if_true]
    have hs := rect_compact' S.lo S.hi (min S.level S.other) (max S.level S.other)
    have hint := MeshDataAffineModes.gradient_modes_integrable m Q hQ n e'
      S.lo S.hi (min S.level S.other) (max S.level S.other)
    refine height_shift _ _ _ _ _ _ _ hae (cont_mul_int hs (by fun_prop) hint.1) ?_
      (cont_mul_int hs (by fun_prop) (presMode_one_int m n hs))
    refine (cont_mul_int hs (B := fun p => (p.2 - S.other) / (S.level - S.other) * S.test d p.1)
      (by fun_prop) (hint.2 2)).congr_fun (fun p _ => ?_) hs.measurableSet
    push_cast
    ring

private def ballGaugeGap (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) : ℝ :=
  (⨍ z in Metric.ball (0 : Space) 1, potentialOf x.2.2.2.2 z) - (L.gaugeValue x / L.gaugeUnit).re

private theorem trueData_eq_head (L : CellLayout)
    (hL : ∀ s, (L.presSegment s).radial = true →
      (L.presSegment s).level ≠ 0 ∧ 0 ≤ min (L.presSegment s).level (L.presSegment s).other)
    {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (hx : IsGradientField x.2.2.2.2) (d : L.Datum) :
    L.trueData x d = headData L x d + (ballGaugeGap L x : ℂ) * presUnitMoment L d := by
  rcases d with i | i | i | i | i | i | i | i
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring
  · exact moment_shift (L.presSegment i.2.1) (hL i.2.1) L.order hx i.1 _ _ i.2.2
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring
  · show L.trueData x _ = L.trueData x _ + _ * 0; ring

theorem cellStateInRowRange_holds : CellStateInRowRangeHolds := by
  intro k C nE nM D R e T W _ hcc _ hrm K q v G H g κ F Pg htup ζ η
  have hgeo : ∀ ι ∈ D.mesh.resolved K, ∀ s, (((R.layouts K).layout ι).presSegment s).radial = true →
      (((R.layouts K).layout ι).presSegment s).level ≠ 0 ∧
        0 ≤ min (((R.layouts K).layout ι).presSegment s).level (((R.layouts K).layout ι).presSegment s).other := by
    intro ι hι s hr
    obtain ⟨hseg, hlev⟩ := hcc.pressure_placed K ι hι
    obtain ⟨c, S, _, _, hcl⟩ := (hcc.layouts_valid K).layout_valid ι hι
    have hb := hcl.box_valid.r_order
    have hbe := hcl.box_eq
    obtain ⟨_, _, hoth⟩ := hseg.2.2.2.2.1 s hr
    refine ⟨hlev s hr, le_min ?_ ?_⟩
    · rcases hseg.1 s with ⟨_, hl | hl⟩ | ⟨hnr, _⟩
      · rw [hl, hbe]; linarith
      · rw [hl, hbe]; linarith
      · exact absurd hr hnr
    · rw [hoth, hbe]
      rcases hseg.1 s with ⟨_, hl | hl⟩ | ⟨hnr, _⟩
      · rw [hl, hbe]; linarith
      · rw [hl, hbe]; linarith
      · exact absurd hr hnr
  have hgr := htup.pressure.harmonic_gradient
  unfold InRowRange
  refine ⟨T.fieldData v G H Pg κ, fun c => -T.fieldGauge c v G H Pg,
    fun ι => (ballGaugeGap ((R.layouts K).layout ι) (cosTuple (labelTime ι) v G H Pg) : ℂ) +
      Complex.I * (ballGaugeGap ((R.layouts K).layout ι) (sinTuple (labelTime ι) v G H Pg) : ℂ), ?_, ?_, ?_⟩
  · intro d hd
    rw [hrm q htup.param v G H g htup.perturbation Pg htup.pressure htup.pressure_flip κ K d hd]
    have hsum : ∀ γ : ℤ × ℤ → ℂ, ∑ ι ∈ D.mesh.resolved K, γ ι * headUnit D R K ι (Sum.inl (Sum.inl d)) =
        γ d.1.1 * presUnitMoment ((R.layouts K).layout d.1.1) d.2 := by
      intro γ
      rw [Finset.sum_eq_single d.1.1]
      · simp [headUnit]
      · intro b _ hb
        simp [headUnit, Ne.symm hb]
      · intro h
        exact absurd d.1.2 h
    rw [hsum]
    simp only [cellState, Sum.elim_inl, modeData, harmonicData, TreeEntry.fieldShifted, TreeEntry.fieldHead,
      headHarmonic]
    rw [trueData_eq_head _ (hgeo _ d.1.2) (cosTuple (labelTime d.1.1) v G H Pg) (hgr _).1 d.2,
      trueData_eq_head _ (hgeo _ d.1.2) (sinTuple (labelTime d.1.1) v G H Pg) (hgr _).2 d.2]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  · intro i
    simp [cellState]
  · intro i
    simp [cellState]

end Assembly

end CertCell

end Breakdown

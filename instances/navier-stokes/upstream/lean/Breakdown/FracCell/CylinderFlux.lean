import Breakdown.FracCell.RelStream
import Breakdown.FracCell.StAngularMode
import Breakdown.FracCell.RelTrace
import Breakdown.FracCell.LowEntry
import Breakdown.FracCert.HeldStateLimitAApply

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def ModeTraceStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → ∑ a : Fin 3, gradMode m n G a a p = 0

def StripTraceStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ z₁ z₂ : ℝ, z₁ < z₂ → ∃ T : ℝ → ℂ, ∀ a b : ℝ, 0 ≤ a → a < b → ∀ α β : ℝ,
      ∫ p in Icc a b ×ˢ Icc z₁ z₂,
          ((α : ℂ) * modeVec m 0 v p.1 p.2 0 + ((α * p.1 + β : ℝ) : ℂ) * gradMode m 0 G 0 0 p)
        = ((α * b + β : ℝ) : ℂ) * T b - ((α * a + β : ℝ) : ℂ) * T a

def RadialFluxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (R o z₁ z₂ : ℝ), 0 < R → 0 ≤ o → o ≠ R → z₁ < z₂ →
      (R : ℂ) * radialStripMoment R o z₁ z₂ (fun p => modeVec m 0 v p.1 p.2 0) (gradMode m 0 G 0 0)
          (fun _ => 1)
        = ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p)

namespace Internal.CylinderFlux

theorem axis_ae : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h0 : volume ({0} ×ˢ univ : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with p hp
  intro h
  exact hp ⟨h, mem_univ _⟩

theorem heightDiff (R z₁ z₂ : ℝ) (hz : z₁ < z₂) (U dU : ℝ × ℝ → ℂ)
    (hU : IntegrableOn U (Icc 0 R ×ˢ Icc z₁ z₂)) (hdU : IntegrableOn dU (Icc 0 R ×ˢ Icc z₁ z₂)) :
    heightStripMoment z₂ z₁ 0 R (fun r => r) U dU (fun _ => 1)
        - heightStripMoment z₁ z₂ 0 R (fun r => r) U dU (fun _ => 1)
      = ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (p.1 : ℂ) * dU p := by
  have hK : IsCompact (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂) := isCompact_Icc.prod isCompact_Icc
  have hne : (z₂ : ℂ) - z₁ ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (ne_of_gt hz)
  have hne' : (z₁ : ℂ) - z₂ ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (ne_of_lt hz)
  have e2 : heightStripMoment z₂ z₁ 0 R (fun r => r) U dU (fun _ => 1) = ∫ p in Icc 0 R ×ˢ Icc z₁ z₂,
      ((((1 / (z₂ - z₁) : ℝ)) : ℂ) * U p + (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ) * dU p) *
        ((p.1 * 1 : ℝ) : ℂ) := by
    simp only [heightStripMoment, edgeSign, if_pos hz, min_eq_right hz.le, max_eq_left hz.le, one_mul]
  have e1 : heightStripMoment z₁ z₂ 0 R (fun r => r) U dU (fun _ => 1) = -∫ p in Icc 0 R ×ˢ Icc z₁ z₂,
      ((((1 / (z₁ - z₂) : ℝ)) : ℂ) * U p + (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ) * dU p) *
        ((p.1 * 1 : ℝ) : ℂ) := by
    simp only [heightStripMoment, edgeSign, if_neg (not_lt.mpr hz.le), min_eq_left hz.le,
      max_eq_right hz.le, neg_one_mul]
  have i2 : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (z₂ - z₁) : ℝ)) : ℂ) * U p
      + (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ) * dU p) * ((p.1 * 1 : ℝ) : ℂ)) (Icc 0 R ×ˢ Icc z₁ z₂) := by
    have a1 : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (z₂ - z₁) : ℝ)) : ℂ) * U p
        + (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ) * dU p)) (Icc 0 R ×ˢ Icc z₁ z₂) :=
      IntegrableOn.add (hU.const_mul _)
        (hdU.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ))
          (Continuous.continuousOn (by fun_prop)) hK)
    exact a1.mul_continuousOn (g' := fun p : ℝ × ℝ => ((p.1 * 1 : ℝ) : ℂ))
      (Continuous.continuousOn (by fun_prop)) hK
  have i1 : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (z₁ - z₂) : ℝ)) : ℂ) * U p
      + (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ) * dU p) * ((p.1 * 1 : ℝ) : ℂ)) (Icc 0 R ×ˢ Icc z₁ z₂) := by
    have a1 : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (z₁ - z₂) : ℝ)) : ℂ) * U p
        + (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ) * dU p)) (Icc 0 R ×ˢ Icc z₁ z₂) :=
      IntegrableOn.add (hU.const_mul _)
        (hdU.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))
          (Continuous.continuousOn (by fun_prop)) hK)
    exact a1.mul_continuousOn (g' := fun p : ℝ × ℝ => ((p.1 * 1 : ℝ) : ℂ))
      (Continuous.continuousOn (by fun_prop)) hK
  rw [e2, e1, sub_neg_eq_add, ← integral_add i2 i1]
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => ?_)
  push_cast
  field_simp
  ring

theorem region_eq : volume.restrict Internal.RelTrace.region =
    (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rfl

theorem slice_ae {P : Space → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      ∀ᵐ θ ∂(volume.restrict (Ioo (-Real.pi) Real.pi)), P (cylPoint q.1 θ q.2) := by
  have h1 : ∀ᵐ x ∂(volume.restrict Internal.RelTrace.region), P (Internal.RelTrace.cylF x) :=
    Internal.RelTrace.qmp_region.ae hP
  rw [region_eq] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h2
  filter_upwards [h2] with q hq hpos
  exact hq ⟨hpos, mem_univ _⟩

theorem slice_aesm {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume) :
    ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      AEStronglyMeasurable (fun θ => G (cylPoint q.1 θ q.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  have h1 : AEStronglyMeasurable (fun x => G (Internal.RelTrace.cylF x))
      (volume.restrict Internal.RelTrace.region) :=
    hG.comp_quasiMeasurePreserving Internal.RelTrace.qmp_region
  rw [region_eq] at h1
  have h2 := h1.prodMk_left
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h2
  filter_upwards [h2] with q hq hpos
  exact hq ⟨hpos, mem_univ _⟩

theorem slice_lint {G : Space → (Space →L[ℝ] Space)} (hG2 : Integrable (fun y => entrySq (G y))) :
    ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 →
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (entrySq (G (cylPoint q.1 θ q.2))) < ⊤ := by
  set h : Space → ENNReal := fun y => ENNReal.ofReal (entrySq (G y)) with hh
  have hm : AEMeasurable h volume := hG2.aemeasurable.ennreal_ofReal
  have hfin : ∫⁻ x in Internal.RelTrace.region, ENNReal.ofReal x.1.1 * h (Internal.RelTrace.cylF x) ≠ ⊤ := by
    rw [Internal.RelTrace.lintegral_cyl]
    exact hG2.lintegral_lt_top.ne
  have hm2 : AEMeasurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * h (Internal.RelTrace.cylF x))
      (volume.restrict Internal.RelTrace.region) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
      (hm.comp_quasiMeasurePreserving Internal.RelTrace.qmp_region)
  rw [region_eq] at hfin hm2
  rw [lintegral_prod _ hm2] at hfin
  have h3 := ae_lt_top' hm2.lintegral_prod_right' hfin
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h3
  filter_upwards [h3] with q hq hpos
  have h4 := hq ⟨hpos, mem_univ _⟩
  change (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal q.1 * h (cylPoint q.1 θ q.2)) < ⊤ at h4
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h4
  exact ENNReal.lt_top_of_mul_ne_top_right h4.ne (ENNReal.ofReal_pos.2 hpos).ne'

theorem entrySq_cont : Continuous (fun M : Space →L[ℝ] Space => entrySq M) := by
  unfold entrySq
  exact continuous_finsetSum _ (fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm).pow 2)

theorem norm_le_entry (M : Space →L[ℝ] Space) : ‖M‖ ≤ 1 + entrySq M := by
  have h0 : 0 ≤ entrySq M := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : ‖M‖ ≤ Real.sqrt (entrySq M) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
      (fun x => SteadyCert.ApplyPairingInternal.apply_norm_le M x)
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (entrySq M), sq_nonneg (Real.sqrt (entrySq M) - 1)]

theorem slice_int (m : ℕ) (n : ℤ) (a b : Fin 3) {G : Space → (Space →L[ℝ] Space)} (p : ℝ × ℝ)
    (hA : AEStronglyMeasurable (fun θ => G (cylPoint p.1 θ p.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (hL : ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (entrySq (G (cylPoint p.1 θ p.2))) < ⊤) :
    Integrable (fun θ => LowEntry.Internal.gradKernel m n a b θ (G (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hE : Integrable (fun θ => entrySq (G (cylPoint p.1 θ p.2))) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    ⟨entrySq_cont.comp_aestronglyMeasurable hA, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => Finset.sum_nonneg fun i _ => sq_nonneg _)).2 hL⟩
  have hB : Integrable (fun θ => 1 + entrySq (G (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := (integrable_const (1 : ℝ)).add hE
  have hP : AEStronglyMeasurable (fun θ => (θ, G (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := aestronglyMeasurable_id.prodMk hA
  have hK : AEStronglyMeasurable (fun θ => LowEntry.Internal.gradKernel m n a b θ (G (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    have h := (LowEntry.Internal.gradKernel_cont m n a b).comp_aestronglyMeasurable hP
    exact h
  refine Integrable.mono' hB hK (Filter.Eventually.of_forall fun θ => ?_)
  exact (LowEntry.Internal.gradKernel_bound m n a b θ _).trans (norm_le_entry _)

theorem strip_eq (F dF : ℝ × ℝ → ℂ) (a b o R z₁ z₂ : ℝ) :
    ∫ p in Icc a b ×ˢ Icc z₁ z₂,
        ((((1 / (R - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (R - o) : ℝ) : ℂ) * dF p) * (((1 : ℝ)) : ℂ)
      = ∫ p in Icc a b ×ˢ Icc z₁ z₂,
          (((1 / (R - o) : ℝ) : ℂ) * F p + ((1 / (R - o) * p.1 + -o / (R - o) : ℝ) : ℂ) * dF p) := by
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => ?_)
  rw [show (p.1 - o) / (R - o) = 1 / (R - o) * p.1 + -o / (R - o) by ring, Complex.ofReal_one, mul_one]

end Internal.CylinderFlux

open Internal.CylinderFlux in
theorem radialFlux_of (hT : StripTraceStatement) : RadialFluxStatement := by
  intro m v G H hs R o z₁ z₂ hR0 ho hoR hz
  obtain ⟨T, hTr⟩ := hT m v G H hs z₁ z₂ hz
  have hne : R - o ≠ 0 := sub_ne_zero.2 (Ne.symm hoR)
  have hα1 : 1 / (R - o) * R + -o / (R - o) = 1 := by field_simp; ring
  have hα0 : 1 / (R - o) * o + -o / (R - o) = 0 := by ring
  have hrhs : (∫ p in Icc 0 R ×ˢ Icc z₁ z₂,
      (modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p)) = (R : ℂ) * T R := by
    have h0 := hTr 0 R le_rfl hR0 1 0
    simp only [Complex.ofReal_one, one_mul, add_zero, mul_zero, Complex.ofReal_zero, zero_mul,
      sub_zero] at h0
    exact h0
  rw [hrhs]
  rcases lt_or_gt_of_ne hoR with h | h
  · simp only [radialStripMoment, edgeSign, if_pos h, min_eq_right h.le, max_eq_left h.le, one_mul]
    rw [strip_eq, hTr o R ho h, hα1, hα0]
    simp
  · simp only [radialStripMoment, edgeSign, if_neg (not_lt.mpr h.le), min_eq_left h.le,
      max_eq_right h.le]
    rw [strip_eq, hTr R o hR0.le h, hα1, hα0]
    simp

namespace Internal.CylinderFlux

end Internal.CylinderFlux

open Internal.CylinderFlux in
theorem modeTrace : ModeTraceStatement := by
  intro m v G H hs n
  filter_upwards [slice_aesm hs.measurable_gradient, slice_lint hs.gradient_two,
    slice_ae hs.divergence] with p hpA hpL hpP hpos
  have hint := fun a : Fin 3 => slice_int m n a a p (hpA hpos) (hpL hpos)
  simp_rw [LowEntry.Internal.gradMode_eq]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun a _ => hint a)]
  have h0 : ∫ θ in Ioo (-Real.pi) Real.pi,
      ∑ a : Fin 3, LowEntry.Internal.gradKernel m n a a θ (G (cylPoint p.1 θ p.2)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hpP hpos] with θ hθ
    simp only [LowEntry.Internal.gradKernel, ← Finset.mul_sum]
    have hs3 : ∑ a : Fin 3, frameMat θ (G (cylPoint p.1 θ p.2)) a a = 0 := by
      simp_rw [Internal.RelTrace.frameMat_diag]
      rw [Internal.RelTrace.diag_sum]
      simpa only [Internal.RelTrace.ent] using hθ
    have hs4 : ∑ a : Fin 3, ((frameMat θ (G (cylPoint p.1 θ p.2)) a a : ℝ) : ℂ) = 0 := by
      exact_mod_cast hs3
    rw [Pi.zero_apply, hs4, mul_zero]
  rw [h0, mul_zero]

namespace Internal.CylinderFlux

end Internal.CylinderFlux

open Internal.CylinderFlux in
theorem cylinderFlux_of (hS : ModeStripIntegrableStatement) (hA : AngularModeStatement)
    (hST : StripTraceStatement) : CylinderFluxStatement := by
  have hT : ModeTraceStatement := modeTrace
  have hR : RadialFluxStatement := radialFlux_of hST
  intro m v G H hs R o z₁ z₂ hR0 ho hoR hz
  obtain ⟨hv, hg⟩ := hS m v G H hs 0 R z₁ z₂
  have hD := heightDiff R z₁ z₂ hz _ _ (hv 2) (hg 2 2)
  have hae : ∀ᵐ p ∂(volume.restrict (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂)),
      (p.1 : ℂ) * gradMode m 0 G 2 2 p = -(modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p) := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc),
      ae_restrict_of_ae (hA m v G H hs 0), ae_restrict_of_ae (hT m v G H hs 0),
      ae_restrict_of_ae axis_ae] with p hpD hAp hTp hp0
    have hpos : 0 < p.1 := lt_of_le_of_ne hpD.1.1 (Ne.symm hp0)
    obtain ⟨-, h11, -⟩ := hAp hpos
    have az : azimuth m 0 = 0 := by simp [azimuth]
    rw [az] at h11
    simp only [Complex.ofReal_zero, zero_mul, zero_add] at h11
    have hTp := hTp hpos
    rw [Fin.sum_univ_three] at hTp
    linear_combination (p.1 : ℂ) * hTp - h11
  have hI : (∫ p in Icc (0 : ℝ) R ×ˢ Icc z₁ z₂, (p.1 : ℂ) * gradMode m 0 G 2 2 p)
      = -∫ p in Icc (0 : ℝ) R ×ˢ Icc z₁ z₂,
          (modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p) := by
    rw [integral_congr_ae hae, integral_neg]
  rw [add_sub_assoc, hD, hI, hR m v G H hs R o z₁ z₂ hR0 ho hoR hz, add_neg_cancel]

end CellFormula

end CellCert

end Breakdown

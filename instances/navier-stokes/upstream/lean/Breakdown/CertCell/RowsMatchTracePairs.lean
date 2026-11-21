import Breakdown.CertCell.RowsMatchKeyData
import Breakdown.CertCell.GaugePlaneFlipFacts
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.CertCell.LocalRadialTrace
import Breakdown.CertCell.LocalHeightWeak
import Breakdown.FracCell.MeshGaugeLinearPotential
import Breakdown.FracCell.SegmentModesHeight
import Breakdown.FracCell.SegmentModesPressure
import Breakdown.FracCell.MeshDataAffineModes
import Breakdown.FracCell.CylModeWeak

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.TraceLocal

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.CellCert.CellFormula
open Breakdown.CertCell.LocalField
open Breakdown.FracInternal.MeshDataAffineModes Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.FracInternal.SegmentHeight Breakdown.FracInternal.SegmentRefl

variable {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem modes_rect (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ) (r₁ r₂ z₁ z₂ : ℝ) :
    (∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc r₁ r₂ ×ˢ Icc z₁ z₂)) ∧
    (∀ a b : Fin 3, IntegrableOn (gradMode m n G a b) (Icc r₁ r₂ ×ˢ Icc z₁ z₂)) ∧
    (∀ a b c : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b c p)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂)) := by
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · obtain ⟨C, hC⟩ := velKernel_pi m n a
    refine int_rect (C := C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · exact mode_refl _ C hC (velKernel_per m n a) v p.1 p.2
    · exact (localModeStripIntegrable m v G H hs n R (-R) R).1 a
  · obtain ⟨C, hC⟩ := gradKernel_pi m n a b
    refine int_rect (C := C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · exact mode_refl _ C hC (gradKernel_per m n a b) G p.1 p.2
    · exact (localModeStripIntegrable m v G H hs n R (-R) R).2 a b
  · obtain ⟨C, hC⟩ := thirdKernel_pi m n a b c
    refine int_rect (C := -C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · show ((-p.1 : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          thirdKernel m n a b c θ (H (cylPoint (-p.1) θ p.2))) =
        -C * ((p.1 : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2))))
      rw [mode_refl _ C hC (thirdKernel_per m n a b c) H p.1 p.2]
      push_cast
      ring
    · exact weighted_strip (second_locInt hs.measurable_second hs.second_two) _ (thirdKernel_cont m n a b c)
        (thirdKernel_bound m n a b c) (thirdKernel_per m n a b c) R

theorem weight_mul {F : ℝ × ℝ → ℂ} {s : Set (ℝ × ℝ)} (hs : IsCompact s) (h : IntegrableOn F s) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp continuous_fst).continuousOn h hs

theorem off_of_weighted {F : ℝ × ℝ → ℂ} {δ R Z : ℝ} (hδ : 0 < δ)
    (h : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc δ R ×ˢ Icc (-Z) Z)) :
    IntegrableOn F (Icc δ R ×ˢ Icc (-Z) Z) :=
  Breakdown.FracInternal.SegmentModes.off_axis_int (measurableSet_Icc.prod measurableSet_Icc) hδ
    (fun p hp => by rw [abs_of_pos (hδ.trans_le hp.1.1)]; exact hp.1.1) h

theorem vel_radial (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ) (a : Fin 3) :
    IsRadialWeakPair (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (gradMode m n G a 0) :=
  ⟨fun R Z => ⟨(modes_rect hs m n 0 R (-Z) Z).1 a,
      weight_mul (isCompact_Icc.prod isCompact_Icc) ((modes_rect hs m n 0 R (-Z) Z).2.1 a 0)⟩,
    fun δ R Z _ => (modes_rect hs m n δ R (-Z) Z).2.1 a 0,
    fun ψ hψ hc hpos => (localModeWeakIdentity m v G H hs n a ψ hψ hc hpos).1⟩

theorem vel_height (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ) (a : Fin 3) :
    IsHeightWeakPair (fun _ => 1) (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (gradMode m n G a 2) := by
  have hrect := fun R Z : ℝ => modes_rect hs m n (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, modeVec m n v (-p.1) p.2 a = (halfTurn m n * (unitSign a : ℂ)) * modeVec m n v p.1 p.2 a :=
    fun p => vel_refl m n v a p
  have hdF : ∀ p : ℝ × ℝ, gradMode m n G a 2 (-p.1, p.2) = (halfTurn m n * (unitSign a : ℂ)) * gradMode m n G a 2 p :=
    fun p => grad_refl2 m n G a p
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (gradMode m n G a 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z _ => ⟨((hrect R Z).1 a).mono_set (box_sub δ R Z), ((hrect R Z).2.1 a 2).mono_set (box_sub δ R Z)⟩
  refine ⟨fun R Z => ⟨?_, ?_⟩, hoff, height_ident_refl (mul_ne_zero (halfTurn_ne _ _) (sign_ne a)) hF hdF hoff
    (fun ψ hψ hc hpos => (localModeWeakIdentity m v G H hs n a ψ hψ hc hpos).2.1)⟩
  · simpa using (hrect R Z).1 a
  · simpa using (hrect R Z).2.1 a 2

theorem grad_radial (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ) (a : Fin 3) :
    IsRadialWeakPair (gradMode m n G a 0) (modeThird m n H a 0 0) :=
  ⟨fun R Z => ⟨(modes_rect hs m n 0 R (-Z) Z).2.1 a 0, (modes_rect hs m n 0 R (-Z) Z).2.2 a 0 0⟩,
    fun δ R Z hδ => off_of_weighted hδ ((modes_rect hs m n δ R (-Z) Z).2.2 a 0 0),
    fun ψ hψ hc hpos => Breakdown.CertCell.LocalField.Internal.localRadialWeakMode (m := m) hs a 0 n ψ hψ hc hpos⟩

theorem grad_height (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ) (a : Fin 3) :
    IsHeightWeakPair (fun r => r) (gradMode m n G a 2) (modeThird m n H a 2 2) := by
  have hrect := fun R Z : ℝ => modes_rect hs m n (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, gradMode m n G a 2 (-p.1, p.2) = (halfTurn m n * (unitSign a : ℂ)) * gradMode m n G a 2 p :=
    fun p => grad_refl2 m n G a p
  have hdF : ∀ p : ℝ × ℝ, modeThird m n H a 2 2 (-p.1, p.2) =
      (halfTurn m n * (unitSign a : ℂ)) * modeThird m n H a 2 2 p :=
    fun p => third_refl22 m n H a p
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (gradMode m n G a 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (modeThird m n H a 2 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z hδ => ⟨((hrect R Z).2.1 a 2).mono_set (box_sub δ R Z),
      Breakdown.FracInternal.SegmentModes.off_axis_int (box_meas δ R Z) hδ (fun p hp => hp.1)
        (((hrect R Z).2.2 a 2 2).mono_set (box_sub δ R Z))⟩
  exact ⟨fun R Z => ⟨weighted_rect ((hrect R Z).2.1 a 2), (hrect R Z).2.2 a 2 2⟩, hoff,
    height_ident_refl (mul_ne_zero (halfTurn_ne _ _) (sign_ne a)) hF hdF hoff
      (fun ψ hψ hc hpos => Breakdown.CertCell.LocalField.Internal.localHeightSmoothWeak (m := m) hs n a 2 ψ hψ hc hpos)⟩

theorem corner_quad (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ) (a : Fin 3) :
    IsMixedWeakQuad (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (gradMode m n G a 0) (gradMode m n G a 2)
      (modeThird m n H a 0 2) :=
  ⟨fun R Z => ⟨(modes_rect hs m n 0 R (-Z) Z).1 a, (modes_rect hs m n 0 R (-Z) Z).2.1 a 2,
      weight_mul (isCompact_Icc.prod isCompact_Icc) ((modes_rect hs m n 0 R (-Z) Z).2.1 a 0),
      (modes_rect hs m n 0 R (-Z) Z).2.2 a 0 2⟩,
    fun δ R Z hδ => ⟨(modes_rect hs m n δ R (-Z) Z).2.1 a 0,
      off_of_weighted hδ ((modes_rect hs m n δ R (-Z) Z).2.2 a 0 2)⟩,
    fun ψ hψ hc hpos => localModeWeakIdentity m v G H hs n a ψ hψ hc hpos⟩

theorem inner_cols_locInt {Q : Space → Space} (hG : IsGradientField Q) (j : Fin 3) :
    LocallyIntegrable (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ) (unitVector j)) volume := by
  obtain ⟨_, _, hQ2, hQm, _⟩ := hG
  have hQloc := Breakdown.FracInternal.MeshDataAffineModes.locInt_of_sq hQm hQ2
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  refine Integrable.mono' ((hQloc.integrableOn_isCompact hK).norm)
    ((hQm.inner aestronglyMeasurable_const).restrict) (Filter.Eventually.of_forall fun y => ?_)
  rw [innerSL_apply_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  simp [unitVector]

theorem shifted_locInt {Q : Space → Space} (hG : IsGradientField Q) (e : ℝ) :
    LocallyIntegrable (fun y => potentialOf Q y - e) volume :=
  (Breakdown.FracInternal.MeshDataAffineModes.pot_locInt
    (MeshGaugeLinearPotential.potentialOf_spec Q hG)).sub (locallyIntegrable_const _)

theorem pres_radial {Q : Space → Space} (hG : IsGradientField Q) (m : ℕ) (n : ℤ) (e : ℝ) :
    IsRadialWeakPair (fun p : ℝ × ℝ => presMode m n (fun y => potentialOf Q y - e) p.1 p.2)
      (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 0) := by
  have hint := fun r₁ r₂ z₁ z₂ => Breakdown.CellCert.CellFormula.MeshDataAffineModes.gradient_modes_integrable m Q hG n e r₁ r₂ z₁ z₂
  refine ⟨fun R Z => ⟨(hint 0 R (-Z) Z).1, (hint 0 R (-Z) Z).2 0⟩,
    fun δ R Z hδ => off_of_weighted hδ ((hint δ R (-Z) Z).2 0), ?_⟩
  intro ψ hψ hc hpos
  have hw := (cylModeWeak ℝ (fun y => potentialOf Q y - e) (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ))
    (shifted_locInt hG e) (inner_cols_locInt hG) (Breakdown.CellCert.CellFormula.pressure_weak hG e)
    (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const m n ψ hψ hc hpos).1
  have hpm : ∀ p : ℝ × ℝ, presMode m n (fun y => potentialOf Q y - e) p.1 p.2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ (potentialOf Q (cylPoint p.1 θ p.2) - e) : ℝ) : ℂ) := fun p => rfl
  have hgm : ∀ p : ℝ × ℝ, modeVec m n Q p.1 p.2 0 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ ((innerSL ℝ (Q (cylPoint p.1 θ p.2)) : Space →L[ℝ] ℝ)
          (radialUnit θ)) : ℝ) : ℂ) := by
    intro p
    simp only [ContinuousLinearMap.id_apply, innerSL_apply_apply]
    rfl
  simp only [hpm, hgm]
  exact Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal.scale _ hw

theorem pres_height {Q : Space → Space} (hG : IsGradientField Q) (m : ℕ) (n : ℤ) (e : ℝ) :
    IsHeightWeakPair (fun r => r) (fun p : ℝ × ℝ => presMode m n (fun y => potentialOf Q y - e) p.1 p.2)
      (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 2) := by
  have hrect := fun R Z : ℝ => Breakdown.CellCert.CellFormula.MeshDataAffineModes.gradient_modes_integrable m Q hG n e (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, presMode m n (fun y => potentialOf Q y - e) (-p.1) p.2 =
      halfTurn m n * presMode m n (fun y => potentialOf Q y - e) p.1 p.2 := fun p => pres_refl' m n _ p
  have hdF : ∀ p : ℝ × ℝ, modeVec m n Q (-p.1) p.2 2 = halfTurn m n * modeVec m n Q p.1 p.2 2 := by
    intro p
    have := vel_refl m n Q 2 p
    rw [sign_two, mul_one] at this
    exact this
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (fun p : ℝ × ℝ => presMode m n (fun y => potentialOf Q y - e) p.1 p.2)
        {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z hδ => ⟨(hrect R Z).1.mono_set (box_sub δ R Z),
      Breakdown.FracInternal.SegmentModes.off_axis_int (box_meas δ R Z) hδ (fun p hp => hp.1)
        (((hrect R Z).2 2).mono_set (box_sub δ R Z))⟩
  refine ⟨fun R Z => ⟨weighted_rect (hrect R Z).1, (hrect R Z).2 2⟩, hoff,
    height_ident_refl (halfTurn_ne _ _) hF hdF hoff ?_⟩
  intro ψ hψ hc hpos
  have hw := (cylModeWeak ℝ (fun y => potentialOf Q y - e) (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ))
    (shifted_locInt hG e) (inner_cols_locInt hG) (Breakdown.CellCert.CellFormula.pressure_weak hG e)
    (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const m n ψ hψ hc hpos).2
  have hpm : ∀ p : ℝ × ℝ, presMode m n (fun y => potentialOf Q y - e) p.1 p.2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ (potentialOf Q (cylPoint p.1 θ p.2) - e) : ℝ) : ℂ) := fun p => rfl
  have hgm : ∀ p : ℝ × ℝ, modeVec m n Q p.1 p.2 2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ ((innerSL ℝ (Q (cylPoint p.1 θ p.2)) : Space →L[ℝ] ℝ)
          axialUnit) : ℝ) : ℂ) := by
    intro p
    simp only [ContinuousLinearMap.id_apply, innerSL_apply_apply]
    rfl
  simp only [hpm, hgm]
  exact Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal.scale _ hw

end Breakdown.CertCell.Assembly.Internal.TraceLocal

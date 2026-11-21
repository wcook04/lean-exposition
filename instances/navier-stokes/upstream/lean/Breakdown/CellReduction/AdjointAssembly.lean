import Breakdown.CellReduction.AdjointAssemblyFields
import Breakdown.CellReduction.AdjointAssemblyPairing
import Breakdown.CellReduction.AdjointAssemblyCentre

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

theorem integral_six {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α} {f1 f2 f4 f5 : α → ℝ}
    {f3 : ι → α → ℝ} {f6 : κ → α → ℝ} (s : Finset ι) (t : Finset κ) (a : ι → ℝ) (b : κ → ℝ) (c : ℝ)
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : ∀ i ∈ s, Integrable (f3 i) μ) (h4 : Integrable f4 μ)
    (h5 : Integrable f5 μ) (h6 : ∀ l ∈ t, Integrable (f6 l) μ) :
    Integrable (fun z => f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z + ∑ l ∈ t, b l * f6 l z) μ ∧
    ∫ z, (f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z + ∑ l ∈ t, b l * f6 l z) ∂μ =
      (∫ z, f1 z ∂μ) + (∫ z, f2 z ∂μ) + (∑ i ∈ s, a i * ∫ z, f3 i z ∂μ) + (∫ z, f4 z ∂μ) - c * (∫ z, f5 z ∂μ)
        + ∑ l ∈ t, b l * ∫ z, f6 l z ∂μ := by
  have i3 : Integrable (fun z => ∑ i ∈ s, a i * f3 i z) μ :=
    integrable_finsetSum s fun i hi => (h3 i hi).const_mul (a i)
  have i6 : Integrable (fun z => ∑ l ∈ t, b l * f6 l z) μ :=
    integrable_finsetSum t fun l hl => (h6 l hl).const_mul (b l)
  have i5 : Integrable (fun z => c * f5 z) μ := h5.const_mul c
  have i12 : Integrable (fun z => f1 z + f2 z) μ := h1.add h2
  have i123 : Integrable (fun z => f1 z + f2 z + ∑ i ∈ s, a i * f3 i z) μ := i12.add i3
  have i1234 : Integrable (fun z => f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z) μ := i123.add h4
  have i12345 : Integrable (fun z => f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z) μ := i1234.sub i5
  refine ⟨i12345.add i6, ?_⟩
  rw [integral_add i12345 i6, integral_sub i1234 i5, integral_add i123 h4, integral_add i12 i3,
    integral_add h1 h2, integral_finsetSum s (fun i hi => (h3 i hi).const_mul (a i)),
    integral_finsetSum t (fun l hl => (h6 l hl).const_mul (b l)), integral_const_mul]
  simp only [integral_const_mul]

theorem dualBounded_nonneg {R : ℝ → Space → Space} {ρ : ℝ} (h : DualBounded R ρ) : 0 ≤ ρ := by
  obtain ⟨R₁, R₂, ρ₁, ρ₂, -, h1, h2, h3⟩ := h
  linarith [h1.1, h2.1]

theorem periodMatrixIntegral_zero (G : ℝ → Space → (Space →L[ℝ] Space)) :
    periodMatrixIntegral G (fun _ _ => 0) = 0 := by
  simp [periodMatrixIntegral, matrixPairing_zero]

theorem colSq_add_le (X Y : Space →L[ℝ] Space) : matSq (X + Y) ≤ 2 * matSq X + 2 * matSq Y := by
  have key : ∀ a b : Space, ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := fun a b => by
    nlinarith [norm_add_le a b, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  simp only [matSq, add_apply, Fin.sum_univ_three]
  linarith [key (X (unitVector 0)) (Y (unitVector 0)), key (X (unitVector 1)) (Y (unitVector 1)),
    key (X (unitVector 2)) (Y (unitVector 2))]

theorem colSq_continuous : Continuous (fun X : Space →L[ℝ] Space => matSq X) := by
  unfold matSq
  fun_prop

theorem periodLIntegral_add_le_of_joint {f g : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : AEMeasurable (fun z : ℝ × Space => g z.1 z.2) volume) :
    periodLIntegral (fun σ y => f σ y + g σ y) ≤ periodLIntegral f + periodLIntegral g := by
  have hμ : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have mes : ∀ h : ℝ → Space → ℝ, AEMeasurable (fun z : ℝ × Space => h z.1 z.2) volume →
      AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (h z.1 z.2))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    intro h hh
    rw [hμ]
    exact hh.ennreal_ofReal.restrict
  have cv : ∀ h : ℝ → Space → ℝ, AEMeasurable (fun z : ℝ × Space => h z.1 z.2) volume →
      periodLIntegral h = ∫⁻ z, ENNReal.ofReal (h z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    fun h hh => (lintegral_prod _ (mes h hh)).symm
  rw [cv _ (hf.add hg), cv _ hf, cv _ hg, ← lintegral_add_left' (mes f hf)]
  exact lintegral_mono fun z => ENNReal.ofReal_add_le

theorem periodLIntegral_two_mul_lt_top {h : ℝ → Space → ℝ} (hh : periodLIntegral h < ⊤) :
    periodLIntegral (fun σ y => 2 * h σ y) < ⊤ := by
  unfold periodLIntegral at *
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh

theorem pinSquare_finite_of_round {k : ℕ} {χ : Fin k → ℝ → Space → (Space →L[ℝ] Space)} {pd : PinData k}
    {C R₀ ρ : ℝ} (hpin : IsPinData χ pd C R₀)
    (hround : ∀ c : Fin k → ℝ, periodLIntegral (fun σ y =>
      matSq (∑ l, c l • (χ l σ y - fderiv ℝ (pd.potential l σ) y))) ≤ ENNReal.ofReal (ρ ^ 2 * ∑ l, c l ^ 2))
    (l : Fin k) : periodLIntegral (fun σ y => matSq (χ l σ y)) < ⊤ := by
  have h1 : periodLIntegral (fun σ y => matSq (χ l σ y - fderiv ℝ (pd.potential l σ) y)) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt (hround (Pi.single l 1)) ENNReal.ofReal_lt_top)
    congr 1
    funext σ y
    simp [Pi.single_apply, ite_smul]
  have m1 : AEMeasurable (fun z : ℝ × Space =>
      2 * matSq (χ l z.1 z.2 - fderiv ℝ (pd.potential l z.1) z.2)) volume :=
    (colSq_continuous.comp_aestronglyMeasurable
      ((hpin.pin_measurable l).sub (hpin.potentialGrad_measurable l))).aemeasurable.const_mul 2
  have m2 : AEMeasurable (fun z : ℝ × Space => 2 * matSq (fderiv ℝ (pd.potential l z.1) z.2)) volume :=
    (colSq_continuous.comp_aestronglyMeasurable (hpin.potentialGrad_measurable l)).aemeasurable.const_mul 2
  have hle : periodLIntegral (fun σ y => matSq (χ l σ y)) ≤ periodLIntegral (fun σ y =>
      2 * matSq (χ l σ y - fderiv ℝ (pd.potential l σ) y) + 2 * matSq (fderiv ℝ (pd.potential l σ) y)) :=
    lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (by
      have e := colSq_add_le (χ l σ y - fderiv ℝ (pd.potential l σ) y) (fderiv ℝ (pd.potential l σ) y)
      rwa [sub_add_cancel] at e)
  exact lt_of_le_of_lt (hle.trans (periodLIntegral_add_le_of_joint m1 m2))
    (ENNReal.add_lt_top.2 ⟨periodLIntegral_two_mul_lt_top h1,
      periodLIntegral_two_mul_lt_top (hpin.potentialGrad_finite l)⟩)

end Internal

open _root_.Breakdown.AdjointDefect.Internal in
theorem adjointDefectBridge_of_parts (hA : WeightedPairingIntegrableHolds) (hC : CentreResidualFieldHolds)
    (h1 : RepresentationHolds) (h2 : PotentialBoundHolds) (h3 : DualBoundedBoundHolds)
    (h4 : PinChargeHolds) (h5 : FreeShiftBoundHolds) : AdjointDefectBridgeHolds := by
  intro k d r hwf hw hS hPF hCert j hj q hq v G H g hp F hFm hFp hF2 hRS
  have S := hS j hj
  have PF := hPF j hj
  have CE := hCert j hj
  rw [S.adjoint_eq q hq, hwf]
  simp only [S.coupling_eq q hq]
  obtain ⟨Cz, γ, hζ⟩ := S.field_class
  obtain ⟨A, Ca, β, hAp⟩ := S.field_potential
  obtain ⟨D, hcen, hfit, hfree⟩ := S.pieces
  obtain ⟨Cp, hpc, hpf⟩ := PF.potentials
  obtain ⟨Cg, R₀, hpin⟩ := PF.pins
  have hγ := hζ.rate_gt
  set R := r j with hR
  set E := R.fittedSet with hE
  set w₀ := d.weight with hw₀
  set freeSum : ℝ → Space → Space := fun σ y => ∑ i ∈ Eᶜ, q i • R.free q i σ y with hfreeSum
  set s : ℝ := ∑ i ∈ Eᶜ, q i * R.periodRate i with hs
  have hfs : IsFlowPiece freeSum ((∑ i ∈ Eᶜ, |q i|) * D) :=
    flowPiece_sum Eᶜ q (R.free q) fun i hi => hfree q hq i hi
  have hfits : IsFlowPiece (fun σ y => ∑ i ∈ E, q i • R.fitted i σ y) ((∑ i ∈ E, |q i|) * D) :=
    flowPiece_sum E q R.fitted hfit
  have hW : IsFlowPiece (d.profile q) (D + (∑ i ∈ E, |q i|) * D + (∑ i ∈ Eᶜ, |q i|) * D) :=
    flowPiece_congr (flowPiece_add (flowPiece_add (hcen q hq) hfits) hfs)
      (fun σ y => (S.profile_split q hq σ y).symm)
  have hζ' := adjointField_mono hζ (le_max_left Cz Ca)
  have hA' := curlPotential_mono hAp (le_max_right Cz Ca)
  have hrep := h1 d.symmetries (d.period q) _ (max Cz Ca) γ β (d.profile q) R.field A d.actuator v g F G H
    hW hζ' hA' hp hFm hFp hF2 hRS
  have hsplit : ∀ σ y, adjointTransport (d.period q) (d.profile q) R.field σ y =
      R.centreResidual q σ y + (∑ i ∈ E, q i • R.fittedResidual i σ y)
        + advectionShift freeSum R.field σ y - s • timeDerivative R.field σ y := fun σ y =>
    transport_split (d.period q) R.centrePeriod R.periodRate q E (d.profile q) (R.centre q) freeSum R.field
      R.fitted (S.period_split q hq) (S.profile_split q hq) (slice_differentiableAt (hcen q hq).smooth)
      (fun i hi => slice_differentiableAt (hfit i hi).smooth) (slice_differentiableAt hfs.smooth) σ y
  obtain ⟨C1, hres⟩ := hC R d.pin R.centrePeriod Cz γ D Cg R₀ (R.centre q) hζ (hcen q hq) hpin
  have I1 : Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (R.centreResidual q z.1 z.2)) periodMeasure :=
    pairing_integrable hA hp hγ hres.residual_measurable (fun σ y => (hres.decay σ y).1)
  have I2 : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (R.pinFlux z.1 z.2)) periodMeasure :=
    matrix_integrable hp (β := γ + 1) (by linarith) hres.flux_measurable (fun σ y => (hres.decay σ y).2)
  have I3 : ∀ i ∈ E, Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (R.fittedResidual i z.1 z.2))
      periodMeasure := fun i hi =>
    pairing_integrable hA hp hγ (fittedField (R.periodRate i) (hfit i hi) hζ).residual_measurable
      (fun σ y => ((fittedField (R.periodRate i) (hfit i hi) hζ).decay σ y).1)
  have I4 : Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (advectionShift freeSum R.field z.1 z.2))
      periodMeasure :=
    pairing_integrable hA hp hγ (continuous_advectionShift hfs.smooth hζ.smooth).aestronglyMeasurable
      (norm_advectionShift_le hfs hζ)
  have I5 : Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (timeDerivative R.field z.1 z.2))
      periodMeasure :=
    pairing_integrable hA hp hγ (timeDerivative_continuous hζ.smooth).aestronglyMeasurable
      (fun σ y => (hζ.decay σ y).2.1)
  have I6 : ∀ l ∈ (Finset.univ : Finset (Fin k)), Integrable (fun z : ℝ × Space => matInner (G z.1 z.2)
      (fderiv ℝ (R.pins.generator l z.1) z.2
        - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l z.1) z.2))) periodMeasure := by
    intro l _
    obtain ⟨B, hB, hBc⟩ := generatorFlux_bound hpin l
    exact matrix_integrable hp (M := fun σ y => fderiv ℝ (R.pins.generator l σ) y
      - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l σ) y)) (β := 2) (by norm_num)
      hBc.aestronglyMeasurable hB
  obtain ⟨hXi, hXe⟩ := integral_six E Finset.univ q R.pinCoef s I1 I2 I3 I4 I5 I6
  have hpoint : ∀ σ y, inner ℝ (v σ y) (adjointTransport (d.period q) (d.profile q) R.field σ y)
      + matInner (G σ y) (fderiv ℝ (R.field σ) y) =
      inner ℝ (v σ y) (R.centreResidual q σ y) + matInner (G σ y) (R.pinFlux σ y)
        + (∑ i ∈ E, q i * inner ℝ (v σ y) (R.fittedResidual i σ y))
        + inner ℝ (v σ y) (advectionShift freeSum R.field σ y)
        - s * inner ℝ (v σ y) (timeDerivative R.field σ y)
        + ∑ l, R.pinCoef l * matInner (G σ y) (fderiv ℝ (R.pins.generator l σ) y
          - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l σ) y)) := by
    intro σ y
    rw [hsplit σ y, matrixPairing_pin_split R (G σ y) σ y]
    simp only [inner_add_right, inner_sub_right, inner_sum, real_inner_smul_right]
    ring
  have hXint : Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2)
      (adjointTransport (d.period q) (d.profile q) R.field z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (R.field z.1) z.2)) periodMeasure := by
    refine hXi.congr (ae_of_all _ fun z => ?_)
    exact (hpoint z.1 z.2).symm
  have hpair : periodPairing F R.field =
      (periodInnerIntegral v (R.centreResidual q) + periodMatrixIntegral G R.pinFlux)
        + (∑ i ∈ E, q i * periodInnerIntegral v (R.fittedResidual i))
        + periodInnerIntegral v (advectionShift freeSum R.field)
        - s * periodInnerIntegral v (timeDerivative R.field)
        + ∑ l, R.pinCoef l * periodMatrixIntegral G (fun σ y => fderiv ℝ (R.pins.generator l σ) y
          - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l σ) y)) := by
    rw [hrep, iterated_eq hXint]
    have hc : ∫ z, (inner ℝ (v z.1 z.2) (adjointTransport (d.period q) (d.profile q) R.field z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (R.field z.1) z.2)) ∂periodMeasure =
        ∫ z, (inner ℝ (v z.1 z.2) (R.centreResidual q z.1 z.2) + matInner (G z.1 z.2) (R.pinFlux z.1 z.2)
          + (∑ i ∈ E, q i * inner ℝ (v z.1 z.2) (R.fittedResidual i z.1 z.2))
          + inner ℝ (v z.1 z.2) (advectionShift freeSum R.field z.1 z.2)
          - s * inner ℝ (v z.1 z.2) (timeDerivative R.field z.1 z.2)
          + ∑ l ∈ Finset.univ, R.pinCoef l * matInner (G z.1 z.2) (fderiv ℝ (R.pins.generator l z.1) z.2
            - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l z.1) z.2))) ∂periodMeasure :=
      integral_congr_ae (ae_of_all _ fun z => hpoint z.1 z.2)
    rw [hc, hXe]
    unfold periodInnerIntegral periodMatrixIntegral
    have s3 : (∑ i ∈ E, q i * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (v σ y) (R.fittedResidual i σ y)) =
        ∑ i ∈ E, q i * ∫ z, inner ℝ (v z.1 z.2) (R.fittedResidual i z.1 z.2) ∂periodMeasure :=
      Finset.sum_congr rfl fun i hi => by rw [iterated_eq (I3 i hi)]
    have s6 : (∑ l, R.pinCoef l * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y)
        (fderiv ℝ (R.pins.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l σ) y))) =
        ∑ l, R.pinCoef l * ∫ z, matInner (G z.1 z.2) (fderiv ℝ (R.pins.generator l z.1) z.2
          - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l z.1) z.2)) ∂periodMeasure :=
      Finset.sum_congr rfl fun l hl => by rw [iterated_eq (I6 l hl)]
    rw [iterated_eq I1, iterated_eq I2, iterated_eq I4, iterated_eq I5, s3, s6]
  have hresC : IsResidualField (R.centreResidual q) R.pinFlux (max C1 Cp) γ :=
    residualField_mono hres (le_max_left _ _)
  have B1 := h2 d.symmetries (d.period q) w₀ (max C1 Cp) γ v g (R.centreResidual q) G H R.pinFlux
    R.centrePotential R.centreNumbers hw hp hresC (potentialData_mono hpc (le_max_right _ _)) CE.centre_norms
    (h3 _ _ (CE.centre_remainder q hq))
  have B3 : ∀ i ∈ E, |periodInnerIntegral v (R.fittedResidual i)| ≤
      potentialDefect w₀ (R.fittedNumbers i) * Real.sqrt (weightedEnergy (fun _ => w₀) G H) := by
    intro i hi
    have hfC := residualField_mono (fittedField (R.periodRate i) (hfit i hi) hζ)
      (le_max_left ((4 * D + |R.periodRate i|) * Cz) Cp)
    have h := h2 d.symmetries (d.period q) w₀ _ γ v g (R.fittedResidual i) G H (fun _ _ => 0)
      (R.fittedPotential i) (R.fittedNumbers i) hw hp hfC (potentialData_mono (hpf i hi) (le_max_right _ _))
      (CE.fitted_norms i hi) (h3 _ _ (CE.fitted_remainder i hi))
    rwa [periodMatrixIntegral_zero, add_zero] at h
  obtain ⟨δ, hδc, hδs⟩ := CE.free_dual
  have B4 := h5 d.symmetries (d.period q) D Cz γ v g R.field G H Eᶜ (R.free q) q R.freeWeight δ R.freeValue
    R.freeDual hp hζ (fun i hi => hfree q hq i hi) CE.freeWeight_pos
    (fun i hi => dualBounded_nonneg (hδc i hi q hq)) CE.freeValue_nonneg CE.freeDual_nonneg (CE.free_value q hq)
    (fun i hi => h3 _ _ (hδc i hi q hq)) hδs
  have B5 := (h3 _ _ CE.time_dual v G hp.measurable_velocity hp.measurable_gradient hp.weak_gradient
    hp.sixth_power hp.gradient_finite).2.2
  have B6 := h4 d.symmetries (d.period q) w₀ Cg R₀ R.pinError R.pinRound R.pinCoefNorm v g G H d.pin R.pins
    R.pinCoef hw hp hpin (pinSquare_finite_of_round hpin CE.pin_round) CE.pinError_nonneg CE.pinRound_nonneg CE.pinCoef_norm CE.pin_error (CE.pin_round R.pinCoef)
  have hgn := gradientNorm_le hp hw
  have hcb : ∀ i, |q i| ≤ R.coordBound i := fun i => coord_le_bound d j R CE hq i
  have hcb0 : ∀ i, 0 ≤ R.coordBound i := fun i => (abs_nonneg _).trans (hcb i)
  set sE := Real.sqrt (weightedEnergy (fun _ => w₀) G H) with hsE
  have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
  have hsw : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  have hgn0 : 0 ≤ gradientNorm G := Real.sqrt_nonneg _
  have htd := dualBounded_nonneg CE.time_dual
  have T3 : |∑ i ∈ E, q i * periodInnerIntegral v (R.fittedResidual i)| ≤
      (∑ i ∈ E, R.coordBound i * potentialDefect w₀ (R.fittedNumbers i)) * sE := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (hcb i) (B3 i hi) (abs_nonneg _) (hcb0 i)
  have hsq : Real.sqrt (∑ i ∈ Eᶜ, q i ^ 2 / R.freeWeight i) ≤
      Real.sqrt (∑ i ∈ Eᶜ, R.coordBound i ^ 2 / R.freeWeight i) := by
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_)
    refine div_le_div_of_nonneg_right ?_ (CE.freeWeight_pos i hi).le
    exact sq_le_sq.2 ((hcb i).trans (le_abs_self _))
  have T4 : |periodInnerIntegral v (advectionShift freeSum R.field)| ≤
      Real.sqrt (∑ i ∈ Eᶜ, R.coordBound i ^ 2 / R.freeWeight i) * (R.freeValue + R.freeDual)
        * (sE / Real.sqrt w₀) := by
    refine B4.trans ?_
    have hv : 0 ≤ R.freeValue + R.freeDual := add_nonneg CE.freeValue_nonneg CE.freeDual_nonneg
    exact mul_le_mul (mul_le_mul_of_nonneg_right hsq hv) hgn hgn0 (by positivity)
  have hsb : |s| ≤ ∑ i ∈ Eᶜ, |R.periodRate i| * R.coordBound i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcb i) (abs_nonneg _)
  have T5 : |s * periodInnerIntegral v (timeDerivative R.field)| ≤
      (∑ i ∈ Eᶜ, |R.periodRate i| * R.coordBound i) * R.timeDual * (sE / Real.sqrt w₀) := by
    rw [abs_mul, mul_assoc]
    refine mul_le_mul hsb (B5.trans (mul_le_mul_of_nonneg_left hgn htd)) (abs_nonneg _) ?_
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hcb0 i)
  have htot := CE.total
  have hid : (R.defectSum w₀ + R.pinCharge w₀) * sE =
      potentialDefect w₀ R.centreNumbers * sE
        + (∑ i ∈ E, R.coordBound i * potentialDefect w₀ (R.fittedNumbers i)) * sE
        + Real.sqrt (∑ i ∈ Eᶜ, R.coordBound i ^ 2 / R.freeWeight i) * (R.freeValue + R.freeDual)
          * (sE / Real.sqrt w₀)
        + (∑ i ∈ Eᶜ, |R.periodRate i| * R.coordBound i) * R.timeDual * (sE / Real.sqrt w₀)
        + (R.pinError + R.pinCoefNorm * R.pinRound / Real.sqrt w₀) * sE := by
    simp only [AdjointDefectEntry.defectSum, AdjointDefectEntry.pinCharge]
    ring
  have hfin : (R.defectSum w₀ + R.pinCharge w₀) * sE ≤ d.adjointDefect j * sE :=
    mul_le_mul_of_nonneg_right htot hsE0
  rw [hpair]
  set a1 := periodInnerIntegral v (R.centreResidual q) + periodMatrixIntegral G R.pinFlux
  set a3 := ∑ i ∈ E, q i * periodInnerIntegral v (R.fittedResidual i)
  set a4 := periodInnerIntegral v (advectionShift freeSum R.field)
  set a5 := s * periodInnerIntegral v (timeDerivative R.field)
  set a6 := ∑ l, R.pinCoef l * periodMatrixIntegral G (fun σ y => fderiv ℝ (R.pins.generator l σ) y
          - ContinuousLinearMap.adjoint (fderiv ℝ (R.pins.generator l σ) y))
  set a7 := ∑ l, R.pinCoef l * pinValue (d.pin l) G
  have e7 : |a7 - a6| ≤ (R.pinError + R.pinCoefNorm * R.pinRound / Real.sqrt w₀) * sE := B6
  have hb : |a1 + a3 + a4 - a5 + a6 - a7| ≤ |a1| + |a3| + |a4| + |a5| + |a7 - a6| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a1, neg_abs_le a3, neg_abs_le a4, le_abs_self a5, le_abs_self (a7 - a6)]
    · linarith [le_abs_self a1, le_abs_self a3, le_abs_self a4, neg_abs_le a5, neg_abs_le (a7 - a6)]
  linarith

theorem adjointDefectBridge_of_pieces (h1 : RepresentationHolds) (h2 : PotentialBoundHolds)
    (h3 : DualBoundedBoundHolds) (h4 : PinChargeHolds) (h5 : FreeShiftBoundHolds) : AdjointDefectBridgeHolds :=
  adjointDefectBridge_of_parts weightedPairingIntegrable_proof centreResidualField_proof h1 h2 h3 h4 h5

end AdjointDefect

end Breakdown

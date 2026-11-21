import Breakdown.FracCell.ReductionAdjointAdjointExtension
import Breakdown.FracCert.InverseSquare
import Breakdown.FracCert.LinearSolveCore

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace AdjointRepresentationInternal

theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp

theorem pair_of_two {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem aesm_of_weighted {X : Space → Space} (hw : MemLp (fun y => ‖y‖ • X y) 2 volume) :
    AEStronglyMeasurable X volume := by
  have hm : AEStronglyMeasurable (fun y => ‖y‖⁻¹ • (‖y‖ • X y)) volume :=
    (measurable_norm.inv).aestronglyMeasurable.smul hw.1
  refine hm.congr ?_
  filter_upwards [ae_ne_zero] with y hy
  rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

theorem weighted_pair {v X : Space → Space} (hv : AEStronglyMeasurable v volume)
    (hh : Integrable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2)) (hw : MemLp (fun y => ‖y‖ • X y) 2 volume) :
    Integrable (fun y => inner ℝ (v y) (X y)) := by
  have h2 : Integrable (fun y => ‖‖y‖ • X y‖ ^ 2) := hw.integrable_norm_pow two_ne_zero
  refine Integrable.mono' ((hh.add h2).div_const 2) (hv.inner (aesm_of_weighted hw)) ?_
  filter_upwards [ae_ne_zero] with y hy
  have ht : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h1 : ‖inner ℝ (v y) (X y)‖ ≤ ‖v y‖ * ‖X y‖ := by
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have e1 : ‖‖y‖ • X y‖ = ‖y‖ * ‖X y‖ := by rw [norm_smul, norm_norm]
  have e2 : (‖v y‖ / ‖y‖ - ‖y‖ * ‖X y‖) ^ 2 =
      ‖v y‖ ^ 2 / ‖y‖ ^ 2 - 2 * (‖v y‖ * ‖X y‖) + (‖y‖ * ‖X y‖) ^ 2 := by
    field_simp
    ring
  simp only [Pi.add_apply, e1]
  nlinarith [sq_nonneg (‖v y‖ / ‖y‖ - ‖y‖ * ‖X y‖)]

theorem negTrace_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    MemLp (negSecondTrace H) 2 volume := by
  have hc : ∀ i j : Fin 3, MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
    intro i j
    have hm : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
      (hs.measurable_second.apply_continuousLinearMap (unitVector i)).apply_continuousLinearMap (unitVector j)
    refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
    refine hs.second_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Finset.single_le_sum (f := fun b => ‖H y (unitVector i) (unitVector b)‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, ‖H y (unitVector a) (unitVector b)‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact (memLp_finsetSum Finset.univ fun j _ => hc j j).neg

theorem integral_eight {f1 f2 f3 f4 f5 f6 f7 f8 : Space → ℝ} (h1 : Integrable f1) (h2 : Integrable f2)
    (h3 : Integrable f3) (h4 : Integrable f4) (h5 : Integrable f5) (h6 : Integrable f6) (h7 : Integrable f7)
    (h8 : Integrable f8) (w : ℝ) :
    ∫ y, (f1 y + f2 y + f3 y - f4 y + f5 y - f6 y - w * f7 y - f8 y) =
      (∫ y, f1 y) + (∫ y, f2 y) + (∫ y, f3 y) - (∫ y, f4 y) + (∫ y, f5 y) - (∫ y, f6 y) - w * (∫ y, f7 y)
        - ∫ y, f8 y := by
  have g7 : Integrable (fun y => w * f7 y) := h7.const_mul w
  have a2 : Integrable (fun y => f1 y + f2 y) := h1.add h2
  have a3 : Integrable (fun y => f1 y + f2 y + f3 y) := a2.add h3
  have a4 : Integrable (fun y => f1 y + f2 y + f3 y - f4 y) := a3.sub h4
  have a5 : Integrable (fun y => f1 y + f2 y + f3 y - f4 y + f5 y) := a4.add h5
  have a6 : Integrable (fun y => f1 y + f2 y + f3 y - f4 y + f5 y - f6 y) := a5.sub h6
  have a7 : Integrable (fun y => f1 y + f2 y + f3 y - f4 y + f5 y - f6 y - w * f7 y) := a6.sub g7
  rw [integral_sub a7 h8, integral_sub a6 g7, integral_sub a5 h6, integral_add a4 h5, integral_sub a3 h4,
    integral_add a2 h3, integral_add h1 h2, integral_const_mul]

end AdjointRepresentationInternal

open AdjointRepresentationInternal in
theorem adjointRepresentation_of (hA : DriftPairingStatement) (hB : ConvectionPairingStatement)
    (hT : NegTracePairingStatement) (hGr : GradientTracePairingStatement) (hY : MatrixDivergencePairingStatement)
    (hQ : ScalarGradientTracePairingStatement) (hK : CompactTraceWeightStatement)
    (hC : CompactWeakGradientStatement) : AdjointRepresentationStatement := by
  intro α hα1 hα2 k N d j p D hD hW1 hWdiv hWb hζs v G H hs hdr
  obtain ⟨C, hCb⟩ := hWb
  have hreg := hD.adjoint_regular
  have hζ2 : MemLp (d.adjoint j p) 2 volume := hreg.1
  have hvm := hs.measurable_velocity
  have hh := (inverseSquareBound v G hs.measurable_velocity hs.velocity_six hs.gradient_two
    hs.weak_gradient).1
  have htr := negTrace_memLp hs
  obtain ⟨iA, eA⟩ := hA α (d.rotationRate p) d.order v G H hs _ _ _ hreg
  obtain ⟨iB, eB⟩ := hB d.order v G H hs _ _ _ hreg (d.profile p) (d.gradProfile p) C hW1 (fun y => rfl)
    hWdiv hCb
  obtain ⟨hsw1, hsw2, -, -, -⟩ := hD.sharp_weighted
  have hX : MemLp (fun y => d.splitVisc • d.adjoint j p y + d.adjointSharp j p y) 2 volume :=
    (hζ2.const_smul d.splitVisc).add hsw2
  have eS := hT d.order v G H hs _ _ hD.sharp_trace hX (aesm_of_weighted hsw1) hsw1
  obtain ⟨hd1, hd2, -, -, -⟩ := hD.dual_two
  have eD := hT d.order v G H hs _ _ hD.dual_trace hd1 (aesm_of_weighted hd2) hd2
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hD.potential_two
  have eP1 := hGr d.order v G H hs _ _ hD.potential_gradient hp1 hp2 hp3
  have eP2 := hT d.order v G H hs _ _ hD.potential_trace hp1 (aesm_of_weighted hp4) hp4
  obtain ⟨hf1, hf2, hf3⟩ := hD.flux_two
  have eF := hY d.order v G H hs _ _ hD.flux_divergence hf1 hf2 (aesm_of_weighted hf3) hf3
  have eQ := hQ d.order v G H hs _ _ hD.pressure_gradient hD.pressure_two.1
    (aesm_of_weighted hD.pressure_two.2) hD.pressure_two.2
  have ePin : ∀ l, pinValue (d.smoothPin l) G = l2Pair v (D.pinDual l) ∧
      Integrable (fun y => inner ℝ (v y) (D.pinDual l y)) := by
    intro l
    obtain ⟨h1, h2, -, -, -, h6, h7, h8⟩ := hD.pin_regular l
    have hw : MemLp (fun y => ‖y‖ • D.pinTrace l y) 2 volume := hK _ _ h1 h2 h6 h7 h8
    have hfe : (fun y => ‖y‖ • D.pinDual l y) = fun y => (1 / D.pinScale l) • (‖y‖ • D.pinTrace l y) := by
      funext y
      simp only [AdjointDual.pinDual, smul_smul, mul_comm]
    have hw' : MemLp (fun y => ‖y‖ • D.pinDual l y) 2 volume := by
      rw [hfe]
      exact hw.const_smul (1 / D.pinScale l)
    refine ⟨?_, weighted_pair hvm hh hw'⟩
    have hΞ2 : MemLp (D.pinPotential l) 2 volume := h1.continuous.memLp_of_hasCompactSupport h2
    have hdc : Continuous (fun y => fderiv ℝ (D.pinPotential l) y) := h1.continuous_fderiv one_ne_zero
    have hec : Continuous (fun y => entrySq (fderiv ℝ (D.pinPotential l) y)) :=
      continuous_finset_sum _ fun i _ => ((hdc.clm_apply continuous_const).norm.pow 2)
    have hds : HasCompactSupport (fun y => entrySq (fderiv ℝ (D.pinPotential l) y)) :=
      (h2.fderiv (𝕜 := ℝ)).comp_left (g := entrySq) (by simp [entrySq])
    have hdi : Integrable (fun y => entrySq (fderiv ℝ (D.pinPotential l) y)) :=
      hec.integrable_of_hasCompactSupport hds
    have e1 := hGr d.order v G H hs _ _ (hC _ h1 h2) hΞ2 hdc.aestronglyMeasurable hdi
    have e2 := hT d.order v G H hs _ _ h6 hΞ2 h7 hw
    have e3 : pinValue (d.smoothPin l) G =
        (1 / D.pinScale l) * ∫ y, entryInner (G y) (fderiv ℝ (D.pinPotential l) y) := by
      unfold pinValue
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hD.pin_field l y, entryInner, ContinuousLinearMap.smul_apply, real_inner_smul_right,
        Finset.mul_sum]
    have e4 : l2Pair v (D.pinDual l) = (1 / D.pinScale l) * l2Pair v (D.pinTrace l) := by
      unfold l2Pair
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [AdjointDual.pinDual, real_inner_smul_right]
    rw [e3, e4, ← e1, e2]
  have hb' : ∀ y, ‖d.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
      ‖fderiv ℝ (d.profile p) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    intro y
    rw [Real.rpow_neg_one]
    exact hCb y
  have hsym : MemLp (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) v G y) 2 volume :=
    (LinearSolveCore.symProduct_memLp inverseSquareBound hW1 hb' hs).const_smul (2 : ℝ)
  have iD : Integrable (fun y => inner ℝ (driftField α (d.rotationRate p) v G y) (d.adjoint j p y)) :=
    pair_of_two hdr hζ2
  have iT : Integrable (fun y => inner ℝ (negSecondTrace H y) (d.adjoint j p y)) := pair_of_two htr hζ2
  have iT2 : Integrable (fun y => inner ℝ (negSecondTrace H y) (d.adjointSharp j p y)) := pair_of_two htr hsw2
  have iS := pair_of_two hsym hζ2
  have eL : l2Pair (d.localField α p v G H 0) (d.adjoint j p) =
      l2Pair (driftField α (d.rotationRate p) v G) (d.adjoint j p)
        + d.splitVisc * l2Pair (negSecondTrace H) (d.adjoint j p)
        + l2Pair (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) v G y) (d.adjoint j p) := by
    have hpt : (fun y => inner ℝ (d.localField α p v G H 0 y) (d.adjoint j p y)) = fun y =>
        (inner ℝ (driftField α (d.rotationRate p) v G y) (d.adjoint j p y)
          + d.splitVisc * inner ℝ (negSecondTrace H y) (d.adjoint j p y))
          + inner ℝ ((2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) v G y) (d.adjoint j p y) := by
      funext y
      simp only [FracCertData.localField, negSecondTrace, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
        add_zero, inner_add_left, inner_sub_left, inner_neg_left, real_inner_smul_left]
      ring
    have j1 : Integrable (fun y => inner ℝ (driftField α (d.rotationRate p) v G y) (d.adjoint j p y)
        + d.splitVisc * inner ℝ (negSecondTrace H y) (d.adjoint j p y)) := iD.add (iT.const_mul _)
    unfold l2Pair
    rw [hpt, integral_add j1 iS, integral_add iD (iT.const_mul _), integral_const_mul]
  have eSplit : l2Pair (negSecondTrace H) (fun y => d.splitVisc • d.adjoint j p y + d.adjointSharp j p y) =
      d.splitVisc * l2Pair (negSecondTrace H) (d.adjoint j p) + l2Pair (negSecondTrace H) (d.adjointSharp j p) := by
    have hpt : (fun y => inner ℝ (negSecondTrace H y) (d.splitVisc • d.adjoint j p y + d.adjointSharp j p y)) =
        fun y => d.splitVisc * inner ℝ (negSecondTrace H y) (d.adjoint j p y)
          + inner ℝ (negSecondTrace H y) (d.adjointSharp j p y) := by
      funext y
      rw [inner_add_right, real_inner_smul_right]
    unfold l2Pair
    rw [hpt, integral_add (iT.const_mul _) iT2, integral_const_mul]
  have i2 := weighted_pair hvm hh hsw1
  have i4 : Integrable (fun y => ∑ l, d.adjointPin j p l * inner ℝ (v y) (D.pinDual l y)) :=
    integrable_finsetSum _ fun l _ => (ePin l).2.const_mul _
  have i5 := weighted_pair hvm hh hD.pressure_two.2
  have i6 := weighted_pair hvm hh hd2
  have i7 := weighted_pair hvm hh hp4
  have i8 := weighted_pair hvm hh hf3
  have eR : l2Pair v (D.remainderField α d j p) =
      (∫ y, inner ℝ (v y) (driftAdjointField α (d.rotationRate p) (d.adjoint j p) D.adjointGrad y))
        + (∫ y, inner ℝ (v y) (D.sharpTrace y))
        + (∫ y, inner ℝ (v y) (convectionAdjointField (d.profile p) (d.gradProfile p) (d.adjoint j p)
            D.adjointGrad y))
        - (∫ y, ∑ l, d.adjointPin j p l * inner ℝ (v y) (D.pinDual l y))
        + (∫ y, inner ℝ (v y) (D.pressureGrad y)) - (∫ y, inner ℝ (v y) (D.dualTrace y))
        - D.potentialScale * (∫ y, inner ℝ (v y) (D.potentialTrace y)) - ∫ y, inner ℝ (v y) (D.fluxDiv y) := by
    rw [← integral_eight iA i2 iB i4 i5 i6 i7 i8 D.potentialScale]
    unfold l2Pair
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [AdjointDual.remainderField, AdjointDual.residualField, inner_add_right, inner_sub_right,
      real_inner_smul_right, inner_sum]
  have ePinSum : (∫ y, ∑ l, d.adjointPin j p l * inner ℝ (v y) (D.pinDual l y)) =
      ∑ l, d.adjointPin j p l * pinValue (d.smoothPin l) G := by
    rw [integral_finsetSum _ fun l _ => (ePin l).2.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (ePin l).1]
    rfl
  rw [eL, eR, ePinSum]
  simp only [l2Pair] at eA eB eS eD eP1 eP2 eF eQ eSplit ⊢
  linear_combination eA + eB + eS - eSplit - eQ - eD + D.potentialScale * eP1 - D.potentialScale * eP2 + eF

theorem adjointRepresentation : AdjointRepresentationStatement :=
  adjointRepresentation_of driftPairing convectionPairing negTracePairing gradientTracePairing
    matrixDivergencePairing scalarGradientPairing compactTraceWeight compactWeakGradient

end Reduction

end CellCert

end Breakdown

import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology ComplexConjugate
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal

lemma component_integrable {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) (i : Fin 3) : Integrable (fun η => f η i) volume := by
  refine ⟨(PiLp.continuous_apply 2 _ i).comp_aestronglyMeasurable hm, ?_⟩
  obtain ⟨C, hC⟩ := freqL1Norm_le_hsNormSq
  simp only [freqL1Norm] at hC
  refine lt_of_le_of_lt (lintegral_mono fun η => ?_) (lt_of_le_of_lt (hC f) ?_)
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le (f η) i)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hf 2).ne)

lemma weighted_lintegral_lt_top {f : Space → CSpace} (hf : ∀ m, hsNormSq m f < ⊤) :
    ∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ 1) * ‖f η‖ₑ < ⊤ := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le 1
  exact lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hf _).ne))

lemma coord_component_integrable {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) (i j : Fin 3) :
    Integrable (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) volume := by
  have hmeas : AEStronglyMeasurable (fun η : Space => ((η j : ℝ) : ℂ) * f η i) volume :=
    ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)).aestronglyMeasurable).mul
      (component_integrable hm hf i).1
  have h : Integrable (fun η : Space => ((η j : ℝ) : ℂ) * f η i) volume := by
    refine ⟨hmeas, lt_of_le_of_lt (lintegral_mono fun η => ?_) (weighted_lintegral_lt_top hf)⟩
    rw [enorm_mul]
    gcongr
    · rw [← ofReal_norm, Complex.norm_real, pow_one]
      exact ENNReal.ofReal_le_ofReal ((PiLp.norm_apply_le η j).trans (by linarith [norm_nonneg η]))
    · rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le (f η) i)
  simpa only [mul_assoc] using h.const_mul (2 * (π : ℂ) * Complex.I)

lemma convC_integrable {u v : Space → ℂ} (hu : Integrable u volume) (hv : Integrable v volume) :
    Integrable (convC u v) volume := by
  have h := hu.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hv
  convert h using 1
  funext ξ
  simp [convC, convolution_def]

lemma advectionSymbol_integrable {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) : Integrable (advectionSymbol f) volume := by
  have hA : ∀ i, Integrable (fun ξ => advectionSymbol f ξ i) volume := by
    intro i
    have h : (fun ξ => advectionSymbol f ξ i) = fun ξ => ∑ j, convC (fun η => f η j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) ξ := by
      funext ξ
      simp [advectionSymbol, advectionBilin]
    rw [h]
    exact integrable_finsetSum _ fun j _ => convC_integrable (component_integrable hm hf j)
      (coord_component_integrable hm hf i j)
  have heq : advectionSymbol f =
      fun ξ => ∑ i, advectionSymbol f ξ i • EuclideanSpace.single i (1 : ℂ) := by
    funext ξ
    ext k
    simp [Pi.single_apply]
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (hA i).smul_const _

lemma conjVec_coord (z : CSpace) (i : Fin 3) : conjVec z i = conj (z i) := rfl

lemma convC_neg_conj {u v u' v' : Space → ℂ} (hu : ∀ η, u (-η) = conj (u' η))
    (hv : ∀ η, v (-η) = conj (v' η)) (ξ : Space) :
    convC u v (-ξ) = conj (convC u' v' ξ) := by
  unfold convC
  calc ∫ η, u η * v (-ξ - η) = ∫ η, u (-η) * v (-ξ - -η) :=
        (integral_neg_eq_self (fun η => u η * v (-ξ - η)) volume).symm
    _ = ∫ η, conj (u' η * v' (ξ - η)) := by
        congr 1
        funext η
        rw [show -ξ - -η = -(ξ - η) by abel, hu, hv, map_mul]
    _ = conj (∫ η, u' η * v' (ξ - η)) := integral_conj

end Internal

theorem memLp_one_advectionSymbol {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    MemLp (advectionSymbol f) 1 volume :=
  memLp_one_iff_integrable.2 (Internal.advectionSymbol_integrable hm hf)

theorem memLp_two_advectionSymbol {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    MemLp (advectionSymbol f) 2 volume := by
  obtain ⟨C, hC⟩ := hsNormSq_advectionBilin_le 0
  obtain ⟨D, hD⟩ := freqL1Norm_le_hsNormSq
  refine ⟨(Internal.advectionSymbol_integrable hm hf).1, ?_⟩
  have hw : freqL1Norm f < ⊤ := lt_of_le_of_lt (hD f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hf 2).ne))
  have hg : gradFreqL1Norm f < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun η => ?_) (Internal.weighted_lintegral_lt_top hf)
    gcongr
    rw [pow_one]
    linarith
  have hfin : hsNormSq 0 (advectionBilin f f) < ⊤ := by
    refine lt_of_le_of_lt (hC f f hm hm) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    have h1 := hf 1
    have h0 := hf 0
    finiteness
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa [hsNormSq, hsWeight, advectionSymbol] using hfin

theorem advectionSymbol_neg {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) (ξ : Space) :
    advectionSymbol f (-ξ) = conjVec (advectionSymbol f ξ) := by
  ext i
  rw [Internal.conjVec_coord]
  simp only [advectionSymbol, advectionBilin, PiLp.toLp_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Internal.convC_neg_conj (fun η => ?_) (fun η => ?_) ξ
  · rw [(hs η).2, Internal.conjVec_coord]
  · rw [(hs η).2, Internal.conjVec_coord]
    simp [map_mul, Complex.conj_ofReal, map_ofNat]

end Breakdown.SmoothFlow

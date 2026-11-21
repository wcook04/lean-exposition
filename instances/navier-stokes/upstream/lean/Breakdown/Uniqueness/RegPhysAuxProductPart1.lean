import Breakdown.Uniqueness.RegDefs

open scoped ContDiff ENNReal FourierTransform Topology ComplexConjugate
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal.ConvProduct

def wt (k : ℕ) (ξ : Space) : ℝ≥0∞ := ENNReal.ofReal ((1 + ‖ξ‖) ^ k)

def polyWeight (k : ℕ) : Measure Space := volume.withDensity (wt k)

theorem measurable_wt (k : ℕ) : Measurable (wt k) :=
  ENNReal.measurable_ofReal.comp ((continuous_const.add continuous_norm).pow k).measurable

theorem wt_le (k : ℕ) (ξ η : Space) : wt k ξ ≤ wt k η * wt k (ξ - η) := by
  unfold wt
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  have h1 : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    have := norm_add_le η (ξ - η)
    rwa [add_sub_cancel] at this
  nlinarith [norm_nonneg η, norm_nonneg (ξ - η)]

theorem volume_le_polyWeight (k : ℕ) : (volume : Measure Space) ≤ polyWeight k := by
  calc (volume : Measure Space) = volume.withDensity 1 := withDensity_one.symm
    _ ≤ polyWeight k := withDensity_mono (Eventually.of_forall fun ξ => by
        simp only [Pi.one_apply, wt]
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg ξ])))

theorem memLp_polyWeight_iff {E : Type*} [NormedAddCommGroup E] {u : Space → E} (k : ℕ) :
    MemLp u 1 (polyWeight k) ↔
      AEStronglyMeasurable u volume ∧ ∫⁻ ξ, wt k ξ * ‖u ξ‖ₑ < ⊤ := by
  have hI : ∫⁻ ξ, ‖u ξ‖ₑ ∂(polyWeight k) = ∫⁻ ξ, wt k ξ * ‖u ξ‖ₑ :=
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_wt k)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  constructor
  · rintro ⟨hm, hn⟩
    refine ⟨hm.mono_ac (Measure.absolutelyContinuous_of_le (volume_le_polyWeight k)), ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm, hI] at hn
    exact hn
  · rintro ⟨hm, hn⟩
    refine ⟨hm.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm, hI]
    exact hn

theorem integrable_of_memLp_polyWeight {E : Type*} [NormedAddCommGroup E] {u : Space → E} {k : ℕ}
    (hu : MemLp u 1 (polyWeight k)) : Integrable u :=
  memLp_one_iff_integrable.1 (hu.mono_measure (volume_le_polyWeight k))

theorem memLp_polyWeight_apply {f : Space → CSpace} {k : ℕ} (hf : MemLp f 1 (polyWeight k)) (i : Fin 3) :
    MemLp (fun ξ => f ξ i) 1 (polyWeight k) :=
  (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).comp_memLp' hf

theorem memLp_freq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : Space → E} {k : ℕ}
    (hg : MemLp g 1 (polyWeight (k + 1))) (j : Fin 3) :
    MemLp (fun η => (2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) • g η) 1 (polyWeight k) := by
  rw [memLp_polyWeight_iff] at hg ⊢
  obtain ⟨hm, hn⟩ := hg
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) := by fun_prop
    exact hc.aestronglyMeasurable.smul hm
  · have hle : ∀ η : Space, wt k η * ‖(2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) • g η‖ₑ ≤
        ENNReal.ofReal (2 * π) * (wt (k + 1) η * ‖g η‖ₑ) := by
      intro η
      have h1 : ‖(2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) • g η‖ₑ =
          ENNReal.ofReal (2 * π * |η j|) * ‖g η‖ₑ := by
        rw [enorm_smul, ← ofReal_norm]
        congr 2
        simp [abs_of_pos pi_pos]
      have h2 : |η j| ≤ 1 + ‖η‖ := by
        have := PiLp.norm_apply_le η j
        rw [Real.norm_eq_abs] at this
        linarith
      rw [h1, ← mul_assoc, ← mul_assoc]
      gcongr ?_ * _
      unfold wt
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h3 : 0 ≤ (1 + ‖η‖) ^ k := by positivity
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left h2 h3, pi_pos, abs_nonneg (η j)]
    calc ∫⁻ η, wt k η * ‖(2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) • g η‖ₑ
        ≤ ∫⁻ η, ENNReal.ofReal (2 * π) * (wt (k + 1) η * ‖g η‖ₑ) := lintegral_mono hle
      _ = ENNReal.ofReal (2 * π) * ∫⁻ η, wt (k + 1) η * ‖g η‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn

theorem convC_eq_convolution (a b : Space → ℂ) :
    convC a b = convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext ξ
  simp [convC, convolution_def]

theorem convC_congr_ae' {a a' b b' : Space → ℂ} (ha : a =ᵐ[volume] a') (hb : b =ᵐ[volume] b')
    (ξ : Space) : convC a b ξ = convC a' b' ξ := by
  unfold convC
  refine integral_congr_ae ?_
  have hb' : ∀ᵐ η ∂(volume : Measure Space), b (ξ - η) = b' (ξ - η) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae hb
  filter_upwards [ha, hb'] with η h1 h2
  rw [h1, h2]

theorem lintegral_convC_le {a b : Space → ℂ} (ha : StronglyMeasurable a) (hb : StronglyMeasurable b)
    (k : ℕ) : ∫⁻ ξ, wt k ξ * ‖convC a b ξ‖ₑ ≤
      (∫⁻ η, wt k η * ‖a η‖ₑ) * ∫⁻ η, wt k η * ‖b η‖ₑ := by
  set A : Space → ℝ≥0∞ := fun η => wt k η * ‖a η‖ₑ with hAdef
  set B : Space → ℝ≥0∞ := fun η => wt k η * ‖b η‖ₑ with hBdef
  have hA : Measurable A := (measurable_wt k).mul ha.measurable.enorm
  have hB : Measurable B := (measurable_wt k).mul hb.measurable.enorm
  have step : ∀ ξ, wt k ξ * ‖convC a b ξ‖ₑ ≤ ∫⁻ η, A η * B (ξ - η) := by
    intro ξ
    calc wt k ξ * ‖convC a b ξ‖ₑ ≤ wt k ξ * ∫⁻ η, ‖a η‖ₑ * ‖b (ξ - η)‖ₑ := by
          gcongr
          unfold convC
          refine (enorm_integral_le_lintegral_enorm _).trans ?_
          simp only [enorm_mul, le_refl]
      _ = ∫⁻ η, wt k ξ * (‖a η‖ₑ * ‖b (ξ - η)‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, A η * B (ξ - η) := lintegral_mono fun η => by
          calc wt k ξ * (‖a η‖ₑ * ‖b (ξ - η)‖ₑ)
              ≤ (wt k η * wt k (ξ - η)) * (‖a η‖ₑ * ‖b (ξ - η)‖ₑ) := by
                gcongr
                exact wt_le k ξ η
            _ = A η * B (ξ - η) := by
                simp only [hAdef, hBdef]
                ring
  have hP : Measurable (fun p : Space × Space => A p.2 * B (p.1 - p.2)) :=
    (hA.comp measurable_snd).mul (hB.comp (measurable_fst.sub measurable_snd))
  calc ∫⁻ ξ, wt k ξ * ‖convC a b ξ‖ₑ ≤ ∫⁻ ξ, ∫⁻ η, A η * B (ξ - η) := lintegral_mono step
    _ = ∫⁻ η, ∫⁻ ξ, A η * B (ξ - η) := lintegral_lintegral_swap hP.aemeasurable
    _ = ∫⁻ η, A η * ∫⁻ ξ, B ξ := by
        congr 1
        funext η
        have h := lintegral_const_mul (μ := (volume : Measure Space)) (A η) (f := fun ξ => B (ξ - η))
          (hB.comp (measurable_id.sub_const η))
        rw [h, lintegral_sub_right_eq_self]
    _ = (∫⁻ η, A η) * ∫⁻ ξ, B ξ := lintegral_mul_const _ hA

theorem memLp_convC {a b : Space → ℂ} {k : ℕ} (ha : MemLp a 1 (polyWeight k))
    (hb : MemLp b 1 (polyWeight k)) : MemLp (convC a b) 1 (polyWeight k) := by
  have hai := integrable_of_memLp_polyWeight ha
  have hbi := integrable_of_memLp_polyWeight hb
  have hm : AEStronglyMeasurable (convC a b) volume := by
    rw [convC_eq_convolution]
    exact (hai.integrable_convolution _ hbi).aestronglyMeasurable
  rw [memLp_polyWeight_iff] at ha hb ⊢
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨hm, ?_⟩
  have hc : convC a b = convC (ha1.mk a) (hb1.mk b) :=
    funext fun ξ => convC_congr_ae' ha1.ae_eq_mk hb1.ae_eq_mk ξ
  have e1 : ∫⁻ η, wt k η * ‖a η‖ₑ = ∫⁻ η, wt k η * ‖ha1.mk a η‖ₑ :=
    lintegral_congr_ae (by filter_upwards [ha1.ae_eq_mk] with η h; rw [h])
  have e2 : ∫⁻ η, wt k η * ‖b η‖ₑ = ∫⁻ η, wt k η * ‖hb1.mk b η‖ₑ :=
    lintegral_congr_ae (by filter_upwards [hb1.ae_eq_mk] with η h; rw [h])
  rw [hc]
  calc _ ≤ _ := lintegral_convC_le ha1.stronglyMeasurable_mk hb1.stronglyMeasurable_mk k
    _ < ⊤ := by
        rw [← e1, ← e2]
        exact ENNReal.mul_lt_top ha2 hb2

theorem advectionSymbol_apply (f : Space → CSpace) (ξ : Space) (i : Fin 3) :
    advectionSymbol f ξ i = ∑ j, convC (fun η => f η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) ξ := by
  simp [advectionSymbol, advectionBilin]

theorem memLp_advectionSymbol_aux {f : Space → CSpace} (hf : ∀ k, MemLp f 1 (polyWeight k)) (k : ℕ) :
    MemLp (advectionSymbol f) 1 (polyWeight k) := by
  have hc : ∀ i, MemLp (fun ξ => advectionSymbol f ξ i) 1 (polyWeight k) := by
    intro i
    have h := memLp_finsetSum' (μ := polyWeight k) (p := 1) Finset.univ
      (f := fun j => convC (fun η => f η j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i))
      (fun j _ => memLp_convC (memLp_polyWeight_apply (hf k) j)
        (memLp_freq_smul (memLp_polyWeight_apply (hf (k + 1)) i) j))
    have heq : (fun ξ => advectionSymbol f ξ i) = ∑ j, convC (fun η => f η j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) := by
      funext ξ
      rw [advectionSymbol_apply, Finset.sum_apply]
    rw [heq]
    exact h
  have heq : advectionSymbol f = ∑ i, fun ξ =>
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (EuclideanSpace.single i (1 : ℂ)))
        (advectionSymbol f ξ i) := by
    funext ξ
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq]
  exact memLp_finsetSum' _ fun i _ =>
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (EuclideanSpace.single i (1 : ℂ))).comp_memLp' (hc i)

end Internal.ConvProduct

end Breakdown.SmoothFlow

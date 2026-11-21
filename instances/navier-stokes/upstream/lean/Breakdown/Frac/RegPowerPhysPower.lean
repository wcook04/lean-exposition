import Breakdown.Frac.StSpaceReg
import Breakdown.Frac.StTorusCoef
import Breakdown.Frac.OpSymbolScalar
import Breakdown.Frac.OpNormalizer
import Breakdown.Frac.OpIntegrable
import Breakdown.Uniqueness.RegPhysAuxDeriv

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter Metric

noncomputable section

namespace Breakdown.SmoothFlow.PowerInternal

open Breakdown.Freq Breakdown.SmoothFlow.Internal Breakdown.FracInternal

private def waveRem (s : ℝ) : ℂ :=
  Complex.exp (((2 * π * s : ℝ) : ℂ) * Complex.I) - 1 - ((2 * π * s : ℝ) : ℂ) * Complex.I
    + (((2 * π * s) ^ 2 / 2 : ℝ) : ℂ)

private theorem norm_ofReal_mul_I (t : ℝ) : ‖(t : ℂ) * Complex.I‖ = |t| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem wave_quad (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      3 * t ^ 2 := by
  have h2 : ‖((t ^ 2 / 2 : ℝ) : ℂ)‖ = t ^ 2 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hA : ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖ ≤ 2 * t ^ 2 := by
    rcases le_or_gt |t| 1 with ht | ht
    · have := Complex.norm_exp_sub_one_sub_id_le (x := (t : ℂ) * Complex.I)
        (by rw [norm_ofReal_mul_I]; exact ht)
      rw [norm_ofReal_mul_I, sq_abs] at this
      nlinarith [sq_nonneg t]
    · have h1 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
        have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
        rw [mul_comm] at this
        simpa [Real.norm_eq_abs] using this
      have hsq : |t| ≤ t ^ 2 := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      calc ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖
          ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ + ‖(t : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ ≤ |t| + |t| := by rw [norm_ofReal_mul_I]; linarith
        _ ≤ 2 * t ^ 2 := by linarith
  calc _ ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖ +
        ‖((t ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * t ^ 2 + t ^ 2 / 2 := by rw [h2]; linarith
    _ ≤ 3 * t ^ 2 := by nlinarith [sq_nonneg t]

private theorem wave_cube (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      3 * |t| ^ 3 := by
  rcases le_or_gt |t| 1 with ht | ht
  · have h := Complex.exp_bound (x := (t : ℂ) * Complex.I) (by rw [norm_ofReal_mul_I]; exact ht)
      (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, ((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + (t : ℂ) * Complex.I - ((t ^ 2 / 2 : ℝ) : ℂ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
        Nat.factorial_one, Nat.factorial_two]
      push_cast
      linear_combination ((t : ℂ) ^ 2 / 2) * Complex.I_sq
    rw [hs, norm_ofReal_mul_I] at h
    have he : Complex.exp ((t : ℂ) * Complex.I) - (1 + (t : ℂ) * Complex.I - ((t ^ 2 / 2 : ℝ) : ℂ)) =
        Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I + ((t ^ 2 / 2 : ℝ) : ℂ) := by
      ring
    rw [he] at h
    refine h.trans ?_
    rw [mul_comm 3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    norm_num [Nat.factorial]
  · have := wave_quad t
    have h3 : t ^ 2 ≤ |t| ^ 3 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t, sq_nonneg |t|]
    linarith

private theorem waveRem_sq (s : ℝ) : ‖waveRem s‖ ≤ 3 * (2 * π * s) ^ 2 := wave_quad _

private theorem waveRem_cube (s : ℝ) : ‖waveRem s‖ ≤ 3 * |2 * π * s| ^ 3 := wave_cube _

private theorem waveRem_eq_trig (s : ℝ) :
    waveRem s = ((Real.cos (2 * π * s) - 1 + (2 * π * s) ^ 2 / 2 : ℝ) : ℂ) +
      ((Real.sin (2 * π * s) - 2 * π * s : ℝ) : ℂ) * Complex.I := by
  unfold waveRem
  rw [Complex.exp_mul_I]
  push_cast
  ring

private theorem integral_waveRem (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2) (ξ : Space) :
    Integrable (fun z : Space => ((‖z‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ) * waveRem (inner ℝ ξ z)) ∧
    ∫ z : Space, ((‖z‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ) * waveRem (inner ℝ ξ z) =
      (((2 * π * ‖ξ‖) ^ (2 * α) * fractionalNormalizer α : ℝ) : ℂ) := by
  obtain ⟨hc, hci, hs, hsi⟩ := symbolScalar normalizer α h1 h2 ((2 * π) • ξ)
  have hpt : ∀ z : Space, ((‖z‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ) * waveRem (inner ℝ ξ z) =
      ((‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (inner ℝ z ((2 * π) • ξ)) - 1 +
        (inner ℝ z ((2 * π) • ξ)) ^ 2 / 2) : ℝ) : ℂ) +
      ((‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ((2 * π) • ξ)) -
        inner ℝ z ((2 * π) • ξ)) : ℝ) : ℂ) * Complex.I := by
    intro z
    rw [real_inner_smul_right, real_inner_comm z ξ, waveRem_eq_trig]
    push_cast
    ring
  have hI1 : Integrable (fun z : Space => ((‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (inner ℝ z ((2 * π) • ξ)) - 1 +
        (inner ℝ z ((2 * π) • ξ)) ^ 2 / 2) : ℝ) : ℂ)) := hc.ofReal
  have hI2 : Integrable (fun z : Space => ((‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ((2 * π) • ξ)) -
        inner ℝ z ((2 * π) • ξ)) : ℝ) : ℂ) * Complex.I) := (hs.ofReal).mul_const Complex.I
  simp_rw [hpt]
  refine ⟨hI1.add hI2, ?_⟩
  rw [integral_add hI1 hI2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hci, hsi]
  have hn : ‖(2 * π) • ξ‖ = 2 * π * ‖ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  push_cast
  ring

end Breakdown.SmoothFlow.PowerInternal

namespace Breakdown.SmoothFlow.PowerInternal

open Breakdown.Freq Breakdown.SmoothFlow.Internal Breakdown.FracInternal

private theorem physField_eq_char (F : Space → CSpace) (x : Space) :
    physField F x = realVec (∫ ξ, 𝐞 (inner ℝ ξ x) • F ξ) := by
  simp only [physField, Real.fourierInv_eq]

private theorem char_smul_eq (t : ℝ) (v : CSpace) :
    𝐞 t • v = Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) • v := rfl

private theorem memLp_weight_mono {f : Space → CSpace} {j k : ℕ} (hjk : j ≤ k)
    (hf : MemLp f 1 (weightL1Measure k)) : MemLp f 1 (weightL1Measure j) := by
  have hm := aestronglyMeasurable_of_weight hf
  rw [memLp_weight_iff hm] at hf ⊢
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hf
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
    (pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hjk)) zero_le

private theorem physField_translate (f : Space → CSpace) (x z : Space) :
    physField f (x + z) = physField (fun ξ => 𝐞 (inner ℝ ξ z) • f ξ) x := by
  rw [physField_eq_char, physField_eq_char]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [inner_add_right, AddChar.map_add_eq_mul, mul_smul]

private theorem second_physField {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 3)) (x z : Space) :
    iteratedFDeriv ℝ 2 (physField f) x ![z, z] =
      physField (fun ξ => ((-(4 * π ^ 2 * (inner ℝ ξ z) ^ 2) : ℝ) : ℂ) • f ξ) x := by
  have hmeas := aestronglyMeasurable_of_weight hf
  have hpow : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (fun v : Space => ‖v‖ ^ n * ‖f v‖) :=
    fun n hn => integrable_pow_mul_of_weight hf (by
      have : n ≤ 2 := by exact_mod_cast hn
      omega)
  have hF : 𝓕⁻ f = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ f :=
    funext fun y => freqTrInv_eq_integral f y
  have hcd := VectorFourier.contDiff_fourierIntegral (μ := volume)
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) (N := 2) hpow
  rw [← hF] at hcd
  have hit : iteratedFDeriv ℝ 2 (𝓕⁻ f) x = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂
      (fun v => VectorFourier.fourierPowSMulRight
        (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f v 2) x := by
    rw [hF, VectorFourier.iteratedFDeriv_fourierIntegral _ hpow hmeas le_rfl]
  have hcomp : iteratedFDeriv ℝ 2 (realVec ∘ 𝓕⁻ f) x =
      realVec.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 (𝓕⁻ f) x) :=
    realVec.iteratedFDeriv_comp_left hcd.contDiffAt (by exact_mod_cast le_rfl)
  have hint := VectorFourier.integrable_fourierPowSMulRight (μ := volume)
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) (hpow 2 le_rfl) hmeas
  have hphys : physField f = realVec ∘ 𝓕⁻ f := rfl
  rw [hphys, hcomp]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [hit, VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hint]
  unfold physField
  rw [freqTrInv_eq_integral]
  refine congrArg (fun F => realVec (VectorFourier.fourierIntegral 𝐞 volume
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ F x)) (funext fun v => ?_)
  simp only [VectorFourier.fourierPowSMulRight_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, neg_apply, neg_mul_neg]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  have hin : ((innerSL ℝ) v) z = inner ℝ v z := rfl
  rw [hin]
  push_cast
  linear_combination (4 * (π : ℂ) ^ 2 * ((inner ℝ v z : ℝ) : ℂ) ^ 2) * Complex.I_sq

private theorem integrable_smul_of_bound {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 3))
    {c : Space → ℂ} (hc : Continuous c) {K : ℝ} (hK : ∀ ξ, ‖c ξ‖ ≤ K * (1 + ‖ξ‖) ^ 3) :
    Integrable (fun ξ => c ξ • f ξ) := by
  refine ((integrable_weight_smul hf).norm.const_mul K).mono'
    (hc.aestronglyMeasurable.smul (aestronglyMeasurable_of_weight hf))
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ 3)]
  calc ‖c ξ‖ * ‖f ξ‖ ≤ K * (1 + ‖ξ‖) ^ 3 * ‖f ξ‖ :=
        mul_le_mul_of_nonneg_right (hK ξ) (norm_nonneg _)
    _ = K * ((1 + ‖ξ‖) ^ 3 * ‖f ξ‖) := by ring

private theorem remainder_physField {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 3))
    (x z : Space) :
    secondOrderRemainder (physField f) x z =
      physField (fun ξ => waveRem (inner ℝ ξ z) • f ξ) x := by
  have h0 := integrable_of_weight hf
  have h1 : Integrable (fun v : Space => ‖v‖ * ‖f v‖) := by
    simpa using integrable_pow_mul_of_weight hf (n := 1) (by norm_num)
  have hA : Integrable (fun ξ => 𝐞 (inner ℝ ξ z) • f ξ) := integrable_char_smul h0 z
  have hB := integrable_symbol_smul h0 h1 z
  have hC : Integrable (fun ξ => ((-(4 * π ^ 2 * (inner ℝ ξ z) ^ 2) : ℝ) : ℂ) • f ξ) := by
    refine integrable_smul_of_bound hf (Complex.continuous_ofReal.comp (by fun_prop))
      (K := 4 * π ^ 2 * ‖z‖ ^ 2) (fun ξ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
    have hs : |inner ℝ ξ z| ≤ ‖ξ‖ * ‖z‖ := abs_real_inner_le_norm ξ z
    have hs2 : (inner ℝ ξ z) ^ 2 ≤ (‖ξ‖ * ‖z‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
    have ha := norm_nonneg ξ
    have hξ : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 3 := by nlinarith [mul_nonneg ha (mul_nonneg ha ha)]
    calc 4 * π ^ 2 * inner ℝ ξ z ^ 2 ≤ 4 * π ^ 2 * (‖ξ‖ * ‖z‖) ^ 2 := by gcongr
      _ = 4 * π ^ 2 * ‖z‖ ^ 2 * ‖ξ‖ ^ 2 := by ring
      _ ≤ 4 * π ^ 2 * ‖z‖ ^ 2 * (1 + ‖ξ‖) ^ 3 := by gcongr
  have iA := integrable_char_smul hA x
  have i0 := integrable_char_smul h0 x
  have iB := integrable_char_smul hB x
  have iC := integrable_char_smul hC x
  unfold secondOrderRemainder
  rw [physField_translate, fderiv_physField_apply (memLp_weight_mono (by norm_num) hf),
    second_physField hf]
  simp only [physField_eq_char]
  have hpt : (fun ξ => 𝐞 (inner ℝ ξ x) • waveRem (inner ℝ ξ z) • f ξ) = fun ξ =>
      𝐞 (inner ℝ ξ x) • 𝐞 (inner ℝ ξ z) • f ξ - 𝐞 (inner ℝ ξ x) • f ξ
        - 𝐞 (inner ℝ ξ x) • (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ z : ℝ) : ℂ)) • f ξ
        - (1 / 2 : ℝ) • (𝐞 (inner ℝ ξ x) • ((-(4 * π ^ 2 * (inner ℝ ξ z) ^ 2) : ℝ) : ℂ) • f ξ) := by
    funext ξ
    simp only [char_smul_eq]
    rw [← Complex.coe_smul]
    simp only [smul_smul, ← sub_smul]
    congr 1
    simp only [waveRem]
    push_cast
    ring
  rw [hpt, integral_sub, integral_sub, integral_sub, integral_smul, map_sub, map_sub, map_sub,
    realVec.map_smul]
  all_goals first
    | rfl
    | exact iA
    | exact i0
    | exact iB
    | exact iC.smul (1 / 2 : ℝ)
    | exact iA.sub i0
    | exact (iA.sub i0).sub iB

private def kernelTerm (α : ℝ) (f : Space → CSpace) (x z ξ : Space) : CSpace :=
  ((‖z‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ) • (𝐞 (inner ℝ ξ x) • (waveRem (inner ℝ ξ z) • f ξ))

private theorem kernel_bound (α : ℝ) (hα : 1 < α) (z ξ : Space) :
    ‖z‖ ^ (-(3 + 2 * α)) * ‖waveRem (inner ℝ ξ z)‖ ≤
      (3 * (2 * π) ^ 3 + 3 * (2 * π) ^ 2) *
        ((ball (0 : Space) 1).indicator (fun z => ‖z‖ ^ (-(2 * α))) z +
          (ball (0 : Space) 1)ᶜ.indicator (fun z => ‖z‖ ^ (-(1 + 2 * α))) z) * (1 + ‖ξ‖) ^ 3 := by
  have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg z) _
  have hs : |inner ℝ ξ z| ≤ (1 + ‖ξ‖) * ‖z‖ :=
    (abs_real_inner_le_norm ξ z).trans
      (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg ξ]) (norm_nonneg _))
  have hπ : 0 < 2 * π := by positivity
  have h1ξ : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  by_cases hz : z ∈ ball (0 : Space) 1
  · have hnot : z ∉ (ball (0 : Space) 1)ᶜ := fun h => h hz
    rw [indicator_of_mem hz, Set.indicator_of_notMem hnot, add_zero]
    have hw := waveRem_cube (inner ℝ ξ z)
    have h3 : |2 * π * inner ℝ ξ z| ^ 3 ≤ (2 * π) ^ 3 * ((1 + ‖ξ‖) ^ 3 * ‖z‖ ^ 3) := by
      rw [abs_mul, abs_of_pos hπ, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hs 3
    have hKz : ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 3 = ‖z‖ ^ (-(2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg z) (by push_cast; intro h; linarith)]
      congr 1
      push_cast
      ring
    have hpos : 0 ≤ ‖z‖ ^ (-(2 * α)) * (1 + ‖ξ‖) ^ 3 := by positivity
    calc ‖z‖ ^ (-(3 + 2 * α)) * ‖waveRem (inner ℝ ξ z)‖
        ≤ ‖z‖ ^ (-(3 + 2 * α)) * (3 * ((2 * π) ^ 3 * ((1 + ‖ξ‖) ^ 3 * ‖z‖ ^ 3))) :=
          mul_le_mul_of_nonneg_left (hw.trans (by linarith)) hK0
      _ = 3 * (2 * π) ^ 3 * ((‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 3) * (1 + ‖ξ‖) ^ 3) := by ring
      _ = 3 * (2 * π) ^ 3 * (‖z‖ ^ (-(2 * α)) * (1 + ‖ξ‖) ^ 3) := by rw [hKz]
      _ ≤ (3 * (2 * π) ^ 3 + 3 * (2 * π) ^ 2) * (‖z‖ ^ (-(2 * α)) * (1 + ‖ξ‖) ^ 3) := by
          gcongr
          nlinarith [sq_nonneg (2 * π)]
      _ = _ := by ring
  · have hin : z ∈ (ball (0 : Space) 1)ᶜ := hz
    rw [Set.indicator_of_notMem hz, zero_add, indicator_of_mem hin]
    have hw := waveRem_sq (inner ℝ ξ z)
    have h2 : (2 * π * inner ℝ ξ z) ^ 2 ≤ (2 * π) ^ 2 * ((1 + ‖ξ‖) ^ 3 * ‖z‖ ^ 2) := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsq : (inner ℝ ξ z) ^ 2 ≤ ((1 + ‖ξ‖) * ‖z‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
      have hp : (1 + ‖ξ‖) ^ 2 ≤ (1 + ‖ξ‖) ^ 3 := pow_le_pow_right₀ h1ξ (by norm_num)
      calc (inner ℝ ξ z) ^ 2 ≤ ((1 + ‖ξ‖) * ‖z‖) ^ 2 := hsq
        _ = (1 + ‖ξ‖) ^ 2 * ‖z‖ ^ 2 := by ring
        _ ≤ (1 + ‖ξ‖) ^ 3 * ‖z‖ ^ 2 := by gcongr
    have hKz : ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 2 = ‖z‖ ^ (-(1 + 2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg z) (by push_cast; intro h; linarith)]
      congr 1
      push_cast
      ring
    have hpos : 0 ≤ ‖z‖ ^ (-(1 + 2 * α)) * (1 + ‖ξ‖) ^ 3 := by positivity
    calc ‖z‖ ^ (-(3 + 2 * α)) * ‖waveRem (inner ℝ ξ z)‖
        ≤ ‖z‖ ^ (-(3 + 2 * α)) * (3 * ((2 * π) ^ 2 * ((1 + ‖ξ‖) ^ 3 * ‖z‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hw.trans (by linarith)) hK0
      _ = 3 * (2 * π) ^ 2 * ((‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 2) * (1 + ‖ξ‖) ^ 3) := by ring
      _ = 3 * (2 * π) ^ 2 * (‖z‖ ^ (-(1 + 2 * α)) * (1 + ‖ξ‖) ^ 3) := by rw [hKz]
      _ ≤ (3 * (2 * π) ^ 3 + 3 * (2 * π) ^ 2) * (‖z‖ ^ (-(1 + 2 * α)) * (1 + ‖ξ‖) ^ 3) := by
          gcongr
          nlinarith [pow_pos hπ 3]
      _ = _ := by ring

private theorem integrable_kernelTerm (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) {f : Space → CSpace}
    (hf : MemLp f 1 (weightL1Measure 3)) (x : Space) :
    Integrable (Function.uncurry (kernelTerm α f x)) (volume.prod volume) := by
  have hH : Integrable (fun z : Space => (ball (0 : Space) 1).indicator (fun z => ‖z‖ ^ (-(2 * α))) z +
      (ball (0 : Space) 1)ᶜ.indicator (fun z => ‖z‖ ^ (-(1 + 2 * α))) z) :=
    ((integrableOn_ball_norm_rpow (by linarith)).integrable_indicator measurableSet_ball).add
      ((integrableOn_compl_ball_norm_rpow (by linarith)).integrable_indicator
        measurableSet_ball.compl)
  have hw : Integrable (fun ξ : Space => (1 + ‖ξ‖) ^ 3 * ‖f ξ‖) := by
    refine (integrable_weight_smul hf).norm.congr (Eventually.of_forall fun ξ => ?_)
    simp only [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ 3)]
  have hprod := (hH.mul_prod hw).const_mul (3 * (2 * π) ^ 3 + 3 * (2 * π) ^ 2)
  have hmeas : AEStronglyMeasurable (Function.uncurry (kernelTerm α f x)) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Space × Space => ((‖p.1‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ))
        (volume.prod volume) :=
      (Complex.measurable_ofReal.comp ((measurable_norm.comp measurable_fst).pow_const _)).aestronglyMeasurable
    have h2 : Continuous (fun p : Space × Space => 𝐞 (inner ℝ p.2 x)) :=
      Real.continuous_fourierChar.comp (by fun_prop)
    have h3 : Continuous (fun p : Space × Space => waveRem (inner ℝ p.2 p.1)) := by
      unfold waveRem; fun_prop
    have h4 : AEStronglyMeasurable (fun p : Space × Space => f p.2) (volume.prod volume) :=
      (aestronglyMeasurable_of_weight hf).comp_snd
    exact h1.smul (h2.aestronglyMeasurable.smul (h3.aestronglyMeasurable.smul h4))
  refine hprod.mono' hmeas (Eventually.of_forall fun p => ?_)
  obtain ⟨z, ξ⟩ := p
  simp only [Function.uncurry_apply_pair, kernelTerm]
  rw [norm_smul, Circle.norm_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  have hb := kernel_bound α hα z ξ
  calc ‖z‖ ^ (-(3 + 2 * α)) * (‖waveRem (inner ℝ ξ z)‖ * ‖f ξ‖)
      = (‖z‖ ^ (-(3 + 2 * α)) * ‖waveRem (inner ℝ ξ z)‖) * ‖f ξ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by ring

end Breakdown.SmoothFlow.PowerInternal

namespace Breakdown.SmoothFlow

open Breakdown.Freq PowerInternal

theorem powerPhysPower_of (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2)
    (hW : Breakdown.Periodic.PlaneWaveEigen α) : PowerPhysPowerStatement α := by
  have _hW := hW
  intro f hf x
  have hM : fractionalNormalizer α ≠ 0 := ((normalizer α hα (by linarith)).2).ne'
  have hM' : ((fractionalNormalizer α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM
  have hG := integrable_kernelTerm α hα hα2 hf x
  have hL : Integrable (fun z => ∫ ξ, kernelTerm α f x z ξ) := hG.integral_prod_left
  have hpt : ∀ z, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (physField f) x z =
      realVec (∫ ξ, kernelTerm α f x z ξ) := by
    intro z
    rw [remainder_physField hf, physField_eq_char, ← realVec.map_smul, ← integral_smul]
    simp only [kernelTerm, Complex.coe_smul]
  have hinner : ∀ ξ, ∫ z, kernelTerm α f x z ξ =
      (((2 * π * ‖ξ‖) ^ (2 * α) * fractionalNormalizer α : ℝ) : ℂ) •
        (𝐞 (inner ℝ ξ x) • f ξ) := by
    intro ξ
    have h1 : (fun z => kernelTerm α f x z ξ) = fun z =>
        (((‖z‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ) * waveRem (inner ℝ ξ z)) •
          (𝐞 (inner ℝ ξ x) • f ξ) := by
      funext z
      simp only [kernelTerm, char_smul_eq, smul_smul]
      congr 1
      ring
    rw [h1, integral_smul_const, (integral_waveRem α hα hα2 ξ).2]
  unfold fractionalPowerAt
  rw [integral_congr_ae (Eventually.of_forall hpt),
    ContinuousLinearMap.integral_comp_comm realVec hL, integral_integral_swap hG,
    integral_congr_ae (Eventually.of_forall hinner), ← realVec.map_smul, ← integral_smul,
    physField_eq_char]
  refine congrArg realVec (integral_congr_ae (Eventually.of_forall fun ξ => ?_))
  simp only [powerSymbol, char_smul_eq]
  rw [← Complex.coe_smul]
  simp only [smul_smul]
  congr 1
  push_cast
  field_simp

end Breakdown.SmoothFlow

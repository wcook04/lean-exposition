import Breakdown.Cert.CoerciveTestDensityCurlApproxBase

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphMollify

open Internal.TestDensityProof


namespace BoundInternal

theorem sq_lintegral_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ (∫⁻ x, a x ∂μ) * ∫⁻ x, a x * b x ^ 2 ∂μ := by
  have hf : AEMeasurable (fun x => a x ^ (1 / 2 : ℝ)) μ := ha.pow_const _
  have hg : AEMeasurable (fun x => a x ^ (1 / 2 : ℝ) * b x) μ := (ha.pow_const _).mul hb
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∀ x, a x ^ (1 / 2 : ℝ) * (a x ^ (1 / 2 : ℝ) * b x) = a x * b x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (a x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (a x ^ (1 / 2 : ℝ) * b x) ^ (2 : ℝ) = a x * b x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ENNReal.rpow_two]
  simp only [Pi.mul_apply, e1, e2, e3] at h
  have e4 : ∀ u v : ℝ≥0∞, (u ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ)) ^ 2 = u * v := by
    intro u v
    rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ x, a x * b x ∂μ) ^ 2
      ≤ ((∫⁻ x, a x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, a x * b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = _ := e4 _ _

theorem lintegral_conv_sq_le {κ : Space → ℝ} (hk : Continuous κ) {g : Space → Space}
    (hg : AEStronglyMeasurable g volume) :
    ∫⁻ y, ‖∫ x, κ x • g (y - x)‖ₑ ^ 2 ≤ (∫⁻ x, ‖κ x‖ₑ) ^ 2 * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
  have hka : AEMeasurable (fun x => ‖κ x‖ₑ) volume := hk.measurable.enorm.aemeasurable
  have hgy : ∀ y : Space, AEMeasurable (fun x => ‖g (y - x)‖ₑ) volume := fun y =>
    (hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume y)).enorm
  have hj : AEMeasurable (Function.uncurry fun y x : Space => ‖κ x‖ₑ * ‖g (y - x)‖ₑ ^ 2)
      ((volume : Measure Space).prod volume) := by
    have h1 : AEMeasurable (fun p : Space × Space => ‖κ p.2‖ₑ) ((volume : Measure Space).prod volume) :=
      (hk.measurable.enorm.comp measurable_snd).aemeasurable
    have h2 : AEMeasurable (fun p : Space × Space => ‖g (p.1 - p.2)‖ₑ)
        ((volume : Measure Space).prod volume) :=
      (hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).enorm
    exact h1.mul (h2.pow_const 2)
  calc ∫⁻ y, ‖∫ x, κ x • g (y - x)‖ₑ ^ 2
      ≤ ∫⁻ y, (∫⁻ x, ‖κ x‖ₑ * ‖g (y - x)‖ₑ) ^ 2 := by
        refine lintegral_mono fun y => ?_
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        simp only [enorm_smul]
    _ ≤ ∫⁻ y, (∫⁻ x, ‖κ x‖ₑ) * ∫⁻ x, ‖κ x‖ₑ * ‖g (y - x)‖ₑ ^ 2 :=
        lintegral_mono fun y => sq_lintegral_mul_le _ hka (hgy y)
    _ = (∫⁻ x, ‖κ x‖ₑ) * ∫⁻ y, ∫⁻ x, ‖κ x‖ₑ * ‖g (y - x)‖ₑ ^ 2 := by
        have hm : AEMeasurable (fun y => ∫⁻ x, ‖κ x‖ₑ * ‖g (y - x)‖ₑ ^ 2) volume :=
          hj.lintegral_prod_right'
        rw [lintegral_const_mul'' _ hm]
    _ = (∫⁻ x, ‖κ x‖ₑ) * ∫⁻ x, ∫⁻ y, ‖κ x‖ₑ * ‖g (y - x)‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap hj]
    _ = (∫⁻ x, ‖κ x‖ₑ) * ∫⁻ x, ‖κ x‖ₑ * ∫⁻ y, ‖g y‖ₑ ^ 2 := by
        congr 1
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        congr 1
        exact lintegral_sub_right_eq_self (fun y => ‖g y‖ₑ ^ 2) x
    _ = _ := by
        rw [lintegral_mul_const'' _ hka]
        ring

theorem ofReal_sq_norm (v : Space) : ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem kern_continuous (k : ℕ) : Continuous (kern k) := (bump k).continuous_normed

theorem kern_compact (k : ℕ) : HasCompactSupport (kern k) := (bump k).hasCompactSupport_normed

theorem kern_smooth (k : ℕ) : ContDiff ℝ ∞ (kern k) := (bump k).contDiff_normed

theorem lintegral_kern (k : ℕ) : ∫⁻ x, ‖kern k x‖ₑ = 1 := by
  have hn : ∀ x, 0 ≤ kern k x := fun x => (bump k).nonneg_normed x
  have e : ∀ x, ‖kern k x‖ₑ = ENNReal.ofReal (kern k x) := fun x => by
    rw [← ofReal_norm, Real.norm_of_nonneg (hn x)]
  have hi : Integrable (kern k) volume := (bump k).integrable_normed
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)]
  rw [show ∫ x, kern k x = 1 from (bump k).integral_normed, ENNReal.ofReal_one]

theorem moll_apply (k : ℕ) (X : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    moll k X σ y = ∫ x, kern k x • X σ (y - x) := by
  simp [moll, convolution_def]

theorem moll_sub_slice (k : ℕ) {X Y : ℝ → Space → Space} {σ : ℝ}
    (hX : LocallyIntegrable (X σ) volume) (hY : LocallyIntegrable (Y σ) volume) (y : Space) :
    moll k X σ y - moll k Y σ y = ∫ x, kern k x • (X σ (y - x) - Y σ (y - x)) := by
  have h1 := (kern_compact k).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kern_continuous k) hX y
  have h2 := (kern_compact k).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kern_continuous k) hY y
  simp only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] at h1 h2
  rw [moll_apply, moll_apply, ← integral_sub h1 h2]
  simp only [smul_sub]

theorem slice_sq_le (k : ℕ) {X Y : ℝ → Space → Space} {σ : ℝ}
    (hX : MemLp (X σ) 2 volume) (hY : MemLp (Y σ) 2 volume) :
    ∫⁻ y, ENNReal.ofReal (‖moll k X σ y - moll k Y σ y‖ ^ 2) ≤
      ∫⁻ y, ENNReal.ofReal (‖X σ y - Y σ y‖ ^ 2) := by
  have h1 := hX.locallyIntegrable (by norm_num)
  have h2 := hY.locallyIntegrable (by norm_num)
  simp_rw [ofReal_sq_norm, moll_sub_slice k h1 h2]
  have h := lintegral_conv_sq_le (kern_continuous k) (hX.1.sub hY.1)
  rw [lintegral_kern, one_pow, one_mul] at h
  simpa using h

theorem norm_curlVec_sub_le (G₁ G₂ : Space →L[ℝ] Space) :
    ‖curlVec G₁ - curlVec G₂‖ ≤ ∑ j : Fin 3, 9 * ‖G₁ (unitVector j) - G₂ (unitVector j)‖ := by
  have hε : ∀ i j l : Fin 3, |alternatingSymbol i j l| ≤ 1 := by
    intro i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]
  unfold curlVec
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G₁ (unitVector j) l) •
        unitVector i - (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G₂ (unitVector j) l) •
        unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ‖G₁ (unitVector j) - G₂ (unitVector j)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_smul, norm_smul, show ‖unitVector i‖ = 1 by simp [unitVector], mul_one,
          ← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [← mul_sub, Real.norm_eq_abs, abs_mul]
        have hl : |G₁ (unitVector j) l - G₂ (unitVector j) l| ≤ ‖G₁ (unitVector j) - G₂ (unitVector j)‖ := by
          have := PiLp.norm_apply_le (G₁ (unitVector j) - G₂ (unitVector j)) l
          simpa [Real.norm_eq_abs] using this
        calc |alternatingSymbol i j l| * |G₁ (unitVector j) l - G₂ (unitVector j) l|
            ≤ 1 * ‖G₁ (unitVector j) - G₂ (unitVector j)‖ :=
              mul_le_mul (hε i j l) hl (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fin.sum_univ_three]
        ring

theorem sq_sum_three_le (a : Fin 3 → ℝ) : (∑ j : Fin 3, 9 * a j) ^ 2 ≤ 243 * ∑ j : Fin 3, a j ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 0 - a 2)]

def dker (k : ℕ) (j : Fin 3) (x : Space) : ℝ := fderiv ℝ (kern k) x (unitVector j)

theorem dker_continuous (k : ℕ) (j : Fin 3) : Continuous (dker k j) :=
  ((kern_smooth k).continuous_fderiv (by simp)).clm_apply continuous_const

theorem dker_compact (k : ℕ) (j : Fin 3) : HasCompactSupport (dker k j) := by
  refine ((kern_compact k).fderiv (𝕜 := ℝ)).mono fun x hx h0 => hx ?_
  simp [dker, h0]

theorem lintegral_dker_lt_top (k : ℕ) (j : Fin 3) : ∫⁻ x, ‖dker k j x‖ₑ < ⊤ :=
  ((dker_continuous k j).integrable_of_hasCompactSupport (dker_compact k j)).hasFiniteIntegral

theorem fderiv_moll_apply (k : ℕ) {X : ℝ → Space → Space} {σ : ℝ}
    (hX : LocallyIntegrable (X σ) volume) (y : Space) (j : Fin 3) :
    fderiv ℝ (moll k X σ) y (unitVector j) = ∫ t, dker k j t • X σ (y - t) := by
  have h := (kern_compact k).hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kern_smooth k).of_le (by simp)) hX y
  have hi := ((kern_compact k).fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space)
    ((kern_smooth k).continuous_fderiv (by simp)) hX y
  unfold moll
  rw [h.fderiv, convolution_def, ContinuousLinearMap.integral_apply hi]
  simp [dker]

theorem dker_sub_slice (k : ℕ) (j : Fin 3) {X Y : ℝ → Space → Space} {σ : ℝ}
    (hX : LocallyIntegrable (X σ) volume) (hY : LocallyIntegrable (Y σ) volume) (y : Space) :
    fderiv ℝ (moll k X σ) y (unitVector j) - fderiv ℝ (moll k Y σ) y (unitVector j) =
      ∫ t, dker k j t • (X σ (y - t) - Y σ (y - t)) := by
  have h1 := (dker_compact k j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (dker_continuous k j) hX y
  have h2 := (dker_compact k j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (dker_continuous k j) hY y
  simp only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] at h1 h2
  rw [fderiv_moll_apply k hX, fderiv_moll_apply k hY, ← integral_sub h1 h2]
  simp only [smul_sub]

theorem curl_slice_sq_le (k : ℕ) {X Y : ℝ → Space → Space} {σ : ℝ}
    (hX : MemLp (X σ) 2 volume) (hY : MemLp (Y σ) 2 volume) :
    ∫⁻ y, ENNReal.ofReal
        (‖curlVec (fderiv ℝ (moll k X σ) y) - curlVec (fderiv ℝ (moll k Y σ) y)‖ ^ 2) ≤
      (243 * ∑ j : Fin 3, (∫⁻ x, ‖dker k j x‖ₑ) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖X σ y - Y σ y‖ ^ 2) := by
  have h1 := hX.locallyIntegrable (by norm_num)
  have h2 := hY.locallyIntegrable (by norm_num)
  set D : Fin 3 → Space → Space := fun j y => ∫ t, dker k j t • (X σ (y - t) - Y σ (y - t)) with hDdef
  have hDc : ∀ j, Continuous (D j) := by
    intro j
    have e : D j = convolution (dker k j) (fun x => X σ x - Y σ x)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext y
      simp [hDdef, convolution_def]
    rw [e]
    exact (dker_compact k j).continuous_convolution_left _ (dker_continuous k j) (h1.sub h2)
  have hpt : ∀ y, ENNReal.ofReal
      (‖curlVec (fderiv ℝ (moll k X σ) y) - curlVec (fderiv ℝ (moll k Y σ) y)‖ ^ 2) ≤
      243 * ∑ j : Fin 3, ‖D j y‖ₑ ^ 2 := by
    intro y
    have hb := norm_curlVec_sub_le (fderiv ℝ (moll k X σ) y) (fderiv ℝ (moll k Y σ) y)
    simp only [dker_sub_slice k _ h1 h2 y] at hb
    have hs : ‖curlVec (fderiv ℝ (moll k X σ) y) - curlVec (fderiv ℝ (moll k Y σ) y)‖ ^ 2 ≤
        243 * ∑ j : Fin 3, ‖D j y‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans (sq_sum_three_le fun j => ‖D j y‖)
    calc _ ≤ ENNReal.ofReal (243 * ∑ j : Fin 3, ‖D j y‖ ^ 2) := ENNReal.ofReal_le_ofReal hs
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
        simp only [ofReal_sq_norm]
        norm_num
  calc _ ≤ ∫⁻ y, 243 * ∑ j : Fin 3, ‖D j y‖ₑ ^ 2 := lintegral_mono hpt
    _ = 243 * ∑ j : Fin 3, ∫⁻ y, ‖D j y‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_finsetSum' _ fun j _ => ((hDc j).measurable.enorm.pow_const 2).aemeasurable]
    _ ≤ 243 * ∑ j : Fin 3, (∫⁻ x, ‖dker k j x‖ₑ) ^ 2 *
          ∫⁻ y, ‖X σ y - Y σ y‖ₑ ^ 2 := by
        gcongr with j
        exact lintegral_conv_sq_le (dker_continuous k j) (g := fun x => X σ x - Y σ x) (hX.1.sub hY.1)
    _ = _ := by
        simp only [ofReal_sq_norm]
        rw [mul_assoc, Finset.sum_mul]

end BoundInternal

open BoundInternal

theorem moll_sub_le (k : ℕ) {X Y : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure)
    (hY : MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure) :
    periodLIntegral (fun σ y => ‖moll k X σ y - moll k Y σ y‖ ^ 2) ≤
      periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2) := by
  unfold periodLIntegral
  refine lintegral_mono_ae ?_
  filter_upwards [slice_memLp hX, slice_memLp hY] with σ h1 h2
  exact slice_sq_le k h1 h2

theorem curl_moll_sub_le (k : ℕ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ X Y : ℝ → Space → Space,
    MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure →
    MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure →
    periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (moll k X σ) y) - curlVec (fderiv ℝ (moll k Y σ) y)‖ ^ 2) ≤
      C * periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2) := by
  have hne : (243 * ∑ j : Fin 3, (∫⁻ x, ‖dker k j x‖ₑ) ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.pow_ne_top (lintegral_dker_lt_top k j).ne)
  refine ⟨_, hne, fun X Y hX hY => ?_⟩
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ hne]
  refine lintegral_mono_ae ?_
  filter_upwards [slice_memLp hX, slice_memLp hY] with σ h1 h2
  exact curl_slice_sq_le k h1 h2

end Internal.CurlGraphMollify

end Breakdown.Coercive

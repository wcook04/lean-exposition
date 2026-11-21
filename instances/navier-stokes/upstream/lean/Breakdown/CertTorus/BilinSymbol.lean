import Breakdown.CertTorus.RegularStatements
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.H1Consistency
import Breakdown.Uniqueness.RegIdentifyAuxDivFree
import Breakdown.Uniqueness.RegIdentifyAuxSymbol
import Breakdown.Uniqueness.RegIdentifyAuxTime
import Breakdown.Uniqueness.RegPhysAuxProduct

open MeasureTheory Set Real Filter
open scoped ENNReal FourierTransform ComplexConjugate

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.BilinSymbolOfVelocity

open SmoothFlow.Internal.RegIdentifyDivFree SmoothFlow.Internal.RegEmbed

theorem sig_ae (x : X) : ∀ᵐ ξ ∂(volume : Measure Space),
    symX x (-ξ) = conjVec (symX x ξ) ∧ longitudinal ξ (symX x ξ) = 0 := by
  have hx := x.2
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    _root_.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hx
  obtain ⟨h1, h2⟩ := hx
  have hr := fieldOpRealized_holds (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖
    aestronglyMeasurable_const (fun _ => le_rfl) (x : L2C)
  have hl := fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1
    aestronglyMeasurable_longitudinal norm_longitudinal_le_one (x : L2C)
  filter_upwards [hr, hl, Lp.coeFn_zero CSpace 2 volume] with ξ a b c
  change (reflConj (x : L2C) : Space → CSpace) ξ = conjVec ((x : L2C) (-ξ)) at a
  change (fieldOp id longitudinal (x : L2C) : Space → CSpace) ξ = longitudinal ξ ((x : L2C) ξ) at b
  rw [h1] at a
  rw [h2] at b
  refine ⟨?_, ?_⟩
  · unfold symX
    rw [a, conjVec_conjVec]
  · unfold symX
    rw [← b, c]
    rfl

theorem velSymbol_ae (x : X) : ∀ᵐ ξ ∂(volume : Measure Space),
    velSymbol x ξ = ((2 * π * ‖ξ‖)⁻¹ : ℝ) • symX x ξ := by
  filter_upwards [sig_ae x] with ξ h
  have e : (1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ))) = symX x ξ := by
    rw [h.1, conjVec_conjVec, ← two_smul ℝ (symX x ξ), smul_smul]
    norm_num
  rw [velSymbol, e, divFreeC_eq_sub, h.2, sub_zero]

theorem smul_velSymbol_ae (x : X) : ∀ᵐ ξ ∂(volume : Measure Space),
    ((2 * π * ‖ξ‖ : ℝ) : ℂ) • velSymbol x ξ = symX x ξ := by
  filter_upwards [velSymbol_ae x, Freq.Internal.H1Consistency.ae_ne_zero] with ξ h hξ
  have hn : (2 * π * ‖ξ‖ : ℝ) ≠ 0 := by
    have := norm_pos_iff.2 hξ
    positivity
  rw [h, Complex.coe_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem aestronglyMeasurable_velSymbol (x : X) : AEStronglyMeasurable (velSymbol x) volume := by
  have hm : Measurable fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ) := by fun_prop
  refine (hm.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (x : L2C))).congr ?_
  filter_upwards [velSymbol_ae x] with ξ h
  rw [h]
  rfl

theorem memLp_weight_velSymbol (hW : HomWiener) {x : X} (hx : IsSmoothX x) (k : ℕ) :
    MemLp (velSymbol x) 1 (weightL1Measure k) := by
  rw [memLp_weight_iff (aestronglyMeasurable_velSymbol x)]
  obtain ⟨C, hC⟩ := hW k
  refine lt_of_le_of_lt (hC x) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.2 ⟨hx 0, hx (k + 1)⟩).ne

theorem isSolenoidal_velSymbol (x : X) : IsSolenoidalSymbol (velSymbol x) := by
  intro ξ
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · rw [← inner_freqVec_eq]
      unfold velSymbol
      rw [← Complex.coe_smul, inner_smul_right, inner_freqVec_divFreeC hξ, mul_zero]
  · have e : conjVec ((1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ)))) =
        (1 / 2 : ℝ) • (symX x (-ξ) + conjVec (symX x ξ)) := by
      rw [map_smul, map_add, conjVec_conjVec, add_comm]
    unfold velSymbol
    rw [norm_neg, neg_neg, map_smul, ← conjVec_divFreeC_neg ξ, conjVec_conjVec, e]

theorem integrable_freq_smul (hW : HomWiener) {x : X} (hx : IsSmoothX x) (j : Fin 3) :
    Integrable (fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • velSymbol x ξ) volume :=
  SmoothFlow.Internal.ConvProduct.integrable_of_memLp_polyWeight
    (SmoothFlow.Internal.ConvProduct.memLp_freq_smul (k := 0) (memLp_weight_velSymbol hW hx 1) j)

theorem derivSymbol_ae (x : X) (j : Fin 3) :
    (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (x : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • velSymbol x ξ := by
  filter_upwards [Freq.Internal.H1Consistency.derivSymbol_ae fieldOpRealized_holds j (x : L2C),
    smul_velSymbol_ae x, Freq.Internal.H1Consistency.ae_ne_zero] with ξ a b hξ
  rw [a]
  change derivSymbol j ξ • symX x ξ = _
  rw [← b, smul_smul]
  congr 1
  unfold derivSymbol
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hξ
  push_cast
  field_simp

theorem memLp_two_freq_smul (x : X) (j : Fin 3) :
    MemLp (fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • velSymbol x ξ) 2 volume :=
  (Lp.memLp _).ae_eq (derivSymbol_ae x j)

theorem partialX_ae (hW : HomWiener) {x : X} (hx : IsSmoothX x) (j : Fin 3) :
    (partialX j x : Space → Space) =ᵐ[volume] partialField (physField (velSymbol x)) j := by
  set h : Space → CSpace := fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • velSymbol x ξ
    with hh
  have hpart : partialField (physField (velSymbol x)) j = physField h := by
    funext y
    unfold partialField
    rw [fderiv_physField_apply (memLp_weight_velSymbol hW hx 1)]
    simp only [Breakdown.SmoothFlow.Internal.RegEmbed.inner_unitVector, hh]
  set m : L2C := fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (x : L2C) with hm
  have h2 : MemLp h 2 volume := memLp_two_freq_smul x j
  have hmeq : m = toLpOrZero 2 h := by
    apply Lp.ext
    filter_upwards [derivSymbol_ae x j, toLpOrZero_ae_eq h2] with ξ a b
    rw [a, b]
  have hre : (realPart (freqTrInvR m) : Space → Space) =ᵐ[volume]
      fun y => realVec ((freqTrInvR m : L2C) y) := ContinuousLinearMap.coeFn_compLpL _ _
  have e1 : partialX j x = realPart (freqTrInvR m) := rfl
  have e2 : freqTrInvR m = freqTrL2.symm m := rfl
  rw [hpart, e1]
  filter_upwards [hre, freqTrInv_ae (integrable_freq_smul hW hx j) h2] with y a b
  rw [a, e2, hmeq, ← b]
  rfl

theorem rpow_half_sq (z : ℝ≥0∞) : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sq_rpow_half (z : ℝ≥0∞) : (z ^ 2) ^ (1 / 2 : ℝ) = z := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem enorm_convC_sq_le {a b : Space → ℂ} (ha : Measurable fun η => ‖a η‖ₑ)
    (hb : Measurable fun η => ‖b η‖ₑ) (ξ : Space) :
    ‖convC a b ξ‖ₑ ^ 2 ≤ (∫⁻ η, ‖a η‖ₑ) * ∫⁻ η, ‖a η‖ₑ * ‖b (ξ - η)‖ₑ ^ 2 := by
  have h1 : ‖convC a b ξ‖ₑ ≤ ∫⁻ η, ‖a η‖ₑ * ‖b (ξ - η)‖ₑ := by
    unfold convC
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp only [enorm_mul]
  have hs : Measurable fun η => ‖b (ξ - η)‖ₑ := hb.comp (measurable_const.sub measurable_id)
  have h2 := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
    (f := fun η => ‖a η‖ₑ * ‖b (ξ - η)‖ₑ ^ 2) (g := fun η => ‖a η‖ₑ)
    (ha.mul (hs.pow_const 2)).aemeasurable ha.aemeasurable (p := 1 / 2) (q := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ η, (‖a η‖ₑ * ‖b (ξ - η)‖ₑ ^ 2) ^ (1 / 2 : ℝ) * ‖a η‖ₑ ^ (1 / 2 : ℝ) =
      ‖a η‖ₑ * ‖b (ξ - η)‖ₑ := by
    intro η
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show ‖a η‖ₑ * ‖b (ξ - η)‖ₑ ^ 2 * ‖a η‖ₑ = (‖a η‖ₑ * ‖b (ξ - η)‖ₑ) ^ 2 by ring, sq_rpow_half]
  simp only [e] at h2
  calc ‖convC a b ξ‖ₑ ^ 2 ≤ (∫⁻ η, ‖a η‖ₑ * ‖b (ξ - η)‖ₑ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ η, ‖a η‖ₑ * ‖b (ξ - η)‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ η, ‖a η‖ₑ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ η, ‖a η‖ₑ) * ∫⁻ η, ‖a η‖ₑ * ‖b (ξ - η)‖ₑ ^ 2 := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq, mul_comm]

theorem memLp_two_convC {a b : Space → ℂ} (ha : Integrable a volume) (hb : MemLp b 2 volume) :
    MemLp (convC a b) 2 volume := by
  have ha1 := ha.aestronglyMeasurable
  have hb1 := hb.aestronglyMeasurable
  have hc : convC a b = convC (ha1.mk a) (hb1.mk b) :=
    funext fun ξ => SmoothFlow.Internal.ConvProduct.convC_congr_ae' ha1.ae_eq_mk hb1.ae_eq_mk ξ
  have ham := ha1.stronglyMeasurable_mk
  have hbm := hb1.stronglyMeasurable_mk
  have hA : ∫⁻ η, ‖ha1.mk a η‖ₑ < ⊤ := by
    have e : ∫⁻ η, ‖ha1.mk a η‖ₑ = ∫⁻ η, ‖a η‖ₑ :=
      lintegral_congr_ae (ha1.ae_eq_mk.mono fun η h => by simp only [h])
    rw [e]
    exact ha.hasFiniteIntegral
  have hB : ∫⁻ η, ‖hb1.mk b η‖ₑ ^ 2 < ⊤ := by
    have h2 := hb.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at h2
    have e : ∫⁻ η, ‖hb1.mk b η‖ₑ ^ 2 = ∫⁻ η, ‖b η‖ₑ ^ 2 :=
      lintegral_congr_ae (hb1.ae_eq_mk.mono fun η h => by simp only [h])
    rw [e]
    simpa using h2
  rw [hc]
  generalize ha1.mk a = a' at ham hA
  generalize hb1.mk b = b' at hbm hB
  refine ⟨(SmoothFlow.Internal.stronglyMeasurable_convC ham hbm).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have hα : Measurable fun η => ‖a' η‖ₑ := ham.measurable.enorm
  have hβ : Measurable fun η => ‖b' η‖ₑ := hbm.measurable.enorm
  have hP : Measurable (fun p : Space × Space => ‖a' p.2‖ₑ * ‖b' (p.1 - p.2)‖ₑ ^ 2) :=
    (hα.comp measurable_snd).mul ((hβ.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  have hfin : ∫⁻ ξ, ‖convC a' b' ξ‖ₑ ^ 2 < ⊤ := by
    calc ∫⁻ ξ, ‖convC a' b' ξ‖ₑ ^ 2
        ≤ ∫⁻ ξ, (∫⁻ η, ‖a' η‖ₑ) * ∫⁻ η, ‖a' η‖ₑ * ‖b' (ξ - η)‖ₑ ^ 2 :=
          lintegral_mono fun ξ => enorm_convC_sq_le hα hβ ξ
      _ = (∫⁻ η, ‖a' η‖ₑ) * ∫⁻ ξ, ∫⁻ η, ‖a' η‖ₑ * ‖b' (ξ - η)‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ hA.ne
      _ = (∫⁻ η, ‖a' η‖ₑ) * ∫⁻ η, ∫⁻ ξ, ‖a' η‖ₑ * ‖b' (ξ - η)‖ₑ ^ 2 := by
          rw [lintegral_lintegral_swap hP.aemeasurable]
      _ = (∫⁻ η, ‖a' η‖ₑ) * ∫⁻ η, ‖a' η‖ₑ * ∫⁻ ξ, ‖b' ξ‖ₑ ^ 2 := by
          congr 1
          refine lintegral_congr fun η => ?_
          have hm : Measurable fun ξ => ‖b' (ξ - η)‖ₑ ^ 2 :=
            (hβ.comp (measurable_id.sub_const η)).pow_const 2
          rw [lintegral_const_mul _ hm]
          congr 1
          exact lintegral_sub_right_eq_self (fun ξ => ‖b' ξ‖ₑ ^ 2) η
      _ = (∫⁻ η, ‖a' η‖ₑ) * ((∫⁻ η, ‖a' η‖ₑ) * ∫⁻ ξ, ‖b' ξ‖ₑ ^ 2) := by
          rw [lintegral_mul_const _ hα]
      _ < ⊤ := ENNReal.mul_lt_top hA (ENNReal.mul_lt_top hA hB)
  simpa using hfin

theorem memLp_two_advectionSymbol_of {f : Space → CSpace} (hf : Integrable f volume)
    (hg : ∀ j : Fin 3,
      MemLp (fun η => (2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) • f η) 2 volume) :
    MemLp (advectionSymbol f) 2 volume := by
  have hc : ∀ i, MemLp (fun ξ => advectionSymbol f ξ i) 2 volume := by
    intro i
    have heq : (fun ξ => advectionSymbol f ξ i) = ∑ j, convC (fun η => f η j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) := by
      funext ξ
      rw [SmoothFlow.Internal.ConvProduct.advectionSymbol_apply, Finset.sum_apply]
    rw [heq]
    refine memLp_finsetSum' _ fun j _ => memLp_two_convC ?_ ?_
    · exact (EuclideanSpace.proj j : CSpace →L[ℂ] ℂ).integrable_comp hf
    · have := (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).comp_memLp' (hg j)
      convert this using 1
      funext η
      simp [Function.comp, smul_eq_mul]
  have heq : advectionSymbol f = ∑ i, fun ξ =>
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (EuclideanSpace.single i (1 : ℂ)))
        (advectionSymbol f ξ i) := by
    funext ξ
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq]
  exact memLp_finsetSum' _ fun i _ =>
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (EuclideanSpace.single i (1 : ℂ))).comp_memLp' (hc i)

theorem advectionSymbol_herm {f : Space → CSpace} (hs : IsSolenoidalSymbol f) (ξ : Space) :
    advectionSymbol f (-ξ) = conjVec (advectionSymbol f ξ) := by
  ext i
  rw [SmoothFlow.Internal.conjVec_coord]
  simp only [advectionSymbol, advectionBilin, PiLp.toLp_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ =>
    SmoothFlow.Internal.convC_neg_conj (fun η => ?_) (fun η => ?_) ξ
  · rw [(hs η).2, SmoothFlow.Internal.conjVec_coord]
  · rw [(hs η).2, SmoothFlow.Internal.conjVec_coord]
    simp [map_mul, Complex.conj_ofReal, map_ofNat]

theorem bilinX_inner {τ : ℝ} (hτ : 0 < τ) (u v ψ : X) :
    inner ℝ (bilinX τ u v) ψ = bilinForm τ u v ψ := by
  have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, bilin_holds.1 τ hτ⟩
  unfold bilinX
  rw [dif_pos h]
  exact h.2.choose_spec u v ψ

theorem advectionAt_eq_sum (g : Space → Space) (y : Space) :
    advectionAt g y = ∑ j : Fin 3, g y j • partialField g j y := by
  unfold advectionAt partialField
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (g y)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  simp [unitVector]

end Internal.BilinSymbolOfVelocity

open Internal.BilinSymbolOfVelocity SmoothFlow.Internal.RegEmbed SmoothFlow.Internal.RegIdentifyDivFree in
theorem bilinSymbolOfVelocity_holds : BilinSymbolOfVelocity := by
  intro hW hV τ hτ u hu
  have hwt := memLp_weight_velSymbol hW hu
  have hs := isSolenoidal_velSymbol u
  have hA1 : Integrable (advectionSymbol (velSymbol u)) volume :=
    integrable_of_memLp_weight (memLp_advectionSymbol hwt 0)
  have hA2 : MemLp (advectionSymbol (velSymbol u)) 2 volume :=
    memLp_two_advectionSymbol_of (integrable_of_memLp_weight (hwt 0)) (memLp_two_freq_smul u)
  have hmem : MemLp (physField (advectionSymbol (velSymbol u))) 2 volume :=
    memLp_realVec_freqTrInv hA1 hA2
  have key : bilinX τ u u =
      -heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol (velSymbol u)))) := by
    refine ext_inner_right ℝ fun ψ => ?_
    rw [bilinX_inner hτ, inner_neg_left,
      Freq.Internal.BilinTestFormula.heatDivFree_inner fieldOpRealized_holds hτ, bilinForm,
      MeasureTheory.L2.inner_def]
    have ht : trilinear u u (phiX τ ψ) = ∫ y, inner ℝ
        ((toLpOrZero 2 (physField (advectionSymbol (velSymbol u))) : Space → Space) y)
        ((phiX τ ψ : Space → Space) y) := by
      unfold trilinear
      refine integral_congr_ae ?_
      filter_upwards [hV u hu, ae_all_iff.2 (partialX_ae hW hu), toLpOrZero_ae_eq_real hmem]
        with y hy hp ha
      rw [ha, ← advectionAt_physField hwt hs y, advectionAt_eq_sum, sum_inner]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hy, hp j, real_inner_smul_left]
    rw [ht]
    ring
  have hL := coe_heatDivFree_physField fieldOpRealized_holds (memLp_one_iff_integrable.2 hA1) hA2
    (advectionSymbol_herm hs) hτ
  have hn := Lp.coeFn_neg
    ((heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol (velSymbol u)))) : X) : L2C)
  unfold symX
  rw [key]
  filter_upwards [hL, hn] with ξ h1 h2
  have h3 : (((-heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol (velSymbol u)))) : X) :
      L2C) : Space → CSpace) ξ =
      -(((heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol (velSymbol u)))) : X) : L2C) :
        Space → CSpace) ξ := h2
  rw [h3, h1, nonlinSymbol, smul_neg]
  rfl

end Breakdown.FarField

import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.FrozenBridge

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedFrozenBridge

theorem memLp_sliceConvection_of_continuous {W : Space → Space} {c : ℝ} (hWc : Continuous W)
    (hDc : Continuous (fderiv ℝ W))
    (h0 : ∀ y, ‖W y‖ ≤ c / (1 + ‖y‖)) (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ c / (1 + ‖y‖) ^ 2) (h : X) :
    MemLp (sliceConvection W h) 2 volume := by
  have hc : 0 ≤ c := by
    have h00 := h0 0
    simp only [norm_zero, add_zero, div_one] at h00
    exact (norm_nonneg _).trans h00
  have hA : MemLp (fun y => ∑ j : Fin 3, (W y) j • (partialX j h : Space → Space) y) 2 volume := by
    refine memLp_finsetSum Finset.univ fun j _ => ?_
    have hφ : MemLp (fun y => (W y) j) ∞ volume := by
      refine memLp_top_of_bound ((EuclideanSpace.proj j).continuous.comp hWc).aestronglyMeasurable c
        (ae_of_all _ fun y => ?_)
      calc ‖(W y) j‖ ≤ ‖W y‖ := PiLp.norm_apply_le (W y) j
        _ ≤ c / (1 + ‖y‖) := h0 y
        _ ≤ c := div_le_self hc (by linarith [norm_nonneg y])
    exact (Lp.memLp (partialX j h)).smul hφ
  have ha : MemLp (fun y : Space => c * (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume := by
    have hm : AEStronglyMeasurable (fun y : Space => c * (1 + ‖y‖) ^ (-2 : ℝ)) volume :=
      (continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
        fun y => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')).aestronglyMeasurable
    refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
    have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) volume :=
      integrable_one_add_norm (by simp; norm_num)
    refine (hint.const_mul (|c| ^ (3 : ℝ))).congr (ae_of_all _ fun y => ?_)
    have hy : 0 < 1 + ‖y‖ := by positivity
    simp only
    rw [show ((3 : ℝ≥0∞)).toReal = (3 : ℝ) by norm_num, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hy _), Real.mul_rpow (abs_nonneg c) (Real.rpow_nonneg hy.le _),
      ← Real.rpow_mul hy.le]
    norm_num
  have hB : MemLp (fun y => (fderiv ℝ W y) ((velocity h : Space → Space) y)) 2 volume := by
    have := Internal.FrozenBridge.conjExponent_three_six
    have hprod := (Lp.memLp (velocity h)).smul (r := 2) ha
    refine hprod.of_le ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hDc.aestronglyMeasurable (Lp.memLp (velocity h)).1) (ae_of_all _ fun y => ?_)
    have hy : 0 < 1 + ‖y‖ := by positivity
    calc ‖(fderiv ℝ W y) ((velocity h : Space → Space) y)‖
        ≤ ‖fderiv ℝ W y‖ * ‖(velocity h : Space → Space) y‖ := (fderiv ℝ W y).le_opNorm _
      _ ≤ c / (1 + ‖y‖) ^ 2 * ‖(velocity h : Space → Space) y‖ :=
          mul_le_mul_of_nonneg_right (h1 y) (norm_nonneg _)
      _ = ‖((fun y : Space => c * (1 + ‖y‖) ^ (-2 : ℝ)) • (velocity h : Space → Space)) y‖ := by
          show c / (1 + ‖y‖) ^ 2 * ‖(velocity h : Space → Space) y‖ =
            ‖(c * (1 + ‖y‖) ^ (-2 : ℝ)) • (velocity h : Space → Space) y‖
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hy.le _)), Real.rpow_neg hy.le, Real.rpow_two,
            div_eq_mul_inv]
  have e : sliceConvection W h = (fun y => ∑ j : Fin 3, (W y) j • (partialX j h : Space → Space) y) +
      fun y => (fderiv ℝ W y) ((velocity h : Space → Space) y) := rfl
  rw [e]
  exact hA.add hB

theorem stationaryEnergy_nonneg {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    0 ≤ stationaryEnergy d.weightFn G H :=
  add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun y => mul_nonneg (hd.weight_pos.le.trans (hd.weightFn_lower y))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem profile_form {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) (σ : ℝ) (w : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hpf : IsProfileField d.symmetries w G H) :
    -d.formBound * stationaryEnergy d.weightFn G H ≤ frozenForm (d.profile q σ) w G H := by
  have h1 := hd.form_shift q hq σ w G H hpf
  have h2 := hd.frozen_form q hq σ w G H hpf
  have h3 := hd.formBound_ge
  have h4 := stationaryEnergy_nonneg hd G H
  nlinarith

set_option maxHeartbeats 4000000 in
theorem slice_bridge {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) (h3 : ProjectionHolds) (σ : ℝ) (x : XBar) (w : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hwg : IsWeakGradient w G)
    (hws : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (hdiv : ∀ᵐ y, ∑ i : Fin 3, (G y (unitVector i)) i = 0)
    (hsix : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤)
    (hvel : w =ᵐ[volume] (velocity (gradPart x) : Space → Space))
    (htr : (fun y => secondDerivTrace (H y)) =ᵐ[volume]
      fun y => -(toPhysH (secondPart x) : Space → Space) y)
    (hinv : ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
      ∀ᵐ y, (velocity (gradPart x) : Space → Space) (R y) =
        R ((velocity (gradPart x) : Space → Space) y)) :
    -d.formBound * (‖secondPart x‖ ^ 2 + sliceWeightedGrad d.weightFn (gradPart x)) ≤
      ‖secondPart x‖ ^ 2 + (1 / 4 : ℝ) * ‖gradPart x‖ ^ 2
        + inner ℝ (solField (sliceConvection (d.profile q σ) (gradPart x))) (secondPart x) := by
  have hsf := slice_fields (gradPart x) (secondPart x) (halfSsp_of_xbar x)
  choose G' H' hsf using hsf
  have hG' := hsf.1
  have hcol' := hsf.2.2.2.2.1
  have hfi := hsf.2.2.2.2.2.1
  have hfint := hsf.2.2.2.2.2.2.1
  have hli := hsf.2.2.2.2.2.2.2.1
  have hlint := hsf.2.2.2.2.2.2.2.2.1
  have htr' := hsf.2.2.2.2.2.2.2.2.2.1
  have hcol : ∀ j : Fin 3, (fun y => G y (unitVector j)) =ᵐ[volume] (partialX j (gradPart x) : Space → Space) :=
    fun j => (Internal.FrozenBridge.col_ae hwg hG' hvel j).trans (hcol' j)
  have hmatSq : (fun y => matSq (G y)) =ᵐ[volume] fun y => matSq (G' y) := by
    filter_upwards [ae_all_iff.2 hcol, ae_all_iff.2 hcol'] with y hy hy'
    simp only [matSq, hy, hy']
  have htrH : (fun y => ‖secondDerivTrace (H y)‖ ^ 2) =ᵐ[volume]
      fun y => ‖secondDerivTrace (H' y)‖ ^ 2 := by
    filter_upwards [htr, htr'] with y hy hy'
    rw [hy, hy']
    rfl
  have hpf : IsProfileField d.symmetries w G H := by
    refine ⟨hwg, hws, hdiv, hsix, (hfi.congr hmatSq.symm).lintegral_lt_top,
      (hli.congr htrH.symm).lintegral_lt_top, ?_⟩
    intro γ hγ hs
    have hγ' : (γ.1, (0 : ℝ)) ∈ d.symmetries := by rw [← hs]; exact hγ
    filter_upwards [hinv γ.1 hγ', hvel, γ.1.measurePreserving.quasiMeasurePreserving.ae_eq_comp hvel]
      with y h1 h2 h3
    simp only [Function.comp_apply] at h3
    rw [h3, h2, h1]
  have hff := profile_form hd hq σ w G H hpf
  have eA : ∫ y, ‖secondDerivTrace (H y)‖ ^ 2 = ‖(secondPart x)‖ ^ 2 := by rw [integral_congr_ae htrH, hlint]
  have eC : ∫ y, matSq (G y) = ‖(gradPart x)‖ ^ 2 := by rw [integral_congr_ae hmatSq, hfint]
  have eB : ∫ y, d.weightFn y * matSq (G y) = sliceWeightedGrad d.weightFn (gradPart x) := by
    unfold sliceWeightedGrad
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 hcol] with y hy
    simp only [matSq, hy]
  have hWs : ContDiff ℝ 1 (d.profile q σ) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hb0 : ∀ y, ‖(d.profile q σ) y‖ ≤ d.decay / (1 + ‖y‖) := fun y =>
    (hd.profile_decay q hq σ y).1
  have hb1 : ∀ y, ‖fderiv ℝ (d.profile q σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ 2 := fun y =>
    (hd.profile_decay q hq σ y).2.1
  have hF := memLp_sliceConvection_of_continuous hWs.continuous
    (hWs.continuous_fderiv (by norm_num)) hb0 hb1 (gradPart x)
  have eD : ∫ y, inner ℝ (G y ((d.profile q σ) y) + fderiv ℝ (d.profile q σ) y (w y)) (-secondDerivTrace (H y)) =
      inner ℝ (solField (sliceConvection (d.profile q σ) (gradPart x))) (secondPart x) := by
    have e1 : ∫ y, inner ℝ (G y ((d.profile q σ) y) + fderiv ℝ (d.profile q σ) y (w y)) (-secondDerivTrace (H y)) =
        ∫ y, inner ℝ ((hF.toLp _ : L2R) y) ((toPhysH (secondPart x) : L2R) y) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hcol, hvel, htr, hF.coeFn_toLp] with y hc hv ht hl
      rw [hl, ht, neg_neg, hv]
      congr 1
      simp only [sliceConvection]
      congr 1
      conv_lhs => rw [Internal.FrozenBridge.vec_sum ((d.profile q σ) y)]
      simp only [map_sum, map_smul, hc]
    rw [e1, ← L2.inner_def, ← h3.2.2.1, solField, toLpOrZero, dif_pos hF]
  unfold stationaryEnergy frozenForm at hff
  rw [eA, eB, eC, eD] at hff
  exact hff

end Internal.ExtendedFrozenBridge

open Internal.ExtendedFrozenBridge

set_option maxHeartbeats 4000000 in
theorem extendedFrozenBridgeHolds_of (h1 : SliceReadingHolds) (h2 : FreeEquivariantHolds)
    (h3 : ProjectionHolds) : ExtendedFrozenBridgeHolds := by
  intro k d hd q hq f hf
  have hP : 0 < d.period q := hd.period_pos q hq
  have hs := h1 (d.period q) hP f
  choose v G H hs using hs
  have hR := hs.1
  have hwg := hs.2.1
  have hdiv := hs.2.2.1
  choose B hB using hs.2.2.2.1
  have hinvt : ∀ᵐ t : TimeCircle, ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
      ∀ᵐ y, (velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) t)) : Space → Space) (R y) =
        R ((velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) t)) : Space → Space) y) := by
    filter_upwards [Internal.FrozenBridge.ae_invariant d.symmetries (gradCLM (freeInv (d.period q) f))
        (h2 d.symmetries (d.period q) hP f hf),
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure TimeCircle)) gradPart (freeInv (d.period q) f)]
      with t ht he
    rw [← he]
    exact ht
  have hQ : ∀ᵐ σ : ℝ, (∀ j : Fin 3, IsWeakGradient (fun y => G σ y (unitVector j))
        (fun y => (H σ y).flip (unitVector j))) ∧
      v σ =ᵐ[volume] (velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) ∧
      (fun y => secondDerivTrace (H σ y)) =ᵐ[volume]
        (fun y => -(toPhysH (secondPart ((freeInv (d.period q) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y) ∧
      ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
        ∀ᵐ y, (velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) (R y) =
          R ((velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y) := by
    filter_upwards [hR.weak_second, hR.velocity_eq, hR.trace_eq, (ae_coe_iff _).1 hinvt]
      with σ a b c e
    exact ⟨a, b, c, e⟩
  exact (Internal.FrozenBridge.ae_circleRep_coe (Q := fun τ σ => (∀ j : Fin 3, IsWeakGradient (fun y => G σ y (unitVector j))
        (fun y => (H σ y).flip (unitVector j))) ∧
      v σ =ᵐ[volume] (velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) τ)) : Space → Space) ∧
      (fun y => secondDerivTrace (H σ y)) =ᵐ[volume]
        (fun y => -(toPhysH (secondPart ((freeInv (d.period q) f : TimeCircle → XBar) τ)) : Space → Space) y) ∧
      ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
        ∀ᵐ y, (velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) τ)) : Space → Space) (R y) =
          R ((velocity (gradPart ((freeInv (d.period q) f : TimeCircle → XBar) τ)) : Space → Space) y)) hQ).mono fun t ht =>
    slice_bridge hd hq h3 (circleRep t) (sliceOf (freeInv (d.period q) f) t) (v (circleRep t))
      (G (circleRep t)) (H (circleRep t)) (hwg _) ht.1 (hdiv _)
      ((hB _).1.trans_lt ENNReal.ofReal_lt_top) ht.2.1 ht.2.2.1 ht.2.2.2

end Breakdown.Cert

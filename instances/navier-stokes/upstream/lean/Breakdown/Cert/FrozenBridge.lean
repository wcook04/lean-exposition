import Breakdown.Cert.Nodes
import Breakdown.Cert.SliceFields
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.HalfOrderGraphMem
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.FrozenBridge

theorem circleRep_coe (σ : ℝ) :
    circleRep (σ : TimeCircle) = σ + ((-⌊σ⌋ : ℤ) : ℝ) := by
  rw [circleRep, AddCircle.coe_equivIco_mk_apply]
  simp [Int.fract, sub_eq_add_neg]

theorem coe_circleRep (t : TimeCircle) : ((circleRep t : ℝ) : TimeCircle) = t :=
  AddCircle.coe_equivIco

theorem ae_circleRep {Q : ℝ → Prop} (h : ∀ᵐ σ : ℝ, Q σ) : ∀ᵐ t : TimeCircle, Q (circleRep t) := by
  rw [ae_coe_iff]
  have hn : ∀ n : ℤ, ∀ᵐ σ : ℝ, Q (σ + n) := fun n =>
    (measurePreserving_add_right volume (n : ℝ)).quasiMeasurePreserving.ae h
  filter_upwards [ae_all_iff.2 hn] with σ hσ
  rw [circleRep_coe]
  exact hσ _

theorem ae_circleRep_coe {Q : TimeCircle → ℝ → Prop} (h : ∀ᵐ σ : ℝ, Q (σ : TimeCircle) σ) :
    ∀ᵐ t : TimeCircle, Q t (circleRep t) := by
  filter_upwards [ae_circleRep h] with t ht
  rwa [coe_circleRep] at ht

def asCLM (R : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space :=
  ((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space)

theorem asCLM_apply (R : Space ≃ₗᵢ[ℝ] Space) (y : Space) : asCLM R y = R y := rfl

theorem asCLM_injective : Function.Injective asCLM := fun R R' h =>
  LinearIsometryEquiv.ext fun y => by rw [← asCLM_apply, h, asCLM_apply]

def asMap (L : Space →L[ℝ] Space) : C(Space, Space) := ⟨L, L.continuous⟩

theorem continuous_asMap : Continuous asMap :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.clm_apply continuous_snd)

theorem measurePreserving_asMap (R : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (asMap (asCLM R)) volume volume :=
  R.measurePreserving

set_option maxHeartbeats 4000000 in
theorem rot_ae {Γ : Set Symmetry} {g : HH} (hg : g ∈ invariantHH Γ) {R : Space ≃ₗᵢ[ℝ] Space}
    (hR : (R, (0 : ℝ)) ∈ Γ) : ∀ᵐ t : TimeCircle, rotX R ((g : TimeCircle → HBar) t) = g t := by
  unfold invariantHH at hg
  have hk := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hg (R, 0)) hR
  rw [LinearMap.mem_ker] at hk
  have he : shiftLp (0 : ℝ) g = rotHH R g := by
    simpa [sub_eq_zero] using hk
  have e0 : (shiftLp (E := HBar) (0 : ℝ) g : HH) = Lp.compMeasurePreserving
      (fun t : TimeCircle => t + ((0 : ℝ) : TimeCircle))
      (measurePreserving_add_right volume ((0 : ℝ) : TimeCircle)) g := rfl
  have e1 : (shiftLp (E := HBar) (0 : ℝ) g : TimeCircle → HBar) =ᵐ[volume] g := by
    rw [e0]
    filter_upwards [Lp.coeFn_compMeasurePreserving g
      (measurePreserving_add_right volume ((0 : ℝ) : TimeCircle))] with t ht
    simpa using ht
  have e2 : (rotHH R g : TimeCircle → HBar) =ᵐ[volume] fun t => rotX R ((g : TimeCircle → HBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [e1, e2] with t h1 h2
  rw [← h2, ← he, h1]

theorem fix_of_rot {R : Space ≃ₗᵢ[ℝ] Space} {x : X} (h : rotX R x = x) :
    ∀ᵐ y, (velocity x : Space → Space) (R y) = R ((velocity x : Space → Space) y) := by
  have e := velocityCov_holds.1 R x
  rw [h] at e
  filter_upwards [R.measurePreserving.quasiMeasurePreserving.ae_eq_comp e] with y hy
  simp only [Function.comp_apply, pushForward, LinearIsometryEquiv.symm_apply_apply] at hy
  exact hy

theorem fix_closed (w : L6R) (Rn : ℕ → Space ≃ₗᵢ[ℝ] Space) (R : Space ≃ₗᵢ[ℝ] Space)
    (hn : Tendsto (fun n => asCLM (Rn n)) atTop (𝓝 (asCLM R)))
    (hfix : ∀ n, ∀ᵐ y, (w : Space → Space) (Rn n y) = Rn n ((w : Space → Space) y)) :
    ∀ᵐ y, (w : Space → Space) (R y) = R ((w : Space → Space) y) := by
  have hT : ∀ R : Space ≃ₗᵢ[ℝ] Space,
      Lp.compMeasurePreserving (asMap (asCLM R)) (measurePreserving_asMap R) w = (asCLM R).compLp w ↔
        ∀ᵐ y, (w : Space → Space) (R y) = R ((w : Space → Space) y) := by
    intro R
    constructor
    · intro h
      filter_upwards [Lp.coeFn_compMeasurePreserving w (measurePreserving_asMap R),
        (asCLM R).coeFn_compLp w] with y h1 h2
      rw [h] at h1
      rw [h1] at h2
      exact h2
    · intro h
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving w (measurePreserving_asMap R),
        (asCLM R).coeFn_compLp w, h] with y h1 h2 h3
      rw [h1, h2]
      exact h3
  have hlim1 : Tendsto (fun n => Lp.compMeasurePreserving (asMap (asCLM (Rn n)))
      (measurePreserving_asMap (Rn n)) w) atTop
      (𝓝 (Lp.compMeasurePreserving (asMap (asCLM R)) (measurePreserving_asMap R) w)) :=
    Filter.Tendsto.compMeasurePreservingLp (g := fun n => asMap (asCLM (Rn n))) tendsto_const_nhds
      ((continuous_asMap.tendsto _).comp hn) (fun n => measurePreserving_asMap (Rn n))
      (measurePreserving_asMap R) (by norm_num)
  have hsub : ∀ A B : Space →L[ℝ] Space, A.compLp w - B.compLp w = (A - B).compLp w := by
    intro A B
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (A.compLp w) (B.compLp w), A.coeFn_compLp w, B.coeFn_compLp w,
      (A - B).coeFn_compLp w] with y h1 h2 h3 h4
    rw [h1, h4, Pi.sub_apply, h2, h3, sub_apply]
  have hlim2 : Tendsto (fun n => (asCLM (Rn n)).compLp w) atTop (𝓝 ((asCLM R).compLp w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hz : Tendsto (fun n => ‖asCLM (Rn n) - asCLM R‖ * ‖w‖) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hn).mul_const ‖w‖
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hz
    rw [hsub]
    exact ContinuousLinearMap.norm_compLp_le _ _
  exact (hT R).1 (tendsto_nhds_unique (hlim1.congr fun n => (hT (Rn n)).2 (hfix n)) hlim2)

theorem exists_countable_dense (T : Set (Space →L[ℝ] Space)) :
    ∃ D, D ⊆ T ∧ D.Countable ∧ T ⊆ closure D :=
  (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset

set_option maxHeartbeats 4000000 in
theorem ae_invariant (Γ : Set Symmetry) (g : HH) (hg : g ∈ invariantHH Γ) :
    ∀ᵐ t : TimeCircle, ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ Γ →
      ∀ᵐ y, (velocity ((g : TimeCircle → HBar) t) : Space → Space) (R y) =
        R ((velocity ((g : TimeCircle → HBar) t) : Space → Space) y) := by
  choose D hDT hDc hTD using exists_countable_dense (asCLM '' {R | (R, (0 : ℝ)) ∈ Γ})
  have hD₀ : ({R | (R, (0 : ℝ)) ∈ Γ} ∩ asCLM ⁻¹' D).Countable :=
    (hDc.preimage asCLM_injective).mono inter_subset_right
  have hae : ∀ᵐ t : TimeCircle, ∀ R ∈ {R | (R, (0 : ℝ)) ∈ Γ} ∩ asCLM ⁻¹' D, rotX R ((g : TimeCircle → HBar) t) = g t :=
    (ae_ball_iff hD₀).2 fun R hR => rot_ae hg hR.1
  filter_upwards [hae] with t ht R hR
  choose L hL using mem_closure_iff_seq_limit.1 (hTD ⟨R, hR, rfl⟩)
  choose Rn hRnS hRn using fun n => hDT (hL.1 n)
  refine fix_closed _ Rn R ?_ fun n => fix_of_rot (ht (Rn n) ⟨hRnS n, ?_⟩)
  · simpa only [hRn] using hL.2
  · show asCLM (Rn n) ∈ D
    rw [hRn]
    exact hL.1 n

theorem col_ae {f f' : Space → Space} {G G' : Space → (Space →L[ℝ] Space)}
    (hG : IsWeakGradient f G) (hG' : IsWeakGradient f' G') (hf : f =ᵐ[volume] f') (j : Fin 3) :
    (fun y => G y (unitVector j)) =ᵐ[volume] fun y => G' y (unitVector j) := by
  have hc : ∀ {K : Space → (Space →L[ℝ] Space)}, LocallyIntegrable K volume →
      LocallyIntegrable (fun y => K y (unitVector j)) volume := fun hK =>
    locallyIntegrableOn_univ.1
      ((ContinuousLinearMap.apply ℝ Space (unitVector j)).locallyIntegrableOn_comp
        (locallyIntegrableOn_univ.2 hK))
  refine ae_eq_of_integral_contDiff_smul_eq (hc hG.2.1) (hc hG'.2.1) fun φ hφ hs => ?_
  rw [hG.2.2 φ ⟨hφ, hs⟩ j, hG'.2.2 φ ⟨hφ, hs⟩ j]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf] with y hy
  rw [hy]

theorem conjExponent_three_six : ENNReal.HolderTriple 3 6 2 := by
  constructor
  have h3 : (3 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 3) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 6) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h3, h6, h2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem memLp_sliceConvection {W : Space → Space} {c : ℝ} (hW : ContDiff ℝ 2 W)
    (h0 : ∀ y, ‖W y‖ ≤ c / (1 + ‖y‖)) (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ c / (1 + ‖y‖) ^ 2) (h : X) :
    MemLp (sliceConvection W h) 2 volume := by
  have hc : 0 ≤ c := by
    have h00 := h0 0
    simp only [norm_zero, add_zero, div_one] at h00
    exact (norm_nonneg _).trans h00
  have hWc : Continuous W := hW.continuous
  have hDc : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by norm_num)
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
    have := conjExponent_three_six
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

theorem vec_sum (v : Space) : v = ∑ j : Fin 3, v j • unitVector j := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

set_option maxHeartbeats 4000000 in
theorem slice_bridge {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) (h3 : ProjectionHolds) (σ : ℝ) (q : XBar) (w : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hwg : IsWeakGradient w G)
    (hws : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (hdiv : ∀ᵐ y, ∑ i : Fin 3, (G y (unitVector i)) i = 0)
    (hsix : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤)
    (hvel : w =ᵐ[volume] (velocity (gradPart q) : Space → Space))
    (htr : (fun y => secondDerivTrace (H y)) =ᵐ[volume]
      fun y => -(toPhysH (secondPart q) : Space → Space) y)
    (hinv : ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
      ∀ᵐ y, (velocity (gradPart q) : Space → Space) (R y) =
        R ((velocity (gradPart q) : Space → Space) y)) :
    -d.formBound * (‖secondPart q‖ ^ 2 + sliceWeightedGrad d.weightFn (gradPart q)) ≤
      ‖secondPart q‖ ^ 2 + (1 / 4 : ℝ) * ‖gradPart q‖ ^ 2
        + inner ℝ (solField (sliceConvection (d.profile p σ) (gradPart q))) (secondPart q) := by
  have hsf := slice_fields (gradPart q) (secondPart q) (halfSsp_of_xbar q)
  choose G' H' hsf using hsf
  have hG' := hsf.1
  have hcol' := hsf.2.2.2.2.1
  have hfi := hsf.2.2.2.2.2.1
  have hfint := hsf.2.2.2.2.2.2.1
  have hli := hsf.2.2.2.2.2.2.2.1
  have hlint := hsf.2.2.2.2.2.2.2.2.1
  have htr' := hsf.2.2.2.2.2.2.2.2.2.1
  have hcol : ∀ j : Fin 3, (fun y => G y (unitVector j)) =ᵐ[volume] (partialX j (gradPart q) : Space → Space) :=
    fun j => (col_ae hwg hG' hvel j).trans (hcol' j)
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
  have hff := hd.frozen_form p hp σ w G H hpf
  have eA : ∫ y, ‖secondDerivTrace (H y)‖ ^ 2 = ‖(secondPart q)‖ ^ 2 := by rw [integral_congr_ae htrH, hlint]
  have eC : ∫ y, matSq (G y) = ‖(gradPart q)‖ ^ 2 := by rw [integral_congr_ae hmatSq, hfint]
  have eB : ∫ y, d.weightFn y * matSq (G y) = sliceWeightedGrad d.weightFn (gradPart q) := by
    unfold sliceWeightedGrad
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 hcol] with y hy
    simp only [matSq, hy]
  have hWs : ContDiff ℝ 2 (d.profile p σ) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hb0 : ∀ y, ‖(d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) := fun y => by
    simpa [norm_iteratedFDeriv_zero] using hd.profile_decay p hp σ y 0 (by norm_num)
  have hb1 : ∀ y, ‖fderiv ℝ (d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ 2 := fun y => by
    simpa [norm_iteratedFDeriv_one] using hd.profile_decay p hp σ y 1 (by norm_num)
  have hF := memLp_sliceConvection hWs hb0 hb1 (gradPart q)
  have eD : ∫ y, inner ℝ (G y ((d.profile p σ) y) + fderiv ℝ (d.profile p σ) y (w y)) (-secondDerivTrace (H y)) =
      inner ℝ (solField (sliceConvection (d.profile p σ) (gradPart q))) (secondPart q) := by
    have e1 : ∫ y, inner ℝ (G y ((d.profile p σ) y) + fderiv ℝ (d.profile p σ) y (w y)) (-secondDerivTrace (H y)) =
        ∫ y, inner ℝ ((hF.toLp _ : L2R) y) ((toPhysH (secondPart q) : L2R) y) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hcol, hvel, htr, hF.coeFn_toLp] with y hc hv ht hl
      rw [hl, ht, neg_neg, hv]
      congr 1
      simp only [sliceConvection]
      congr 1
      conv_lhs => rw [vec_sum ((d.profile p σ) y)]
      simp only [map_sum, map_smul, hc]
    rw [e1, ← L2.inner_def, ← h3.2.2.1, solField, toLpOrZero, dif_pos hF]
  unfold stationaryEnergy frozenForm at hff
  rw [eA, eB, eC, eD] at hff
  exact hff

end Internal.FrozenBridge

open Internal.FrozenBridge

set_option maxHeartbeats 4000000 in
theorem frozenBridgeHolds_of (h1 : SliceReadingHolds) (h2 : FreeEquivariantHolds)
    (h3 : ProjectionHolds) (h4 : ConvectionHolds) : FrozenBridgeHolds := by
  intro k d hd p hp f hf
  have hP : 0 < d.period p := hd.period_pos p hp
  have hs := h1 (d.period p) hP f
  choose v G H hs using hs
  have hR := hs.1
  have hwg := hs.2.1
  have hdiv := hs.2.2.1
  choose B hB using hs.2.2.2.1
  have hinvt : ∀ᵐ t : TimeCircle, ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
      ∀ᵐ y, (velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) t)) : Space → Space) (R y) =
        R ((velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) t)) : Space → Space) y) := by
    filter_upwards [ae_invariant d.symmetries (gradCLM (freeInv (d.period p) f)) (h2 d.symmetries (d.period p) hP f hf),
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure TimeCircle)) gradPart (freeInv (d.period p) f)]
      with t ht he
    rw [← he]
    exact ht
  have hQ : ∀ᵐ σ : ℝ, (∀ j : Fin 3, IsWeakGradient (fun y => G σ y (unitVector j))
        (fun y => (H σ y).flip (unitVector j))) ∧
      v σ =ᵐ[volume] (velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) ∧
      (fun y => secondDerivTrace (H σ y)) =ᵐ[volume]
        (fun y => -(toPhysH (secondPart ((freeInv (d.period p) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y) ∧
      ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
        ∀ᵐ y, (velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) (R y) =
          R ((velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y) := by
    filter_upwards [hR.weak_second, hR.velocity_eq, hR.trace_eq, (ae_coe_iff _).1 hinvt]
      with σ a b c e
    exact ⟨a, b, c, e⟩
  exact (ae_circleRep_coe (Q := fun τ σ => (∀ j : Fin 3, IsWeakGradient (fun y => G σ y (unitVector j))
        (fun y => (H σ y).flip (unitVector j))) ∧
      v σ =ᵐ[volume] (velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) τ)) : Space → Space) ∧
      (fun y => secondDerivTrace (H σ y)) =ᵐ[volume]
        (fun y => -(toPhysH (secondPart ((freeInv (d.period p) f : TimeCircle → XBar) τ)) : Space → Space) y) ∧
      ∀ R : Space ≃ₗᵢ[ℝ] Space, (R, (0 : ℝ)) ∈ d.symmetries →
        ∀ᵐ y, (velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) τ)) : Space → Space) (R y) =
          R ((velocity (gradPart ((freeInv (d.period p) f : TimeCircle → XBar) τ)) : Space → Space) y)) hQ).mono fun t ht =>
    slice_bridge hd hp h3 (circleRep t) (sliceOf (freeInv (d.period p) f) t) (v (circleRep t))
      (G (circleRep t)) (H (circleRep t)) (hwg _) ht.1 (hdiv _)
      ((hB _).1.trans_lt ENNReal.ofReal_lt_top) ht.2.1 ht.2.2.1 ht.2.2.2

end Breakdown.Cert

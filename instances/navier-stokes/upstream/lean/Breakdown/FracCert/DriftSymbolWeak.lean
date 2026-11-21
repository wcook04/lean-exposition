import Breakdown.FracCert.DriftSymbolWeakParts
import Breakdown.FreqTr.NiceApprox
import Breakdown.FracCert.SecondPairRapid

open scoped ContDiff ENNReal SchwartzMap FourierTransform
open MeasureTheory Real LineDeriv

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace Internal.DriftSymbolWeak

theorem inner_complexifyVec (u : Space) (z : Freq.CSpace) :
    inner ℝ (Freq.complexifyVec u) z = inner ℝ u (Freq.realVec z) := by
  rw [show inner ℝ (Freq.complexifyVec u) z = RCLike.re (inner ℂ (Freq.complexifyVec u) z) from
    real_inner_eq_re_inner ℂ _ _]
  simp [Freq.complexifyVec, Freq.realVec, PiLp.inner_apply]

theorem pairing {F : Space → Space} (hF : MemLp F 2 volume) (Θ : 𝓢(Space, Freq.CSpace)) :
    ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ) ((𝓕 Θ) ξ) =
      ∫ y, inner ℝ (F y) (Freq.realVec (Θ y)) := by
  have h1 : ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ) ((𝓕 Θ) ξ) =
      inner ℝ (fieldSymbol F) ((𝓕 Θ).toLp 2) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(𝓕 Θ).coeFn_toLp 2 volume] with ξ hξ
    rw [hξ]
  have h2 : Freq.freqTrR (Θ.toLp 2) = (𝓕 Θ).toLp 2 := SchwartzMap.toLp_fourier_eq Θ
  rw [h1, ← h2]
  unfold fieldSymbol
  rw [Freq.Internal.VelocityInjective.freqTrR_inner, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) Freq.complexifyVec
      (Freq.toLpOrZero 2 F), Internal.DriftPower.toLpOrZero_ae' hF, Θ.coeFn_toLp 2 volume] with y h1 h2 h3
  unfold Freq.complexify
  rw [h1, h2, h3, inner_complexifyVec]

theorem memLp_negSecondTrace {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField m v G H) :
    MemLp (negSecondTrace H) 2 volume := by
  have hm : ∀ i j : Fin 3, AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    fun i j => ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous).comp_aestronglyMeasurable
        hv.measurable_second
  have hterm : ∀ j : Fin 3, MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := by
    intro j
    refine (memLp_two_iff_integrable_sq_norm (hm j j)).2 (hv.second_two.mono' ((hm j j).norm.pow 2)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Finset.single_le_sum (f := fun k => ‖H y (unitVector j) (unitVector k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ k : Fin 3, ‖H y (unitVector i) (unitVector k)‖ ^ 2)
        (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ j))
  exact (memLp_finsetSum Finset.univ (fun j _ => hterm j)).neg

theorem flowAdjoint_eq_zero {α a : ℝ} {ψ : Space → Freq.CSpace} {ξ : Space} (h : ξ ∉ tsupport ψ) :
    flowAdjoint α a ψ ξ = 0 := by
  have h0 : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport h
  have h1 : fderiv ℝ ψ ξ = 0 := by
    by_contra hne
    exact h (support_fderiv_subset ℝ hne)
  have hs : ∀ i : Fin 3, EuclideanSpace.single i (0 : ℂ) = 0 := fun i => by
    ext j
    simp
  simp [flowAdjoint, h0, h1, freqTurn, hs]

theorem support_flowAdjoint_subset (α a : ℝ) (ψ : Space → Freq.CSpace) :
    Function.support (flowAdjoint α a ψ) ⊆ tsupport ψ := fun ξ hξ => by
  by_contra h
  exact hξ (flowAdjoint_eq_zero h)

theorem tsupport_flowAdjoint_subset (α a : ℝ) (ψ : Space → Freq.CSpace) :
    tsupport (flowAdjoint α a ψ) ⊆ tsupport ψ :=
  closure_minimal (support_flowAdjoint_subset α a ψ) (isClosed_tsupport ψ)

theorem contDiff_axialTurn : ContDiff ℝ ∞ axialTurn := by
  rw [contDiff_piLp 2]
  intro i
  have hid := (contDiff_piLp 2).1 (contDiff_id (𝕜 := ℝ) (n := ∞) (E := Space))
  have h0 : ContDiff ℝ ∞ (fun y : Space => y 0) := hid 0
  have h1 : ContDiff ℝ ∞ (fun y : Space => y 1) := hid 1
  fin_cases i <;> simp [axialTurn] <;> first | exact h1.neg | exact h0 | exact contDiff_const

theorem contDiff_freqTurn : ContDiff ℝ ∞ freqTurn := by
  rw [contDiff_piLp 2]
  intro i
  have hid := (contDiff_piLp 2).1 (contDiff_id (𝕜 := ℝ) (n := ∞) (E := Freq.CSpace))
  have h0 : ContDiff ℝ ∞ (fun z : Freq.CSpace => z 0) := hid 0
  have h1 : ContDiff ℝ ∞ (fun z : Freq.CSpace => z 1) := hid 1
  fin_cases i <;> simp [freqTurn] <;> first | exact h1.neg | exact h0 | exact contDiff_const

theorem contDiff_flowAdjoint {α a : ℝ} {ψ : Space → Freq.CSpace} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (flowAdjoint α a ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2
  have e1 : ContDiff ℝ ∞ (fun ξ => (1 - 1 / (2 * α)) • ψ ξ) := hψ.const_smul _
  have e2 : ContDiff ℝ ∞ (fun ξ : Space => fderiv ℝ ψ ξ ξ) := hd.clm_apply contDiff_id
  have e3 : ContDiff ℝ ∞ (fun ξ : Space => fderiv ℝ ψ ξ (axialTurn ξ)) := hd.clm_apply contDiff_axialTurn
  have e4 : ContDiff ℝ ∞ (fun ξ => freqTurn (ψ ξ)) := contDiff_freqTurn.comp hψ
  have e : ContDiff ℝ ∞ (fun ξ => (1 - 1 / (2 * α)) • ψ ξ + (1 / (2 * α)) • fderiv ℝ ψ ξ ξ
      - a • fderiv ℝ ψ ξ (axialTurn ξ) + a • freqTurn (ψ ξ)) :=
    ((e1.add (e2.const_smul _)).sub (e3.const_smul _)).add (e4.const_smul _)
  exact e

theorem exists_rapid {f : Space → Freq.CSpace} (hc : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) :
    ∃ S : 𝓢(Space, Freq.CSpace), ∀ ξ, S ξ = f ξ :=
  ⟨hc.toSchwartzMap hs, fun _ => rfl⟩

theorem freqPow_two_eq (ξ : Space) : freqPow 2 ξ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
  unfold freqPow
  rw [Real.rpow_two, mul_pow]

theorem contDiff_scaled {f : Space → Freq.CSpace} (hf : ContDiff ℝ ∞ f) (h0 : (0 : Space) ∉ tsupport f) :
    ContDiff ℝ ∞ (fun ξ => (freqPow 2 ξ)⁻¹ • f ξ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ ∈ tsupport f
  · have hne : ξ ≠ 0 := fun h => h0 (h ▸ hξ)
    have he : (fun ξ => (freqPow 2 ξ)⁻¹ • f ξ) = fun ξ => ((2 * π) ^ 2 * ‖ξ‖ ^ 2)⁻¹ • f ξ := by
      funext x
      rw [freqPow_two_eq]
    rw [he]
    have hi : ContDiffAt ℝ ∞ (fun x : Space => ((2 * π) ^ 2 * ‖x‖ ^ 2)⁻¹) ξ := by
      apply ContDiffAt.inv
      · exact contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt
      · have : 0 < ‖ξ‖ := norm_pos_iff.2 hne
        positivity
    exact hi.smul hf.contDiffAt
  · have hev : (fun ξ => (freqPow 2 ξ)⁻¹ • f ξ) =ᶠ[nhds ξ] fun _ => 0 := by
      have : (tsupport f)ᶜ ∈ nhds ξ := (isClosed_tsupport f).isOpen_compl.mem_nhds hξ
      filter_upwards [this] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hev

open LineDeriv in
theorem lineDeriv_postcomp (f : 𝓢(Space, Freq.CSpace)) (w : Space) :
    ∂_{w} (SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec f) =
      SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec (∂_{w} f) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.postcompCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : (⇑(SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec f)) = Freq.realVec ∘ f := by
    ext1 y
    rfl
  rw [he, ((Freq.realVec.hasFDerivAt).comp x (f.differentiableAt.hasFDerivAt)).fderiv]
  rfl

theorem sum_sq_inner (ξ : Space) :
    ∑ j : Fin 3, inner ℝ ξ (unitVector j) * inner ℝ ξ (unitVector j) = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [unitVector, EuclideanSpace.inner_single_right, sq]

open LineDeriv in
theorem sum_second_invTransform (Ψ Φ : 𝓢(Space, Freq.CSpace)) (h : ∀ ξ, Φ ξ = freqPow 2 ξ • Ψ ξ) :
    ∑ j : Fin 3, ∂_{unitVector j} (∂_{unitVector j} (𝓕⁻ Ψ)) = -(𝓕⁻ Φ) := by
  have hg : ∀ j : Fin 3, (fun ξ : Space => inner ℝ ξ (unitVector j)).HasTemperateGrowth :=
    fun j => ((innerSL ℝ).flip (unitVector j)).hasTemperateGrowth
  simp_rw [SchwartzMap.lineDerivOp_fourierInv_eq]
  have hsum : ∑ j : Fin 3, (2 * (π : ℂ) * Complex.I) • SchwartzMap.smulLeftCLM Freq.CSpace
      (fun x : Space => inner ℝ x (unitVector j)) ((2 * (π : ℂ) * Complex.I) •
        SchwartzMap.smulLeftCLM Freq.CSpace (fun x : Space => inner ℝ x (unitVector j)) Ψ) = -Φ := by
    refine SchwartzMap.ext fun ξ => ?_
    simp only [Fin.sum_univ_three, SchwartzMap.add_apply, SchwartzMap.smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply (hg _), SchwartzMap.neg_apply, h, freqPow_two_eq]
    have hs := sum_sq_inner ξ
    rw [Fin.sum_univ_three] at hs
    simp only [← Complex.coe_smul, smul_smul, ← add_smul, ← neg_smul]
    set r0 := inner ℝ ξ (unitVector 0)
    set r1 := inner ℝ ξ (unitVector 1)
    set r2 := inner ℝ ξ (unitVector 2)
    have hsC : (r0 : ℂ) * r0 + r1 * r1 + r2 * r2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hs
    congr 1
    push_cast
    push_cast at hsC
    linear_combination ((2 * (π : ℂ)) ^ 2 * ((r0 : ℂ) * r0 + r1 * r1 + r2 * r2)) * Complex.I_sq
      - (2 * (π : ℂ)) ^ 2 * hsC
  rw [← FourierTransform.fourierInv_sum, hsum, FourierTransform.fourierInv_neg]

end Internal.DriftSymbolWeak

open Internal.DriftSymbolWeak LineDeriv in
theorem velocitySecondPhysical_of (h : SecondTracePairingStatement) : VelocitySecondPhysicalStatement := by
  intro m v G H hv Ψ Φ hΦ
  have key := h m v G H hv (SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec (𝓕⁻ Ψ))
  have hS := sum_second_invTransform Ψ Φ hΦ
  have hpt : ∀ y, Freq.realVec ((𝓕⁻ Φ) y) =
      Freq.negSsp (SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec (𝓕⁻ Ψ)) y := by
    intro y
    rw [← Freq.Internal.NiceApprox.negSspS_apply]
    have e1 : (𝓕⁻ Φ) y = -∑ j : Fin 3, (∂_{unitVector j} (∂_{unitVector j} (𝓕⁻ Ψ))) y := by
      rw [← neg_neg (𝓕⁻ Φ), ← hS]
      simp only [Fin.sum_univ_three, SchwartzMap.add_apply, SchwartzMap.neg_apply]
    rw [e1, map_neg, map_sum]
    simp only [Freq.Internal.NiceApprox.negSspS, lineDeriv_postcomp, SchwartzMap.postcompCLM_apply,
      Fin.sum_univ_three, SchwartzMap.add_apply, SchwartzMap.neg_apply]
  have hfun : (fun y => inner ℝ (v y) (Freq.realVec ((𝓕⁻ Φ) y))) = fun y => inner ℝ (v y)
      (Freq.negSsp (SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec (𝓕⁻ Ψ)) y) :=
    funext fun y => by rw [hpt]
  rw [hfun, key]
  rfl

open Internal.DriftSymbolWeak in
theorem driftSymbolWeak_of (hA : DriftAdjointPhysicalStatement) (hB : VelocitySecondPhysicalStatement) :
    DriftSymbolWeakStatement := by
  intro α hα1 hα2 a m v G H hv hD ψ hψ
  obtain ⟨hψs, hψc, hψ0⟩ := hψ
  have hΦs : ContDiff ℝ ∞ (flowAdjoint α a ψ) := contDiff_flowAdjoint hψs
  have hΦc : HasCompactSupport (flowAdjoint α a ψ) := hψc.mono' (support_flowAdjoint_subset α a ψ)
  have hΦ0 : (0 : Space) ∉ tsupport (flowAdjoint α a ψ) := fun h => hψ0 (tsupport_flowAdjoint_subset α a ψ h)
  have hΨc : HasCompactSupport (fun ξ => (freqPow 2 ξ)⁻¹ • flowAdjoint α a ψ ξ) := by
    refine hΦc.mono' fun ξ hξ => subset_tsupport _ fun h => hξ ?_
    simp only [h, smul_zero]
  obtain ⟨ψS, hψS⟩ := exists_rapid hψc hψs
  obtain ⟨ΦS, hΦS⟩ := exists_rapid hΦc hΦs
  obtain ⟨ΨS, hΨS⟩ := exists_rapid hΨc (contDiff_scaled hΦs hΦ0)
  have hrel : ∀ ξ, ΦS ξ = freqPow 2 ξ • ΨS ξ := by
    intro ξ
    rw [hΦS, hΨS, smul_smul]
    by_cases h : freqPow 2 ξ = 0
    · have hξ : ξ = 0 := by
        rw [freqPow_two_eq] at h
        simpa [Real.pi_ne_zero] using h
      rw [hξ, flowAdjoint_eq_zero hψ0, smul_zero]
    · rw [mul_inv_cancel₀ h, one_smul]
  have hN : MemLp (negSecondTrace H) 2 volume := memLp_negSecondTrace hv
  have eL : ∫ ξ, inner ℝ ((fieldSymbol (driftField α a v G) : Space → Freq.CSpace) ξ) (ψ ξ) =
      ∫ y, inner ℝ (driftField α a v G y) (Freq.realVec ((𝓕⁻ ψS) y)) := by
    rw [← pairing hD (𝓕⁻ ψS), FourierInvPair.fourier_fourierInv_eq]
    simp_rw [hψS]
  have eR : ∫ ξ, inner ℝ ((freqPow 2 ξ)⁻¹ • (secondSymbol H : Space → Freq.CSpace) ξ)
        (flowAdjoint α a ψ ξ) =
      ∫ y, inner ℝ (negSecondTrace H y) (Freq.realVec ((𝓕⁻ ΨS) y)) := by
    rw [← pairing hN (𝓕⁻ ΨS), FourierInvPair.fourier_fourierInv_eq]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun ξ => ?_
    dsimp only
    rw [hΨS, real_inner_smul_left, real_inner_smul_right]
    simp only [secondSymbol, fieldSymbol]
  have hψfun : (ψS : Space → Freq.CSpace) = ψ := funext hψS
  rw [eL, eR, hA α hα1 hα2 a m v G H hv hD ψS ΦS (by rw [hψfun]; exact hΦS), hB m v G H hv ΨS ΦS hrel]

theorem driftAdjointPhysical_of (h1 : DriftTransportPairingStatement) (h2 : FlowAdjointInverseStatement) :
    DriftAdjointPhysicalStatement := by
  intro α hα1 hα2 a m v G H hv hD ψ Φ hΦ
  have key := h1 α hα1 hα2 a m v G H hv hD (SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec (𝓕⁻ ψ))
  have hc : (⇑(SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.realVec (𝓕⁻ ψ))) = fun x => Freq.realVec ((𝓕⁻ ψ) x) := by
    funext x
    rfl
  rw [hc] at key
  refine key.trans ?_
  congr 1
  funext y
  rw [h2 α a ψ Φ hΦ y]

theorem driftSymbolWeak_of_parts (h1 : DriftTransportPairingStatement) (h2 : FlowAdjointInverseStatement)
    (h3 : SecondTracePairingStatement) : DriftSymbolWeakStatement :=
  driftSymbolWeak_of (driftAdjointPhysical_of h1 h2) (velocitySecondPhysical_of h3)

namespace Internal.DriftSymbolWeakFreq

theorem hasFDerivAt_inner_smul (χ : 𝓢(Space, Freq.CSpace)) (m y : Space) :
    HasFDerivAt (fun x : Space => inner ℝ x m • χ x)
      (inner ℝ y m • fderiv ℝ χ y + ((innerSL ℝ).flip m).smulRight (χ y)) y := by
  have h1 : HasFDerivAt (fun x : Space => inner ℝ x m) ((innerSL ℝ).flip m) y :=
    ((innerSL ℝ).flip m).hasFDerivAt
  exact h1.smul (χ.differentiableAt.hasFDerivAt)

theorem lineDeriv_inner_smul (χ : 𝓢(Space, Freq.CSpace)) (w m y : Space) :
    (∂_{w} (SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ m) χ)) y =
      inner ℝ w m • χ y + inner ℝ y m • fderiv ℝ χ y w := by
  have hm : (fun ξ : Space => inner ℝ ξ m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.smulLeftCLM_apply hm]
  rw [(hasFDerivAt_inner_smul χ m y).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply]
  rw [add_comm, real_inner_comm]

theorem invTransform_inner_lineDeriv (ψ : 𝓢(Space, Freq.CSpace)) (w m y : Space) :
    (𝓕⁻ (SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ w) (∂_{m} ψ))) y =
      -(inner ℝ w m • (𝓕⁻ ψ) y + inner ℝ y m • fderiv ℝ ((𝓕⁻ ψ : 𝓢(Space, Freq.CSpace)) : Space → Freq.CSpace) y w) := by
  have c0 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h1 := SchwartzMap.lineDerivOp_fourierInv_eq (∂_{m} ψ) w
  rw [FourierInvSMul.fourierInv_smul, SchwartzMap.fourierInv_lineDerivOp_eq, lineDerivOp_smul] at h1
  have h2 := congrArg (fun F : 𝓢(Space, Freq.CSpace) => F y) h1
  simp only [SchwartzMap.smul_apply, lineDeriv_inner_smul] at h2
  have h3 := congrArg (fun z : Freq.CSpace => (2 * (π : ℂ) * Complex.I)⁻¹ • z) h2
  simp only [smul_smul, inv_mul_cancel₀ c0, one_smul] at h3
  rw [← h3]
  simp only [smul_smul, mul_neg, inv_mul_cancel₀ c0, neg_smul, one_smul]

def turnL : Freq.CSpace →L[ℂ] Freq.CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := freqTurn
      map_add' := fun z w => by
        ext i
        fin_cases i <;> simp [freqTurn] <;> ring
      map_smul' := fun c z => by
        ext i
        fin_cases i <;> simp [freqTurn] }

theorem turnL_apply (z : Freq.CSpace) : turnL z = freqTurn z := rfl

theorem invTransform_turn (f : 𝓢(Space, Freq.CSpace)) (y : Space) :
    (𝓕⁻ (SchwartzMap.postcompCLM turnL f)) y = freqTurn ((𝓕⁻ f) y) := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    Real.fourierInv_eq]
  have hi : Integrable (fun v : Space => 𝐞 (inner ℝ v y) • f v) := by
    refine f.integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        f.continuous).aestronglyMeasurable
    · rw [Circle.norm_smul]
  rw [← turnL_apply, ← turnL.integral_comp_comm hi]
  congr 1
  funext v
  rw [SchwartzMap.postcompCLM_apply, Circle.smul_def, Circle.smul_def, map_smul]

theorem decomp (ξ : Space) : ξ = ξ 0 • unitVector 0 + ξ 1 • unitVector 1 + ξ 2 • unitVector 2 := by
  ext i
  fin_cases i <;> simp [unitVector]

theorem decomp_turn (ξ : Space) : axialTurn ξ = (-(ξ 1)) • unitVector 0 + ξ 0 • unitVector 1 := by
  ext i
  fin_cases i <;> simp [unitVector, axialTurn]

theorem inner_unit (ξ : Space) (j : Fin 3) : inner ℝ ξ (unitVector j) = ξ j := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem realVec_turn (z : Freq.CSpace) : Freq.realVec (freqTurn z) = axialTurn (Freq.realVec z) := by
  ext i
  fin_cases i <;> simp [freqTurn, axialTurn, Freq.realVec]

theorem fderiv_realVec (χ : 𝓢(Space, Freq.CSpace)) (y w : Space) :
    fderiv ℝ (fun x => Freq.realVec (χ x)) y w = Freq.realVec (fderiv ℝ χ y w) := by
  show fderiv ℝ (Freq.realVec ∘ χ) y w = _
  rw [((Freq.realVec.hasFDerivAt).comp y (χ.differentiableAt.hasFDerivAt)).fderiv]
  rfl

theorem fderiv_self (f : Space → Freq.CSpace) (ξ : Space) :
    fderiv ℝ f ξ ξ = ξ 0 • fderiv ℝ f ξ (unitVector 0) + ξ 1 • fderiv ℝ f ξ (unitVector 1)
      + ξ 2 • fderiv ℝ f ξ (unitVector 2) := by
  rw [congrArg (fderiv ℝ f ξ) (decomp ξ)]
  simp only [map_add, map_smul]

theorem fderiv_turn (f : Space → Freq.CSpace) (ξ : Space) :
    fderiv ℝ f ξ (axialTurn ξ) = (-(ξ 1)) • fderiv ℝ f ξ (unitVector 0) + ξ 0 • fderiv ℝ f ξ (unitVector 1) := by
  rw [decomp_turn ξ]
  simp only [map_add, map_smul]

end Internal.DriftSymbolWeakFreq

open Internal.DriftSymbolWeakFreq in
theorem flowAdjointInverse : FlowAdjointInverseStatement := by
  intro α a ψ Φ hΦ y
  have ht : ∀ w : Space, (fun ξ : Space => inner ℝ ξ w).HasTemperateGrowth :=
    fun w => ((innerSL ℝ).flip w).hasTemperateGrowth
  have hdec : Φ = (1 - 1 / (2 * α)) • ψ + (1 / (2 * α)) •
      (SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ (unitVector 0)) (∂_{unitVector 0} ψ)
        + SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ (unitVector 1)) (∂_{unitVector 1} ψ)
        + SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ (unitVector 2)) (∂_{unitVector 2} ψ))
      + (-a) • (SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ (-unitVector 1)) (∂_{unitVector 0} ψ)
        + SchwartzMap.smulLeftCLM Freq.CSpace (fun ξ : Space => inner ℝ ξ (unitVector 0)) (∂_{unitVector 1} ψ))
      + a • SchwartzMap.postcompCLM turnL ψ := by
    refine SchwartzMap.ext fun ξ => ?_
    rw [hΦ]
    simp only [flowAdjoint, SchwartzMap.add_apply, SchwartzMap.smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply (ht (unitVector 0)), SchwartzMap.smulLeftCLM_apply_apply (ht (unitVector 1)),
      SchwartzMap.smulLeftCLM_apply_apply (ht (unitVector 2)), SchwartzMap.smulLeftCLM_apply_apply (ht (-unitVector 1)),
      SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.postcompCLM_apply, turnL_apply]
    simp only [inner_unit, inner_neg_right]
    rw [fderiv_self, fderiv_turn]
    module
  rw [hdec]
  simp only [FourierInvAdd.fourierInv_add, FourierInvSMul.fourierInv_smul, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, invTransform_inner_lineDeriv, invTransform_turn]
  simp only [transportAdjoint, fderiv_realVec]
  rw [fderiv_self ((𝓕⁻ ψ : 𝓢(Space, Freq.CSpace)) : Space → Freq.CSpace) y,
    fderiv_turn ((𝓕⁻ ψ : 𝓢(Space, Freq.CSpace)) : Space → Freq.CSpace) y]
  simp only [map_add, map_neg, map_smul, realVec_turn, inner_unit, inner_neg_left]
  simp [unitVector]
  module

theorem driftSymbolWeak_of_two (h1 : DriftTransportPairingStatement) (h3 : SecondTracePairingStatement) :
    DriftSymbolWeakStatement :=
  driftSymbolWeak_of_parts h1 flowAdjointInverse h3

namespace Internal.DriftSymbolWeakTransport

def axialL : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurn
      map_add' := fun z w => by
        ext i
        fin_cases i <;> simp [axialTurn] <;> ring
      map_smul' := fun c z => by
        ext i
        fin_cases i <;> simp [axialTurn] }

theorem axialL_apply (z : Space) : axialL z = axialTurn z := rfl

theorem inner_axialTurn (u w : Space) : inner ℝ (axialTurn u) w = -inner ℝ u (axialTurn w) := by
  simp [axialTurn, PiLp.inner_apply, Fin.sum_univ_three]

end Internal.DriftSymbolWeakTransport

open Internal.DriftSymbolWeakTransport in
theorem driftTransportPairing_of (h : LinearTransportPairStatement) : DriftTransportPairingStatement := by
  intro α hα1 hα2 a m v G H hv hD χ
  set g : ℝ := 1 / (2 * α) with hg
  obtain ⟨i1, i2, j2, e2⟩ := h m v G H hv χ (ContinuousLinearMap.id ℝ Space)
  obtain ⟨-, i3, j3, e3⟩ := h m v G H hv χ axialL
  obtain ⟨i4, -, -, -⟩ := h m v G H hv (SchwartzMap.postcompCLM (𝕜 := ℝ) axialL χ) axialL
  simp only [ContinuousLinearMap.id_apply, axialL_apply, SchwartzMap.postcompCLM_apply] at i2 j2 e2 i3 j3 e3 i4
  have d1 : (∑ j : Fin 3, inner ℝ (unitVector j) (unitVector j)) = (3 : ℝ) := by
    simp [unitVector]
  have d2 : (∑ j : Fin 3, inner ℝ (axialTurn (unitVector j)) (unitVector j)) = (0 : ℝ) := by
    simp [unitVector, axialTurn, Fin.sum_univ_three, PiLp.inner_apply]
  rw [d1] at j2 e2
  rw [d2] at j3 e3
  simp only [zero_smul, add_zero] at j3 e3
  have hL : (fun y => inner ℝ (driftField α a v G y) (χ y)) = fun y =>
      ((1 - g) * inner ℝ (v y) (χ y) + g * inner ℝ (G y y) (χ y))
        + (a * inner ℝ (G y (axialTurn y)) (χ y) + a * inner ℝ (v y) (axialTurn (χ y))) := by
    funext y
    simp only [driftField, inner_add_left, inner_sub_left, inner_smul_left, inner_axialTurn]
    simp
    ring
  have hR : (fun y => inner ℝ (v y) (transportAdjoint α a χ y)) = fun y =>
      ((1 - g) * inner ℝ (v y) (χ y) + (-g) * inner ℝ (v y) (fderiv ℝ χ y y + (3 : ℝ) • χ y))
        + ((-a) * inner ℝ (v y) (fderiv ℝ χ y (axialTurn y)) + a * inner ℝ (v y) (axialTurn (χ y))) := by
    funext y
    simp only [transportAdjoint, inner_add_right, inner_sub_right, inner_smul_right]
    ring
  have A1 : Integrable (fun y => (1 - g) * inner ℝ (v y) (χ y)) := i1.const_mul _
  have A2 : Integrable (fun y => g * inner ℝ (G y y) (χ y)) := i2.const_mul _
  have A3 : Integrable (fun y => a * inner ℝ (G y (axialTurn y)) (χ y)) := i3.const_mul _
  have A4 : Integrable (fun y => a * inner ℝ (v y) (axialTurn (χ y))) := i4.const_mul _
  have B2 : Integrable (fun y => (-g) * inner ℝ (v y) (fderiv ℝ χ y y + (3 : ℝ) • χ y)) := j2.const_mul _
  have B3 : Integrable (fun y => (-a) * inner ℝ (v y) (fderiv ℝ χ y (axialTurn y))) := j3.const_mul _
  have S1 : Integrable (fun y => (1 - g) * inner ℝ (v y) (χ y) + g * inner ℝ (G y y) (χ y)) := A1.add A2
  have S2 : Integrable (fun y => a * inner ℝ (G y (axialTurn y)) (χ y) + a * inner ℝ (v y) (axialTurn (χ y))) :=
    A3.add A4
  have S3 : Integrable (fun y => (1 - g) * inner ℝ (v y) (χ y)
      + (-g) * inner ℝ (v y) (fderiv ℝ χ y y + (3 : ℝ) • χ y)) := A1.add B2
  have S4 : Integrable (fun y => (-a) * inner ℝ (v y) (fderiv ℝ χ y (axialTurn y))
      + a * inner ℝ (v y) (axialTurn (χ y))) := B3.add A4
  rw [hL, hR, integral_add S1 S2, integral_add S3 S4,
    integral_add A1 A2, integral_add A3 A4, integral_add A1 B2, integral_add B3 A4,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, e2, e3]
  ring

theorem driftSymbolWeak_of_transport (h : LinearTransportPairStatement) : DriftSymbolWeakStatement :=
  driftSymbolWeak_of_two (driftTransportPairing_of h) rapidSecondPair

namespace Internal.DriftSymbolWeakLinear

theorem clm_decomp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) (x : Space) :
    L x = ∑ k : Fin 3, x k • L (unitVector k) := by
  conv_lhs => rw [Internal.DriftSymbolWeakFreq.decomp x]
  simp [Fin.sum_univ_three]

theorem hasTG (W : Space →L[ℝ] Space) (k : Fin 3) :
    (fun y : Space => (W y) k).HasTemperateGrowth :=
  ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp W).hasTemperateGrowth

theorem lineDeriv_coord_smul (W : Space →L[ℝ] Space) (θ : 𝓢(Space, Space)) (k : Fin 3) (y : Space) :
    (∂_{unitVector k} (SchwartzMap.smulLeftCLM Space (fun y : Space => (W y) k) θ)) y =
      (W y) k • fderiv ℝ θ y (unitVector k) + (W (unitVector k)) k • θ y := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.smulLeftCLM_apply (hasTG W k)]
  have hc : HasFDerivAt (fun y : Space => (W y) k) ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp W) y :=
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp W).hasFDerivAt
  have hf : HasFDerivAt (fun x : Space => (W x) k • θ x)
      ((W y) k • fderiv ℝ θ y + ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp W).smulRight (θ y)) y :=
    hc.smul θ.differentiableAt.hasFDerivAt
  rw [hf.fderiv]
  simp

end Internal.DriftSymbolWeakLinear

open Internal.DriftSymbolWeakLinear Internal.SecondPairRapid in
theorem linearTransportPair : LinearTransportPairStatement := by
  intro k v G H hS θ W
  have hGm : ∀ j, MemLp (fun y => G y (unitVector j)) 2 volume := fun j =>
    Internal.SecondSymbol.memLp_comp hS.measurable_gradient hS.gradient_two j
  have hv := pairable_six hS.velocity_six
  set θk : Fin 3 → 𝓢(Space, Space) := fun j => SchwartzMap.smulLeftCLM Space (fun y : Space => (W y) j) θ
  have hθk : ∀ j y, θk j y = (W y) j • θ y := fun j y => by
    simp only [θk, SchwartzMap.smulLeftCLM_apply_apply (hasTG W j)]
  have P1 : ∀ y, inner ℝ (G y (W y)) (θ y) = ∑ j, inner ℝ (G y (unitVector j)) (θk j y) := by
    intro y
    rw [clm_decomp (G y) (W y), sum_inner]
    simp only [hθk, inner_smul_left, inner_smul_right]
    simp
  have P2 : ∀ y, inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y) =
      ∑ j, inner ℝ (v y) ((∂_{unitVector j} (θk j)) y) := by
    intro y
    simp only [θk, lineDeriv_coord_smul]
    rw [clm_decomp (fderiv ℝ θ y) (W y)]
    simp only [Internal.DriftSymbolWeakFreq.inner_unit, Finset.sum_smul, ← inner_sum, Finset.sum_add_distrib]
  have I1 : ∀ j, Integrable (fun y => inner ℝ (G y (unitVector j)) (θk j y)) := fun j =>
    integrable_inner (pairable_two (hGm j)) (hGm j).1 (θk j)
  have I2 : ∀ j, Integrable (fun y => inner ℝ (v y) ((∂_{unitVector j} (θk j)) y)) := fun j =>
    integrable_inner hv hS.measurable_velocity _
  have W1 : ∀ j, ∫ y, inner ℝ (v y) ((∂_{unitVector j} (θk j)) y) =
      -∫ y, inner ℝ (G y (unitVector j)) (θk j y) := fun j =>
    weak_vec hv hS.measurable_velocity (pairable_two (hGm j)) (hGm j).1
      (fun ψ hψ => hS.weak_gradient ψ hψ j) _
  have eP1 : (fun y => inner ℝ (G y (W y)) (θ y)) = fun y => ∑ j, inner ℝ (G y (unitVector j)) (θk j y) :=
    funext P1
  have eP2 : (fun y => inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y)) =
      fun y => ∑ j, inner ℝ (v y) ((∂_{unitVector j} (θk j)) y) := funext P2
  refine ⟨integrable_inner hv hS.measurable_velocity θ, ?_, ?_, ?_⟩
  · rw [eP1]
    exact integrable_finsetSum _ fun j _ => I1 j
  · rw [eP2]
    exact integrable_finsetSum _ fun j _ => I2 j
  · rw [eP1, eP2, integral_finsetSum _ fun j _ => I1 j, integral_finsetSum _ fun j _ => I2 j,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [W1, neg_neg]

theorem driftSymbolWeak : DriftSymbolWeakStatement :=
  driftSymbolWeak_of_transport linearTransportPair

end SteadyCert

end Breakdown

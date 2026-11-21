import Breakdown.FracCert.PowerSymbolSplit
import Breakdown.FreqTr.FreqTrConjSym
import Breakdown.FreqTr.FieldOp
import Breakdown.FreqTr.VelocityInjective
import Breakdown.FreqTr.NiceApprox
import Breakdown.Frac.NNiceField
import Breakdown.Frac.OpExports

open scoped ContDiff ENNReal SchwartzMap FourierTransform
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace PowerSymbolInternal

theorem conjVec_conjVec (w : Freq.CSpace) : Freq.conjVec (Freq.conjVec w) = w := by
  ext i
  simp [Freq.conjVec]

theorem inner_conjVec (a b : Freq.CSpace) :
    inner ℝ (Freq.conjVec a) (Freq.conjVec b) = inner ℝ a b := by
  refine (real_inner_eq_re_inner ℂ _ _).trans (Eq.trans ?_ (real_inner_eq_re_inner ℂ _ _).symm)
  simp only [PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Freq.conjVec]

theorem integrable_inner_of_compact {f : Space → Freq.CSpace} (hf : LocallyIntegrable f volume)
    {m : Space → Freq.CSpace} (hm : Continuous m) (hmc : HasCompactSupport m) :
    Integrable (fun ξ => inner ℝ (f ξ) (m ξ)) := by
  refine Integrable.mono' (hf.integrable_smul_left_of_hasCompactSupport hm.norm hmc.norm).norm
    (hf.aestronglyMeasurable.inner hm.aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, norm_smul, norm_norm, mul_comm]
  exact abs_real_inner_le_norm _ _

theorem band_of_scalar {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ {0}ᶜ) (w : Freq.CSpace) :
    IsBandSymbol (fun ξ => g ξ • w + g (-ξ) • Freq.conjVec w) := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have h0 : (0 : Space) ∉ tsupport g := fun h => hgU h rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport g).isOpen_compl 0 h0
  have zero_of : ∀ ξ, ξ ∉ tsupport g → g ξ = 0 := fun ξ h => image_eq_zero_of_notMem_tsupport h
  refine ⟨?_, ?_, ⟨ε, hε, fun ξ hξ => ?_⟩, fun ξ => ?_⟩
  · exact (hg.smul contDiff_const).add ((hg.comp contDiff_neg).smul contDiff_const)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun ξ hξ => ?_
    have h1 : ξ ∉ tsupport g := fun h => hξ (hR h)
    have h2 : -ξ ∉ tsupport g := fun h => hξ (by simpa [Metric.mem_closedBall] using hR h)
    simp [zero_of ξ h1, zero_of (-ξ) h2]
  · have h1 : ξ ∉ tsupport g := fun h => hball (by simpa [Metric.mem_ball] using hξ) h
    have h2 : -ξ ∉ tsupport g := fun h => hball (by simpa [Metric.mem_ball] using hξ) h
    simp [zero_of ξ h1, zero_of (-ξ) h2]
  · simp only [neg_neg, map_add, map_smul, conjVec_conjVec]
    abel

theorem integral_band_scalar {f : Space → Freq.CSpace} (hf : LocallyIntegrable f volume)
    (ef : ∀ᵐ ξ ∂volume, f (-ξ) = Freq.conjVec (f ξ)) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (w : Freq.CSpace) :
    ∫ ξ, inner ℝ (f ξ) (g ξ • w + g (-ξ) • Freq.conjVec w) = 2 * ∫ ξ, inner ℝ (g ξ • f ξ) w := by
  have hI1 : Integrable (fun ξ => inner ℝ (g ξ • f ξ) w) :=
    (hf.integrable_smul_left_of_hasCompactSupport hg.continuous hgc).inner_const w
  have hneg : Integrable (fun ξ => inner ℝ (g (-ξ) • f ξ) (Freq.conjVec w)) := by
    have h2 : Integrable (fun ξ => inner ℝ (g ξ • f (-ξ)) (Freq.conjVec w)) := by
      refine hI1.congr ?_
      have ef' : ∀ᵐ ξ ∂volume, f (-ξ) = Freq.conjVec (f ξ) := ef
      filter_upwards [ef'] with ξ hξ
      rw [hξ, real_inner_smul_left, real_inner_smul_left, inner_conjVec]
    have := h2.comp_neg
    simpa using this
  have hsplit : ∀ ξ, inner ℝ (f ξ) (g ξ • w + g (-ξ) • Freq.conjVec w) =
      inner ℝ (g ξ • f ξ) w + inner ℝ (g (-ξ) • f ξ) (Freq.conjVec w) := fun ξ => by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_left]
  simp_rw [hsplit]
  rw [integral_add hI1 hneg, two_mul]
  congr 1
  rw [← integral_neg_eq_self]
  refine integral_congr_ae ?_
  filter_upwards [ef] with ξ hξ
  rw [neg_neg, hξ, real_inner_smul_left, real_inner_smul_left, inner_conjVec]

end PowerSymbolInternal

open PowerSymbolInternal in
theorem PowerSymbolInternal.bandUnique : BandUniqueStatement := by
  intro g₁ g₂ h₁ h₂ e₁ e₂ hI
  set f : Space → Freq.CSpace := fun ξ => g₁ ξ - g₂ ξ with hfdef
  have hf : LocallyIntegrable f volume := h₁.sub h₂
  have ef : ∀ᵐ ξ ∂volume, f (-ξ) = Freq.conjVec (f ξ) := by
    filter_upwards [e₁, e₂] with ξ a b
    simp only [hfdef, a, b, map_sub]
  have key : ∀ m, IsBandSymbol m → ∫ ξ, inner ℝ (f ξ) (m ξ) = 0 := by
    intro m hm
    have hmc : Continuous m := hm.1.continuous
    have i1 := integrable_inner_of_compact h₁ hmc hm.2.1
    have i2 := integrable_inner_of_compact h₂ hmc hm.2.1
    simp only [hfdef, inner_sub_left]
    rw [integral_sub i1 i2, hI m hm, sub_self]
  have hz : ∀ᵐ ξ ∂volume, ξ ∈ ({0}ᶜ : Set Space) → f ξ = 0 := by
    refine isOpen_compl_singleton.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn _) fun g hg hgc hgU => ?_
    have hint : Integrable (fun ξ => g ξ • f ξ) :=
      hf.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    have hw : ∀ w : Freq.CSpace, inner ℝ (∫ ξ, g ξ • f ξ) w = 0 := by
      intro w
      have h0 := key _ (band_of_scalar hg hgc hgU w)
      rw [integral_band_scalar hf ef hg hgc w] at h0
      have hc : ∫ ξ, inner ℝ w (g ξ • f ξ) = ∫ ξ, inner ℝ (g ξ • f ξ) w :=
        integral_congr_ae (ae_of_all _ fun ξ => real_inner_comm _ _)
      rw [real_inner_comm, ← integral_inner hint w, hc]
      linarith
    exact inner_self_eq_zero.mp (hw _)
  have h0 : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    have : (volume : Measure Space) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with ξ hξ
    simpa using hξ
  filter_upwards [hz, h0] with ξ a b
  exact sub_eq_zero.mp (a b)


theorem PowerSymbolInternal.symbolConjSym : SymbolConjSymStatement := by
  intro F
  have hH : Freq.reflConj (fieldSymbol F) = fieldSymbol F :=
    Freq.freqTrConjSym Freq.fieldOpRealized (Freq.toLpOrZero 2 F)
  have hae : (Freq.reflConj (fieldSymbol F) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => Freq.conjVec ((fieldSymbol F : Space → Freq.CSpace) (-ξ)) :=
    Freq.fieldOpRealized (ContinuousLinearEquiv.neg ℝ) (fun _ => Freq.conjVec) ‖Freq.conjVec‖
      aestronglyMeasurable_const (fun _ => le_rfl) (fieldSymbol F)
  rw [hH] at hae
  have h2 := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae hae
  filter_upwards [h2] with ξ hξ
  simpa using hξ

theorem PowerSymbolInternal.bandScale : BandScaleStatement := by
  intro s hs m hm
  obtain ⟨hsm, hcs, ⟨r, hr, hz⟩, hh⟩ := hm
  refine ⟨?_, ?_, ⟨r, hr, fun ξ hξ => by simp [hz ξ hξ]⟩, fun ξ => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ‖ξ‖ < r
    · have hev : (fun η => freqPow s η • m η) =ᶠ[nhds ξ] fun _ => (0 : Freq.CSpace) := by
        have hopen : IsOpen {η : Space | ‖η‖ < r} := isOpen_lt continuous_norm continuous_const
        filter_upwards [hopen.mem_nhds hξ] with η hη
        simp [hz η hη]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have h0 : ξ ≠ 0 := by
        intro h
        apply hξ
        simpa [h] using hr
      have hn : ContDiffAt ℝ ∞ (fun η : Space => 2 * π * ‖η‖) ξ :=
        contDiffAt_const.mul (contDiffAt_norm ℝ h0)
      have hne : 2 * π * ‖ξ‖ ≠ 0 := by
        have := norm_pos_iff.mpr h0
        positivity
      have hp : ContDiffAt ℝ ∞ (fun η : Space => freqPow s η) ξ := by
        unfold freqPow
        exact hn.rpow_const_of_ne hne
      exact hp.smul (hsm.contDiffAt)
  · refine hcs.mono fun ξ hξ => ?_
    rw [Function.mem_support] at hξ ⊢
    intro h0
    exact hξ (by simp [h0])
  · simp only [freqPow, norm_neg, hh, map_smul]

theorem PowerSymbolInternal.bandPair : BandPairStatement := by
  intro F hF m hm
  set Mc : 𝓢(Space, Freq.CSpace) := hm.2.1.toSchwartzMap hm.1 with hMc
  have hMf : ⇑Mc = m := rfl
  have conjSym : ∀ ξ, Mc (-ξ) = Freq.conjVec (Mc ξ) := fun ξ => hm.2.2.2 ξ
  set φ : 𝓢(Space, Space) := SchwartzMap.postcompCLM Freq.realVec (𝓕⁻ Mc) with hφ
  have hφf : ⇑φ = Freq.niceField m := by
    funext x
    rw [hφ, SchwartzMap.postcompCLM_apply, SchwartzMap.fourierInv_coe, hMf]
    rfl
  have hψ : SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.complexifyVec φ = 𝓕⁻ Mc := by
    ext x : 1
    rw [SchwartzMap.postcompCLM_apply, hφ, SchwartzMap.postcompCLM_apply]
    exact Freq.Internal.NiceApprox.complexify_realVec_of_conj
      (Freq.Internal.NiceApprox.freqTrInv_conj Mc conjSym x)
  have hT : Freq.freqTrR (Freq.complexify (φ.toLp 2)) = Mc.toLp 2 := by
    rw [Freq.Internal.FreqTrConjSym.complexify_toLp, Freq.Internal.FreqTrConjSym.freqTrR_toLp, hψ,
      FourierTransform.fourier_fourierInv_eq]
  have hFl : Freq.toLpOrZero 2 F = hF.toLp F := by
    simp [Freq.toLpOrZero, hF]
  have hiso : ∀ a b : Freq.L2C, inner ℝ (Freq.freqTrR a) (Freq.freqTrR b) = inner ℝ a b := by
    intro a b
    rw [Freq.Internal.VelocityInjective.l2c_real_inner, Freq.Internal.VelocityInjective.l2c_real_inner]
    exact congrArg _ (Freq.freqTrL2.inner_map_map a b)
  have key : inner ℝ (hF.toLp F) (φ.toLp 2) = inner ℝ (fieldSymbol F) (Mc.toLp 2) := by
    rw [← Freq.Internal.VelocityInjective.complexify_inner, ← hiso, hT, fieldSymbol, hFl]
  rw [L2.inner_def, L2.inner_def] at key
  have e1 : ∫ y, inner ℝ (F y) (Freq.niceField m y) = ∫ y, inner ℝ ((hF.toLp F) y) ((φ.toLp 2) y) := by
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp, φ.coeFn_toLp 2 volume] with y h1 h2
    rw [h1, h2, hφf]
  have e2 : ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ) ((Mc.toLp 2) ξ) =
      ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ) (m ξ) := by
    refine integral_congr_ae ?_
    filter_upwards [Mc.coeFn_toLp 2 volume] with ξ h
    rw [h, hMf]
  rw [e1, key, e2]

namespace PowerSymbolInternal

open Freq Freq.Internal.NiceApprox Freq.FracInternal.NiceEmbed

theorem band_field {m : Space → CSpace} (hm : IsBandSymbol m) :
    ∃ G : 𝓢(Space, Space), ⇑G = niceField m ∧ 𝓕 (fun x => complexifyVec (G x)) = m := by
  set a : 𝓢(Space, CSpace) := hm.2.1.toSchwartzMap hm.1 with ha
  have haf : ⇑a = m := rfl
  refine ⟨SchwartzMap.postcompCLM realVec (𝓕⁻ a), ?_, ?_⟩
  · funext x
    rw [SchwartzMap.postcompCLM_apply, SchwartzMap.fourierInv_coe, haf]
    rfl
  · have e : (fun x => complexifyVec (SchwartzMap.postcompCLM realVec (𝓕⁻ a) x)) = ⇑(𝓕⁻ a : 𝓢(Space, CSpace)) := by
      funext x
      rw [SchwartzMap.postcompCLM_apply]
      exact complexify_realVec_of_conj (freqTrInv_conj a (fun ξ => hm.2.2.2 ξ) x)
    rw [e, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    exact haf

theorem band_eq_of_transform {f : Space → Space} (hc : Continuous f) (hi : Integrable f)
    {n : Space → CSpace} (hn : IsBandSymbol n) (hF : 𝓕 (fun x => complexifyVec (f x)) = n) :
    f = niceField n := by
  have hint : Integrable (𝓕 (fun x => complexifyVec (f x))) := by
    rw [hF]
    exact (hn.2.1.toSchwartzMap hn.1).integrable
  have h : 𝓕⁻ (𝓕 (fun x => complexifyVec (f x))) = fun x => complexifyVec (f x) :=
    Continuous.fourierInv_fourier_eq (complexifyVec.continuous.comp hc)
      (complexifyVec.integrable_comp hi) hint
  funext x
  have hx := congrFun h x
  rw [hF] at hx
  rw [niceField, hx]
  exact (realVec_complexifyVec_eq (f x)).symm

theorem band_negSecondTrace {m : Space → CSpace} (hm : IsBandSymbol m)
    (hm' : IsBandSymbol (fun ξ => sspFactor ξ • m ξ)) :
    negSsp (niceField m) = niceField (fun ξ => sspFactor ξ • m ξ) := by
  obtain ⟨G, hG, hT⟩ := band_field hm
  rw [← hG, ← negSspS_apply]
  refine band_eq_of_transform (negSspS G).continuous (negSspS G).integrable hm' ?_
  funext ξ
  rw [negSspS_apply, freqTr_negSsp, hT]

theorem band_power {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) {m : Space → CSpace} (hm : IsBandSymbol m)
    (hm' : IsBandSymbol (fun ξ => freqPow (2 * α) ξ • m ξ)) :
    fractionalPowerAt α (niceField m) = niceField (fun ξ => freqPow (2 * α) ξ • m ξ) := by
  obtain ⟨G, hG, hT⟩ := band_field hm
  rw [← hG]
  refine band_eq_of_transform (FracInternal.NiceField.continuous_fracPower α hα hα2 G)
    (FracInternal.NiceField.integrable_fracPower α hα hα2 G) hm' ?_
  funext ξ
  rw [symbol α hα hα2 G ξ, hT, Complex.coe_smul]
  rfl

end PowerSymbolInternal

open PowerSymbolInternal in
theorem PowerSymbolInternal.bandPowerTrace (hS : BandScaleStatement) : BandPowerTraceStatement := by
  intro α hα hα2 m hm
  have hs : (0 : ℝ) < 2 * α - 2 := by linarith
  have h1 := hS (2 * α - 2) hs m hm
  have h2 := hS (2 * α) (by linarith) m hm
  have he : (fun ξ => Freq.sspFactor ξ • (fun ξ => freqPow (2 * α - 2) ξ • m ξ) ξ) =
      fun ξ => freqPow (2 * α) ξ • m ξ := by
    funext ξ
    by_cases h0 : ξ = 0
    · obtain ⟨r, hr, hz⟩ := hm.2.2.1
      simp [hz ξ (by simpa [h0] using hr)]
    · have hp : 0 < 2 * π * ‖ξ‖ := by
        have := norm_pos_iff.mpr h0
        positivity
      rw [smul_smul]
      congr 1
      simp only [Freq.sspFactor, freqPow]
      have key : (2 * π * ‖ξ‖) ^ (2 * α) = (2 * π * ‖ξ‖) ^ (2 : ℝ) * (2 * π * ‖ξ‖) ^ (2 * α - 2) := by
        rw [← Real.rpow_add hp]
        ring_nf
      rw [key, Real.rpow_two]
      ring
  rw [band_power hα hα2 hm h2, ← he, band_negSecondTrace h1 (he ▸ h2)]

theorem weakPowerSymbol_of_band (_h1 : SecondSymbolEnergyStatement) (hA : BandWeakPowerStatement)
    (hB : BandSecondPairStatement) :
    WeakPowerSymbolStatement := by
  intro α hα hα2 k v G H P hv hP
  have hs : (0 : ℝ) < 2 * α - 2 := by linarith
  have hcont : Continuous (fun ξ : Space => freqPow (2 * α - 2) ξ) := by
    unfold freqPow
    exact (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr hs.le)
  have hsec : secondSymbol H = fieldSymbol (negSecondTrace H) := rfl
  refine PowerSymbolInternal.bandUnique _ _ ?_ ?_ ?_ ?_ ?_
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact ((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul hcont
  · exact PowerSymbolInternal.symbolConjSym P
  · filter_upwards [PowerSymbolInternal.symbolConjSym (negSecondTrace H)] with ξ hξ
    rw [hsec, hξ, map_smul]
    simp [freqPow, norm_neg]
  · intro m hm
    have hm' := PowerSymbolInternal.bandScale (2 * α - 2) hs m hm
    rw [← PowerSymbolInternal.bandPair P hP.1 m hm, hA α hα hα2 v P hv.measurable_velocity hv.velocity_six hP m hm,
      PowerSymbolInternal.bandPowerTrace PowerSymbolInternal.bandScale α hα hα2 m hm, hB k v G H hv _ hm']
    congr 1
    ext ξ
    rw [real_inner_smul_left, real_inner_smul_right]

theorem PowerSymbolInternal.memLp_trace_of {k : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField k v G H) :
    MemLp (negSecondTrace H) 2 volume := by
  have hm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector j)) volume :=
    fun j => ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous).comp_aestronglyMeasurable
        hv.measurable_second
  have hj : ∀ j : Fin 3, MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := by
    intro j
    refine (memLp_two_iff_integrable_sq_norm (hm j)).2 (hv.second_two.mono' ((hm j).norm.pow 2)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖H y (unitVector j) (unitVector j)‖ ^ 2 ≤ ∑ l : Fin 3, ‖H y (unitVector j) (unitVector l)‖ ^ 2 :=
      Finset.single_le_sum (f := fun l => ‖H y (unitVector j) (unitVector l)‖ ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ l : Fin 3, ‖H y (unitVector j) (unitVector l)‖ ^ 2 ≤
        ∑ i : Fin 3, ∑ l : Fin 3, ‖H y (unitVector i) (unitVector l)‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ l : Fin 3, ‖H y (unitVector i) (unitVector l)‖ ^ 2)
        (fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ j)
    exact h1.trans h2
  have hs := (memLp_finsetSum Finset.univ (fun j _ => hj j)).neg
  refine hs.congr_norm ?_ ?_
  · exact hs.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun y => by
      simp [negSecondTrace, secondTrace])
  · exact Filter.Eventually.of_forall fun y => by simp [negSecondTrace, secondTrace]

open PowerSymbolInternal in
theorem PowerSymbolInternal.bandWeakPower_of (h : RapidWeakPowerStatement) : BandWeakPowerStatement := by
  intro α hα hα2 v P hv hv6 hP m hm
  obtain ⟨G, hG, -⟩ := band_field hm
  rw [← hG]
  exact h α hα hα2 v P hv hv6 hP G

open PowerSymbolInternal in
theorem PowerSymbolInternal.bandSecondPair_of (h : RapidSecondPairStatement) : BandSecondPairStatement := by
  intro k v G H hv m hm
  obtain ⟨φ, hφ, -⟩ := band_field hm
  rw [← hφ, h k v G H hv φ, hφ, PowerSymbolInternal.bandPair _ (PowerSymbolInternal.memLp_trace_of hv) m hm]
  rfl

theorem weakPowerSymbol_of (h1 : SecondSymbolEnergyStatement) (hA : RapidWeakPowerStatement)
    (hB : RapidSecondPairStatement) : WeakPowerSymbolStatement :=
  weakPowerSymbol_of_band h1 (PowerSymbolInternal.bandWeakPower_of hA) (PowerSymbolInternal.bandSecondPair_of hB)

end SteadyCert

end Breakdown

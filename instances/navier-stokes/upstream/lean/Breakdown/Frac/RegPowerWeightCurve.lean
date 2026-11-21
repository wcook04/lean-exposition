import Breakdown.Frac.StSpaceReg

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal

private theorem weightL1_toLp {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure k)) :
    toWeightL1 k f = hf.toLp f := by
  unfold toWeightL1
  rw [dif_pos hf]

private theorem memLp_weight_of_allCurve {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    MemLp (F t) 1 (weightL1Measure k) :=
  memLp_weightedVolume_of_hsNormSq ((hF (k + 2)).1 t ht).1 ((hF (k + 2)).1 t ht).2

private theorem continuousOn_weight_allCurve {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (k : ℕ) :
    ContinuousOn (fun τ => toWeightL1 k (F τ)) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le k
  intro t ht
  have key : ∀ s ∈ Icc 0 T, edist (toWeightL1 k (F s)) (toWeightL1 k (F t)) ≤
      ENNReal.ofReal C * hsNormSq (k + 2) (F s - F t) ^ (1 / 2 : ℝ) := by
    intro s hs
    rw [weightL1_toLp (memLp_weight_of_allCurve hF k hs),
      weightL1_toLp (memLp_weight_of_allCurve hF k ht), Lp.edist_toLp_toLp,
      eLpNorm_one_eq_lintegral_enorm]
    have := lintegral_weightedVolume k (fun ξ => ‖(F s - F t) ξ‖ₑ)
    rw [show weightL1Measure k = weightedVolume k from rfl, this]
    exact hC _
  have hlim : Tendsto (fun s => ENNReal.ofReal C * hsNormSq (k + 2) (F s - F t) ^ (1 / 2 : ℝ))
      (𝓝[Icc 0 T] t) (𝓝 0) := by
    have h0 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp
      ((hF (k + 2)).2 t ht)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h0
    have := ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal C)
    rw [mul_zero] at this
    exact this
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs using key s hs

private theorem powerFactor_le {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) (ξ : Space) :
    (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π) ^ (2 * α) * (1 + ‖ξ‖) ^ 3 := by
  have hn : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have he : 0 ≤ 2 * α := by linarith
  rw [Real.mul_rpow (by positivity) hn]
  gcongr
  calc ‖ξ‖ ^ (2 * α) ≤ (1 + ‖ξ‖) ^ (2 * α) := Real.rpow_le_rpow hn (by linarith) he
    _ ≤ (1 + ‖ξ‖) ^ ((3 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
    _ = (1 + ‖ξ‖) ^ 3 := Real.rpow_natCast _ 3

private theorem exists_clm_power {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) (k : ℕ) :
    ∃ L : Lp CSpace 1 (weightedVolume (k + 3)) →L[ℝ] Lp CSpace 1 (weightedVolume k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightedVolume (k + 3))),
        ∃ hg : MemLp (fun ξ => -((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ)) : ℂ) • f ξ) 1 (weightedVolume k),
          L (hf.toLp f) = hg.toLp _ := by
  refine Internal.exists_clm_mult k (k + 3)
    (fun ξ z => -((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ)) : ℂ) • z) ?_
    (fun ξ z w => smul_add _ z w) (fun ξ c z => smul_comm _ c z) ((2 * π) ^ (2 * α))
    (by positivity) ?_
  · change Measurable fun p : Space × CSpace => -((((2 * π * ‖p.1‖) ^ (2 * α) : ℝ)) : ℂ) • p.2
    fun_prop
  · intro ξ z
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity), pow_add]
    have h0 := powerFactor_le hα hα2 ξ
    calc (1 + ‖ξ‖) ^ k * ((2 * π * ‖ξ‖) ^ (2 * α) * ‖z‖)
        ≤ (1 + ‖ξ‖) ^ k * (((2 * π) ^ (2 * α) * (1 + ‖ξ‖) ^ 3) * ‖z‖) := by gcongr
      _ = (2 * π) ^ (2 * α) * ((1 + ‖ξ‖) ^ k * (1 + ‖ξ‖) ^ 3 * ‖z‖) := by ring

private theorem powerTimeDeriv_repr {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) (k : ℕ) :
    ∃ Φ : Lp CSpace 1 (weightL1Measure (k + 3)) × Lp CSpace 1 (weightL1Measure (k + 1)) →
        Lp CSpace 1 (weightL1Measure k), (∀ n : WithTop ℕ∞, ContDiff ℝ n Φ) ∧
      ∀ (f : Space → CSpace) (hf3 : MemLp f 1 (weightL1Measure (k + 3)))
        (hf1 : MemLp f 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (powerTimeDerivSymbol α f) 1 (weightL1Measure k),
          Φ (hf3.toLp f, hf1.toLp f) = h.toLp _ := by
  obtain ⟨L, hL⟩ : ∃ L : Lp CSpace 1 (weightL1Measure (k + 3)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 3))),
        ∃ hg : MemLp (fun ξ => -((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ)) : ℂ) • f ξ) 1 (weightL1Measure k),
          L (hf.toLp f) = hg.toLp _ := exists_clm_power hα hα2 k
  obtain ⟨P, hP⟩ : ∃ L : Lp CSpace 1 (weightL1Measure k) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure k)),
        ∃ hg : MemLp (fun ξ => -divFreeC ξ (f ξ)) 1 (weightL1Measure k),
          L (hf.toLp f) = hg.toLp _ := exists_clm_divFree k
  obtain ⟨B, hB⟩ : ∃ B : Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ]
      Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 1)))
        (hg : MemLp g 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (advectionBilin f g) 1 (weightL1Measure k),
          B (hf.toLp f) (hg.toLp g) = h.toLp _ := exists_bilin_advection k
  refine ⟨fun p => L p.1 + P (B p.2 p.2), fun n => ?_, ?_⟩
  · exact (L.contDiff.comp contDiff_fst).add
      (P.contDiff.comp (B.isBoundedBilinearMap.contDiff.comp (contDiff_snd.prodMk contDiff_snd)))
  · intro f hf3 hf1
    obtain ⟨hg, hLg⟩ := hL f hf3
    obtain ⟨hb, hBb⟩ := hB f f hf1 hf1
    obtain ⟨hp, hPp⟩ := hP _ hb
    have hsum := hg.add hp
    have heq : (fun ξ => -((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ)) : ℂ) • f ξ) +
        (fun ξ => -divFreeC ξ (advectionBilin f f ξ)) = powerTimeDerivSymbol α f := by
      funext ξ
      simp only [Pi.add_apply, powerTimeDerivSymbol, powerSymbol, neg_smul]
      rfl
    refine ⟨heq ▸ hsum, ?_⟩
    simp only
    rw [hLg, hBb, hPp, ← MemLp.toLp_add hg hp]
    congr 1

end PowerInternal

open PowerInternal

private theorem continuous_projC_fixed (ξ : Space) : Continuous (fun z : CSpace => divFreeC ξ z) := by
  unfold divFreeC
  fun_prop

theorem powerWeightCurve_of (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2)
    (h1 : PowerPointwiseDerivStatement α) : PowerWeightCurveStatement α := by
  intro T hT F hF hd hs
  have hderiv : ∀ (k : ℕ), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun τ => toWeightL1 k (F τ)) (toWeightL1 k (powerTimeDerivSymbol α (F t)))
        (Icc 0 T) t := by
    intro k t ht
    obtain ⟨Φ, hΦ, hΦeq⟩ := powerTimeDeriv_repr hα hα2 k
    have hD : ∀ s ∈ Icc 0 T, ∃ h : MemLp (powerTimeDerivSymbol α (F s)) 1 (weightL1Measure k),
        Φ (toWeightL1 (k + 3) (F s), toWeightL1 (k + 1) (F s)) = h.toLp _ := by
      intro s hs
      rw [weightL1_toLp (memLp_weight_of_allCurve hF (k + 3) hs),
        weightL1_toLp (memLp_weight_of_allCurve hF (k + 1) hs)]
      exact hΦeq _ _ _
    choose hDm hDeq using hD
    have hcN : ∀ ξ, ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T) := fun ξ =>
      ((continuous_projC_fixed ξ).comp_continuousOn
        (continuousOn_advectionSymbol_apply (hF 1) ξ)).neg
    have hder : ∀ ξ, ∀ s ∈ Icc 0 T,
        HasDerivWithinAt (fun τ => F τ ξ) (powerTimeDerivSymbol α (F s) ξ) (Icc 0 T) s :=
      fun ξ s hs => h1 T hT F hd ξ (hcN ξ) s hs
    have hvc : ∀ ξ, ContinuousOn (fun s => powerTimeDerivSymbol α (F s) ξ) (Icc 0 T) := by
      intro ξ
      have hc : ContinuousOn (fun s => F s ξ) (Icc 0 T) := fun s hs =>
        (hder ξ s hs).continuousWithinAt
      exact ((hc.const_smul ((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ)) : ℂ)).neg).add (hcN ξ)
    have hcont : ContinuousWithinAt
        (fun s => Φ (toWeightL1 (k + 3) (F s), toWeightL1 (k + 1) (F s))) (Icc 0 T) t :=
      ((hΦ 0).continuous.comp_continuousOn ((continuousOn_weight_allCurve hF (k + 3)).prodMk
        (continuousOn_weight_allCurve hF (k + 1)))) t ht
    have hlim : Tendsto (fun s => ∫⁻ ξ, ‖powerTimeDerivSymbol α (F s) ξ -
        powerTimeDerivSymbol α (F t) ξ‖ₑ ∂weightL1Measure k) (𝓝[Icc 0 T] t) (𝓝 0) := by
      rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0] at hcont
      refine hcont.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hDeq s hs, hDeq t ht, Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm]
      rfl
    rw [weightL1_toLp (hDm t ht)]
    exact hasDerivWithinAt_toLp_of_pointwise (convex_Icc 0 T) ht
      (fun s hs => memLp_weight_of_allCurve hF k hs) hDm hder hvc hlim
      (fun s hs => weightL1_toLp _)
  refine ⟨hderiv, fun k n => ?_⟩
  induction n generalizing k with
  | zero => exact contDiffOn_zero.mpr (continuousOn_weight_allCurve hF k)
  | succ n ih =>
    obtain ⟨Φ, hΦ, hΦeq⟩ := powerTimeDeriv_repr hα hα2 k
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
    refine ⟨fun t ht => (hderiv k t ht).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have heq : ∀ t ∈ Icc 0 T, derivWithin (fun τ => toWeightL1 k (F τ)) (Icc 0 T) t =
        Φ (toWeightL1 (k + 3) (F t), toWeightL1 (k + 1) (F t)) := by
      intro t ht
      rw [(hderiv k t ht).derivWithin (uniqueDiffOn_Icc hT t ht)]
      obtain ⟨h, hh⟩ := hΦeq (F t) (memLp_weight_of_allCurve hF (k + 3) ht)
        (memLp_weight_of_allCurve hF (k + 1) ht)
      rw [weightL1_toLp (memLp_weight_of_allCurve hF (k + 3) ht),
        weightL1_toLp (memLp_weight_of_allCurve hF (k + 1) ht), hh, weightL1_toLp h]
    exact ContDiffOn.congr ((hΦ n).comp_contDiffOn ((ih (k + 3)).prodMk (ih (k + 1)))) heq

end Breakdown.SmoothFlow

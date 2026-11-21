import Breakdown.Uniqueness.RegPhysAuxPressurePart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PressureSingle.Internal

theorem pressureBilin_congr {f f' g g' : Space → CSpace} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g')
    (ξ : Space) : pressureBilinSymbol f g ξ = pressureBilinSymbol f' g' ξ := by
  unfold pressureBilinSymbol
  congr 1
  refine integral_congr_ae ?_
  have h2 : ∀ᵐ η ∂(volume : Measure Space), g (ξ - η) = g' (ξ - η) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae hg
  filter_upwards [hf, h2] with η h1 h2
  rw [h1, h2]

theorem pressureBilin_add_left {f f' g : Space → CSpace} {ξ : Space}
    (h1 : Integrable (fun η => pressurePairTerm ξ (f η) (g (ξ - η))))
    (h2 : Integrable (fun η => pressurePairTerm ξ (f' η) (g (ξ - η)))) :
    pressureBilinSymbol (f + f') g ξ = pressureBilinSymbol f g ξ + pressureBilinSymbol f' g ξ := by
  unfold pressureBilinSymbol
  simp only [Pi.add_apply, pairTerm_add_left]
  rw [integral_add h1 h2, neg_add]

theorem pressureBilin_add_right {f g g' : Space → CSpace} {ξ : Space}
    (h1 : Integrable (fun η => pressurePairTerm ξ (f η) (g (ξ - η))))
    (h2 : Integrable (fun η => pressurePairTerm ξ (f η) (g' (ξ - η)))) :
    pressureBilinSymbol f (g + g') ξ = pressureBilinSymbol f g ξ + pressureBilinSymbol f g' ξ := by
  unfold pressureBilinSymbol
  simp only [Pi.add_apply, pairTerm_add_right]
  rw [integral_add h1 h2, neg_add]

theorem pressureBilin_smul_left (r : ℝ) (f g : Space → CSpace) (ξ : Space) :
    pressureBilinSymbol (r • f) g ξ = (r : ℂ) * pressureBilinSymbol f g ξ := by
  unfold pressureBilinSymbol
  simp only [Pi.smul_apply, pairTerm_smul_left]
  rw [integral_const_mul]
  ring

theorem pressureBilin_smul_right (r : ℝ) (f g : Space → CSpace) (ξ : Space) :
    pressureBilinSymbol f (r • g) ξ = (r : ℂ) * pressureBilinSymbol f g ξ := by
  unfold pressureBilinSymbol
  simp only [Pi.smul_apply, pairTerm_smul_right]
  rw [integral_const_mul]
  ring

theorem measurable_freqDot {a : Space × Space → Space} {b : Space × Space → CSpace} (ha : Measurable a)
    (hb : Measurable b) : Measurable (fun p => freqDot (a p) (b p)) := by
  unfold freqDot
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((by fun_prop : Continuous fun ξ : Space => ((ξ j : ℝ) : ℂ)).measurable.comp ha).mul
    ((by fun_prop : Continuous fun z : CSpace => z j).measurable.comp hb)

theorem measurable_pairTerm_prod {f g : Space → CSpace} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : Space × Space => pressurePairTerm p.1 (f p.2) (g (p.1 - p.2))) := by
  have hc : Measurable (fun ξ : Space => (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((by fun_prop : Continuous fun ξ : Space => ‖ξ‖ ^ 2).measurable.inv)
  have h2 : Measurable (fun p : Space × Space => freqDot p.1 (f p.2) * freqDot p.1 (g (p.1 - p.2))) :=
    (measurable_freqDot measurable_fst (hf.comp measurable_snd)).mul
      (measurable_freqDot measurable_fst (hg.comp (measurable_fst.sub measurable_snd)))
  have h1 : Measurable (fun p : Space × Space => (((‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ)) := hc.comp measurable_fst
  unfold pressurePairTerm
  exact h1.mul h2

theorem aesm_pressureBilin {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) : AEStronglyMeasurable (pressureBilinSymbol f g) volume := by
  have e : pressureBilinSymbol f g = pressureBilinSymbol (hf.mk f) (hg.mk g) :=
    funext (pressureBilin_congr hf.ae_eq_mk hg.ae_eq_mk)
  rw [e]
  unfold pressureBilinSymbol
  exact (measurable_pairTerm_prod hf.stronglyMeasurable_mk.measurable
    hg.stronglyMeasurable_mk.measurable).aestronglyMeasurable.integral_prod_right'.neg

theorem enorm_single_one : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ₑ = 1 := by
  rw [← ofReal_norm, PiLp.norm_single]
  simp

theorem eLpNorm_pressureSingle_le {k : ℕ} {f g : Space → CSpace} (hf : MemLp f 1 (weightedVolume k))
    (hg : MemLp g 1 (weightedVolume k)) :
    eLpNorm (fun ξ => pressureBilinSymbol f g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
        (weightedVolume k) ≤
      9 * (eLpNorm f 1 (weightedVolume k) * eLpNorm g 1 (weightedVolume k)) := by
  have hmf := aesm_of_memLp hf
  have hmg := aesm_of_memLp hg
  rw [eLpNorm_eq ((aesm_pressureBilin hmf hmg).smul_const _), eLpNorm_eq hmf, eLpNorm_eq hmg]
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) *
        ‖pressureBilinSymbol f g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ₑ
      ≤ ∫⁻ ξ, 9 * (ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ) := by
        refine lintegral_mono fun ξ => ?_
        rw [enorm_smul, enorm_single_one, mul_one]
        calc _ ≤ ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * (9 * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ) := by
              gcongr
              exact enorm_pressureBilinSymbol_le f g ξ
          _ = _ := by ring
    _ = 9 * ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ :=
        lintegral_const_mul' _ _ (by simp)
    _ ≤ _ := by
        gcongr
        exact lintegral_weight_conv_le k hmf.enorm hmg.enorm

theorem memLp_pressureSingle {k : ℕ} {f g : Space → CSpace} (hf : MemLp f 1 (weightedVolume k))
    (hg : MemLp g 1 (weightedVolume k)) :
    MemLp (fun ξ => pressureBilinSymbol f g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
      (weightedVolume k) :=
  ⟨((aesm_pressureBilin (aesm_of_memLp hf) (aesm_of_memLp hg)).smul_const _).mono_ac (weighted_ac k),
    lt_of_le_of_lt (eLpNorm_pressureSingle_le hf hg)
      (ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top hf.2 hg.2))⟩

end PressureSingle.Internal

open PressureSingle.Internal in
theorem exists_bilin_pressureSingle (k : ℕ) :
    ∃ B : Lp CSpace 1 (weightedVolume k) →L[ℝ] Lp CSpace 1 (weightedVolume k) →L[ℝ]
        Lp CSpace 1 (weightedVolume k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightedVolume k)) (hg : MemLp g 1 (weightedVolume k)),
        ∃ h : MemLp (fun ξ => pressureBilinSymbol f g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
          (weightedVolume k), B (hf.toLp f) (hg.toLp g) = h.toLp _ := by
  let Bf : Lp CSpace 1 (weightedVolume k) → Lp CSpace 1 (weightedVolume k) →
      Lp CSpace 1 (weightedVolume k) := fun u v =>
    (memLp_pressureSingle (Lp.memLp u) (Lp.memLp v)).toLp _
  have H1 : ∀ u u' v, Bf (u + u') v = Bf u v + Bf u' v := by
    intro u u' v
    simp only [Bf]
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ((weighted_ac k).ae_le ?_)
    have hadd := (volume_ac k).ae_le (Lp.coeFn_add u u')
    filter_upwards [ae_conv_lt_top (Lp.memLp u) (Lp.memLp v),
      ae_conv_lt_top (Lp.memLp u') (Lp.memLp v)] with ξ h1 h2
    rw [Pi.add_apply, pressureBilin_congr hadd (EventuallyEq.refl _ _) ξ,
      pressureBilin_add_left (integrable_pairTerm (aesm_of_memLp (Lp.memLp u))
        (aesm_of_memLp (Lp.memLp v)) h1) (integrable_pairTerm (aesm_of_memLp (Lp.memLp u'))
        (aesm_of_memLp (Lp.memLp v)) h2), add_smul]
  have H3 : ∀ u v v', Bf u (v + v') = Bf u v + Bf u v' := by
    intro u v v'
    simp only [Bf]
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ((weighted_ac k).ae_le ?_)
    have hadd := (volume_ac k).ae_le (Lp.coeFn_add v v')
    filter_upwards [ae_conv_lt_top (Lp.memLp u) (Lp.memLp v),
      ae_conv_lt_top (Lp.memLp u) (Lp.memLp v')] with ξ h1 h2
    rw [Pi.add_apply, pressureBilin_congr (EventuallyEq.refl _ _) hadd ξ,
      pressureBilin_add_right (integrable_pairTerm (aesm_of_memLp (Lp.memLp u))
        (aesm_of_memLp (Lp.memLp v)) h1) (integrable_pairTerm (aesm_of_memLp (Lp.memLp u))
        (aesm_of_memLp (Lp.memLp v')) h2), add_smul]
  have H2 : ∀ (r : ℝ) u v, Bf (r • u) v = r • Bf u v := by
    intro r u v
    simp only [Bf]
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ((weighted_ac k).ae_le ?_)
    have hs := (volume_ac k).ae_le (Lp.coeFn_smul r u)
    refine Eventually.of_forall fun ξ => ?_
    dsimp only
    rw [Pi.smul_apply, pressureBilin_congr hs (EventuallyEq.refl _ _) ξ, pressureBilin_smul_left,
      ← smul_assoc, Complex.real_smul]
  have H4 : ∀ (r : ℝ) u v, Bf u (r • v) = r • Bf u v := by
    intro r u v
    simp only [Bf]
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ((weighted_ac k).ae_le ?_)
    have hs := (volume_ac k).ae_le (Lp.coeFn_smul r v)
    refine Eventually.of_forall fun ξ => ?_
    dsimp only
    rw [Pi.smul_apply, pressureBilin_congr (EventuallyEq.refl _ _) hs ξ, pressureBilin_smul_right,
      ← smul_assoc, Complex.real_smul]
  let L := LinearMap.mk₂ ℝ Bf H1 H2 H3 H4
  have hbound : ∀ u v, ‖L u v‖ ≤ 9 * ‖u‖ * ‖v‖ := by
    intro u v
    simp only [L, LinearMap.mk₂_apply, Bf]
    rw [Lp.norm_toLp, Lp.norm_def u, Lp.norm_def v, mul_assoc,
      show (9 : ℝ) = (9 : ℝ≥0∞).toReal by simp, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top u) (Lp.eLpNorm_ne_top v)))
      (eLpNorm_pressureSingle_le (Lp.memLp u) (Lp.memLp v))
  refine ⟨L.mkContinuous₂ 9 hbound, fun f g hf hg => ⟨memLp_pressureSingle hf hg, ?_⟩⟩
  simp only [LinearMap.mkContinuous₂_apply, L, LinearMap.mk₂_apply, Bf]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [pressureBilin_congr ((volume_ac k).ae_le hf.coeFn_toLp) ((volume_ac k).ae_le hg.coeFn_toLp) ξ]

end Breakdown.SmoothFlow

import Breakdown.Uniqueness.RegToolkit
import Breakdown.Uniqueness.RegCurveAuxMult
import Breakdown.Uniqueness.RegCurveAuxBilin
import Breakdown.Uniqueness.RegCurveAuxPointwise
import Breakdown.Uniqueness.RegCurveAuxPartition

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def weightL1Measure (k : ℕ) : Measure Space :=
  volume.withDensity (fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ k))

open scoped Classical in
def toWeightL1 (k : ℕ) (f : Space → CSpace) : Lp CSpace 1 (weightL1Measure k) :=
  if h : MemLp f 1 (weightL1Measure k) then h.toLp f else 0

def timeDerivSymbol (f : Space → CSpace) (ξ : Space) : CSpace :=
  -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • f ξ + nonlinSymbol f ξ

private theorem toWeightL1_eq_toLp {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure k)) :
    toWeightL1 k f = hf.toLp f := by
  unfold toWeightL1
  rw [dif_pos hf]

private theorem memLp_weightL1_of_curve {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    MemLp (F t) 1 (weightL1Measure k) :=
  memLp_weightedVolume_of_hsNormSq ((hF (k + 2)).1 t ht).1 ((hF (k + 2)).1 t ht).2

private theorem continuousOn_toWeightL1_curve {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (k : ℕ) :
    ContinuousOn (fun τ => toWeightL1 k (F τ)) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le k
  intro t ht
  have key : ∀ s ∈ Icc 0 T, edist (toWeightL1 k (F s)) (toWeightL1 k (F t)) ≤
      ENNReal.ofReal C * hsNormSq (k + 2) (F s - F t) ^ (1 / 2 : ℝ) := by
    intro s hs
    rw [toWeightL1_eq_toLp (memLp_weightL1_of_curve hF k hs),
      toWeightL1_eq_toLp (memLp_weightL1_of_curve hF k ht), Lp.edist_toLp_toLp,
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

private theorem bilin_weightL1 (k : ℕ) :
    ∃ B : Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ] Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ]
        Lp CSpace 1 (weightL1Measure k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 1)))
        (hg : MemLp g 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (advectionBilin f g) 1 (weightL1Measure k),
          B (hf.toLp f) (hg.toLp g) = h.toLp _ :=
  exists_bilin_advection k

private theorem timeDeriv_repr (k : ℕ) :
    ∃ Φ : Lp CSpace 1 (weightL1Measure (k + 2)) × Lp CSpace 1 (weightL1Measure (k + 1)) →
        Lp CSpace 1 (weightL1Measure k), (∀ n : WithTop ℕ∞, ContDiff ℝ n Φ) ∧
      ∀ (f : Space → CSpace) (hf2 : MemLp f 1 (weightL1Measure (k + 2)))
        (hf1 : MemLp f 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (timeDerivSymbol f) 1 (weightL1Measure k),
          Φ (hf2.toLp f, hf1.toLp f) = h.toLp _ := by
  obtain ⟨L, hL⟩ : ∃ L : Lp CSpace 1 (weightL1Measure (k + 2)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 2))),
        ∃ hg : MemLp (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • f ξ) 1 (weightL1Measure k),
          L (hf.toLp f) = hg.toLp _ := exists_clm_mulNormSq k
  obtain ⟨P, hP⟩ : ∃ L : Lp CSpace 1 (weightL1Measure k) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure k)),
        ∃ hg : MemLp (fun ξ => -divFreeC ξ (f ξ)) 1 (weightL1Measure k),
          L (hf.toLp f) = hg.toLp _ := exists_clm_divFree k
  obtain ⟨B, hB⟩ := bilin_weightL1 k
  refine ⟨fun p => L p.1 + P (B p.2 p.2), fun n => ?_, ?_⟩
  · exact (L.contDiff.comp contDiff_fst).add
      (P.contDiff.comp (B.isBoundedBilinearMap.contDiff.comp (contDiff_snd.prodMk contDiff_snd)))
  · intro f hf2 hf1
    obtain ⟨hg, hLg⟩ := hL f hf2
    obtain ⟨hb, hBb⟩ := hB f f hf1 hf1
    obtain ⟨hp, hPp⟩ := hP _ hb
    refine ⟨hg.add hp, ?_⟩
    simp only
    rw [hLg, hBb, hPp]
    exact (MemLp.toLp_add hg hp).symm

private theorem continuous_divFreeC (ξ : Space) : Continuous (fun z : CSpace => divFreeC ξ z) := by
  unfold divFreeC
  fun_prop

theorem hasDerivWithinAt_toWeightL1 {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hd : IsVarConstSymbol F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => toWeightL1 k (F τ)) (toWeightL1 k (timeDerivSymbol (F t)))
      (Icc 0 T) t := by
  obtain ⟨Φ, hΦ, hΦeq⟩ := timeDeriv_repr k
  have hD : ∀ s ∈ Icc 0 T, ∃ h : MemLp (timeDerivSymbol (F s)) 1 (weightL1Measure k),
      Φ (toWeightL1 (k + 2) (F s), toWeightL1 (k + 1) (F s)) = h.toLp _ := by
    intro s hs
    rw [toWeightL1_eq_toLp (memLp_weightL1_of_curve hF (k + 2) hs),
      toWeightL1_eq_toLp (memLp_weightL1_of_curve hF (k + 1) hs)]
    exact hΦeq _ _ _
  choose hDm hDeq using hD
  have hcN : ∀ ξ, ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T) := fun ξ =>
    ((continuous_divFreeC ξ).comp_continuousOn (continuousOn_advectionSymbol_apply (hF 1) ξ)).neg
  have hder : ∀ ξ, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun τ => F τ ξ) (timeDerivSymbol (F s) ξ) (Icc 0 T) s :=
    fun ξ s hs => hasDerivWithinAt_apply_of_varConst hT hd (hcN ξ) hs
  have hvc : ∀ ξ, ContinuousOn (fun s => timeDerivSymbol (F s) ξ) (Icc 0 T) := by
    intro ξ
    have h1 : ContinuousOn (fun s => F s ξ) (Icc 0 T) := fun s hs => (hder ξ s hs).continuousWithinAt
    exact (h1.const_smul (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ))).add (hcN ξ)
  have hcont : ContinuousWithinAt
      (fun s => Φ (toWeightL1 (k + 2) (F s), toWeightL1 (k + 1) (F s))) (Icc 0 T) t :=
    ((hΦ 0).continuous.comp_continuousOn ((continuousOn_toWeightL1_curve hF (k + 2)).prodMk
      (continuousOn_toWeightL1_curve hF (k + 1)))) t ht
  have hlim : Tendsto (fun s => ∫⁻ ξ, ‖timeDerivSymbol (F s) ξ - timeDerivSymbol (F t) ξ‖ₑ
      ∂weightL1Measure k) (𝓝[Icc 0 T] t) (𝓝 0) := by
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0] at hcont
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hDeq s hs, hDeq t ht, Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm]
    rfl
  rw [toWeightL1_eq_toLp (hDm t ht)]
  exact hasDerivWithinAt_toLp_of_pointwise (convex_Icc 0 T) ht
    (fun s hs => memLp_weightL1_of_curve hF k hs) hDm hder hvc hlim
    (fun s hs => toWeightL1_eq_toLp _)

theorem contDiffOn_toWeightL1 {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hd : IsVarConstSymbol F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) (k n : ℕ) :
    ContDiffOn ℝ n (fun τ => toWeightL1 k (F τ)) (Icc 0 T) := by
  induction n generalizing k with
  | zero => exact contDiffOn_zero.mpr (continuousOn_toWeightL1_curve hF k)
  | succ n ih =>
    obtain ⟨Φ, hΦ, hΦeq⟩ := timeDeriv_repr k
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
    refine ⟨fun t ht => (hasDerivWithinAt_toWeightL1 hT hF hd hs k ht).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have heq : ∀ t ∈ Icc 0 T, derivWithin (fun τ => toWeightL1 k (F τ)) (Icc 0 T) t =
        Φ (toWeightL1 (k + 2) (F t), toWeightL1 (k + 1) (F t)) := by
      intro t ht
      rw [(hasDerivWithinAt_toWeightL1 hT hF hd hs k ht).derivWithin (uniqueDiffOn_Icc hT t ht)]
      obtain ⟨h, hh⟩ := hΦeq (F t) (memLp_weightL1_of_curve hF (k + 2) ht)
        (memLp_weightL1_of_curve hF (k + 1) ht)
      rw [toWeightL1_eq_toLp (memLp_weightL1_of_curve hF (k + 2) ht),
        toWeightL1_eq_toLp (memLp_weightL1_of_curve hF (k + 1) ht), hh, toWeightL1_eq_toLp h]
    exact ContDiffOn.congr ((hΦ n).comp_contDiffOn ((ih (k + 2)).prodMk (ih (k + 1)))) heq

end Breakdown.SmoothFlow

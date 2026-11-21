import Breakdown.FracCert.DriftPower
import Breakdown.Frac.PAxial
import Breakdown.FreqTr.DilationCont
import Breakdown.FreqTr.Rotation
import Breakdown.FreqTr.FieldOp

open scoped ContDiff ENNReal Topology
open MeasureTheory Real Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

def flowLin (g a t : ℝ) : Space ≃L[ℝ] Space :=
  (axialRotation (a * t)).toContinuousLinearEquiv.trans
    (Freq.Internal.DilationCont.scaleEquiv (Real.exp (-(g * t))) (Real.exp_pos _).ne')

def flowValue (a c t : ℝ) : Freq.CSpace →L[ℝ] Freq.CSpace :=
  Real.exp (c * t) • Freq.rotC (axialRotation (-(a * t)))

def flowPull (g a c t : ℝ) (f : Space → Freq.CSpace) (ξ : Space) : Freq.CSpace :=
  flowValue a c t (f (flowLin g a t ξ))

def flowOp (g a c t : ℝ) : Freq.L2C →L[ℝ] Freq.L2C :=
  Freq.fieldOp (flowLin g a t) (fun _ => flowValue a c t)

def FlowContinuityStatement : Prop :=
  ∀ (g a c : ℝ) (f : Freq.L2C), Continuous (fun t => flowOp g a c t f)

def FlowIntegralStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (D h : Space → Freq.CSpace) (hD : MemLp D 2 volume),
    MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume → MemLp (fun ξ => freqPow (2 * α) ξ • h ξ) 2 volume →
    (∀ ψ : Space → Freq.CSpace, IsFreqTest ψ →
      ∫ ξ, inner ℝ (D ξ) (ψ ξ) = ∫ ξ, inner ℝ (h ξ) (flowAdjoint α a ψ ξ)) →
    ∀ t : ℝ, (fun ξ => flowPull (1 / (2 * α)) a (1 - 2 / α) t h ξ - h ξ) =ᵐ[volume]
      ((∫ s in (0 : ℝ)..t, flowOp (1 / (2 * α)) a (1 - 2 / α) s (hD.toLp D) : Freq.L2C) :
        Space → Freq.CSpace)

namespace Internal.FlowPairing

theorem flowLin_apply (g a t : ℝ) (ξ : Space) :
    flowLin g a t ξ = Real.exp (-(g * t)) • axialRotation (a * t) ξ := rfl

theorem flowOp_ae (g a c t : ℝ) (f : Freq.L2C) :
    (flowOp g a c t f : Space → Freq.CSpace) =ᵐ[volume] flowPull g a c t f :=
  Freq.fieldOpRealized (flowLin g a t) (fun _ => flowValue a c t) ‖flowValue a c t‖
    aestronglyMeasurable_const (fun _ => le_rfl) f

theorem norm_flowValue (a c t : ℝ) (z : Freq.CSpace) :
    ‖flowValue a c t z‖ = Real.exp (c * t) * ‖z‖ := by
  simp only [flowValue, ContinuousLinearMap.coe_smul', Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Freq.Internal.Rotation.norm_rotC]

theorem flowValue_succ (a c t : ℝ) (z : Freq.CSpace) :
    flowValue a (c + 1) t z = Real.exp t • flowValue a c t z := by
  simp only [flowValue, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_smul, ← Real.exp_add]
  congr 2
  ring

theorem rotC_refl (z : Freq.CSpace) : Freq.rotC (LinearIsometryEquiv.refl ℝ Space) z = z := by
  ext i
  rw [Freq.Internal.Rotation.rotC_apply]
  simp [unitVector, apply_ite (fun r : ℝ => (r : ℂ)), ite_mul]

theorem flowOp_zero (g a c : ℝ) (f : Freq.L2C) : flowOp g a c 0 f = f := by
  apply Lp.ext
  filter_upwards [flowOp_ae g a c 0 f] with ξ hξ
  rw [hξ]
  simp [flowPull, flowValue, flowLin_apply, axialRotationSpec.2.1, rotC_refl]

theorem qmp_flowLin (g a t : ℝ) :
    Measure.QuasiMeasurePreserving (fun ξ => flowLin g a t ξ) volume volume :=
  (Freq.Internal.Rotation.qmp_smul (Real.exp_pos (-(g * t))).ne').comp
    (Freq.Internal.Rotation.qmp_liso (axialRotation (a * t)))

theorem integrable_flowLin {g a t : ℝ} {F : Space → ℝ} (hF : Integrable F) :
    Integrable (fun ξ => F (flowLin g a t ξ)) := by
  have hR := (axialRotation (a * t)).measurePreserving
  have hs : Integrable (fun ξ => F (Real.exp (-(g * t)) • ξ)) :=
    hF.comp_smul (Real.exp_pos _).ne'
  have := (hR.integrable_comp_emb (axialRotation (a * t)).toHomeomorph.measurableEmbedding).2 hs
  exact this

theorem integral_flowLin (g a t : ℝ) (F : Space → ℝ) :
    ∫ ξ, F (flowLin g a t ξ) = Real.exp (3 * (g * t)) * ∫ ξ, F ξ := by
  have hR := (axialRotation (a * t)).measurePreserving
  have h1 : ∫ ξ, F (flowLin g a t ξ) = ∫ ξ, F (Real.exp (-(g * t)) • ξ) :=
    hR.integral_comp (axialRotation (a * t)).toHomeomorph.measurableEmbedding
      (fun ξ => F (Real.exp (-(g * t)) • ξ))
  rw [h1, Measure.integral_comp_smul, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    abs_of_pos (by positivity), ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 2
  push_cast
  ring

theorem freqPow_flowLin (g a t s : ℝ) (ξ : Space) :
    freqPow s (flowLin g a t ξ) = Real.exp (-(g * t) * s) * freqPow s ξ := by
  unfold freqPow
  rw [flowLin_apply, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), show 2 * π * (Real.exp (-(g * t)) * ‖ξ‖) =
      Real.exp (-(g * t)) * (2 * π * ‖ξ‖) by ring,
    Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul]

theorem integrable_weight {α : ℝ} (hα : 1 ≤ α) {h : Space → Freq.CSpace}
    (h1 : MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume)
    (h2 : MemLp (fun ξ => freqPow (2 * α) ξ • h ξ) 2 volume) :
    Integrable (fun ξ => freqPow (2 * α) ξ * ‖h ξ‖ ^ 2) := by
  have i1 := h1.integrable_norm_pow two_ne_zero
  have i2 := h2.integrable_norm_pow two_ne_zero
  have hm : AEStronglyMeasurable h volume := by
    have := ((Internal.DriftPower.measurable_freqPow 1).inv.aestronglyMeasurable).smul h1.1
    refine this.congr ?_
    filter_upwards [Internal.DriftPower.ae_ne_zero] with ξ hξ
    have : freqPow 1 ξ ≠ 0 := by unfold freqPow; rw [Real.rpow_one]; positivity
    simp only [Pi.smul_apply', Pi.inv_apply, smul_smul, inv_mul_cancel₀ this, one_smul]
  have key : ∀ ξ, freqPow (2 * α) ξ ≤ freqPow 1 ξ ^ 2 + freqPow (2 * α) ξ ^ 2 := by
    intro ξ
    unfold freqPow
    rw [Real.rpow_one]
    have k0 : 0 ≤ 2 * π * ‖ξ‖ := by positivity
    rcases le_total (2 * π * ‖ξ‖) 1 with hk | hk
    · rcases k0.eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
        positivity
      · have : (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π * ‖ξ‖) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge h0 hk (by linarith)
        rw [Real.rpow_two] at this
        nlinarith [sq_nonneg ((2 * π * ‖ξ‖) ^ (2 * α))]
    · have : 1 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := Real.one_le_rpow hk (by linarith)
      nlinarith [sq_nonneg (2 * π * ‖ξ‖)]
  refine Integrable.mono' (i1.add i2)
    ((Internal.DriftPower.measurable_freqPow _).aestronglyMeasurable.mul (hm.norm.pow 2))
    (Filter.Eventually.of_forall fun ξ => ?_)
  have p0 : 0 ≤ freqPow (2 * α) ξ := Internal.DriftPower.freqPow_nonneg _ _
  have q0 : 0 ≤ freqPow 1 ξ := Internal.DriftPower.freqPow_nonneg _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg p0, abs_of_nonneg q0, mul_pow]
  have := mul_le_mul_of_nonneg_right (key ξ) (sq_nonneg ‖h ξ‖)
  linarith

theorem norm_flowLin (g a t : ℝ) (ξ : Space) : ‖flowLin g a t ξ‖ = Real.exp (-(g * t)) * ‖ξ‖ := by
  rw [flowLin_apply, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_sq_L2 (F : Freq.L2C) : ‖F‖ ^ 2 = ∫ ξ, ‖(F : Space → Freq.CSpace) ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

theorem norm_flowOp (g a c t : ℝ) (f : Freq.L2C) :
    ‖flowOp g a c t f‖ = Real.exp ((c + 3 * g / 2) * t) * ‖f‖ := by
  have hsq : ‖flowOp g a c t f‖ ^ 2 = (Real.exp ((c + 3 * g / 2) * t) * ‖f‖) ^ 2 := by
    rw [mul_pow, norm_sq_L2, norm_sq_L2]
    have e1 : ∫ ξ, ‖(flowOp g a c t f : Space → Freq.CSpace) ξ‖ ^ 2 =
        ∫ ξ, Real.exp (c * t) ^ 2 * ‖(f : Space → Freq.CSpace) (flowLin g a t ξ)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [flowOp_ae g a c t f] with ξ hξ
      rw [hξ, flowPull, norm_flowValue, mul_pow]
    have e2 := integral_flowLin g a t (fun η => ‖(f : Space → Freq.CSpace) η‖ ^ 2)
    rw [e1, integral_const_mul, e2, ← mul_assoc]
    congr 1
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem continuous_rotC (a : ℝ) {w : ℝ → Freq.CSpace} (hw : Continuous w) :
    Continuous fun t => Freq.rotC (axialRotation (-(a * t))) (w t) := by
  have hc : ∀ j i, Continuous fun t => (axialRotation (-(a * t)) (unitVector j) i : ℝ) := by
    intro j i
    exact (EuclideanSpace.proj i).continuous.comp
      ((axialRotationSpec.2.2.2.2.1 (unitVector j)).comp (continuous_const.mul continuous_id).neg)
  have hw' : ∀ j, Continuous fun t => (w t) j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp hw
  change Continuous fun t => WithLp.toLp 2 (fun i => ∑ j : Fin 3,
    ((axialRotation (-(a * t)) (unitVector j) i : ℝ) : ℂ) * (w t) j)
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_finsetSum _
    fun j _ => (Complex.continuous_ofReal.comp (hc j i)).mul (hw' j))

theorem continuous_flowValue (a c : ℝ) {w : ℝ → Freq.CSpace} (hw : Continuous w) :
    Continuous fun t => flowValue a c t (w t) := by
  simp only [flowValue, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (continuous_rotC a hw)

theorem continuous_flowLin (g a : ℝ) (ξ : Space) : Continuous fun t => flowLin g a t ξ := by
  simp only [flowLin_apply]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).smul
    ((axialRotationSpec.2.2.2.2.1 ξ).comp (continuous_const.mul continuous_id))

theorem tendsto_flowOp_of_compact (g a c t₀ : ℝ) {φ : Space → Freq.CSpace} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) {G : Freq.L2C} (hG : (G : Space → Freq.CSpace) =ᵐ[volume] φ) :
    Tendsto (fun t => flowOp g a c t G) (𝓝 t₀) (𝓝 (flowOp g a c t₀ G)) := by
  have hreal : ∀ t, (flowOp g a c t G : Space → Freq.CSpace) =ᵐ[volume] flowPull g a c t φ := by
    intro t
    refine (flowOp_ae g a c t G).trans ?_
    filter_upwards [Freq.Internal.Rotation.ae_comp (qmp_flowLin g a t) hG] with ξ hξ
    simp only [flowPull]
    rw [hξ]
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφs
  obtain ⟨R₀, hR₀⟩ := hφs.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ y : Space, R₀ < ‖y‖ → φ y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport (fun hm => ?_)
    have := hR₀ hm
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact absurd hy (not_lt.2 this)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set T : ℝ := |t₀| + 1 with hT
  set Lc : ℝ := Real.exp (|c| * T) with hLc
  set Sg : ℝ := Real.exp (|g| * T) with hSg
  set H : ℝ → Space → Freq.CSpace := fun t ξ => flowPull g a c t φ ξ - flowPull g a c t₀ φ ξ
    with hH
  set K : Set Space := Metric.closedBall 0 (|R₀| * Sg) with hK
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * Lc * C) ^ (2 : ℝ) with hB
  have hexp : ∀ t, |t - t₀| < 1 → Real.exp (c * t) ≤ Lc ∧ Real.exp (g * t) ≤ Sg := by
    intro t ht
    have htT : |t| ≤ T := by
      have := abs_sub_abs_le_abs_sub t t₀
      rw [hT]; linarith
    constructor
    · refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left htT (abs_nonneg _)
    · refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left htT (abs_nonneg _)
  have hpull : ∀ t, |t - t₀| < 1 → ∀ ξ, ‖flowPull g a c t φ ξ‖ ≤ Lc * C ∧
      (ξ ∉ K → flowPull g a c t φ ξ = 0) := by
    intro t ht ξ
    obtain ⟨e1, e2⟩ := hexp t ht
    constructor
    · rw [flowPull, norm_flowValue]
      exact mul_le_mul e1 (hC _) (norm_nonneg _) (by positivity)
    · intro hξ
      have hn : |R₀| * Sg < ‖ξ‖ := by
        simpa [hK, Metric.mem_closedBall, dist_zero_right, not_le] using hξ
      have hz : φ (flowLin g a t ξ) = 0 := by
        apply hsupp
        rw [norm_flowLin]
        have h1 : 1 ≤ Real.exp (-(g * t)) * Sg := by
          have : Real.exp (-(g * t)) * Real.exp (g * t) = 1 := by rw [← Real.exp_add]; simp
          rw [← this]
          exact mul_le_mul_of_nonneg_left e2 (Real.exp_pos _).le
        have h2 : |R₀| ≤ Real.exp (-(g * t)) * (|R₀| * Sg) := by nlinarith [abs_nonneg R₀]
        have h3 : Real.exp (-(g * t)) * (|R₀| * Sg) < Real.exp (-(g * t)) * ‖ξ‖ :=
          mul_lt_mul_of_pos_left hn (Real.exp_pos _)
        linarith [le_abs_self R₀]
      rw [flowPull, hz, map_zero]
  have hHc : ∀ t, Continuous (H t) := fun t =>
    ((flowValue a c t).continuous.comp (hφc.comp (flowLin g a t).continuous)).sub
      ((flowValue a c t₀).continuous.comp (hφc.comp (flowLin g a t₀).continuous))
  have hL : Tendsto (fun t => ∫⁻ ξ, ‖H t ξ‖ₑ ^ (2 : ℝ)) (𝓝 t₀) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 t₀)
      (F := fun t ξ => ‖H t ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) (K.indicator fun _ => B)
      (Eventually.of_forall fun t => ((hHc t).measurable.enorm.pow_const _))
      ?_ ?_ ?_
    · simpa using this
    · have hball : {t : ℝ | |t - t₀| < 1} ∈ 𝓝 t₀ := by
        have := Metric.ball_mem_nhds t₀ one_pos
        simpa [Metric.ball, Real.dist_eq] using this
      filter_upwards [hball] with t ht
      refine Eventually.of_forall fun ξ => ?_
      have ht0 : |t₀ - t₀| < 1 := by simp
      by_cases hξ : ξ ∈ K
      · rw [Set.indicator_of_mem hξ]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖H t ξ‖ ≤ ‖flowPull g a c t φ ξ‖ + ‖flowPull g a c t₀ φ ξ‖ := norm_sub_le _ _
          _ ≤ Lc * C + Lc * C := add_le_add (hpull t ht ξ).1 (hpull t₀ ht0 ξ).1
          _ = 2 * Lc * C := by ring
      · simp [hH, (hpull t ht ξ).2 hξ, (hpull t₀ ht0 ξ).2 hξ]
    · rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun ξ => ?_
      have hcont : Continuous fun t : ℝ => H t ξ :=
        (continuous_flowValue a c (hφc.comp (continuous_flowLin g a ξ))).sub continuous_const
      have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp (hcont.tendsto t₀))
      simpa [hH, Function.comp_def] using this
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hev : (fun t => eLpNorm (⇑(flowOp g a c t G) - ⇑(flowOp g a c t₀ G)) 2 volume) =ᶠ[𝓝 t₀]
      fun t => (∫⁻ ξ, ‖H t ξ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    refine Eventually.of_forall fun t => ?_
    beta_reduce
    rw [eLpNorm_congr_ae ((hreal t).sub (hreal t₀)),
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp [hH]
  rw [tendsto_congr' hev]
  have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _).comp hL
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using this


theorem freqPow_two_eq (ξ : Space) : freqPow 2 ξ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
  unfold freqPow
  rw [Real.rpow_two, mul_pow]

theorem freqPow_two_mul (ξ : Space) : freqPow 2 ξ = freqPow 1 ξ * freqPow 1 ξ := by
  unfold freqPow
  rw [Real.rpow_two, Real.rpow_one, sq]

theorem continuous_freqPow_one : Continuous (freqPow 1) := by
  have : freqPow 1 = fun ξ : Space => 2 * π * ‖ξ‖ := by
    funext ξ; unfold freqPow; rw [Real.rpow_one]
  rw [this]
  exact continuous_const.mul continuous_norm

theorem contDiff_freqPow_two : ContDiff ℝ ∞ (freqPow 2) := by
  have : freqPow 2 = fun ξ : Space => (2 * π) ^ 2 * ‖ξ‖ ^ 2 := funext freqPow_two_eq
  rw [this]
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

theorem memLp_weight_pull {g a c t : ℝ} {h : Space → Freq.CSpace}
    (h1 : MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume) :
    MemLp (fun ξ => freqPow 1 ξ • flowPull g a c t h ξ) 2 volume := by
  set P : Freq.L2C := h1.toLp _
  refine (Lp.memLp (flowOp g a (c + g) t P)).ae_eq ?_
  have hcomp := Freq.Internal.Rotation.ae_comp (qmp_flowLin g a t) h1.coeFn_toLp
  filter_upwards [flowOp_ae g a (c + g) t P, hcomp] with ξ e1 e2
  rw [e1, flowPull, e2, flowPull]
  simp only [flowValue, ContinuousLinearMap.coe_smul', Pi.smul_apply, map_smul, smul_smul,
    freqPow_flowLin]
  congr 1
  have : Real.exp (g * t) * Real.exp (-(g * t) * 1) = 1 := by rw [← Real.exp_add]; simp
  rw [show (c + g) * t = c * t + g * t by ring, Real.exp_add]
  linear_combination (Real.exp (c * t) * freqPow 1 ξ) * this

theorem locallyIntegrable_weight_two {f : Space → Freq.CSpace}
    (hf : MemLp (fun ξ => freqPow 1 ξ • f ξ) 2 volume) :
    LocallyIntegrable (fun ξ => freqPow 2 ξ • f ξ) volume := by
  have := (hf.locallyIntegrable (by norm_num)).continuous_smul continuous_freqPow_one
  refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_smul, freqPow_two_mul]

end Internal.FlowPairing

open Internal.FlowPairing in
theorem flowPairing_of (hI : FlowIntegralStatement) (hC : FlowContinuityStatement) :
    FlowPairingStatement := by
  intro α hα1 hα2 a D h hD h1 h2 hw
  have hI' := hI α hα1 hα2 a D h hD h1 h2 hw
  have hα0 : 0 < α := by linarith
  set g : ℝ := 1 / (2 * α) with hg
  set c : ℝ := 1 - 2 / α with hc
  set Dl : Freq.L2C := hD.toLp D with hDl
  set Q : Freq.L2C := h2.toLp (fun ξ => freqPow (2 * α) ξ • h ξ) with hQ
  set E0 : ℝ := ∫ ξ, freqPow (2 * α) ξ * ‖h ξ‖ ^ 2 with hE0
  set lam : ℝ := 3 - 5 / (2 * α) with hlam
  have hint := integrable_weight hα1.le h1 h2
  have hgt : ∀ t : ℝ, -(g * t) * (2 * α) = -t := by
    intro t; rw [hg]; field_simp
  have hpt : ∀ t ξ, freqPow (2 * α) ξ * ‖flowPull g a c t h ξ‖ ^ 2 =
      Real.exp ((2 * c + 1) * t) *
        (freqPow (2 * α) (flowLin g a t ξ) * ‖h (flowLin g a t ξ)‖ ^ 2) := by
    intro t ξ
    rw [flowPull, norm_flowValue, freqPow_flowLin, hgt]
    have e1 : Real.exp ((2 * c + 1) * t) = Real.exp (c * t) ^ 2 * Real.exp t := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    have e2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    rw [e1]
    calc freqPow (2 * α) ξ * (Real.exp (c * t) * ‖h (flowLin g a t ξ)‖) ^ 2
        = Real.exp (c * t) ^ 2 * (Real.exp t * Real.exp (-t)) * freqPow (2 * α) ξ *
            ‖h (flowLin g a t ξ)‖ ^ 2 := by rw [e2]; ring
      _ = _ := by ring
  have hEt : ∀ t, ∫ ξ, freqPow (2 * α) ξ * ‖flowPull g a c t h ξ‖ ^ 2 = Real.exp (lam * t) * E0 := by
    intro t
    simp_rw [hpt t]
    rw [integral_const_mul]
    have := integral_flowLin g a t (fun η => freqPow (2 * α) η * ‖h η‖ ^ 2)
    rw [this, ← mul_assoc, ← Real.exp_add]
    congr 2
    rw [hc, hg, hlam]
    field_simp
    ring
  have hintt : ∀ t, Integrable (fun ξ => freqPow (2 * α) ξ * ‖flowPull g a c t h ξ‖ ^ 2) := by
    intro t
    simp_rw [hpt t]
    exact (integrable_flowLin (g := g) (a := a) (t := t) hint).const_mul _
  set G : ℝ → Freq.L2C := fun t => ∫ s in (0 : ℝ)..t, flowOp g a c s Dl with hG
  set W : ℝ → Freq.L2C := fun t => flowOp g a (c + 1) t Q + Q with hW
  have hWae : ∀ t, (W t : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => freqPow (2 * α) ξ • (flowPull g a c t h ξ + h ξ) := by
    intro t
    have hcomp := Freq.Internal.Rotation.ae_comp (qmp_flowLin g a t) h2.coeFn_toLp
    filter_upwards [Lp.coeFn_add (flowOp g a (c + 1) t Q) Q, flowOp_ae g a (c + 1) t Q,
      h2.coeFn_toLp, hcomp] with ξ e1 e2 e3 e4
    simp only [hW]
    rw [e1, Pi.add_apply, e2, e3, flowPull, e4]
    rw [ContinuousLinearMap.map_smul, flowValue_succ, smul_smul, freqPow_flowLin, hgt, smul_add,
      flowPull]
    congr 1
    congr 1
    have e5 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-t) * freqPow (2 * α) ξ * Real.exp t
        = (Real.exp (-t) * Real.exp t) * freqPow (2 * α) ξ := by ring
      _ = _ := by rw [e5, one_mul]
  have hdiff : ∀ t, inner ℝ (G t) (W t) = Real.exp (lam * t) * E0 - E0 := by
    intro t
    rw [L2.inner_def, ← hEt t, ← integral_sub (hintt t) hint]
    apply integral_congr_ae
    filter_upwards [hI' t, hWae t] with ξ e1 e2
    rw [e2]
    simp only [hG]
    rw [← e1, real_inner_smul_right, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm (flowPull g a c t h ξ) (h ξ)]
    ring
  have hGd : HasDerivAt G Dl 0 := by
    have := ((hC g a c Dl).integral_hasStrictDerivAt 0 0).hasDerivAt
    rwa [flowOp_zero] at this
  have hWt : Tendsto W (𝓝 0) (𝓝 (Q + Q)) := by
    have := ((hC g a (c + 1) Q).tendsto 0).add_const Q
    rwa [flowOp_zero] at this
  have hG0 : G 0 = 0 := by simp [hG]
  have hlim1 : Tendsto (fun t => inner ℝ (slope G 0 t) (W t)) (𝓝[≠] 0)
      (𝓝 (inner ℝ Dl (Q + Q))) :=
    (hasDerivAt_iff_tendsto_slope.mp hGd).inner (hWt.mono_left nhdsWithin_le_nhds)
  have hφ : HasDerivAt (fun t => Real.exp (lam * t) * E0 - E0) (lam * E0) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul lam).exp.mul_const E0).sub_const E0
    simpa using this
  have heq : ∀ t, inner ℝ (slope G 0 t) (W t) =
      slope (fun t => Real.exp (lam * t) * E0 - E0) 0 t := by
    intro t
    simp only [slope_def_module, hG0, sub_zero, real_inner_smul_left, hdiff,
      mul_zero, Real.exp_zero, one_mul, sub_self, smul_eq_mul]
  have huniq : inner ℝ Dl (Q + Q) = lam * E0 :=
    tendsto_nhds_unique (hlim1.congr heq) (hasDerivAt_iff_tendsto_slope.mp hφ)
  have hpair : inner ℝ Dl Q = ∫ ξ, inner ℝ (D ξ) (freqPow (2 * α) ξ • h ξ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hD.coeFn_toLp, h2.coeFn_toLp] with ξ e1 e2
    rw [e1, e2]
  rw [inner_add_right, hpair] at huniq
  have hconst : (3 / 2 - 5 / (4 * α)) = lam / 2 := by rw [hlam]; field_simp; ring
  rw [hconst]
  linear_combination huniq / 2


open Internal.FlowPairing in
theorem flowContinuity : FlowContinuityStatement := by
  intro g a c f
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set k : ℝ → ℝ := fun t => Real.exp ((c + 3 * g / 2) * t) with hk
  have hkc : Continuous k := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  set K := k t₀ + 1 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨G, ⟨φ, hGφ, hφs, hφd⟩, hfG⟩ :=
    (Lp.dense_hasCompactSupport_contDiff (E := Space) (F := Freq.CSpace) (μ := volume) (p := 2)
      ENNReal.ofNat_ne_top).exists_dist_lt f (show 0 < ε / (3 * K) by positivity)
  have hsm := tendsto_flowOp_of_compact g a c t₀ hφd.continuous hφs hGφ
  have hbound : ∀ t, k t ≤ K → dist (flowOp g a c t f) (flowOp g a c t G) < ε / 3 := by
    intro t hkt
    rw [dist_eq_norm, ← map_sub, norm_flowOp, ← dist_eq_norm]
    calc k t * dist f G ≤ K * dist f G := by gcongr
      _ < K * (ε / (3 * K)) := by gcongr
      _ = ε / 3 := by field_simp
  filter_upwards [hkc.continuousAt.eventually_lt continuousAt_const (lt_add_one (k t₀)),
    Metric.tendsto_nhds.1 hsm (ε / 3) (by positivity)] with t hkt hcG
  calc dist (flowOp g a c t f) (flowOp g a c t₀ f)
      ≤ dist (flowOp g a c t f) (flowOp g a c t G) + dist (flowOp g a c t G) (flowOp g a c t₀ G) +
        dist (flowOp g a c t₀ G) (flowOp g a c t₀ f) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hbound t hkt.le
      · rw [dist_comm]; exact hbound t₀ (by rw [hK]; linarith)
    _ = ε := by ring

theorem flowPairing_of_integral (hI : FlowIntegralStatement) : FlowPairingStatement :=
  flowPairing_of hI flowContinuity

def FlowTestStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (D h : Space → Freq.CSpace) (hD : MemLp D 2 volume),
    MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume → MemLp (fun ξ => freqPow (2 * α) ξ • h ξ) 2 volume →
    (∀ ψ : Space → Freq.CSpace, IsFreqTest ψ →
      ∫ ξ, inner ℝ (D ξ) (ψ ξ) = ∫ ξ, inner ℝ (h ξ) (flowAdjoint α a ψ ξ)) →
    ∀ ψ : Space → Freq.CSpace, IsFreqTest ψ → ∀ t : ℝ,
      ∫ ξ, inner ℝ (flowPull (1 / (2 * α)) a (1 - 2 / α) t h ξ - h ξ) (ψ ξ) =
        ∫ ξ, inner ℝ (((∫ s in (0 : ℝ)..t, flowOp (1 / (2 * α)) a (1 - 2 / α) s (hD.toLp D) :
          Freq.L2C) : Space → Freq.CSpace) ξ) (ψ ξ)

open Internal.FlowPairing in
theorem flowIntegral_of_test (hT : FlowTestStatement) : FlowIntegralStatement := by
  intro α hα1 hα2 a D h hD h1 h2 hw t
  have hT' := hT α hα1 hα2 a D h hD h1 h2 hw
  set g : ℝ := 1 / (2 * α) with hg
  set c : ℝ := 1 - 2 / α with hc
  set Gt : Freq.L2C := ∫ s in (0 : ℝ)..t, flowOp g a c s (hD.toLp D) with hGt
  have hp1 := memLp_weight_pull (g := g) (a := a) (c := c) (t := t) h1
  set Y : Space → Freq.CSpace := fun ξ => freqPow 2 ξ • (flowPull g a c t h ξ - h ξ) with hY
  have hYl : LocallyIntegrable Y volume := by
    have := (locallyIntegrable_weight_two hp1).sub (locallyIntegrable_weight_two h1)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hY, Pi.sub_apply, smul_sub]
  have hGl : LocallyIntegrable (fun ξ => freqPow 2 ξ • (Gt : Space → Freq.CSpace) ξ) volume :=
    ((Lp.memLp Gt).locallyIntegrable (by norm_num)).continuous_smul contDiff_freqPow_two.continuous
  set F2 : Space → Freq.CSpace := fun ξ => Y ξ - freqPow 2 ξ • (Gt : Space → Freq.CSpace) ξ with hF2
  have hFl : LocallyIntegrable F2 volume := hYl.sub hGl
  have hU : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hFl.locallyIntegrableOn _) ?_
  · filter_upwards [hzero, Internal.DriftPower.ae_ne_zero] with ξ e1 e2
    have e3 := e1 e2
    have hk : freqPow 2 ξ ≠ 0 := by
      rw [freqPow_two_eq]; have := norm_pos_iff.2 e2; positivity
    simp only [hF2, hY, ← smul_sub] at e3
    have := (smul_eq_zero.1 e3).resolve_left hk
    exact sub_eq_zero.1 this
  · intro φ hφd hφs hφU
    have hi1 : Integrable (fun ξ => φ ξ • Y ξ) volume :=
      hYl.integrable_smul_left_of_hasCompactSupport hφd.continuous hφs
    have hi2 : Integrable (fun ξ => φ ξ • (freqPow 2 ξ • (Gt : Space → Freq.CSpace) ξ)) volume :=
      hGl.integrable_smul_left_of_hasCompactSupport hφd.continuous hφs
    have key : ∀ e : Freq.CSpace, inner ℝ e (∫ ξ, φ ξ • F2 ξ) = 0 := by
      intro e
      set ψ : Space → Freq.CSpace := fun ξ => (φ ξ * freqPow 2 ξ) • e with hψ
      have hψt : IsFreqTest ψ := by
        refine ⟨(hφd.mul contDiff_freqPow_two).smul contDiff_const, ?_, ?_⟩
        · exact (hφs.mul_right (f' := freqPow 2)).smul_right (f' := fun _ => e)
        · intro h0
          have := (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left) h0
          exact hφU this rfl
      have hsplit : ∫ ξ, φ ξ • F2 ξ = (∫ ξ, φ ξ • Y ξ) -
          ∫ ξ, φ ξ • (freqPow 2 ξ • (Gt : Space → Freq.CSpace) ξ) := by
        rw [← integral_sub hi1 hi2]
        simp only [hF2, smul_sub]
      have c1 := (innerSL ℝ e).integral_comp_comm hi1
      have c2 := (innerSL ℝ e).integral_comp_comm hi2
      simp only [innerSL_apply_apply] at c1 c2
      rw [hsplit, inner_sub_right, ← c1, ← c2]
      have p1 : ∀ ξ, inner ℝ e (φ ξ • Y ξ) = inner ℝ (flowPull g a c t h ξ - h ξ) (ψ ξ) := by
        intro ξ
        simp only [hY, hψ]
        rw [real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm]
        ring
      have p2 : ∀ ξ, inner ℝ e (φ ξ • (freqPow 2 ξ • (Gt : Space → Freq.CSpace) ξ)) =
          inner ℝ ((Gt : Space → Freq.CSpace) ξ) (ψ ξ) := by
        intro ξ
        simp only [hψ]
        rw [real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm]
        ring
      simp_rw [p1, p2]
      rw [hT' ψ hψt t, sub_self]
    exact inner_self_eq_zero.1 (key _)

theorem flowPairing_of_test (hT : FlowTestStatement) : FlowPairingStatement :=
  flowPairing_of_integral (flowIntegral_of_test hT)


namespace Internal.FlowPairing

theorem real_inner_rotC (R : Space ≃ₗᵢ[ℝ] Space) (w z : Freq.CSpace) :
    inner ℝ (Freq.rotC R w) z = inner ℝ w (Freq.rotC R.symm z) := by
  have hc := congrArg Complex.re (Freq.Internal.Rotation.rotC_inner R w z)
  have e1 := real_inner_eq_re_inner ℂ (Freq.rotC R w) z
  have e2 := real_inner_eq_re_inner ℂ w (Freq.rotC R.symm z)
  simp only [RCLike.re_to_complex] at e1 e2
  exact e1.trans (hc.trans e2.symm)

theorem flowLin_inv (g a t : ℝ) (ξ : Space) : flowLin (-g) (-a) t (flowLin g a t ξ) = ξ := by
  rw [flowLin_apply, flowLin_apply, LinearIsometryEquiv.map_smul, smul_smul, ← Real.exp_add,
    ← axialRotationSpec.2.2.1]
  have e1 : -(-g * t) + -(g * t) = 0 := by ring
  have e2 : -a * t + a * t = 0 := by ring
  rw [e1, e2, axialRotationSpec.2.1]
  simp

theorem integral_inner_flowPull (g a c t : ℝ) (f ψ : Space → Freq.CSpace) :
    ∫ ξ, inner ℝ (flowPull g a c t f ξ) (ψ ξ) =
      ∫ ξ, inner ℝ (f ξ) (flowPull (-g) (-a) (c + 3 * g) t ψ ξ) := by
  set H : Space → ℝ := fun η => inner ℝ (f η)
    (Freq.rotC (axialRotation (a * t)) (ψ (flowLin (-g) (-a) t η))) with hH
  have e1 : ∀ ξ, inner ℝ (flowPull g a c t f ξ) (ψ ξ) = Real.exp (c * t) * H (flowLin g a t ξ) := by
    intro ξ
    simp only [hH, flowPull, flowValue, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      real_inner_smul_left, flowLin_inv]
    rw [real_inner_rotC, axialRotationSpec.2.2.2.1, neg_neg]
  have e2 : ∀ η, inner ℝ (f η) (flowPull (-g) (-a) (c + 3 * g) t ψ η) =
      Real.exp ((c + 3 * g) * t) * H η := by
    intro η
    simp only [hH, flowPull, flowValue, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      real_inner_smul_right]
    rw [show -(-a * t) = a * t by ring]
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul, integral_flowLin, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem continuous_invWeight {ψ : Space → Freq.CSpace} (hψ : IsFreqTest ψ) :
    Continuous fun ξ => (freqPow 1 ξ)⁻¹ • ψ ξ := by
  have hev : ∀ᶠ ξ in 𝓝 (0 : Space), ψ ξ = 0 := by
    have := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hψ.2.2
    filter_upwards [this] with ξ hξ
    exact image_eq_zero_of_notMem_tsupport hξ
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have : (fun ξ => (freqPow 1 ξ)⁻¹ • ψ ξ) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hev] with ξ hξ
      simp [hξ]
    rw [continuousAt_congr this]
    exact continuousAt_const
  · have hne : freqPow 1 x ≠ 0 := by
      unfold freqPow; rw [Real.rpow_one]; have := norm_pos_iff.2 hx; positivity
    exact (continuous_freqPow_one.continuousAt.inv₀ hne).smul hψ.1.continuous.continuousAt

theorem integrable_inner_test {f : Space → Freq.CSpace}
    (hf : MemLp (fun ξ => freqPow 1 ξ • f ξ) 2 volume) {ψ : Space → Freq.CSpace}
    (hψ : IsFreqTest ψ) : Integrable (fun ξ => inner ℝ (f ξ) (ψ ξ)) := by
  have hψ1 : MemLp (fun ξ => (freqPow 1 ξ)⁻¹ • ψ ξ) 2 volume :=
    (continuous_invWeight hψ).memLp_of_hasCompactSupport
      (hψ.2.1.smul_left (f := fun ξ => (freqPow 1 ξ)⁻¹))
  have := L2.integrable_inner (𝕜 := ℝ) (hf.toLp _) (hψ1.toLp _)
  refine this.congr ?_
  filter_upwards [hf.coeFn_toLp, hψ1.coeFn_toLp, Internal.DriftPower.ae_ne_zero] with ξ e1 e2 e3
  rw [e1, e2]
  have hne : freqPow 1 ξ ≠ 0 := by
    unfold freqPow; rw [Real.rpow_one]; have := norm_pos_iff.2 e3; positivity
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem isFreqTest_flowPull (g a c t : ℝ) {ψ : Space → Freq.CSpace} (hψ : IsFreqTest ψ) :
    IsFreqTest (flowPull g a c t ψ) := by
  refine ⟨(flowValue a c t).contDiff.comp (hψ.1.comp (flowLin g a t).contDiff), ?_, ?_⟩
  · exact (hψ.2.1.comp_homeomorph (flowLin g a t).toHomeomorph).comp_left
      (map_zero (flowValue a c t))
  · rw [notMem_tsupport_iff_eventuallyEq]
    have h0 := notMem_tsupport_iff_eventuallyEq.1 hψ.2.2
    have hM : Tendsto (fun ξ => flowLin g a t ξ) (𝓝 0) (𝓝 0) := by
      have := (flowLin g a t).continuous.tendsto 0
      rwa [map_zero] at this
    filter_upwards [hM.eventually h0] with ξ hξ
    simp only [flowPull, Pi.zero_apply] at hξ ⊢
    rw [hξ, map_zero]

end Internal.FlowPairing

def flowPush (α a s : ℝ) (ψ : Space → Freq.CSpace) : Space → Freq.CSpace :=
  flowPull (-(1 / (2 * α))) (-a) (1 - 1 / (2 * α)) s ψ

def FlowDerivStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (h : Space → Freq.CSpace),
    MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume → ∀ ψ : Space → Freq.CSpace, IsFreqTest ψ →
    ∀ s, HasDerivAt (fun s => ∫ ξ, inner ℝ (h ξ) (flowPush α a s ψ ξ))
      (∫ ξ, inner ℝ (h ξ) (flowAdjoint α a (flowPush α a s ψ) ξ)) s

open Internal.FlowPairing in
theorem flowTest_of_deriv (hV : FlowDerivStatement) : FlowTestStatement := by
  intro α hα1 hα2 a D h hD h1 h2 hw ψ hψ t
  have hα0 : 0 < α := by linarith
  have hder := hV α hα1 hα2 a h h1 ψ hψ
  have hpt : ∀ s, IsFreqTest (flowPush α a s ψ) := fun s => isFreqTest_flowPull _ _ _ s hψ
  set g : ℝ := 1 / (2 * α) with hg
  set c : ℝ := 1 - 2 / α with hc
  set Dl : Freq.L2C := hD.toLp D with hDl
  have hψ2 : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  set Ψ : Freq.L2C := hψ2.toLp ψ with hΨ
  have hconst : c + 3 * g = 1 - 1 / (2 * α) := by rw [hc, hg]; field_simp; ring
  have hadj : ∀ s (f : Space → Freq.CSpace), ∫ ξ, inner ℝ (flowPull g a c s f ξ) (ψ ξ) =
      ∫ ξ, inner ℝ (f ξ) (flowPush α a s ψ ξ) := by
    intro s f
    rw [integral_inner_flowPull, hconst]
    rfl
  have hDs : ∀ s, ∫ ξ, inner ℝ (h ξ) (flowAdjoint α a (flowPush α a s ψ) ξ) =
      inner ℝ (flowOp g a c s Dl) Ψ := by
    intro s
    rw [← hw _ (hpt s), ← hadj, L2.inner_def]
    apply integral_congr_ae
    have hcomp := Freq.Internal.Rotation.ae_comp (qmp_flowLin g a s) hD.coeFn_toLp
    filter_upwards [flowOp_ae g a c s Dl, hΨ ▸ hψ2.coeFn_toLp, hcomp] with ξ e1 e2 e3
    rw [e1, e2, flowPull, flowPull, e3]
  have hcontF : Continuous fun s => inner ℝ (flowOp g a c s Dl) Ψ :=
    (flowContinuity g a c Dl).inner continuous_const
  have hpush0 : flowPush α a 0 ψ = ψ := by
    funext ξ
    simp [flowPush, flowPull, flowValue, flowLin_apply, axialRotationSpec.2.1, rotC_refl]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => ∫ ξ, inner ℝ (h ξ) (flowPush α a s ψ ξ))
    (f' := fun s => inner ℝ (flowOp g a c s Dl) Ψ) (a := 0) (b := t)
    (fun s _ => by rw [← hDs s]; exact hder s) (hcontF.intervalIntegrable 0 t)
  have hp1 := memLp_weight_pull (g := g) (a := a) (c := c) (t := t) h1
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ξ => inner_sub_left _ _ _),
    integral_sub (integrable_inner_test hp1 hψ) (integrable_inner_test h1 hψ), hadj t h]
  have hh0 : ∫ ξ, inner ℝ (h ξ) (ψ ξ) = ∫ ξ, inner ℝ (h ξ) (flowPush α a 0 ψ ξ) := by
    rw [hpush0]
  rw [hh0]
  rw [← hFTC]
  have hcomm := (innerSL ℝ Ψ).intervalIntegral_comp_comm
    (((flowContinuity g a c Dl).intervalIntegrable 0 t) : IntervalIntegrable (fun s => flowOp g a c s Dl) volume 0 t)
  simp only [innerSL_apply_apply] at hcomm
  have hG : ∫ ξ, inner ℝ (((∫ s in (0 : ℝ)..t, flowOp g a c s Dl : Freq.L2C) : Space → Freq.CSpace) ξ)
      (ψ ξ) = inner ℝ (∫ s in (0 : ℝ)..t, flowOp g a c s Dl) Ψ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΨ ▸ hψ2.coeFn_toLp] with ξ e
    rw [e]
  rw [hG, real_inner_comm, ← hcomm]
  congr 1
  funext s
  rw [real_inner_comm]

theorem flowPairing_of_deriv (hV : FlowDerivStatement) : FlowPairingStatement :=
  flowPairing_of_test (flowTest_of_deriv hV)

end SteadyCert

end Breakdown

import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.SliceFields

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.SupBound

open Internal.SliceFields

theorem sub_le_of_identity {y h g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hid : ∀ a b, a ≤ b → y b - y a = c * ∫ σ in a..b, h σ)
    (hhg : ∀ᵐ σ, h σ ≤ g σ) (hg0 : ∀ σ, 0 ≤ g σ) (hgi : ∀ a b, IntervalIntegrable g volume a b)
    {b s e : ℝ} (hbs : b ≤ s) (hse : s ≤ e) : y s - y b ≤ c * ∫ σ in b..e, g σ := by
  rw [hid b s hbs]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h1 : ∫ σ in b..s, h σ ≤ ∫ σ in b..s, g σ := by
    by_cases hi : IntervalIntegrable h volume b s
    · exact intervalIntegral.integral_mono_ae hbs hi (hgi b s) hhg
    · rw [intervalIntegral.integral_undef hi]
      exact intervalIntegral.integral_nonneg hbs fun x _ => hg0 x
  exact h1.trans (intervalIntegral.integral_mono_interval le_rfl hbs hse
    (ae_of_all _ fun x => hg0 x) (hgi b e))

theorem le_of_identity {y h g : ℝ → ℝ} {c : ℝ} {N : ℕ} (hN : N = 1 ∨ N = 2) (hc : 0 ≤ c)
    (hy : Continuous y) (hper : ∀ σ, y (σ + 1) = y σ) (hhalf : N = 2 → ∀ σ, y (σ + 1 / 2) = y σ)
    (hid : ∀ a b, a ≤ b → y b - y a = c * ∫ σ in a..b, h σ)
    (hhg : ∀ᵐ σ, h σ ≤ g σ) (hg0 : ∀ σ, 0 ≤ g σ) (hgper : ∀ σ, g (σ + 1) = g σ)
    (hgi : IntervalIntegrable g volume 0 1) (σ : ℝ) :
    y σ ≤ (∫ s in (0 : ℝ)..1, y s) + c / N * ∫ s in (0 : ℝ)..1, g s := by
  have hgp : Function.Periodic g 1 := hgper
  have hgi' : ∀ a b, IntervalIntegrable g volume a b := fun a b =>
    hgp.intervalIntegrable one_ne_zero (t := 0) (by simpa using hgi) a b
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ))
    hy.continuousOn
  have hmean : y a ≤ ∫ s in (0 : ℝ)..1, y s := by
    have := intervalIntegral.integral_mono_on (μ := volume) (zero_le_one' ℝ) intervalIntegrable_const
      (hy.intervalIntegrable 0 1) fun x hx => (hmin hx : y a ≤ y x)
    simpa using this
  have hfull : ∫ s in a..a + 1, g s = ∫ s in (0 : ℝ)..1, g s := by
    simpa using hgp.intervalIntegral_add_eq a 0
  have K := fun {b s e : ℝ} (h1 : b ≤ s) (h2 : s ≤ e) =>
    sub_le_of_identity (y := y) hc hid hhg hg0 hgi' h1 h2
  rcases hN with rfl | rfl
  · have hyp : Function.Periodic y 1 := hper
    set s := toIcoMod one_pos a σ with hs
    have hmem := toIcoMod_mem_Ico one_pos a σ
    have hys : y s = y σ := by
      rw [hs, toIcoMod]
      exact hyp.sub_zsmul_eq _
    have := K hmem.1 hmem.2.le
    rw [hys, hfull] at this
    simp only [Nat.cast_one, div_one]
    linarith
  · have hyp : Function.Periodic y (1 / 2) := hhalf rfl
    have h2 : (0 : ℝ) < 1 / 2 := by norm_num
    set s := toIcoMod h2 a σ with hs
    have hmem := toIcoMod_mem_Ico h2 a σ
    have hys : y s = y σ := by
      rw [hs, toIcoMod]
      exact hyp.sub_zsmul_eq _
    have e1 := K hmem.1 hmem.2.le
    have e2 := K (b := a + 1 / 2) (s := s + 1 / 2) (e := a + 1) (by linarith [hmem.1])
      (by linarith [hmem.2])
    rw [hyp s, hys, hyp a] at e2
    rw [hys] at e1
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi' a (a + 1 / 2))
      (hgi' (a + 1 / 2) (a + 1))
    rw [hfull] at hsplit
    have : (c * ∫ s in a..a + 1 / 2, g s) + (c * ∫ s in a + 1 / 2..a + 1, g s) =
        c * ∫ s in (0 : ℝ)..1, g s := by rw [← mul_add, hsplit]
    have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hcast]
    have : c / 2 * ∫ s in (0 : ℝ)..1, g s = (c * ∫ s in (0 : ℝ)..1, g s) / 2 := by ring
    linarith


theorem integral_norm_sq_eq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (F : Lp E 2 μ) :
    ∫ t, ‖F t‖ ^ 2 ∂μ = ‖F‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext t
  exact (real_inner_self_eq_norm_sq _).symm

theorem integrable_norm_mul {α E E' : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup E'] (F : Lp E 2 μ) (G : Lp E' 2 μ) :
    Integrable (fun t => ‖F t‖ * ‖G t‖) μ := by
  refine Integrable.mono' (((Lp.memLp F).integrable_norm_pow two_ne_zero).add
    ((Lp.memLp G).integrable_norm_pow two_ne_zero))
    ((Lp.aestronglyMeasurable F).norm.mul (Lp.aestronglyMeasurable G).norm) (ae_of_all _ fun t => ?_)
  show ‖‖F t‖ * ‖G t‖‖ ≤ ‖F t‖ ^ 2 + ‖G t‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [sq_nonneg (‖F t‖ - ‖G t‖), norm_nonneg (F t), norm_nonneg (G t)]

theorem rpow_integral_eq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (F : Lp E 2 μ) :
    (∫ t, ‖F t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖F‖ := by
  simp_rw [Real.rpow_two]
  rw [integral_norm_sq_eq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

theorem integral_norm_mul_le {α E E' : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (F : Lp E 2 μ) (G : Lp E' 2 μ) :
    ∫ t, ‖F t‖ * ‖G t‖ ∂μ ≤ ‖F‖ * ‖G‖ := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hF : MemLp (fun t => ‖F t‖) (ENNReal.ofReal 2) μ := by rw [h2]; exact (Lp.memLp F).norm
  have hG : MemLp (fun t => ‖G t‖) (ENNReal.ofReal 2) μ := by rw [h2]; exact (Lp.memLp G).norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun t => norm_nonneg (F t)) (ae_of_all _ fun t => norm_nonneg (G t)) hF hG
  rwa [rpow_integral_eq, rpow_integral_eq] at this

theorem integrable_weighted {w : Space → ℝ} {C : ℝ} (hw : Measurable w) (h0 : ∀ y, 0 ≤ w y)
    (hC : ∀ y, w y ≤ C) (F : L2R) : Integrable (fun y => w y * ‖(F : Space → Space) y‖ ^ 2) volume := by
  refine Integrable.mono' ((integrable_norm_sq_L2R F).const_mul C)
    (hw.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable F).norm.pow 2)) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 y) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hC y) (sq_nonneg _)

theorem weighted_sub_le {w : Space → ℝ} {C : ℝ} (hw : Measurable w) (h0 : ∀ y, 0 ≤ w y)
    (hC : ∀ y, w y ≤ C) (F G : L2R) :
    |(∫ y, w y * ‖(F : Space → Space) y‖ ^ 2) - ∫ y, w y * ‖(G : Space → Space) y‖ ^ 2| ≤
      C * (‖F - G‖ * ‖F‖ + ‖F - G‖ * ‖G‖) := by
  have hC0 : 0 ≤ C := (h0 0).trans (hC 0)
  rw [← integral_sub (integrable_weighted hw h0 hC F) (integrable_weighted hw h0 hC G)]
  refine abs_integral_le_integral_abs.trans ?_
  have hi := ((integrable_norm_mul (F - G) F).add (integrable_norm_mul (F - G) G)).const_mul C
  refine (integral_mono_ae (integrable_weighted hw h0 hC F |>.sub
    (integrable_weighted hw h0 hC G)).abs hi ?_).trans ?_
  · filter_upwards [Lp.coeFn_sub F G] with y hy
    show |w y * ‖F y‖ ^ 2 - w y * ‖G y‖ ^ 2| ≤ C * (‖(F - G) y‖ * ‖F y‖ + ‖(F - G) y‖ * ‖G y‖)
    rw [hy, Pi.sub_apply, ← mul_sub, abs_mul, abs_of_nonneg (h0 y)]
    have e : ‖F y‖ ^ 2 - ‖G y‖ ^ 2 = (‖F y‖ - ‖G y‖) * (‖F y‖ + ‖G y‖) := by ring
    have h1 : |‖F y‖ ^ 2 - ‖G y‖ ^ 2| ≤ ‖F y - G y‖ * ‖F y‖ + ‖F y - G y‖ * ‖G y‖ := by
      rw [e, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← mul_add]
      exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    exact mul_le_mul (hC y) h1 (abs_nonneg _) hC0
  · rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add (integrable_norm_mul (F - G) F) (integrable_norm_mul (F - G) G)]
    exact mul_le_mul_of_nonneg_left (add_le_add (integral_norm_mul_le _ _) (integral_norm_mul_le _ _)) hC0

theorem continuous_weighted {w : Space → ℝ} {C : ℝ} (hw : Measurable w) (h0 : ∀ y, 0 ≤ w y)
    (hC : ∀ y, w y ≤ C) : Continuous fun F : L2R => ∫ y, w y * ‖(F : Space → Space) y‖ ^ 2 := by
  refine continuous_iff_continuousAt.2 fun F => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun G => ?_) (g := fun G : L2R => C * (‖G - F‖ * ‖G‖ + ‖G - F‖ * ‖F‖)) ?_
  · rw [Real.norm_eq_abs]
    exact weighted_sub_le hw h0 hC G F
  · have : Continuous fun G : L2R => C * (‖G - F‖ * ‖G‖ + ‖G - F‖ * ‖F‖) := by fun_prop
    simpa using this.tendsto F

theorem sliceWeightedGrad_eq {w : Space → ℝ} {C : ℝ} (hw : Measurable w) (h0 : ∀ y, 0 ≤ w y)
    (hC : ∀ y, w y ≤ C) (h : Freq.X) :
    sliceWeightedGrad w h = ∑ j : Fin 3, ∫ y, w y * ‖(Freq.partialX j h : Space → Space) y‖ ^ 2 := by
  unfold sliceWeightedGrad
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ fun j _ => integrable_weighted hw h0 hC _

theorem continuous_sliceWeightedGrad {w : Space → ℝ} {C : ℝ} (hw : Measurable w) (h0 : ∀ y, 0 ≤ w y)
    (hC : ∀ y, w y ≤ C) : Continuous (sliceWeightedGrad w) := by
  have : sliceWeightedGrad w = fun h : Freq.X =>
      ∑ j : Fin 3, ∫ y, w y * ‖(Freq.partialX j h : Space → Space) y‖ ^ 2 :=
    funext (sliceWeightedGrad_eq hw h0 hC)
  rw [this]
  exact continuous_finsetSum _ fun j _ => (continuous_weighted hw h0 hC).comp (Freq.partialX j).continuous

theorem sliceWeightedGrad_ge {w : Space → ℝ} {C w₀ : ℝ} (hw : Measurable w) (hl : ∀ y, w₀ ≤ w y)
    (h0 : ∀ y, 0 ≤ w y) (hC : ∀ y, w y ≤ C) (h : Freq.X) :
    w₀ * ‖h‖ ^ 2 ≤ sliceWeightedGrad w h := by
  rw [sliceWeightedGrad_eq hw h0 hC, ← sum_norm_partialX_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← integral_norm_sq_L2R, ← integral_const_mul]
  exact integral_mono ((integrable_norm_sq_L2R _).const_mul w₀) (integrable_weighted hw h0 hC _)
    fun y => mul_le_mul_of_nonneg_right (hl y) (sq_nonneg _)

theorem sliceWeightedGrad_le {w : Space → ℝ} {C : ℝ} (hw : Measurable w)
    (h0 : ∀ y, 0 ≤ w y) (hC : ∀ y, w y ≤ C) (h : Freq.X) :
    sliceWeightedGrad w h ≤ C * ‖h‖ ^ 2 := by
  rw [sliceWeightedGrad_eq hw h0 hC, ← sum_norm_partialX_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← integral_norm_sq_L2R, ← integral_const_mul]
  exact integral_mono (integrable_weighted hw h0 hC _) ((integrable_norm_sq_L2R _).const_mul C)
    fun y => mul_le_mul_of_nonneg_right (hC y) (sq_nonneg _)

theorem supGrad_bound (u : XX) (y : ℝ → ℝ) (M : ℝ)
    (hy : ∀ᵐ σ : ℝ, y σ = ‖gradPart (sliceOf u (σ : TimeCircle))‖ ^ 2) (hM : ∀ σ, y σ ≤ M) :
    supGrad u < ⊤ ∧ (supGrad u).toReal ^ 2 ≤ M := by
  have hae : ∀ᵐ t : TimeCircle, ‖gradPart ((u : TimeCircle → XBar) t)‖ ≤ Real.sqrt M := by
    rw [ae_coe_iff]
    filter_upwards [hy] with σ hσ
    have hσ' : y σ = ‖gradPart ((u : TimeCircle → XBar) σ)‖ ^ 2 := hσ
    rw [← Real.sqrt_sq (norm_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    rw [← hσ']
    exact hM σ
  have hle : supGrad u ≤ ENNReal.ofReal (Real.sqrt M) := by
    unfold supGrad
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hae
  have hM0 : 0 ≤ M := by
    obtain ⟨σ, hσ⟩ := hy.exists
    have := hM σ
    rw [hσ] at this
    exact (sq_nonneg _).trans this
  refine ⟨hle.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  have := ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) hle
  calc (supGrad u).toReal ^ 2 ≤ Real.sqrt M ^ 2 := pow_le_pow_left₀ ENNReal.toReal_nonneg this 2
    _ = M := Real.sq_sqrt hM0


set_option maxHeartbeats 1000000 in
theorem half_periodic (u : XX) (Γ : Set Symmetry) (Q : Space ≃ₗᵢ[ℝ] Space)
    (hQ : (Q, (1 / 2 : ℝ)) ∈ Γ) (hu : IsInvariantXX Γ u) (y : ℝ → ℝ) (hyc : Continuous y)
    (hy : ∀ᵐ σ : ℝ, y σ = ‖gradPart (sliceOf u (σ : TimeCircle))‖ ^ 2) :
    ∀ σ, y (σ + 1 / 2) = y σ := by
  have hGd : (gradCLM u : TimeCircle → Freq.X) =ᵐ[volume] fun t => gradPart (sliceOf u t) :=
    ContinuousLinearMap.coeFn_compLpL gradPart u
  have hm := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hu (Q, (1 / 2 : ℝ))) hQ
  rw [LinearMap.mem_ker] at hm
  have heq : shiftLp (1 / 2 : ℝ) (gradCLM u) = rotHH Q (gradCLM u) := by
    have : shiftLp (1 / 2 : ℝ) (gradCLM u) - rotHH Q (gradCLM u) = 0 := hm
    exact sub_eq_zero.1 this
  have hmp := measurePreserving_add_right (volume : Measure TimeCircle) ((1 / 2 : ℝ) : TimeCircle)
  have hsh : (shiftLp (1 / 2 : ℝ) (gradCLM u) : TimeCircle → Freq.X) =ᵐ[volume]
      fun t => (gradCLM u : TimeCircle → Freq.X) (t + ((1 / 2 : ℝ) : TimeCircle)) :=
    Lp.coeFn_compMeasurePreserving (gradCLM u) hmp
  have hrot : (rotHH Q (gradCLM u) : TimeCircle → Freq.X) =ᵐ[volume]
      fun t => rotX Q ((gradCLM u : TimeCircle → Freq.X) t) :=
    ContinuousLinearMap.coeFn_compLpL _ (gradCLM u)
  have hGd' : ∀ᵐ t : TimeCircle, (gradCLM u : TimeCircle → Freq.X) (t + ((1 / 2 : ℝ) : TimeCircle)) =
      gradPart (sliceOf u (t + ((1 / 2 : ℝ) : TimeCircle))) :=
    hmp.quasiMeasurePreserving.ae (p := fun t => (gradCLM u : TimeCircle → Freq.X) t = gradPart (sliceOf u t)) hGd
  have hcirc : ∀ᵐ t : TimeCircle, ‖gradPart (sliceOf u (t + ((1 / 2 : ℝ) : TimeCircle)))‖ =
      ‖gradPart (sliceOf u t)‖ := by
    filter_upwards [hsh, hrot, hGd, hGd'] with t a b c e
    have h3 : (shiftLp (1 / 2 : ℝ) (gradCLM u) : TimeCircle → Freq.X) t =
        (rotHH Q (gradCLM u) : TimeCircle → Freq.X) t :=
      congrFun (congrArg (fun F : HH => (F : TimeCircle → Freq.X)) heq) t
    have h5 : ‖rotX Q ((gradCLM u : TimeCircle → Freq.X) t)‖ = ‖(gradCLM u : TimeCircle → Freq.X) t‖ :=
      LinearIsometryEquiv.norm_map _ _
    exact (congrArg norm e.symm).trans ((congrArg norm (a.symm.trans (h3.trans b))).trans
      (h5.trans (congrArg norm c)))
  rw [ae_coe_iff] at hcirc
  have hmpR := measurePreserving_add_right (volume : Measure ℝ) (1 / 2 : ℝ)
  have hy' : ∀ᵐ σ : ℝ, y (σ + 1 / 2) = ‖gradPart (sliceOf u ((σ + 1 / 2 : ℝ) : TimeCircle))‖ ^ 2 :=
    hmpR.quasiMeasurePreserving.ae (p := fun σ => y σ = ‖gradPart (sliceOf u (σ : TimeCircle))‖ ^ 2) hy
  have hae : (fun σ => y (σ + 1 / 2)) =ᵐ[volume] y := by
    filter_upwards [hy, hy', hcirc] with σ a b c
    have hc : ((σ + 1 / 2 : ℝ) : TimeCircle) = (σ : TimeCircle) + ((1 / 2 : ℝ) : TimeCircle) := rfl
    rw [b, a, hc]
    exact congrArg (· ^ 2) c
  have hcont : Continuous fun σ => y (σ + 1 / 2) := hyc.comp (continuous_add_const _)
  exact congrFun ((hcont.ae_eq_iff_eq volume hyc).1 hae)

set_option maxHeartbeats 1000000 in
theorem core_bound {N : ℕ} (hN : N = 1 ∨ N = 2) {P w₀ Wm fb Ab vn : ℝ} (hP : 0 < P) (hw0 : 0 < w₀)
    {w : Space → ℝ} (hwm : Measurable w) (hwl : ∀ y, w₀ ≤ w y) (hwu : ∀ y, w y ≤ Wm) (hfb : 0 ≤ fb)
    (u : XX) (f B A C : HH) (cv : TimeCircle → HBar) (y : ℝ → ℝ)
    (hyc : Continuous y) (hyper : ∀ σ, y (σ + 1) = y σ)
    (hyae : ∀ᵐ σ : ℝ, y σ = ‖gradPart (sliceOf u (σ : TimeCircle))‖ ^ 2)
    (hid : ∀ a b, a ≤ b → (1 / (2 * P)) * (y b - y a) =
      ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf u (σ : TimeCircle)))
        - ‖secondPart (sliceOf u (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * y σ))
    (hhalf : N = 2 → ∀ σ, y (σ + 1 / 2) = y σ)
    (hbr : ∀ᵐ t : TimeCircle, -fb * (‖secondPart (sliceOf u t)‖ ^ 2
        + sliceWeightedGrad w (gradPart (sliceOf u t))) ≤
      ‖secondPart (sliceOf u t)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradPart (sliceOf u t)‖ ^ 2
        + inner ℝ (cv t) (secondPart (sliceOf u t)))
    (hconv : (C : TimeCircle → HBar) =ᵐ[volume] cv)
    (hB : B = f + C + A) (hA : ‖A‖ ≤ Ab * vn) (σ : ℝ) :
    y σ ≤ (1 / w₀ + 2 * (P / N) * fb) * energyW w u
      + 2 * (P / N) * (‖B‖ + Ab * vn) * Real.sqrt (energyW w u) := by
  have hwn : ∀ y, 0 ≤ w y := fun y => hw0.le.trans (hwl y)
  have hS : (secondCLM u : TimeCircle → HBar) =ᵐ[volume] fun t => secondPart (sliceOf u t) :=
    ContinuousLinearMap.coeFn_compLpL secondPart u
  have hGd : (gradCLM u : TimeCircle → Freq.X) =ᵐ[volume] fun t => gradPart (sliceOf u t) :=
    ContinuousLinearMap.coeFn_compLpL gradPart u
  have hwc := continuous_sliceWeightedGrad hwm hwn hwu
  have hgpm : AEStronglyMeasurable (fun t => gradPart (sliceOf u t)) volume :=
    gradPart.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)
  have hgp2 : Integrable (fun t => ‖gradPart (sliceOf u t)‖ ^ 2) volume :=
    ((Lp.memLp (gradCLM u)).integrable_norm_pow two_ne_zero).congr
      (hGd.mono fun t ht => by simp only [ht])
  have hsp2 : Integrable (fun t => ‖secondPart (sliceOf u t)‖ ^ 2) volume :=
    ((Lp.memLp (secondCLM u)).integrable_norm_pow two_ne_zero).congr
      (hS.mono fun t ht => by simp only [ht])
  have hwg0 : ∀ t, 0 ≤ sliceWeightedGrad w (gradPart (sliceOf u t)) := fun t =>
    (mul_nonneg hw0.le (sq_nonneg _)).trans (sliceWeightedGrad_ge hwm hwl hwn hwu _)
  have hwgi : Integrable (fun t => sliceWeightedGrad w (gradPart (sliceOf u t))) volume := by
    refine Integrable.mono' (hgp2.const_mul Wm) (hwc.comp_aestronglyMeasurable hgpm)
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hwg0 t)]
    exact sliceWeightedGrad_le hwm hwn hwu _
  obtain ⟨G, hG⟩ : ∃ G : TimeCircle → ℝ, ∀ t, G t =
      ‖(B : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖
        + ‖(A : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖
        + fb * (‖secondPart (sliceOf u t)‖ ^ 2 + sliceWeightedGrad w (gradPart (sliceOf u t))) :=
    ⟨_, fun t => rfl⟩
  have hBi : Integrable (fun t => ‖(B : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖) volume :=
    (integrable_norm_mul B (secondCLM u)).congr (hS.mono fun t ht => by simp only [ht])
  have hAi : Integrable (fun t => ‖(A : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖) volume :=
    (integrable_norm_mul A (secondCLM u)).congr (hS.mono fun t ht => by simp only [ht])
  have hBA : Integrable (fun t => ‖(B : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖
      + ‖(A : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖) volume := hBi.add hAi
  have hsw : Integrable (fun t => ‖secondPart (sliceOf u t)‖ ^ 2
      + sliceWeightedGrad w (gradPart (sliceOf u t))) volume := hsp2.add hwgi
  have hrest : Integrable (fun t => fb * (‖secondPart (sliceOf u t)‖ ^ 2
      + sliceWeightedGrad w (gradPart (sliceOf u t)))) volume := hsw.const_mul fb
  have hGi : Integrable G volume := by
    have := hBA.add hrest
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, hG]
  have hG0 : ∀ t, 0 ≤ G t := fun t => by
    rw [hG]
    exact add_nonneg (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (mul_nonneg hfb (add_nonneg (sq_nonneg _) (hwg0 t)))
  have hE : energyW w u = ‖secondCLM u‖ ^ 2 + ∫ t, sliceWeightedGrad w (gradPart (sliceOf u t)) := rfl
  have hwgI : 0 ≤ ∫ t, sliceWeightedGrad w (gradPart (sliceOf u t)) := integral_nonneg hwg0
  have hSE : ‖secondCLM u‖ ≤ Real.sqrt (energyW w u) := by
    rw [← Real.sqrt_sq (norm_nonneg (secondCLM u))]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : ∫ t, ‖secondPart (sliceOf u t)‖ ^ 2 = ‖secondCLM u‖ ^ 2 := by
    rw [← integral_norm_sq_eq (secondCLM u)]
    exact integral_congr_ae (hS.mono fun t ht => by simp only [ht])
  have eB : ∫ t, ‖(B : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖ =
      ∫ t, ‖(B : TimeCircle → HBar) t‖ * ‖(secondCLM u : TimeCircle → HBar) t‖ :=
    integral_congr_ae (hS.mono fun t ht => by simp only [ht])
  have eA : ∫ t, ‖(A : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖ =
      ∫ t, ‖(A : TimeCircle → HBar) t‖ * ‖(secondCLM u : TimeCircle → HBar) t‖ :=
    integral_congr_ae (hS.mono fun t ht => by simp only [ht])
  have hIG : ∫ t, G t ≤ (‖B‖ + Ab * vn) * Real.sqrt (energyW w u) + fb * energyW w u := by
    have a0 : ∫ t, G t = ∫ t, (‖(B : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖
        + ‖(A : TimeCircle → HBar) t‖ * ‖secondPart (sliceOf u t)‖)
        + fb * (‖secondPart (sliceOf u t)‖ ^ 2 + sliceWeightedGrad w (gradPart (sliceOf u t))) :=
      integral_congr_ae (ae_of_all _ fun t => hG t)
    have a1 := integral_add hBA hrest
    have a2 := integral_add hBi hAi
    have a3 := integral_const_mul (μ := (volume : Measure TimeCircle)) fb
      (fun t => ‖secondPart (sliceOf u t)‖ ^ 2 + sliceWeightedGrad w (gradPart (sliceOf u t)))
    have a4 := integral_add hsp2 hwgi
    have hE' := congrArg (HMul.hMul fb) hE
    have a5 := congrArg (HMul.hMul fb) a4
    have a6 : fb * ((∫ t, ‖secondPart (sliceOf u t)‖ ^ 2)
        + ∫ t, sliceWeightedGrad w (gradPart (sliceOf u t))) =
        fb * (‖secondCLM u‖ ^ 2 + ∫ t, sliceWeightedGrad w (gradPart (sliceOf u t))) :=
      congrArg (fun z => fb * (z + ∫ t, sliceWeightedGrad w (gradPart (sliceOf u t)))) hsq
    have i1 := integral_norm_mul_le B (secondCLM u)
    have i2 := integral_norm_mul_le A (secondCLM u)
    have j1 : ‖B‖ * ‖secondCLM u‖ ≤ ‖B‖ * Real.sqrt (energyW w u) :=
      mul_le_mul_of_nonneg_left hSE (norm_nonneg _)
    have j2 : ‖A‖ * ‖secondCLM u‖ ≤ Ab * vn * Real.sqrt (energyW w u) :=
      (mul_le_mul_of_nonneg_left hSE (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _))
    linarith
  have hcirc : ∀ g : TimeCircle → ℝ, ∫ s in (0 : ℝ)..1, g (s : TimeCircle) = ∫ t, g t := by
    intro g
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc, integral_Icc_coe]
  have hmean : ∫ s in (0 : ℝ)..1, y s ≤ energyW w u / w₀ := by
    have e1 : ∫ s in (0 : ℝ)..1, y s = ∫ s in (0 : ℝ)..1, ‖gradPart (sliceOf u (s : TimeCircle))‖ ^ 2 :=
      intervalIntegral.integral_congr_ae (hyae.mono fun s hs _ => hs)
    rw [e1, hcirc (fun t => ‖gradPart (sliceOf u t)‖ ^ 2)]
    have h3 : w₀ * ∫ t, ‖gradPart (sliceOf u t)‖ ^ 2 ≤ ∫ t, sliceWeightedGrad w (gradPart (sliceOf u t)) := by
      rw [← integral_const_mul]
      exact integral_mono (hgp2.const_mul w₀) hwgi fun t => sliceWeightedGrad_ge hwm hwl hwn hwu _
    rw [le_div_iff₀ hw0]
    have := sq_nonneg ‖secondCLM u‖
    linarith [hE]
  have hid' : ∀ a b, a ≤ b → y b - y a = (2 * P) * ∫ σ in a..b,
      (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle)) (secondPart (sliceOf u (σ : TimeCircle)))
        - ‖secondPart (sliceOf u (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * y σ) := by
    intro a b hab
    rw [← hid a b hab, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
  have hadd : (B : TimeCircle → HBar) =ᵐ[volume] fun t => (f : TimeCircle → HBar) t
      + (C : TimeCircle → HBar) t + (A : TimeCircle → HBar) t := by
    rw [hB]
    filter_upwards [Lp.coeFn_add (f + C) A, Lp.coeFn_add f C] with t h1 h2
    exact h1.trans (congrArg (· + (A : TimeCircle → HBar) t) h2)
  have hpt : ∀ᵐ t : TimeCircle, ∀ r : ℝ, r = ‖gradPart (sliceOf u t)‖ ^ 2 →
      inner ℝ ((f : TimeCircle → HBar) t) (secondPart (sliceOf u t))
        - ‖secondPart (sliceOf u t)‖ ^ 2 - (1 / 4 : ℝ) * r ≤ G t := by
    filter_upwards [hbr, hconv, hadd] with t hb hc ha r hr
    rw [hG, hr]
    have q0 : inner ℝ ((B : TimeCircle → HBar) t) (secondPart (sliceOf u t)) =
        inner ℝ ((f : TimeCircle → HBar) t + (C : TimeCircle → HBar) t + (A : TimeCircle → HBar) t)
          (secondPart (sliceOf u t)) :=
      congrArg (fun z => inner ℝ z (secondPart (sliceOf u t))) ha
    have q1 := inner_add_left (𝕜 := ℝ) ((f : TimeCircle → HBar) t + (C : TimeCircle → HBar) t)
      ((A : TimeCircle → HBar) t) (secondPart (sliceOf u t))
    have q2 := inner_add_left (𝕜 := ℝ) ((f : TimeCircle → HBar) t) ((C : TimeCircle → HBar) t)
      (secondPart (sliceOf u t))
    have q3 : inner ℝ ((C : TimeCircle → HBar) t) (secondPart (sliceOf u t)) =
        inner ℝ (cv t) (secondPart (sliceOf u t)) :=
      congrArg (fun z => inner ℝ z (secondPart (sliceOf u t))) hc
    have i1 := real_inner_le_norm ((B : TimeCircle → HBar) t) (secondPart (sliceOf u t))
    have i2 := (neg_le_abs (inner ℝ ((A : TimeCircle → HBar) t) (secondPart (sliceOf u t)))).trans
      (abs_real_inner_le_norm ((A : TimeCircle → HBar) t) (secondPart (sliceOf u t)))
    linarith
  have hhg : ∀ᵐ σ : ℝ, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
        (secondPart (sliceOf u (σ : TimeCircle)))
      - ‖secondPart (sliceOf u (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * y σ) ≤ G (σ : TimeCircle) := by
    filter_upwards [(ae_coe_iff _).1 hpt, hyae] with σ a b
    exact a _ b
  have hgper : ∀ σ : ℝ, G ((σ + 1 : ℝ) : TimeCircle) = G (σ : TimeCircle) := fun σ => by
    rw [AddCircle.coe_add_period]
  have hgi : IntervalIntegrable (fun σ : ℝ => G (σ : TimeCircle)) volume 0 1 := by
    have hmp := AddCircle.measurePreserving_mk (1 : ℝ) (0 : ℝ)
    have := (hmp.integrable_comp hGi.aestronglyMeasurable).2 hGi
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 ?_
    have h' : Integrable (G ∘ QuotientAddGroup.mk) (volume.restrict (Ioc (0 : ℝ) 1)) := by
      simpa using this
    exact h'
  have hmain := le_of_identity (g := fun σ : ℝ => G (σ : TimeCircle)) hN (by positivity) hyc hyper
    hhalf hid' hhg (fun σ => hG0 _) hgper hgi σ
  rw [hcirc G] at hmain
  have hc' : 0 ≤ 2 * P / N := div_nonneg (by positivity) (Nat.cast_nonneg N)
  have key := mul_le_mul_of_nonneg_left hIG hc'
  have e1 : 2 * P / (N : ℝ) = 2 * (P / N) := by ring
  have e2 : energyW w u / w₀ = 1 / w₀ * energyW w u := by ring
  rw [e1] at key hmain
  rw [e2] at hmean
  linarith

end Internal.SupBound

set_option maxHeartbeats 4000000 in
open Internal.SupBound in
theorem supBoundHolds_of (h1 : FreeEnergyLocalHolds) (h2 : FrozenBridgeHolds) (h3 : InvarianceHolds)
    (h4 : DataHolds) (h5 : ReadingEnergyHolds) (h6 : ConvectionHolds) (h7 : FreeEquivariantHolds) :
    SupBoundHolds := by
  intro k d hd p hp f hf κ
  have hP : 0 < d.period p := hd.period_pos p hp
  obtain ⟨y, hyc, hyper, hyae, hid⟩ := h1 (d.period p) hP f
  have hN : d.twist = 1 ∨ d.twist = 2 := hd.twist_mem.imp id fun h => h.1
  have hhalf : d.twist = 2 → ∀ σ, y (σ + 1 / 2) = y σ := by
    intro htw
    rcases hd.twist_mem with h | ⟨_, Q, hQ⟩
    · omega
    · exact half_periodic _ d.symmetries Q hQ (h7 d.symmetries (d.period p) hP f hf) y hyc hyae
  have hex := (h6 d hd p hp).1
  have hconv : ConvectionSpec d p (convection d p) := by
    unfold convection
    rw [dif_pos hex]
    exact hex.choose_spec
  have hB : (bordered d p (f, κ)).1 = f + convection d p (freeInv (d.period p) f) + actuatorH d κ := by simp [bordered]
  have hb := core_bound hN hP hd.weight_pos hd.weightFn_measurable hd.weightFn_lower
    hd.weightFn_upper hd.formBound_nonneg (freeInv (d.period p) f) f (bordered d p (f, κ)).1
    (actuatorH d κ) (convection d p (freeInv (d.period p) f))
    (fun t => solField (sliceConvection (d.profile p (circleRep t))
      (gradPart (sliceOf (freeInv (d.period p) f) t))))
    y hyc hyper hyae hid hhalf (h2 d hd p hp f hf) (hconv _) hB ((h4 d hd p hp).2.2.2.1 κ)
  exact supGrad_bound _ y _ hyae hb

end Breakdown.Cert

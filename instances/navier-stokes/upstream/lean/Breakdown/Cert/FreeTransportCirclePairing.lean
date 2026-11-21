import Breakdown.Cert.GradInvSpec
import Breakdown.Cert.PeriodIntegral

open scoped ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.SlicePairingSwap

def IsSlicePairingBound (Φ : ℝ → Freq.X → ℝ) (C R : ℝ) : Prop :=
  Continuous (fun p : ℝ × Freq.X => Φ p.1 p.2) ∧ 0 ≤ C ∧
    (∀ r h h', Φ r (h + h') = Φ r h + Φ r h') ∧ (∀ r (c : ℝ) h, Φ r (c • h) = c * Φ r h) ∧
    (∀ r h, |Φ r h| ≤ C * ‖h‖) ∧ ∀ r h, r ∉ Icc (-R) R → Φ r h = 0

theorem lintegral_Ioc_nat (F : TimeCircle → ℝ≥0∞) (t : ℝ) (m : ℕ) :
    ∫⁻ σ in Ioc t (t + m), F (σ : TimeCircle) = m * ∫⁻ s, F s := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hu : Ioc t (t + ((m + 1 : ℕ) : ℝ)) = Ioc t (t + m) ∪ Ioc (t + m) (t + m + 1) := by
      rw [Nat.cast_succ, ← add_assoc]
      exact (Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
    rw [hu, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), ih,
      AddCircle.lintegral_preimage 1 (t + m) F]
    push_cast
    ring

theorem lintegral_Icc_le (F : TimeCircle → ℝ≥0∞) {a b ℓ : ℝ} (h : b ≤ a + ℓ) :
    ∫⁻ σ in Icc a b, F (σ : TimeCircle) ≤ ((⌈ℓ⌉₊ + 1 : ℕ) : ℝ≥0∞) * ∫⁻ s, F s := by
  rw [← lintegral_Ioc_nat F (a - 1)]
  refine lintegral_mono_set fun x hx => ⟨by linarith [hx.1], ?_⟩
  have h1 : ℓ ≤ (⌈ℓ⌉₊ : ℝ) := Nat.le_ceil ℓ
  push_cast
  linarith [hx.2]

set_option maxHeartbeats 1000000 in
theorem lintegral_enorm_le (g : HH) :
    ∫⁻ s, ENNReal.ofReal ‖(g : TimeCircle → HBar) s‖ ≤ ENNReal.ofReal ‖g‖ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (μ := (volume : Measure TimeCircle)) (by norm_num) (Lp.aestronglyMeasurable g)
  rw [AddCircle.measure_univ, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one,
    eLpNorm_one_eq_lintegral_enorm] at h
  have e1 : ∫⁻ s, ENNReal.ofReal ‖(g : TimeCircle → HBar) s‖ = eLpNorm (g : TimeCircle → HBar) 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_congr fun s => ofReal_norm _
  have e2 : eLpNorm (g : TimeCircle → HBar) 2 volume = ENNReal.ofReal ‖g‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)]
  rw [e1, ← e2, eLpNorm_one_eq_lintegral_enorm]
  exact h

theorem stronglyMeasurable_coe (g : HH) :
    StronglyMeasurable (fun σ : ℝ => (g : TimeCircle → HBar) (σ : TimeCircle)) :=
  (Lp.stronglyMeasurable g).comp_measurable (AddCircle.continuous_mk' (1 : ℝ)).measurable

theorem integrableOn_norm_coe (g : HH) (a b : ℝ) :
    IntegrableOn (fun σ : ℝ => ‖(g : TimeCircle → HBar) (σ : TimeCircle)‖) (Icc a b) := by
  refine ⟨(stronglyMeasurable_coe g).norm.aestronglyMeasurable, ?_⟩
  show ∫⁻ σ in Icc a b, ‖‖(g : TimeCircle → HBar) (σ : TimeCircle)‖‖ₑ < ⊤
  have e : ∫⁻ σ in Icc a b, ‖‖(g : TimeCircle → HBar) (σ : TimeCircle)‖‖ₑ =
      ∫⁻ σ in Icc a b, ENNReal.ofReal ‖(g : TimeCircle → HBar) (σ : TimeCircle)‖ :=
    lintegral_congr fun σ => (ofReal_norm _).symm.trans (congrArg ENNReal.ofReal (norm_norm _))
  rw [e]
  refine (lintegral_Icc_le (fun s => ENNReal.ofReal ‖(g : TimeCircle → HBar) s‖) (ℓ := b - a)
    (by linarith)).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ((lintegral_enorm_le g).trans_lt ENNReal.ofReal_lt_top)

set_option maxHeartbeats 1000000 in
theorem integral_norm_coe_le (g : HH) {a b ℓ : ℝ} (h : b ≤ a + ℓ) :
    ∫ σ in Icc a b, ‖(g : TimeCircle → HBar) (σ : TimeCircle)‖ ≤ ((⌈ℓ⌉₊ + 1 : ℕ) : ℝ) * ‖g‖ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun σ => norm_nonneg _)
    (stronglyMeasurable_coe g).norm.aestronglyMeasurable]
  have h1 := (lintegral_Icc_le (fun s => ENNReal.ofReal ‖(g : TimeCircle → HBar) s‖) h).trans
    (mul_le_mul_of_nonneg_left (lintegral_enorm_le g) zero_le)
  have h2 : (((⌈ℓ⌉₊ + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ‖g‖).toReal = ((⌈ℓ⌉₊ + 1 : ℕ) : ℝ) * ‖g‖ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_natCast]
  rw [← h2]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) h1

def circlePairing (Φ : ℝ → Freq.X → ℝ) (g : HH) : ℝ :=
  ∫ σ : ℝ, Φ σ ((g : TimeCircle → HBar) (σ : TimeCircle))

variable {Φ : ℝ → Freq.X → ℝ} {C R : ℝ}

theorem integrable_pairing (hΦ : IsSlicePairingBound Φ C R) (g : HH) :
    Integrable (fun σ : ℝ => Φ σ ((g : TimeCircle → HBar) (σ : TimeCircle))) := by
  have hm : AEStronglyMeasurable (fun σ : ℝ => Φ σ ((g : TimeCircle → HBar) (σ : TimeCircle))) volume :=
    (hΦ.1.comp_stronglyMeasurable (stronglyMeasurable_id.prodMk (stronglyMeasurable_coe g))).aestronglyMeasurable
  refine Integrable.mono' (IntegrableOn.integrable_indicator ((integrableOn_norm_coe g (-R) R).const_mul C) measurableSet_Icc)
    hm (ae_of_all _ fun σ => ?_)
  by_cases hσ : σ ∈ Icc (-R) R
  · rw [indicator_of_mem hσ, Real.norm_eq_abs]
    exact hΦ.2.2.2.2.1 σ _
  · rw [indicator_of_notMem hσ, hΦ.2.2.2.2.2 σ _ hσ, norm_zero]

theorem circlePairing_add (hΦ : IsSlicePairingBound Φ C R) (g g' : HH) :
    circlePairing Φ (g + g') = circlePairing Φ g + circlePairing Φ g' := by
  have e : ∀ᵐ σ : ℝ, ((g + g' : HH) : TimeCircle → HBar) (σ : TimeCircle) =
      (g : TimeCircle → HBar) σ + (g' : TimeCircle → HBar) σ :=
    (ae_coe_iff (fun t => ((g + g' : HH) : TimeCircle → HBar) t =
      (g : TimeCircle → HBar) t + (g' : TimeCircle → HBar) t)).1 (Lp.coeFn_add g g')
  unfold circlePairing
  refine (integral_congr_ae ?_).trans (integral_add (integrable_pairing hΦ g) (integrable_pairing hΦ g'))
  filter_upwards [e] with σ hσ
  exact (congrArg (Φ σ) hσ).trans (hΦ.2.2.1 σ _ _)

theorem circlePairing_smul (hΦ : IsSlicePairingBound Φ C R) (c : ℝ) (g : HH) :
    circlePairing Φ (c • g) = c * circlePairing Φ g := by
  have e : ∀ᵐ σ : ℝ, ((c • g : HH) : TimeCircle → HBar) (σ : TimeCircle) = c • (g : TimeCircle → HBar) σ :=
    (ae_coe_iff (fun t => ((c • g : HH) : TimeCircle → HBar) t = c • (g : TimeCircle → HBar) t)).1
      (Lp.coeFn_smul c g)
  unfold circlePairing
  refine (integral_congr_ae ?_).trans (integral_const_mul c _)
  filter_upwards [e] with σ hσ
  exact (congrArg (Φ σ) hσ).trans (hΦ.2.2.2.1 σ c _)

set_option maxHeartbeats 1000000 in
theorem abs_circlePairing_le (hΦ : IsSlicePairingBound Φ C R) (g : HH) :
    |circlePairing Φ g| ≤ C * ((⌈2 * R⌉₊ + 1 : ℕ) : ℝ) * ‖g‖ := by
  rw [← Real.norm_eq_abs]
  unfold circlePairing
  have hb := IntegrableOn.integrable_indicator ((integrableOn_norm_coe g (-R) R).const_mul C) measurableSet_Icc
  refine (norm_integral_le_of_norm_le hb (ae_of_all _ fun σ => ?_)).trans ?_
  · by_cases hσ : σ ∈ Icc (-R) R
    · rw [indicator_of_mem hσ, Real.norm_eq_abs]
      exact hΦ.2.2.2.2.1 σ _
    · rw [indicator_of_notMem hσ, hΦ.2.2.2.2.2 σ _ hσ, norm_zero]
  rw [integral_indicator measurableSet_Icc, integral_const_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (integral_norm_coe_le g (ℓ := 2 * R) (by linarith)) hΦ.2.1

def circlePairingCLM (hΦ : IsSlicePairingBound Φ C R) : HH →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := circlePairing Φ
      map_add' := circlePairing_add hΦ
      map_smul' := fun c g => (circlePairing_smul hΦ c g).trans (smul_eq_mul c _).symm }
    (C * ((⌈2 * R⌉₊ + 1 : ℕ) : ℝ)) fun g => (Real.norm_eq_abs _).trans_le (abs_circlePairing_le hΦ g)

theorem circlePairingCLM_apply (hΦ : IsSlicePairingBound Φ C R) (g : HH) :
    circlePairingCLM hΦ g = circlePairing Φ g := rfl

theorem shiftLp_apply_ae (a : ℝ) (f : HH) :
    ∀ᵐ t : TimeCircle, ((shiftLp a f : HH) : TimeCircle → HBar) t =
      (f : TimeCircle → HBar) (t + (a : TimeCircle)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (a : TimeCircle))

theorem propagatorIntegrand_apply_ae (P : ℝ) (f : HH) (τ : ℝ) :
    ∀ᵐ t : TimeCircle, ((propagatorIntegrand P f τ : HH) : TimeCircle → HBar) t =
      slicePropagator τ (((shiftLp (-(τ / P)) f : HH) : TimeCircle → HBar) t) :=
  ContinuousLinearMap.coeFn_compLpL (slicePropagator τ) (shiftLp (-(τ / P)) f)

set_option maxHeartbeats 1000000 in
theorem coe_propagatorIntegrand_ae (P : ℝ) (f : HH) (τ : ℝ) :
    ∀ᵐ σ : ℝ, ((propagatorIntegrand P f τ : HH) : TimeCircle → HBar) (σ : TimeCircle) =
      slicePropagator τ ((f : TimeCircle → HBar) ((σ - τ / P : ℝ) : TimeCircle)) := by
  have h1 := propagatorIntegrand_apply_ae P f τ
  have h2 := shiftLp_apply_ae (-(τ / P)) f
  have h3 := (ae_coe_iff (fun t : TimeCircle =>
    ((propagatorIntegrand P f τ : HH) : TimeCircle → HBar) t =
      slicePropagator τ (((shiftLp (-(τ / P)) f : HH) : TimeCircle → HBar) t) ∧
    ((shiftLp (-(τ / P)) f : HH) : TimeCircle → HBar) t =
      (f : TimeCircle → HBar) (t + ((-(τ / P) : ℝ) : TimeCircle)))).1 (h1.and h2)
  filter_upwards [h3] with σ hσ
  refine hσ.1.trans ?_
  refine congrArg (slicePropagator τ) (hσ.2.trans ?_)
  rw [sub_eq_add_neg, AddCircle.coe_add]

theorem circlePairing_propagatorIntegrand (P : ℝ) (f : HH) (τ : ℝ) :
    circlePairing Φ (propagatorIntegrand P f τ) =
      ∫ σ : ℝ, Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) := by
  have e1 : circlePairing Φ (propagatorIntegrand P f τ) =
      ∫ σ : ℝ, Φ σ (slicePropagator τ ((f : TimeCircle → HBar) ((σ - τ / P : ℝ) : TimeCircle))) := by
    unfold circlePairing
    refine integral_congr_ae ?_
    filter_upwards [coe_propagatorIntegrand_ae P f τ] with σ hσ
    exact congrArg (Φ σ) hσ
  have e2 := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun σ : ℝ => Φ σ (slicePropagator τ ((f : TimeCircle → HBar) ((σ - τ / P : ℝ) : TimeCircle)))) (τ / P)
  refine e1.trans (e2.symm.trans (integral_congr_ae (ae_of_all _ fun σ => ?_)))
  show Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) ((σ + τ / P - τ / P : ℝ) : TimeCircle))) = _
  rw [add_sub_cancel_right]

theorem circlePairing_gradInv (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) :
    circlePairing Φ (gradInv P f) =
      ∫ τ in Ioi (0 : ℝ), ∫ σ : ℝ, Φ (σ + τ / P)
        (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) := by
  have h1 : circlePairingCLM hΦ (gradInv P f) =
      circlePairingCLM hΦ (∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ) :=
    congrArg (circlePairingCLM hΦ) (gradInv_spec P f)
  have h2 := (circlePairingCLM hΦ).integral_comp_comm (integrable_propagatorIntegrand P f)
  refine (circlePairingCLM_apply hΦ _).symm.trans (h1.trans (h2.symm.trans ?_))
  exact integral_congr_ae (ae_of_all _ fun τ =>
    (circlePairingCLM_apply hΦ _).trans (circlePairing_propagatorIntegrand P f τ))

theorem stronglyMeasurable_shifted (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) (τ : ℝ) :
    StronglyMeasurable (fun σ : ℝ =>
      Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))) :=
  hΦ.1.comp_stronglyMeasurable
    ((continuous_id.add continuous_const).stronglyMeasurable.prodMk
      ((slicePropagator τ).continuous.comp_stronglyMeasurable (stronglyMeasurable_coe f)))

theorem continuous_shifted_max (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) (σ ε : ℝ)
    (hε : 0 < ε) :
    Continuous (fun τ : ℝ => Φ (σ + max τ ε / P)
      (slicePropagator (max τ ε) ((f : TimeCircle → HBar) (σ : TimeCircle)))) := by
  have hm : Continuous (fun τ : ℝ => max τ ε) := continuous_id.max continuous_const
  have hS : Continuous (fun τ : ℝ => slicePropagator (max τ ε) ((f : TimeCircle → HBar) (σ : TimeCircle))) :=
    (GradInv.Internal.continuousOn_slicePropagator _).comp_continuous hm
      fun τ => lt_of_lt_of_le hε (le_max_right τ ε)
  exact hΦ.1.comp ((continuous_const.add (hm.div_const P)).prodMk hS)

theorem aestronglyMeasurable_kernelPairing (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) :
    AEStronglyMeasurable (Function.uncurry fun τ σ : ℝ =>
      Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hn : ∀ n : ℕ, AEStronglyMeasurable (Function.uncurry fun τ σ : ℝ =>
      Φ (σ + max τ (1 / ((n : ℝ) + 1)) / P)
        (slicePropagator (max τ (1 / ((n : ℝ) + 1))) ((f : TimeCircle → HBar) (σ : TimeCircle))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := fun n =>
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun σ => continuous_shifted_max hΦ P f σ _ Nat.one_div_pos_of_nat)
      (fun τ => stronglyMeasurable_shifted hΦ P f (max τ (1 / ((n : ℝ) + 1))))).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hn ?_
  have hpos : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)), 0 < p.1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).2
      ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => ae_of_all _ fun _ => hτ)
  filter_upwards [hpos] with p hp
  refine tendsto_const_nhds.congr' ?_
  have hN := (exists_nat_one_div_lt hp).choose_spec
  filter_upwards [eventually_ge_atTop (exists_nat_one_div_lt hp).choose] with n hn
  have hle : 1 / ((n : ℝ) + 1) ≤ p.1 := by
    refine le_trans ?_ hN.le
    gcongr
  show Φ (p.2 + p.1 / P) (slicePropagator p.1 ((f : TimeCircle → HBar) (p.2 : TimeCircle))) =
    Φ (p.2 + max p.1 (1 / ((n : ℝ) + 1)) / P)
      (slicePropagator (max p.1 (1 / ((n : ℝ) + 1))) ((f : TimeCircle → HBar) (p.2 : TimeCircle)))
  rw [max_eq_left hle]

set_option maxHeartbeats 1000000 in
theorem lintegral_kernelPairing_le (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) {τ : ℝ}
    (hτ : 0 < τ) :
    ∫⁻ σ : ℝ, ‖Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))‖ₑ ≤
      ENNReal.ofReal (C * GradInv.Internal.kernel τ) *
        (((⌈2 * R⌉₊ + 1 : ℕ) : ℝ≥0∞) * ∫⁻ s, ENNReal.ofReal ‖(f : TimeCircle → HBar) s‖) := by
  have hpt : ∀ σ : ℝ, ‖Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))‖ₑ ≤
      (Icc (-R - τ / P) (R - τ / P)).indicator (fun σ => ENNReal.ofReal (C * GradInv.Internal.kernel τ) *
        ENNReal.ofReal ‖(f : TimeCircle → HBar) (σ : TimeCircle)‖) σ := by
    intro σ
    by_cases hσ : σ ∈ Icc (-R - τ / P) (R - τ / P)
    · rw [indicator_of_mem hσ]
      have hr : ‖Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))‖ ≤
          C * GradInv.Internal.kernel τ * ‖(f : TimeCircle → HBar) (σ : TimeCircle)‖ := by
        rw [Real.norm_eq_abs, mul_assoc]
        refine (hΦ.2.2.2.2.1 _ _).trans (mul_le_mul_of_nonneg_left ?_ hΦ.2.1)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (GradInv.Internal.norm_slicePropagator_op_le hτ) (norm_nonneg _))
      calc ‖Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))‖ₑ
          = ENNReal.ofReal ‖Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))‖ :=
            (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (C * GradInv.Internal.kernel τ * ‖(f : TimeCircle → HBar) (σ : TimeCircle)‖) :=
            ENNReal.ofReal_le_ofReal hr
        _ = ENNReal.ofReal (C * GradInv.Internal.kernel τ) *
              ENNReal.ofReal ‖(f : TimeCircle → HBar) (σ : TimeCircle)‖ :=
            ENNReal.ofReal_mul (mul_nonneg hΦ.2.1 (GradInv.Internal.kernel_pos hτ).le)
    · rw [indicator_of_notMem hσ, hΦ.2.2.2.2.2 _ _ ?_, enorm_zero]
      intro h
      exact hσ ⟨by linarith [h.1], by linarith [h.2]⟩
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator measurableSet_Icc, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_of_nonneg_left (lintegral_Icc_le (fun s => ENNReal.ofReal ‖(f : TimeCircle → HBar) s‖) (ℓ := 2 * R)
    (by linarith)) zero_le

theorem integrable_kernelPairing (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) :
    Integrable (Function.uncurry fun τ σ : ℝ =>
      Φ (σ + τ / P) (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hm := aestronglyMeasurable_kernelPairing hΦ P f
  refine ⟨hm, ?_⟩
  have hB : ((⌈2 * R⌉₊ + 1 : ℕ) : ℝ≥0∞) * ∫⁻ s, ENNReal.ofReal ‖(f : TimeCircle → HBar) s‖ < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ((lintegral_enorm_le f).trans_lt ENNReal.ofReal_lt_top)
  show ∫⁻ p, ‖Function.uncurry (fun τ σ : ℝ => Φ (σ + τ / P)
    (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle)))) p‖ₑ
      ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) < ⊤
  rw [lintegral_prod _ hm.enorm]
  refine lt_of_le_of_lt (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun τ hτ => lintegral_kernelPairing_le hΦ P f hτ))) ?_
  rw [lintegral_mul_const' _ _ hB.ne]
  exact ENNReal.mul_lt_top ((GradInv.Internal.integrableOn_kernel.const_mul C).lintegral_lt_top) hB

theorem integral_swap_kernelPairing (hΦ : IsSlicePairingBound Φ C R) (P : ℝ) (f : HH) :
    ∫ τ in Ioi (0 : ℝ), ∫ σ : ℝ, Φ (σ + τ / P)
        (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) =
      ∫ σ : ℝ, ∫ τ in Ioi (0 : ℝ), Φ (σ + τ / P)
        (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) :=
  integral_integral_swap (integrable_kernelPairing hΦ P f)

end Internal.SlicePairingSwap

end Breakdown.Cert

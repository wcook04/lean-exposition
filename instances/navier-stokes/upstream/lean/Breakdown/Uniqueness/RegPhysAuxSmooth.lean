import Breakdown.Uniqueness.RegPhysAuxEval

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal

def WeightBounded (k : ℕ) (a : Space → ℂ) : Prop :=
  Measurable a ∧ ∃ C, ∀ ξ, ‖a ξ‖ ≤ C * (1 + ‖ξ‖) ^ k

theorem weight_mono {ℓ k : ℕ} (h : ℓ ≤ k) (ξ : Space) : (1 + ‖ξ‖) ^ ℓ ≤ (1 + ‖ξ‖) ^ k :=
  pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) h

theorem nonneg_of_bound {k : ℕ} {r : Space → ℂ} {C : ℝ} (hC : ∀ ξ, ‖r ξ‖ ≤ C * (1 + ‖ξ‖) ^ k) :
    0 ≤ C := by
  have := hC 0
  simp only [norm_zero, add_zero, one_pow, mul_one] at this
  exact (norm_nonneg _).trans this

theorem WeightBounded.mono {ℓ k : ℕ} {a : Space → ℂ} (ha : WeightBounded ℓ a) (h : ℓ ≤ k) :
    WeightBounded k a := by
  obtain ⟨hm, C, hC⟩ := ha
  exact ⟨hm, C, fun ξ => (hC ξ).trans
    (mul_le_mul_of_nonneg_left (weight_mono h ξ) (nonneg_of_bound hC))⟩

theorem volume_ac_weight (k : ℕ) : (volume : Measure Space) ≪ weightL1Measure k := by
  refine withDensity_absolutelyContinuous' ?_ ?_
  · fun_prop
  · exact Eventually.of_forall fun ξ => by
      have : 0 < (1 + ‖ξ‖) ^ k := by positivity
      simpa using this

theorem lintegral_weight (k : ℕ) (f : Space → CSpace) :
    ∫⁻ ξ, ‖f ξ‖ₑ ∂weightL1Measure k =
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable volume (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _

theorem integrable_and_norm_le {k : ℕ} {r : Space → ℂ} (hr : AEStronglyMeasurable r volume)
    {C : ℝ} (hC : ∀ ξ, ‖r ξ‖ ≤ C * (1 + ‖ξ‖) ^ k) (g : Lp CSpace 1 (weightL1Measure k)) :
    Integrable (fun ξ => r ξ • (g : Space → CSpace) ξ) volume ∧
      ‖∫ ξ, r ξ • (g : Space → CSpace) ξ‖ ≤ C * ‖g‖ := by
  have hC0 : 0 ≤ C := nonneg_of_bound hC
  have hgm : AEStronglyMeasurable (g : Space → CSpace) volume :=
    (Lp.aestronglyMeasurable g).mono_ac (volume_ac_weight k)
  have hpt : ∀ ξ, ‖r ξ • (g : Space → CSpace) ξ‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖(g : Space → CSpace) ξ‖ₑ) := by
    intro ξ
    rw [enorm_smul, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC ξ)
  have hlin : ∫⁻ ξ, ‖r ξ • (g : Space → CSpace) ξ‖ₑ ≤
      ENNReal.ofReal C * eLpNorm g 1 (weightL1Measure k) := by
    calc _ ≤ ∫⁻ ξ, ENNReal.ofReal C *
          (ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖(g : Space → CSpace) ξ‖ₑ) := lintegral_mono hpt
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_weight,
          eLpNorm_one_eq_lintegral_enorm]
  have hfin : ENNReal.ofReal C * eLpNorm g 1 (weightL1Measure k) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g)
  refine ⟨⟨hr.smul hgm, lt_of_le_of_lt hlin (lt_top_iff_ne_top.2 hfin)⟩, ?_⟩
  calc ‖∫ ξ, r ξ • (g : Space → CSpace) ξ‖ = (‖∫ ξ, r ξ • (g : Space → CSpace) ξ‖ₑ).toReal := by
        simp
    _ ≤ (ENNReal.ofReal C * eLpNorm g 1 (weightL1Measure k)).toReal :=
        ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans hlin)
    _ = C * ‖g‖ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0, Lp.norm_def]

def phase (x ξ : Space) : ℂ := Complex.exp (↑(2 * π * inner ℝ ξ x) * Complex.I)

theorem norm_phase (x ξ : Space) : ‖phase x ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_phase (x : Space) : Continuous (phase x) := by
  unfold phase
  fun_prop

theorem phase_add (x h ξ : Space) : phase (x + h) ξ = phase x ξ * phase h ξ := by
  unfold phase
  rw [inner_add_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem amp_meas {k : ℕ} {a : Space → ℂ} (ha : WeightBounded k a) (x : Space) :
    AEStronglyMeasurable (fun ξ => a ξ * phase x ξ) volume :=
  (ha.1.mul (continuous_phase x).measurable).aestronglyMeasurable

theorem amp_bound {k : ℕ} {a : Space → ℂ} {C : ℝ} (hC : ∀ ξ, ‖a ξ‖ ≤ C * (1 + ‖ξ‖) ^ k)
    (x : Space) : ∀ ξ, ‖a ξ * phase x ξ‖ ≤ C * (1 + ‖ξ‖) ^ k := by
  intro ξ
  rw [norm_mul, norm_phase, mul_one]
  exact hC ξ

theorem amp_integrable {k : ℕ} {a : Space → ℂ} (ha : WeightBounded k a) (x : Space)
    (g : Lp CSpace 1 (weightL1Measure k)) :
    Integrable (fun ξ => (a ξ * phase x ξ) • (g : Space → CSpace) ξ) volume :=
  (integrable_and_norm_le (amp_meas ha x) (amp_bound ha.2.choose_spec x) g).1

def ampOp (k : ℕ) (a : Space → ℂ) (ha : WeightBounded k a) (x : Space) :
    Lp CSpace 1 (weightL1Measure k) →L[ℝ] CSpace :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun g => ∫ ξ, (a ξ * phase x ξ) • (g : Space → CSpace) ξ
      map_add' := fun f g => by
        rw [← integral_add (amp_integrable ha x f) (amp_integrable ha x g)]
        refine integral_congr_ae ?_
        filter_upwards [(volume_ac_weight k).ae_le (Lp.coeFn_add f g)] with ξ hξ
        rw [hξ, Pi.add_apply, smul_add]
      map_smul' := fun c g => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [(volume_ac_weight k).ae_le (Lp.coeFn_smul c g)] with ξ hξ
        rw [hξ, Pi.smul_apply, smul_comm] }
    ⟨ha.2.choose, fun g => (integrable_and_norm_le (amp_meas ha x)
      (amp_bound ha.2.choose_spec x) g).2⟩

theorem ampOp_apply (k : ℕ) (a : Space → ℂ) (ha : WeightBounded k a) (x : Space)
    (g : Lp CSpace 1 (weightL1Measure k)) :
    ampOp k a ha x g = ∫ ξ, (a ξ * phase x ξ) • (g : Space → CSpace) ξ := rfl

def ampDir (a : Space → ℂ) (h ξ : Space) : ℂ :=
  a ξ * (2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ))

theorem ampDir_bound {ℓ : ℕ} {a : Space → ℂ} (ha : WeightBounded ℓ a) (h : Space) :
    WeightBounded (ℓ + 1) (ampDir a h) := by
  obtain ⟨hm, C, hC⟩ := ha
  have hC0 := nonneg_of_bound hC
  refine ⟨hm.mul (by fun_prop), 2 * π * C * ‖h‖, fun ξ => ?_⟩
  have hi : |inner ℝ ξ h| ≤ ‖ξ‖ * ‖h‖ := abs_real_inner_le_norm ξ h
  have hn : ‖(2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ))‖ = 2 * π * |inner ℝ ξ h| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
    ring
  rw [ampDir, norm_mul, hn, pow_succ]
  calc ‖a ξ‖ * (2 * π * |inner ℝ ξ h|) ≤ (C * (1 + ‖ξ‖) ^ ℓ) * (2 * π * (‖h‖ * (1 + ‖ξ‖))) := by
        gcongr
        · exact hC ξ
        · nlinarith [norm_nonneg ξ, norm_nonneg h]
    _ = _ := by ring

def ampDeriv (k : ℕ) (a : Space → ℂ) (hb : ∀ h, WeightBounded k (ampDir a h)) (x : Space) :
    Space →L[ℝ] Lp CSpace 1 (weightL1Measure k) →L[ℝ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => ampOp k (ampDir a h) (hb h) x
      map_add' := fun h h' => by
        refine ContinuousLinearMap.ext fun g => ?_
        rw [ContinuousLinearMap.add_apply, ampOp_apply, ampOp_apply, ampOp_apply,
          ← integral_add (amp_integrable (hb h) x g) (amp_integrable (hb h') x g)]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [← add_smul]
        congr 1
        simp only [ampDir, inner_add_right]
        push_cast
        ring
      map_smul' := fun c h => by
        refine ContinuousLinearMap.ext fun g => ?_
        rw [ContinuousLinearMap.smul_apply, ampOp_apply, ampOp_apply, RingHom.id_apply,
          ← integral_smul]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [← Complex.coe_smul, smul_smul]
        congr 1
        simp only [ampDir, inner_smul_right]
        push_cast
        ring }

theorem ampDeriv_apply (k : ℕ) (a : Space → ℂ) (hb : ∀ h, WeightBounded k (ampDir a h))
    (x h : Space) : ampDeriv k a hb x h = ampOp k (ampDir a h) (hb h) x := rfl

theorem norm_cexp_sub_le (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1 - θ * Complex.I‖ ≤ θ ^ 2 := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (s * Complex.I) - 1 - s * Complex.I)
      (Complex.I * (Complex.exp (s * Complex.I) - 1)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I s := by
      simpa using (hasDerivAt_id s).ofReal_comp.mul_const Complex.I
    have h2 := (h1.cexp.sub_const 1).sub h1
    rw [show Complex.I * (Complex.exp (s * Complex.I) - 1) =
      Complex.exp (s * Complex.I) * Complex.I - Complex.I by ring]
    exact h2
  have hb : ∀ s ∈ Metric.closedBall (0 : ℝ) |θ|,
      ‖Complex.I * (Complex.exp (s * Complex.I) - 1)‖ ≤ |θ| := by
    intro s hs
    rw [norm_mul, Complex.norm_I, one_mul]
    have hs' : ‖s‖ ≤ |θ| := by simpa using hs
    refine le_trans ?_ hs'
    have := norm_exp_I_mul_ofReal_sub_one_le (x := s)
    rwa [mul_comm] at this
  have hθ : θ ∈ Metric.closedBall (0 : ℝ) |θ| := by simp
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => Complex.exp (s * Complex.I) - 1 - s * Complex.I)
    (fun s _ => (hd s).hasDerivWithinAt) hb (convex_closedBall (0 : ℝ) |θ|)
    (Metric.mem_closedBall_self (abs_nonneg θ)) hθ
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at this
  rw [Real.norm_eq_abs, ← pow_two, sq_abs] at this
  exact this

theorem hasFDerivAt_ampOp {k ℓ : ℕ} {a : Space → ℂ} (ha : WeightBounded k a)
    (haℓ : WeightBounded ℓ a) (hℓ : ℓ + 2 ≤ k) (hb : ∀ h, WeightBounded k (ampDir a h))
    (x : Space) : HasFDerivAt (ampOp k a ha) (ampDeriv k a hb x) x := by
  obtain ⟨hm, C, hC⟩ := haℓ
  have hC0 := nonneg_of_bound hC
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound (4 * π ^ 2 * C) (Eventually.of_forall fun h => ?_)).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  rw [Real.norm_of_nonneg (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  have key : (ampOp k a ha (x + h) - ampOp k a ha x - ampDeriv k a hb x h) g =
      ∫ ξ, (a ξ * (phase (x + h) ξ - phase x ξ -
        2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) * phase x ξ)) • (g : Space → CSpace) ξ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, ampDeriv_apply, ampOp_apply,
      ampOp_apply, ampOp_apply]
    have hA := amp_integrable ha (x + h) g
    have hB := amp_integrable ha x g
    have hD := amp_integrable (hb h) x g
    rw [← integral_sub hA hB, ← integral_sub (f := fun ξ => (a ξ * phase (x + h) ξ) • (g : Space → CSpace) ξ -
      (a ξ * phase x ξ) • (g : Space → CSpace) ξ) (hA.sub hB) hD]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.sub_apply]
    rw [← sub_smul, ← sub_smul]
    congr 1
    simp only [ampDir]
    ring
  rw [key]
  have hpt : ∀ ξ, ‖a ξ * (phase (x + h) ξ - phase x ξ -
      2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) * phase x ξ)‖ ≤
      4 * π ^ 2 * C * ‖h‖ ^ 2 * (1 + ‖ξ‖) ^ k := by
    intro ξ
    have hi : |inner ℝ ξ h| ≤ (1 + ‖ξ‖) * ‖h‖ :=
      (abs_real_inner_le_norm ξ h).trans (by nlinarith [norm_nonneg ξ, norm_nonneg h])
    have hv2 : (inner ℝ ξ h) ^ 2 ≤ ((1 + ‖ξ‖) * ‖h‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hi 2
    have e1 : phase (x + h) ξ - phase x ξ - 2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) * phase x ξ =
        phase x ξ * (Complex.exp (↑(2 * π * inner ℝ ξ h) * Complex.I) - 1 -
          ↑(2 * π * inner ℝ ξ h) * Complex.I) := by
      rw [phase_add]
      simp only [phase]
      push_cast
      ring
    have hP : ‖phase (x + h) ξ - phase x ξ -
        2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) * phase x ξ‖ ≤
        4 * π ^ 2 * ‖h‖ ^ 2 * (1 + ‖ξ‖) ^ 2 := by
      rw [e1, norm_mul, norm_phase, one_mul]
      refine (norm_cexp_sub_le _).trans ?_
      calc (2 * π * inner ℝ ξ h) ^ 2 = 4 * π ^ 2 * (inner ℝ ξ h) ^ 2 := by ring
        _ ≤ 4 * π ^ 2 * ((1 + ‖ξ‖) * ‖h‖) ^ 2 := by gcongr
        _ = _ := by ring
    calc _ = ‖a ξ‖ * ‖phase (x + h) ξ - phase x ξ -
          2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) * phase x ξ‖ := norm_mul _ _
      _ ≤ (C * (1 + ‖ξ‖) ^ ℓ) * (4 * π ^ 2 * ‖h‖ ^ 2 * (1 + ‖ξ‖) ^ 2) := by
        gcongr
        exact hC ξ
      _ = 4 * π ^ 2 * C * ‖h‖ ^ 2 * (1 + ‖ξ‖) ^ (ℓ + 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (weight_mono hℓ ξ) (by positivity)
  have hc1 := continuous_phase (x + h)
  have hc2 := continuous_phase x
  have hmeas : Measurable fun ξ => phase (x + h) ξ - phase x ξ -
      2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) * phase x ξ :=
    Continuous.measurable (by fun_prop)
  refine ((integrable_and_norm_le ((hm.mul hmeas).aestronglyMeasurable) hpt g).2).trans
    (le_of_eq ?_)
  ring

theorem contDiff_ampOp (m : ℕ) : ∀ (k ℓ : ℕ) (a : Space → ℂ) (ha : WeightBounded k a),
    WeightBounded ℓ a → ℓ + m + 2 ≤ k → ContDiff ℝ m (ampOp k a ha) := by
  induction m with
  | zero =>
    intro k ℓ a ha haℓ hk
    have hb : ∀ h, WeightBounded k (ampDir a h) :=
      fun h => (ampDir_bound haℓ h).mono (by omega)
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_ampOp ha haℓ (by omega) hb x).continuousAt
  | succ m ih =>
    intro k ℓ a ha haℓ hk
    have hb : ∀ h, WeightBounded k (ampDir a h) :=
      fun h => (ampDir_bound haℓ h).mono (by omega)
    have hD := hasFDerivAt_ampOp ha haℓ (by omega) hb
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hD x).differentiableAt, fun h => by simp at h, fun h => ?_⟩
    have heq : (fun x => fderiv ℝ (ampOp k a ha) x h) = ampOp k (ampDir a h) (hb h) :=
      funext fun x => by rw [(hD x).fderiv]; rfl
    rw [heq]
    exact ih k (ℓ + 1) _ _ (ampDir_bound haℓ h) (by omega)

end Internal

open Internal in
theorem contDiffOn_freqTrInv_curve {T : ℝ} (hT : 0 < T) {c : ℝ → Space → CSpace}
    (hm : ∀ t ∈ Icc 0 T, ∀ k, MemLp (c t) 1 (weightL1Measure k))
    (hc : ∀ k n : ℕ, ContDiffOn ℝ n (fun τ => toWeightL1 k (c τ)) (Icc 0 T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => 𝓕⁻ (c z.1) z.2) (Icc 0 T ×ˢ univ) := by
  refine contDiffOn_infty.2 fun n => ?_
  have h0 : ∀ j, WeightBounded j (fun _ => (1 : ℂ)) := fun j =>
    ⟨measurable_const, 1, fun ξ => by
      rw [norm_one, one_mul]
      exact one_le_pow₀ (by linarith [norm_nonneg ξ])⟩
  have hE := contDiff_ampOp n (n + 2) 0 _ (h0 (n + 2)) (h0 0) (by omega)
  have hG := (hc (n + 2) n).comp (contDiff_fst : ContDiff ℝ n (Prod.fst : ℝ × Space → ℝ)).contDiffOn (fun z (hz : z ∈ Icc 0 T ×ˢ univ) => hz.1)
  refine ((hE.comp (contDiff_snd : ContDiff ℝ n (Prod.snd : ℝ × Space → Space))).contDiffOn.clm_apply hG).congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  simp only [Function.comp_apply, ampOp_apply, one_mul]
  rw [Real.fourierInv_eq', toWeightL1, dif_pos (hm t ht _)]
  refine integral_congr_ae ?_
  filter_upwards [(volume_ac_weight _).ae_le (hm t ht (n + 2)).coeFn_toLp] with ξ hξ
  rw [hξ]
  rfl

end Breakdown.SmoothFlow

import Breakdown.Cert.FreePerturbation
import Breakdown.Cert.TimeModulusGradient
import Breakdown.Cert.TimeModulusTransport

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.TimeModulus

theorem isReadingOf_readingOf (h3 : ReadingExistsHolds) (u : XX) :
    IsReadingOf u (readingOf u).1 (readingOf u).2.1 (readingOf u).2.2 := by
  have h : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 := by
    obtain ⟨v, G, H, hr, -⟩ := h3 u
    exact ⟨(v, G, H), hr⟩
  unfold readingOf
  rw [dif_pos h]
  exact h.choose_spec

theorem periodBallNorm_le_of_lintegral_le {R c : ℝ} {F : ℝ → Space → Space}
    (h : periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal (c ^ 2)) (hc : 0 ≤ c) :
    periodBallNorm R F ≤ c := by
  unfold periodBallNorm
  have h' : (periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2)).toReal ≤ c ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (sq_nonneg c)] at this
  calc Real.sqrt _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h'
    _ = c := Real.sqrt_sq hc

theorem le_of_sq_add_le {s g f : ℝ} (hf : 0 ≤ f)
    (h : s ^ 2 + (1 / 4 : ℝ) * g ^ 2 ≤ f ^ 2) : s ≤ f := by
  nlinarith [sq_nonneg g]

theorem second_le_of_freeInv (h1 : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ‖secondCLM (freeInv P f)‖ ≤ ‖f‖ :=
  le_of_sq_add_le (norm_nonneg _) ((h1 P hP).2 f)

theorem le_two_mul_of_sq_add_le {s g f : ℝ} (hf : 0 ≤ f)
    (h : s ^ 2 + (1 / 4 : ℝ) * g ^ 2 ≤ f ^ 2) : g ≤ 2 * f := by
  nlinarith [sq_nonneg s]

theorem grad_le_of_freeInv (h1 : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ‖gradCLM (freeInv P f)‖ ≤ 2 * ‖f‖ :=
  le_two_mul_of_sq_add_le (norm_nonneg _) ((h1 P hP).2 f)

theorem rate_tendsto {r s : ℝ → ℝ} (C : ℝ) (hr : Tendsto r (𝓝[>] 0) (𝓝 0))
    (hs : Tendsto s (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ => max (r δ) (Real.sqrt (C * (s δ + s δ ^ 2)))) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun δ => C * (s δ + s δ ^ 2)) (𝓝[>] 0) (𝓝 (C * (0 + 0 ^ 2))) :=
    (hs.add (hs.pow 2)).const_mul C
  have hq : Tendsto (fun δ => Real.sqrt (C * (s δ + s δ ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have := h0.sqrt
    simpa using this
  have := hr.max hq
  simpa using this

theorem ofReal_sq_le_max {x m y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ m) :
    ENNReal.ofReal ((x * y) ^ 2) ≤ ENNReal.ofReal ((m * y) ^ 2) :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg hx hy) (mul_le_mul_of_nonneg_right h hy) 2)

theorem column_algebra {C s y S m : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s) (hy : 0 ≤ y)
    (hS : S ≤ y) (hm : Real.sqrt (C * (s + s ^ 2)) ≤ m) :
    C * (s * y * S + (s * y) ^ 2) ≤ (m * y) ^ 2 := by
  have hq0 : 0 ≤ C * (s + s ^ 2) := mul_nonneg hC (by positivity)
  have hsq : (Real.sqrt (C * (s + s ^ 2)) * y) ^ 2 = C * (s + s ^ 2) * y ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq0]
  have h1 : s * y * S ≤ s * y * y := mul_le_mul_of_nonneg_left hS (mul_nonneg hs hy)
  have h2 : C * (s * y * S + (s * y) ^ 2) ≤ C * (s + s ^ 2) * y ^ 2 := by
    have : C * (s * y * S + (s * y) ^ 2) ≤ C * (s * y * y + (s * y) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    nlinarith
  calc C * (s * y * S + (s * y) ^ 2) ≤ (Real.sqrt (C * (s + s ^ 2)) * y) ^ 2 := by rw [hsq]; exact h2
    _ ≤ (m * y) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hy) (mul_le_mul_of_nonneg_right hm hy) 2

theorem norm_toPhysH (x : HBar) : ‖toPhysH x‖ = ‖x‖ :=
  norm_toPhys_of_mem_sig _ x.2

theorem toPhysH_opNorm_le : ‖toPhysH‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [norm_toPhysH, one_mul]

theorem norm_eq_of_ae_norm_eq {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (a : Lp E 2 μ) (b : Lp F 2 μ)
    (h : ∀ᵐ t ∂μ, ‖(a : α → E) t‖ = ‖(b : α → F) t‖) : ‖a‖ = ‖b‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_norm_ae h]

theorem transportCurve_norm_le (f : HH) (u : XX) :
    ‖Internal.FreePerturbation.transportCurve f u‖ ≤ ‖f‖ + ‖secondCLM u‖ := by
  unfold Internal.FreePerturbation.transportCurve
  refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
  · calc _ ≤ ‖ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) toPhysH‖ * ‖f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.norm_compLpL_le _).trans toPhysH_opNorm_le) (norm_nonneg _)
      _ = ‖f‖ := one_mul _
  · have h2 : ∀ᵐ t, (secondCLM u : TimeCircle → HBar) t = secondPart ((u : TimeCircle → XBar) t) :=
      ContinuousLinearMap.coeFn_compLpL _ u
    refine norm_eq_of_ae_norm_eq _ _ ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (toPhysH.comp secondPart) u, h2] with t h1 h2
    exact (congrArg norm h1).trans ((norm_toPhysH _).trans (congrArg norm h2).symm)

theorem periodLIntegral_eq_of_slices {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    (c : ι → Lp (α := TimeCircle) (Lp (α := Space) F 2) 2) (q : ℝ → Space → ℝ)
    (h : ∀ᵐ σ : ℝ, ∀ᵐ y, q σ y = ∑ i, ‖((c i (σ : TimeCircle) : Lp (α := Space) F 2) : Space → F) y‖ ^ 2) :
    periodLIntegral q = ∑ i, ‖c i‖ₑ ^ 2 := by
  have hin : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal (q σ y) = ∑ i, ‖c i (σ : TimeCircle)‖ₑ ^ 2 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [h] with σ hσ
    rw [← Internal.FreePerturbation.lintegral_sum_slices]
    exact lintegral_congr_ae (hσ.mono fun y hy => congrArg ENNReal.ofReal hy)
  unfold periodLIntegral
  rw [lintegral_congr_ae hin]
  have hm : ∀ i, AEMeasurable (fun t : TimeCircle => ‖c i t‖ₑ ^ 2) volume := fun i =>
    (Lp.aestronglyMeasurable (c i)).enorm.pow_const 2
  have hs : AEMeasurable (fun t : TimeCircle => ∑ i, ‖c i t‖ₑ ^ 2) volume :=
    Finset.aemeasurable_fun_sum _ fun i _ => hm i
  refine (lintegral_Icc_coe (fun t : TimeCircle => ∑ i, ‖c i t‖ₑ ^ 2) hs).trans ?_
  rw [lintegral_finsetSum' _ fun i _ => hm i]
  exact Finset.sum_congr rfl fun i _ => Internal.FreePerturbation.lintegral_enorm_sq_Lp (c i)

theorem transportPart_periodLIntegral {f : HH} {u : XX} {g : ℝ → Space → Space}
    (hg : Internal.FreePerturbation.IsTransportPart f u g) :
    periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) = ‖Internal.FreePerturbation.transportCurve f u‖ₑ ^ 2 := by
  have h := periodLIntegral_eq_of_slices (fun _ : Unit => Internal.FreePerturbation.transportCurve f u)
    (fun σ y => ‖g σ y‖ ^ 2) (by
      filter_upwards [hg.2.2] with σ h1
      filter_upwards [h1] with y hy
      simp only [hy, Finset.univ_unique, Finset.sum_singleton])
  simpa using h

theorem enorm_sq_le_ofReal {E : Type*} [NormedAddCommGroup E] {x : E} {c : ℝ} (h : ‖x‖ ≤ c) :
    ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

theorem perturbation_bound (h1 : FreeInvHolds) (h4 : ProjectionHolds) (hB : PropagatorBoundHolds)
    (hG : GradInvHolds) (hGr : GraphClosedHolds) {P : ℝ} (hP : 0 < P) (f : HH)
    (v : VelField) (G : GradField) (H : SecondField) (hr : IsReadingOf (freeInv P f) v G H) :
    ∃ g, IsPerturbation ∅ P v G H g ∧
      periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) ≤ ENNReal.ofReal ((2 * ‖f‖) ^ 2) := by
  choose g hg using Internal.FreePerturbation.exists_transportPart f (freeInv P f)
  refine ⟨g, ⟨hr.measurable_velocity, hr.measurable_gradient, hr.measurable_second, hg.1,
    hr.periodic_velocity, hr.periodic_gradient, hr.periodic_second, hg.2.1, hr.weak_gradient,
    hr.weak_second, Internal.FreePerturbation.divergence_free_of_reading hr,
    Internal.FreePerturbation.sixth_power_of_reading hr,
    Internal.FreePerturbation.gradient_finite_of_reading hr,
    Internal.FreePerturbation.sumSecondPartials_finite_of_reading hr,
    Internal.FreePerturbation.derivative_finite_of_transportPart hg,
    fun φ hφ => Internal.FreePerturbation.transport_of_reading h1 h4 hB hG hGr hP f hr hg φ hφ,
    fun γ hγ => by simp at hγ⟩, ?_⟩
  rw [transportPart_periodLIntegral hg]
  refine enorm_sq_le_ofReal ((transportCurve_norm_le f _).trans ?_)
  have := second_le_of_freeInv h1 hP f
  linarith

def ballFactor (R : ℝ) : ℝ≥0∞ :=
  volume (Metric.closedBall (0 : Space) R) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)

theorem ballFactor_ne_top (R : ℝ) : ballFactor R ≠ ⊤ := by
  unfold ballFactor
  refine ENNReal.rpow_ne_top_of_nonneg ?_ (measure_closedBall_lt_top).ne
  norm_num

theorem ball_lintegral_le (w : L6R) (R : ℝ) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ‖(w : Space → Space) y‖ₑ ^ 2 ≤ (‖w‖ₑ * ballFactor R) ^ 2 := by
  rw [← JointRepresentativeInternal.sq_eLpNorm_two]
  refine pow_le_pow_left₀ (by simp) ?_ 2
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6) (by norm_num)
    (Lp.aestronglyMeasurable w).restrict).trans ?_
  rw [Measure.restrict_apply_univ]
  exact mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq (Lp.enorm_def w).symm) le_rfl

theorem ofReal_sq_mul_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a ^ 2 * ENNReal.ofReal b ^ 2 = ENNReal.ofReal ((a * b) ^ 2) := by
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

theorem slice_velocity_le (x : X) (R : ℝ) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ‖(velocity x : Space → Space) y‖ₑ ^ 2 ≤
      (‖velocity‖ₑ * ballFactor R) ^ 2 * ‖x‖ₑ ^ 2 := by
  refine (ball_lintegral_le _ R).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by simp) ?_ 2
  rw [mul_right_comm]
  exact mul_le_mul' (ContinuousLinearMap.le_opENorm_of_le velocity le_rfl) le_rfl

theorem ofReal_norm_sq_eq {E : Type*} [NormedAddCommGroup E] (a : E) :
    ENNReal.ofReal (‖a‖ ^ 2) = ‖a‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem enorm_factor_eq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {K : ℝ≥0∞}
    (hK : K ≠ ⊤) (x : E) (y : F) :
    (‖x‖ₑ * K) ^ 2 * ‖y‖ₑ ^ 2 = ENNReal.ofReal ((‖x‖ * K.toReal * ‖y‖) ^ 2) := by
  calc (‖x‖ₑ * K) ^ 2 * ‖y‖ₑ ^ 2
      = (ENNReal.ofReal ‖x‖ * ENNReal.ofReal K.toReal) ^ 2 * ENNReal.ofReal ‖y‖ ^ 2 := by
        rw [ofReal_norm, ofReal_norm, ENNReal.ofReal_toReal hK]
    _ = ENNReal.ofReal ((‖x‖ * K.toReal * ‖y‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _),
          ofReal_sq_mul_sq (mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg) (norm_nonneg _)]

theorem velocity_ball_slice {x : X} {w : Space → Space} (h : w =ᵐ[volume] (velocity x : Space → Space))
    (R : ℝ) : ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖w y‖ ^ 2) ≤
      (‖velocity‖ₑ * ballFactor R) ^ 2 * ‖x‖ₑ ^ 2 := by
  refine le_trans (le_of_eq ?_) (slice_velocity_le x R)
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  exact (congrArg (fun a : Space => ENNReal.ofReal (‖a‖ ^ 2)) hy).trans (ofReal_norm_sq_eq _)

theorem period_const_mul_le {E : Type*} [NormedAddCommGroup E] {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (q : ℝ → ℝ≥0∞) (w : Lp (α := TimeCircle) E 2)
    (hin : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), q σ ≤ A * ‖w (σ : TimeCircle)‖ₑ ^ 2) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, q σ ≤ A * ‖w‖ₑ ^ 2 := by
  refine (lintegral_mono_ae hin).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ hA]
  have hm : AEMeasurable (fun t : TimeCircle => ‖w t‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable _).enorm.pow_const 2
  rw [lintegral_Icc_coe (fun t : TimeCircle => ‖w t‖ₑ ^ 2) hm,
    Internal.FreePerturbation.lintegral_enorm_sq_Lp]

theorem local_velocity_le (R : ℝ) (u : XX) (v : VelField) (G : GradField) (H : SecondField)
    (hr : IsReadingOf u v G H) :
    periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) ≤
      ENNReal.ofReal ((‖velocity‖ * (ballFactor R).toReal * ‖gradCLM u‖) ^ 2) := by
  have hg : ∀ᵐ t : TimeCircle, (gradCLM u : TimeCircle → HBar) t = gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ u
  have hg' := (ae_coe_iff _).1 hg
  have hin : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖v σ y‖ ^ 2) ≤
        (‖velocity‖ₑ * ballFactor R) ^ 2 * ‖(gradCLM u : TimeCircle → HBar) (σ : TimeCircle)‖ₑ ^ 2 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hr.velocity_eq, hg'] with σ h1 h2
    exact (velocity_ball_slice h1 R).trans_eq
      (congrArg (fun z : X => (‖velocity‖ₑ * ballFactor R) ^ 2 * ‖z‖ₑ ^ 2) h2.symm)
  exact (period_const_mul_le (ENNReal.pow_ne_top (ENNReal.mul_ne_top enorm_ne_top (ballFactor_ne_top R)))
    _ (gradCLM u) hin).trans_eq (enorm_factor_eq (ballFactor_ne_top R) velocity (gradCLM u))

theorem local_velocity_bound (R : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u : XX) (v : VelField) (G : GradField) (H : SecondField),
      IsReadingOf u v G H →
        periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) ≤ ENNReal.ofReal ((c * ‖gradCLM u‖) ^ 2) :=
  ⟨‖velocity‖ * (ballFactor R).toReal, mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    fun u v G H hr => local_velocity_le R u v G H hr⟩

theorem sum_enorm_partialX_sq (z : X) : ∑ i : Fin 3, ‖partialX i z‖ₑ ^ 2 = ‖z‖ₑ ^ 2 := by
  rw [← Internal.FreePerturbation.ofReal_sum_norm_sq (fun i => partialX i z),
    Internal.SliceFields.sum_norm_partialX_sq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem sum_enorm_column_le (u : XX) :
    ∑ i : Fin 3, ‖ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u‖ₑ ^ 2 ≤
      ENNReal.ofReal (‖gradCLM u‖ ^ 2) := by
  have hm : ∀ i : Fin 3, AEMeasurable (fun t : TimeCircle =>
      ‖ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u t‖ₑ ^ 2) volume := fun i =>
    (Lp.aestronglyMeasurable _).enorm.pow_const 2
  have hc' : ∀ i : Fin 3, ∀ᵐ t : TimeCircle,
      ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u t =
        partialX i (gradPart ((u : TimeCircle → XBar) t)) := fun i =>
    ContinuousLinearMap.coeFn_compLpL _ u
  have hg : ∀ᵐ t : TimeCircle, (gradCLM u : TimeCircle → HBar) t = gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ u
  calc ∑ i : Fin 3, ‖ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u‖ₑ ^ 2
      = ∑ i : Fin 3, ∫⁻ t, ‖ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u t‖ₑ ^ 2 :=
        Finset.sum_congr rfl fun i _ => (Internal.FreePerturbation.lintegral_enorm_sq_Lp _).symm
    _ = ∫⁻ t, ∑ i : Fin 3, ‖ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u t‖ₑ ^ 2 :=
        (lintegral_finsetSum' _ fun i _ => hm i).symm
    _ = ∫⁻ t, ‖(gradCLM u : TimeCircle → HBar) t‖ₑ ^ 2 := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_all_iff.2 hc', hg] with t h3 h4
        calc ∑ i : Fin 3, ‖ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u t‖ₑ ^ 2
            = ∑ i : Fin 3, ‖partialX i (gradPart ((u : TimeCircle → XBar) t))‖ₑ ^ 2 :=
              Finset.sum_congr rfl fun i _ => congrArg (fun x => ‖x‖ₑ ^ 2) (h3 i)
          _ = ‖gradPart ((u : TimeCircle → XBar) t)‖ₑ ^ 2 := sum_enorm_partialX_sq _
          _ = ‖(gradCLM u : TimeCircle → HBar) t‖ₑ ^ 2 := congrArg (fun x => ‖x‖ₑ ^ 2) h4.symm
    _ = ‖gradCLM u‖ₑ ^ 2 := Internal.FreePerturbation.lintegral_enorm_sq_Lp _
    _ ≤ _ := enorm_sq_le_ofReal le_rfl

theorem gradient_energy_bound (u : XX) (v : VelField) (G : GradField) (H : SecondField)
    (hr : IsReadingOf u v G H) :
    periodLIntegral (fun σ y => matSq (G σ y)) ≤ ENNReal.ofReal (‖gradCLM u‖ ^ 2) := by
  refine le_of_eq_of_le (periodLIntegral_eq_of_slices
    (fun i : Fin 3 => ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u) _ ?_)
    (sum_enorm_column_le u)
  have hc : ∀ i : Fin 3, ∀ᵐ σ : ℝ,
      (ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u (σ : TimeCircle) : L2R) =
        partialX i (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := fun i =>
    (ae_coe_iff _).1 (ContinuousLinearMap.coeFn_compLpL _ u)
  filter_upwards [hr.velocity_eq, hr.weak_gradient, ae_all_iff.2 hc] with σ h1 h2 h3
  filter_upwards [ae_all_iff.2 (Internal.FreePerturbation.column_ae_eq_partialX _ h2 h1)] with y hy
  simp only [matSq, hy, h3]

theorem sq_le_of_le {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ y) : ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (y ^ 2) :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hx h 2)

theorem velocity_algebra {c F N : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ F) (hNF : N ≤ 2 * F) :
    0 ≤ (2 + 2 * c) * F ∧ 2 * F ≤ (2 + 2 * c) * F ∧ c * N ≤ (2 + 2 * c) * F := by
  refine ⟨by positivity, by nlinarith, ?_⟩
  have : c * N ≤ c * (2 * F) := mul_le_mul_of_nonneg_left hNF hc
  nlinarith

theorem sqrt_rate_sq {C δ K F : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    C * δ * (K * F) ^ 2 = (Real.sqrt (C * δ) * K * F) ^ 2 := by
  rw [show (Real.sqrt (C * δ) * K * F) ^ 2 = Real.sqrt (C * δ) ^ 2 * K ^ 2 * F ^ 2 by ring,
    Real.sq_sqrt (mul_nonneg hC hδ)]
  ring

theorem velocity_shift_bound (h1 : FreeInvHolds) (h3 : ReadingExistsHolds) (h4 : ProjectionHolds)
    (hB : PropagatorBoundHolds) (hG : GradInvHolds) (hGr : GraphClosedHolds) (a b R : ℝ) (ha : 0 < a) (hR : 0 < R) :
    ∃ rate : ℝ → ℝ, Tendsto rate (𝓝[>] 0) (𝓝 0) ∧ (∀ δ, 0 ≤ rate δ) ∧
      ∀ P ∈ Set.Icc a b, ∀ f : HH, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
        periodBallLIntegral R (fun σ y => ‖(readingOf (freeInv P f)).1 (σ + δ) y
          - (readingOf (freeInv P f)).1 σ y‖ ^ 2) ≤ ENNReal.ofReal ((rate δ * ‖f‖) ^ 2) := by
  choose c hc hcb using local_velocity_bound R
  choose C hC hCb using transport_shift_bound b R hR
  refine ⟨fun δ => Real.sqrt (C * δ) * (2 + 2 * c), ?_, fun δ => by positivity, ?_⟩
  · have h0 : Tendsto (fun δ : ℝ => C * δ) (𝓝[>] 0) (𝓝 (C * 0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_mul C
    have := (h0.sqrt).mul_const (2 + 2 * c)
    simpa using this
  · intro P hP f δ hδ
    have hPpos : 0 < P := lt_of_lt_of_le ha hP.1
    have hread := isReadingOf_readingOf h3 (freeInv P f)
    choose g hg hgb using perturbation_bound h1 h4 hB hG hGr hPpos f _ _ _ hread
    have hgr := grad_le_of_freeInv h1 hPpos f
    have hgn := norm_nonneg (gradCLM (freeInv P f))
    have hva := velocity_algebra hc (norm_nonneg f) hgr
    have hM := hva.1
    have e1 := hva.2.1
    have e2 := hva.2.2
    have hb := hCb P hPpos hP.2 _ _ _ g hg ((2 + 2 * c) * ‖f‖) hM
      (le_trans hgb (sq_le_of_le (mul_nonneg zero_le_two (norm_nonneg f)) e1))
      (le_trans (gradient_energy_bound _ _ _ _ hread)
        (sq_le_of_le hgn (le_trans hgr e1)))
      (le_trans (hcb _ _ _ _ hread) (sq_le_of_le (mul_nonneg hc hgn) e2)) δ hδ
    refine le_trans hb (le_of_eq ?_)
    rw [sqrt_rate_sq hC hδ.1.le]

end Internal.TimeModulus

open Internal.TimeModulus in
theorem timeModulusHolds_of (h1 : FreeInvHolds) (h3 : ReadingExistsHolds) (h4 : ProjectionHolds)
    (hB : PropagatorBoundHolds) (hG : GradInvHolds) (hGr : GraphClosedHolds) : TimeModulusHolds := by
  intro a b R ha hR
  choose r hr hr0 hrb using velocity_shift_bound h1 h3 h4 hB hG hGr a b R ha hR
  choose s hs hs0 hsb using velocity_shift_bound h1 h3 h4 hB hG hGr a b (R + 1) ha (by linarith)
  choose C hC hCb using gradient_shift_bound R hR
  refine ⟨fun δ => max (r δ) (Real.sqrt (C * (s δ + s δ ^ 2))), rate_tendsto C hr hs, ?_⟩
  intro P hP f δ hδ
  have hPpos : 0 < P := lt_of_lt_of_le ha hP.1
  refine ⟨?_, fun j => ?_⟩
  · exact periodBallNorm_le_of_lintegral_le
      (le_trans (hrb P hP f δ hδ) (ofReal_sq_le_max (hr0 δ) (norm_nonneg f) (le_max_left _ _)))
      (mul_nonneg (le_trans (hr0 δ) (le_max_left _ _)) (norm_nonneg f))
  · have hcol := hCb _ _ _ _ (isReadingOf_readingOf h3 (freeInv P f)) δ (s δ * ‖f‖) j
      (mul_nonneg (hs0 δ) (norm_nonneg f)) (hsb P hP f δ hδ)
    exact periodBallNorm_le_of_lintegral_le
      (le_trans hcol (ENNReal.ofReal_le_ofReal (column_algebra hC (hs0 δ) (norm_nonneg f)
        (second_le_of_freeInv h1 hPpos f) (le_max_right _ _))))
      (mul_nonneg (le_trans (Real.sqrt_nonneg _) (le_max_right _ _)) (norm_nonneg f))

end Breakdown.Cert

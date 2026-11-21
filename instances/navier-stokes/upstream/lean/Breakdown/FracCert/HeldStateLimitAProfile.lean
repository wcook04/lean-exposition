import Breakdown.FracCert.HeldStateLimitADefect
import Breakdown.FracCert.SixthGradientBound
import Breakdown.FracCert.FreeExists
import Breakdown.Frac.NNiceField

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

def ProfilePowerTestLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Tendsto p atTop (nhds q) → ∀ ψ : Space → Space, IsTestVectorField ψ →
        Tendsto (fun n => ∫ y, inner ℝ (d.profilePower (p n) y) (ψ y)) atTop
          (nhds (∫ y, inner ℝ (d.profilePower q y) (ψ y)))

namespace ProfileTestInternal

theorem test_bound {ψ : Space → Space} (hψ : IsTestVectorField ψ) :
    ∃ M r : ℝ, 0 ≤ M ∧ (∀ y, ‖ψ y‖ ≤ M) ∧ ∀ y, y ∉ Metric.ball (0 : Space) r → ψ y = 0 := by
  obtain ⟨M₁, hM₁⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2
  obtain ⟨r, hr⟩ := hψ.2.isCompact.isBounded.subset_ball (0 : Space)
  exact ⟨max M₁ 0, r, le_max_right _ _, fun y => (hM₁ y).trans (le_max_left _ _),
    fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hr h))⟩

theorem pair_int {A : Space → (Space →L[ℝ] Space)} (hAm : AEStronglyMeasurable A volume)
    (hAi : Integrable (fun y => entrySq (A y))) {b : Space → Space} (hbm : AEStronglyMeasurable b volume)
    (hbi : ∀ r, IntegrableOn (fun y => ‖b y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) : Integrable (fun y => inner ℝ (A y (b y)) (ψ y)) volume := by
  obtain ⟨M, r, hM0, hM, hz⟩ := test_bound hψ
  exact (ApplyPairingInternal.small_bound hAm hAi hbm hψ.1.continuous hM0 hM hz (hbi r)).1

def cutoff (L : Space →L[ℝ] Space) (r : ℝ) : Space → (Space →L[ℝ] Space) :=
  fun y => (Metric.ball (0 : Space) r).indicator (fun _ => L) y

theorem cutoff_meas (L : Space →L[ℝ] Space) (r : ℝ) : AEStronglyMeasurable (cutoff L r) volume :=
  (aestronglyMeasurable_const (b := L)).indicator measurableSet_ball

theorem cutoff_sq (L : Space →L[ℝ] Space) (r : ℝ) : Integrable (fun y => entrySq (cutoff L r y)) volume := by
  have hi : Integrable ((Metric.ball (0 : Space) r).indicator (fun _ => entrySq L)) volume :=
    (integrableOn_const (measure_ball_lt_top (x := (0 : Space)) (r := r)).ne).integrable_indicator
      measurableSet_ball
  refine hi.congr (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Metric.ball (0 : Space) r
  · simp [cutoff, Set.indicator_of_mem hy]
  · simp [cutoff, Set.indicator_of_notMem hy, entrySq]

theorem cutoff_pair (L : Space →L[ℝ] Space) {r : ℝ} {ψ : Space → Space}
    (hz : ∀ y, y ∉ Metric.ball (0 : Space) r → ψ y = 0) (x y : Space) :
    inner ℝ (cutoff L r y x) (ψ y) = inner ℝ (L x) (ψ y) := by
  by_cases hy : y ∈ Metric.ball (0 : Space) r
  · simp [cutoff, Set.indicator_of_mem hy]
  · simp [hz y hy]

theorem fixed_pair_limit (L : Space →L[ℝ] Space) {a : ℕ → Space → Space} {a₀ : Space → Space}
    (ham : ∀ n, AEStronglyMeasurable (a n) volume) (ha₀m : AEStronglyMeasurable a₀ volume)
    (hai : ∀ n r, IntegrableOn (fun y => ‖a n y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    (ha₀i : ∀ r, IntegrableOn (fun y => ‖a₀ y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    (hloc : ∀ r, Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖a n y - a₀ y‖ ^ 2) atTop (nhds 0))
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) :
    Tendsto (fun n => ∫ y, inner ℝ (L (a n y)) (ψ y)) atTop (nhds (∫ y, inner ℝ (L (a₀ y)) (ψ y))) := by
  obtain ⟨M, r, hM0, hM, hz⟩ := test_bound hψ
  have h := ApplyPairingInternal.apply_pairing_limit (A := fun _ => cutoff L r) (A₀ := cutoff L r)
    (K := ∫ y, entrySq (cutoff L r y)) (fun _ => cutoff_meas L r) (fun _ => cutoff_sq L r) (fun _ => le_rfl)
    (fun E _ _ => tendsto_const_nhds) ham ha₀m hai ha₀i hloc hψ
  simp only [cutoff_pair L hz] at h
  exact h

theorem pair_int_fixed (L : Space →L[ℝ] Space) {b : Space → Space} (hbm : AEStronglyMeasurable b volume)
    (hbi : ∀ r, IntegrableOn (fun y => ‖b y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) : Integrable (fun y => inner ℝ (L (b y)) (ψ y)) volume := by
  obtain ⟨M, r, hM0, hM, hz⟩ := test_bound hψ
  have h := pair_int (cutoff_meas L r) (cutoff_sq L r) hbm hbi hψ
  simp only [cutoff_pair L hz] at h
  exact h

theorem grad_sq_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} {d : FracCertData k N}
    (hd : IsFracCert α d) {p : ℕ → Fin k → ℝ} {q : Fin k → ℝ} (hp : ∀ n, p n ∈ box d.radius)
    (hq : q ∈ box d.radius) (hdn : Tendsto (fun n => ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y))
      atTop (nhds 0)) :
    ∃ K : ℝ, ∀ n, ∫ y, entrySq (d.gradProfile (p n) y) ≤ K := by
  have hemb := fun p' (hp' : p' ∈ box d.radius) => profileEmbedData α hα1 hα2 d hd p' hp'
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hdn)
  refine ⟨2 * D + 2 * ∫ y, entrySq (d.gradProfile q y), fun n => ?_⟩
  have hsub := CrossTestInternal.entrySq_sub_integrable (hemb _ (hp n)).2.2.1 (hemb _ (hp n)).2.2.2.1
    (hemb q hq).2.2.1 (hemb q hq).2.2.2.1
  have hDn : ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y) ≤ D := by
    have := hD _ ⟨n, rfl⟩
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have hh : ∀ a b : Space, ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have h3 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
      calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
        _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]
  calc ∫ y, entrySq (d.gradProfile (p n) y) ≤
      ∫ y, (2 * entrySq (d.gradProfile (p n) y - d.gradProfile q y) + 2 * entrySq (d.gradProfile q y)) := by
        refine integral_mono (hemb _ (hp n)).2.2.2.1 ((hsub.const_mul 2).add ((hemb q hq).2.2.2.1.const_mul 2))
          fun y => ?_
        simp only [entrySq, sub_apply, Fin.sum_univ_three]
        linarith [hh (d.gradProfile (p n) y (unitVector 0)) (d.gradProfile q y (unitVector 0)),
          hh (d.gradProfile (p n) y (unitVector 1)) (d.gradProfile q y (unitVector 1)),
          hh (d.gradProfile (p n) y (unitVector 2)) (d.gradProfile q y (unitVector 2))]
    _ = 2 * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) + 2 * ∫ y, entrySq (d.gradProfile q y) := by
        rw [integral_add (hsub.const_mul 2) ((hemb q hq).2.2.2.1.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by linarith

theorem combine {f1 f2 f3 f4 f5 : Space → ℝ} (c₁ c₂ a : ℝ) (h1 : Integrable f1 volume)
    (h2 : Integrable f2 volume) (h3 : Integrable f3 volume) (h4 : Integrable f4 volume)
    (h5 : Integrable f5 volume) :
    ∫ y, (c₁ * f1 y + c₂ * f2 y + a * (f3 y - f4 y) + f5 y) =
      c₁ * (∫ y, f1 y) + c₂ * (∫ y, f2 y) + a * ((∫ y, f3 y) - ∫ y, f4 y) + ∫ y, f5 y := by
  have i1 : Integrable (fun y => c₁ * f1 y) volume := h1.const_mul c₁
  have i2 : Integrable (fun y => c₂ * f2 y) volume := h2.const_mul c₂
  have i34 : Integrable (fun y => a * (f3 y - f4 y)) volume := (h3.sub h4).const_mul a
  have i12 : Integrable (fun y => c₁ * f1 y + c₂ * f2 y) volume := i1.add i2
  have i123 : Integrable (fun y => c₁ * f1 y + c₂ * f2 y + a * (f3 y - f4 y)) volume := i12.add i34
  rw [integral_add i123 h5, integral_add i12 i34, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_sub h3 h4]

end ProfileTestInternal

open ProfileTestInternal in
theorem profileFreeTestLimit_of (hpow : ProfilePowerTestLimitStatement) : ProfileFreeTestLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq ψ hψ
  have hemb := fun p' (hp' : p' ∈ box d.radius) => profileEmbedData α hα1 hα2 d hd p' hp'
  have hWc : ∀ p' ∈ box d.radius, Continuous (d.profile p') := fun p' hp' => (hd.profile_smooth p' hp').continuous
  have hψ2 : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
  set T := HeldWeakProfilePartsInternal.turnCLM
  have hloc := profileLocalLimit α hα1 hα2 d hd p q hp hq hpq
  have hWi := fun n r => CrossTestInternal.cont_sq (hWc _ (hp n)) r
  have hWqi := CrossTestInternal.cont_sq (hWc q hq)
  have hWm : ∀ n, AEStronglyMeasurable (d.profile (p n)) volume := fun n => (hWc _ (hp n)).aestronglyMeasurable
  have hWqm : AEStronglyMeasurable (d.profile q) volume := (hWc q hq).aestronglyMeasurable
  have t1 := fixed_pair_limit (ContinuousLinearMap.id ℝ Space) hWm hWqm hWi hWqi hloc hψ
  have t4 := fixed_pair_limit T hWm hWqm hWi hWqi hloc hψ
  have hdn := CrossTestInternal.grad_tendsto hd hp hq hpq
  obtain ⟨K, hK⟩ := grad_sq_bound hα1 hα2 hd hp hq hdn
  have hDm := fun p' (hp' : p' ∈ box d.radius) => (hemb p' hp').2.2.1
  have hDi := fun p' (hp' : p' ∈ box d.radius) => (hemb p' hp').2.2.2.1
  have hw := CrossTestInternal.strong_weak (fun n => hDm _ (hp n)) (fun n => hDi _ (hp n)) (hDm q hq)
    (hDi q hq) hdn
  have hzero : ∀ (g : Space → Space) (r : ℝ),
      Tendsto (fun _ : ℕ => ∫ y in Metric.ball (0 : Space) r, ‖g y - g y‖ ^ 2) atTop (nhds 0) := by
    intro g r
    simp
  have t2 := ApplyPairingInternal.apply_pairing_limit (A := fun n => d.gradProfile (p n)) (A₀ := d.gradProfile q)
    (a := fun _ => fun y => y) (a₀ := fun y => y) (fun n => hDm _ (hp n)) (fun n => hDi _ (hp n)) hK hw
    (fun _ => (continuous_id.aestronglyMeasurable (μ := volume))) (continuous_id.aestronglyMeasurable (μ := volume))
    (fun _ r => CrossTestInternal.cont_sq continuous_id r) (CrossTestInternal.cont_sq continuous_id)
    (hzero (fun y => y)) hψ
  have t3 := ApplyPairingInternal.apply_pairing_limit (A := fun n => d.gradProfile (p n)) (A₀ := d.gradProfile q)
    (a := fun _ => fun y => T y) (a₀ := fun y => T y) (fun n => hDm _ (hp n)) (fun n => hDi _ (hp n)) hK hw
    (fun _ => (T.continuous.aestronglyMeasurable (μ := volume))) (T.continuous.aestronglyMeasurable (μ := volume))
    (fun _ r => CrossTestInternal.cont_sq T.continuous r) (CrossTestInternal.cont_sq T.continuous)
    (hzero (fun y => T y)) hψ
  have t5 := hpow α hα1 hα2 d hd p q hp hq hpq ψ hψ
  have ha : Tendsto (fun n => d.rotationRate (p n)) atTop (nhds (d.rotationRate q)) :=
    (hd.rotationRate_continuous q hq).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpq, Eventually.of_forall hp⟩)
  have expand : ∀ p' ∈ box d.radius, ∫ y, inner ℝ (driftField α (d.rotationRate p') (d.profile p')
      (d.gradProfile p') y + d.profilePower p' y) (ψ y) =
      (1 - 1 / (2 * α)) * (∫ y, inner ℝ (ContinuousLinearMap.id ℝ Space (d.profile p' y)) (ψ y))
        + (1 / (2 * α)) * (∫ y, inner ℝ (d.gradProfile p' y y) (ψ y))
        + d.rotationRate p' * ((∫ y, inner ℝ (d.gradProfile p' y (T y)) (ψ y))
          - ∫ y, inner ℝ (T (d.profile p' y)) (ψ y))
        + ∫ y, inner ℝ (d.profilePower p' y) (ψ y) := by
    intro p' hp'
    rw [← combine _ _ _ (pair_int_fixed (ContinuousLinearMap.id ℝ Space) ((hWc p' hp').aestronglyMeasurable (μ := volume)) (CrossTestInternal.cont_sq (hWc p' hp')) hψ)
      (pair_int (hDm p' hp') (hDi p' hp') (b := fun y => y) (continuous_id.aestronglyMeasurable (μ := volume))
        (CrossTestInternal.cont_sq continuous_id) hψ)
      (pair_int (hDm p' hp') (hDi p' hp') (b := fun y => T y) (T.continuous.aestronglyMeasurable (μ := volume))
        (CrossTestInternal.cont_sq T.continuous) hψ)
      (pair_int_fixed T ((hWc p' hp').aestronglyMeasurable (μ := volume)) (CrossTestInternal.cont_sq (hWc p' hp')) hψ)
      (ActiveEnclosureInternal.pair_integrable (hd.profile_power p' hp').1 hψ2)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [driftField, inner_add_left, inner_sub_left, real_inner_smul_left, ContinuousLinearMap.id_apply,
      HeldWeakProfilePartsInternal.turnCLM_apply, T]
  rw [expand q hq]
  exact ((((t1.const_mul _).add (t2.const_mul _)).add (ha.mul (t3.sub t4))).add t5).congr
    (fun n => (expand (p n) (hp n)).symm)

theorem profilePowerTestLimit : ProfilePowerTestLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq ψ hψ
  obtain ⟨C, hC⟩ := ActiveEnclosureInternal.profile_bounds_of hd
  have hemb := fun p' (hp' : p' ∈ box d.radius) => profileEmbedData α hα1 hα2 d hd p' hp'
  have hg6 : MemLp (fractionalPowerAt α ψ) (ENNReal.ofReal (6 / 5)) volume :=
    FreeExistsInternal.power_memLp hα1 (by linarith) hψ
  have hgi : Integrable (fractionalPowerAt α ψ) volume := by
    have := FracInternal.NiceField.integrable_fracPower α hα1 (by linarith) (hψ.2.toSchwartzMap hψ.1)
    exact this
  have hpw : ∀ p' ∈ box d.radius, ∫ y, inner ℝ (d.profilePower p' y) (ψ y) =
      ∫ y, inner ℝ (d.profile p' y) (fractionalPowerAt α ψ y) := fun p' hp' => (hd.profile_power p' hp').2 ψ hψ
  have hint : ∀ p' ∈ box d.radius, Integrable (fun y => inner ℝ (d.profile p' y) (fractionalPowerAt α ψ y)) volume := by
    intro p' hp'
    refine (hgi.norm.const_mul |C|).mono' ((hemb p' hp').1.inner hgi.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (ActiveEnclosureInternal.profile_le (fun y => (hC p' hp' y).1) y) (norm_nonneg _))
  obtain ⟨C₆, hC₆⟩ := sixthGradientBound
  have hdn := CrossTestInternal.grad_tendsto hd hp hq hpq
  have hq2 := CrossTestInternal.profile_second_order hα1 hα2 hd hq
  have h6 : ∀ n, ∫ y, ‖d.profile (p n) y - d.profile q y‖ ^ 6 ≤
      C₆ * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) ^ 3 := by
    intro n
    have hs := secondOrderLinear d.order _ _ _ _ _ _ (-1)
      (CrossTestInternal.profile_second_order hα1 hα2 hd (hp n)) hq2
    have h := hC₆ _ _ hs.measurable_velocity hs.velocity_six hs.gradient_two hs.weak_gradient
    simpa only [neg_one_smul, ← sub_eq_add_neg] using h
  have hf6 : ∀ n, MemLp (fun y => ‖d.profile (p n) y - d.profile q y‖) (ENNReal.ofReal 6) volume := by
    intro n
    have := ((hemb _ (hp n)).2.1.sub (hemb q hq).2.1).norm
    simpa using this
  have hG : Real.HolderConjugate 6 (6 / 5) := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  set Γ := (∫ y, ‖fractionalPowerAt α ψ y‖ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ))
  have hbound : ∀ n, |(∫ y, inner ℝ (d.profile (p n) y) (fractionalPowerAt α ψ y))
      - ∫ y, inner ℝ (d.profile q y) (fractionalPowerAt α ψ y)| ≤
      (C₆ * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) ^ 3) ^ (1 / (6 : ℝ)) * Γ := by
    intro n
    rw [← integral_sub (hint _ (hp n)) (hint q hq)]
    have e : (fun y => inner ℝ (d.profile (p n) y) (fractionalPowerAt α ψ y)
        - inner ℝ (d.profile q y) (fractionalPowerAt α ψ y)) =
        fun y => inner ℝ (d.profile (p n) y - d.profile q y) (fractionalPowerAt α ψ y) := by
      funext y; rw [inner_sub_left]
    rw [e]
    have hi := (hint _ (hp n)).sub (hint q hq)
    have hi' : Integrable (fun y => inner ℝ (d.profile (p n) y - d.profile q y) (fractionalPowerAt α ψ y)) volume := by
      rw [← e]; exact hi
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hG (Eventually.of_forall fun y => norm_nonneg _)
      (Eventually.of_forall fun y => norm_nonneg _) (hf6 n) hg6.norm
    have hpow : ∫ y, ‖d.profile (p n) y - d.profile q y‖ ^ (6 : ℝ) = ∫ y, ‖d.profile (p n) y - d.profile q y‖ ^ 6 := by
      congr 1; funext y
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow] at hH
    have hmono : (∫ y, ‖d.profile (p n) y - d.profile q y‖ ^ 6) ^ (1 / (6 : ℝ)) ≤
        (C₆ * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) ^ 3) ^ (1 / (6 : ℝ)) :=
      Real.rpow_le_rpow (integral_nonneg fun y => by positivity) (h6 n) (by norm_num)
    have hΓ : 0 ≤ Γ := Real.rpow_nonneg (integral_nonneg fun y => by positivity) _
    have hprod : Integrable (fun y => ‖d.profile (p n) y - d.profile q y‖ * ‖fractionalPowerAt α ψ y‖) volume := by
      refine (hgi.norm.const_mul (2 * |C|)).mono'
        ((((hemb _ (hp n)).1.sub (hemb q hq).1).norm).mul hgi.aestronglyMeasurable.norm)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : ‖d.profile (p n) y - d.profile q y‖ ≤ 2 * |C| := by
        have a1 := ActiveEnclosureInternal.profile_le (fun y => (hC _ (hp n) y).1) y
        have a2 := ActiveEnclosureInternal.profile_le (fun y => (hC q hq y).1) y
        linarith [norm_sub_le (d.profile (p n) y) (d.profile q y)]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    calc |∫ y, inner ℝ (d.profile (p n) y - d.profile q y) (fractionalPowerAt α ψ y)|
        ≤ ∫ y, |inner ℝ (d.profile (p n) y - d.profile q y) (fractionalPowerAt α ψ y)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, ‖d.profile (p n) y - d.profile q y‖ * ‖fractionalPowerAt α ψ y‖ := by
          exact integral_mono hi'.abs hprod fun y => abs_real_inner_le_norm _ _
      _ ≤ _ := hH
      _ ≤ _ := mul_le_mul_of_nonneg_right hmono hΓ
  rw [hpw q hq]
  refine Tendsto.congr (fun n => (hpw (p n) (hp n)).symm) ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) (a := fun n =>
    (C₆ * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) ^ 3) ^ (1 / (6 : ℝ)) * Γ) ?_
  · rw [norm_norm, Real.norm_eq_abs]
    exact hbound n
  · have h1 : Tendsto (fun n => C₆ * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) ^ 3) atTop
        (nhds 0) := by simpa using (hdn.pow 3).const_mul C₆
    have h2 := (h1.rpow_const (p := 1 / (6 : ℝ)) (Or.inr (by norm_num))).mul_const Γ
    simpa [Real.zero_rpow (show (1 / (6 : ℝ)) ≠ 0 by norm_num)] using h2

end SteadyCert

end Breakdown

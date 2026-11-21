import Breakdown.Cert.ExtendedNodes

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedSigmaProfileOfHeld

theorem isWeakGradient_of_contDiff {f : Space → Space} (hf : ContDiff ℝ 1 f) :
    IsWeakGradient f (fderiv ℝ f) := by
  refine ⟨hf.continuous.locallyIntegrable, (hf.continuous_fderiv one_ne_zero).locallyIntegrable,
    fun φ hφ i => ?_⟩
  have hφc : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hφd : Continuous fun y => fderiv ℝ φ y (unitVector i) :=
    (hφc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfd : Continuous fun y => fderiv ℝ f y (unitVector i) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable ?_ ?_ ?_
    (fun y _ => (hφc.differentiable one_ne_zero) y) (fun y _ => (hf.differentiable one_ne_zero) y)
  · exact (hφd.smul hf.continuous).integrable_of_hasCompactSupport
      ((hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right)
  · exact (hφc.continuous.smul hfd).integrable_of_hasCompactSupport hφ.2.smul_right
  · exact (hφc.continuous.smul hf.continuous).integrable_of_hasCompactSupport hφ.2.smul_right

theorem isWeakGradient_add {f₁ f₂ : Space → Space} {g₁ g₂ : Space → (Space →L[ℝ] Space)}
    (h₁ : IsWeakGradient f₁ g₁) (h₂ : IsWeakGradient f₂ g₂) :
    IsWeakGradient (fun y => f₁ y + f₂ y) (fun y => g₁ y + g₂ y) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ hφ i => ?_⟩
  have hφc : Continuous φ := hφ.1.continuous
  have hφd : Continuous fun y => fderiv ℝ φ y (unitVector i) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφs : HasCompactSupport fun y => fderiv ℝ φ y (unitVector i) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)
  have hg : ∀ g : Space → (Space →L[ℝ] Space), LocallyIntegrable g →
      Integrable fun y => φ y • g y (unitVector i) := by
    intro g hgl
    have h := (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrable_comp
      (hgl.integrable_smul_left_of_hasCompactSupport hφc hφ.2)
    simpa using h
  have hf : ∀ f : Space → Space, LocallyIntegrable f →
      Integrable fun y => fderiv ℝ φ y (unitVector i) • f y :=
    fun f hfl => hfl.integrable_smul_left_of_hasCompactSupport hφd hφs
  have e₁ : (fun y => φ y • (g₁ y + g₂ y) (unitVector i)) =
      fun y => φ y • g₁ y (unitVector i) + φ y • g₂ y (unitVector i) := by
    funext y
    simp [smul_add]
  have e₂ : (fun y => fderiv ℝ φ y (unitVector i) • (f₁ y + f₂ y)) =
      fun y => fderiv ℝ φ y (unitVector i) • f₁ y + fderiv ℝ φ y (unitVector i) • f₂ y := by
    funext y
    simp [smul_add]
  rw [e₁, e₂, integral_add (hg g₁ h₁.2.1) (hg g₂ h₂.2.1), integral_add (hf f₁ h₁.1) (hf f₂ h₂.1),
    h₁.2.2 φ hφ i, h₂.2.2 φ hφ i, neg_add]

theorem norm_add_pow_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) (n : ℕ) :
    ‖a + b‖ ^ n ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n) := by
  have hab := norm_add_le a b
  rcases le_total ‖a‖ ‖b‖ with h | h
  · calc ‖a + b‖ ^ n ≤ (2 * ‖b‖) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
      _ = 2 ^ n * ‖b‖ ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n) := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  · calc ‖a + b‖ ^ n ≤ (2 * ‖a‖) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
      _ = 2 ^ n * ‖a‖ ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n) := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)

theorem continuous_decay (c r : ℝ) : Continuous fun y : Space => c * (1 + ‖y‖) ^ (-r) :=
  continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
    fun y => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')

theorem lintegral_norm_add_pow_le {E : Type*} [NormedAddCommGroup E] {a b : Space → E}
    {D : Space → ℝ} (hD : Continuous D) (n : ℕ) (haD : ∀ y, ‖a y‖ ^ n ≤ D y) :
    ∫⁻ y, ENNReal.ofReal (‖a y + b y‖ ^ n) ≤
      ENNReal.ofReal (2 ^ n) * (∫⁻ y, ENNReal.ofReal (D y))
        + ENNReal.ofReal (2 ^ n) * ∫⁻ y, ENNReal.ofReal (‖b y‖ ^ n) := by
  calc ∫⁻ y, ENNReal.ofReal (‖a y + b y‖ ^ n)
      ≤ ∫⁻ y, (ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (D y)
          + ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (‖b y‖ ^ n)) := by
        refine lintegral_mono fun y => ?_
        have hDy : 0 ≤ D y := (by positivity : (0 : ℝ) ≤ ‖a y‖ ^ n).trans (haD y)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← mul_add]
        refine ENNReal.ofReal_le_ofReal ((norm_add_pow_le _ _ n).trans ?_)
        gcongr
        exact haD y
    _ = _ := by
        have hm : Measurable fun y => ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (D y) :=
          (hD.measurable.ennreal_ofReal).const_mul _
        rw [lintegral_add_left hm,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem lintegral_le_of_decay {c r : ℝ} (hc : 0 ≤ c) (hr : 3 < r) :
    ∫⁻ y : Space, ENNReal.ofReal (c * (1 + ‖y‖) ^ (-r)) ≤
      ENNReal.ofReal (∫ y : Space, c * (1 + ‖y‖) ^ (-r)) := by
  have hi : Integrable (fun y : Space => c * (1 + ‖y‖) ^ (-r)) :=
    (integrable_one_add_norm (by simpa [finrank_euclideanSpace] using hr)).const_mul c
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => by positivity)]

theorem integral_decay_nonneg (c r : ℝ) (hc : 0 ≤ c) : 0 ≤ ∫ y : Space, c * (1 + ‖y‖) ^ (-r) :=
  integral_nonneg fun y => by positivity

theorem pow_le_of_decay {x D t r : ℝ} (m n : ℕ) (hx0 : 0 ≤ x) (ht : 0 ≤ t)
    (hr : (m : ℝ) * n = r) (hx : x ≤ D / (1 + t) ^ m) : x ^ n ≤ D ^ n * (1 + t) ^ (-r) := by
  have hpos : 0 < 1 + t := by linarith
  calc x ^ n ≤ (D / (1 + t) ^ m) ^ n := pow_le_pow_left₀ hx0 hx n
    _ = D ^ n * (1 + t) ^ (-r) := by
        rw [Real.rpow_neg hpos.le, ← hr, Real.rpow_mul hpos.le, Real.rpow_natCast,
          Real.rpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv, pow_mul]

variable {k : ℕ} {d : ExtendedCertificateData k}

theorem decay_nonneg (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    0 ≤ d.decay := by
  have h := (hd.profile_decay q hq 0 0).1
  simp only [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem profile_slice (hd : IsExtendedCertificate d) (q : Fin k → ℝ) (σ : ℝ) :
    ContDiff ℝ 1 (d.profile q σ) :=
  hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

theorem profile_joint (hd : IsExtendedCertificate d) (q : Fin k → ℝ) :
    ContDiff ℝ 1 (fun z : ℝ × Space => d.profile q z.1 z.2) :=
  hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem profile_sixth (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) (σ : ℝ)
    (y : Space) : ‖d.profile q σ y‖ ^ 6 ≤ d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) := by
  have h := (hd.profile_decay q hq σ y).1
  exact pow_le_of_decay 1 6 (norm_nonneg _) (norm_nonneg _) (by norm_num) (by simpa using h)

theorem profile_grad_sq (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) (σ : ℝ)
    (y : Space) : ‖fderiv ℝ (d.profile q σ) y‖ ^ 2 ≤ d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
  pow_le_of_decay 2 2 (norm_nonneg _) (norm_nonneg _) (by norm_num) (hd.profile_decay q hq σ y).2.1

theorem profile_secondDeriv_sq (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) (σ : ℝ)
    (y : Space) : ‖d.profileSecondDeriv q σ y‖ ^ 2 ≤ d.decay ^ 2 * (1 + ‖y‖) ^ (-(6 : ℝ)) :=
  pow_le_of_decay 3 2 (norm_nonneg _) (norm_nonneg _) (by norm_num) (hd.profile_decay q hq σ y).2.2

theorem sixth_bound (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {v : VelField} {B : ℝ} (hB : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) ≤ ENNReal.ofReal B)
    (σ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (‖d.profile q σ y + v σ y‖ ^ 6) ≤
      ENNReal.ofReal (2 ^ 6 * (∫ y : Space, d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)))
        + 2 ^ 6 * max B 0) := by
  have hD := decay_nonneg hd hq
  have hK : 0 ≤ ∫ y : Space, d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) :=
    integral_decay_nonneg _ _ (by positivity)
  refine (lintegral_norm_add_pow_le (b := v σ) (continuous_decay _ _) 6
    (profile_sixth hd hq σ)).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num)]
  gcongr
  · exact lintegral_le_of_decay (by positivity) (by norm_num)
  · exact (hB σ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem grad_bound (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {G : GradField} {B : ℝ} (hB : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖G σ y‖ ^ 2) ≤ ENNReal.ofReal B)
    (σ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (d.profile q σ) y + G σ y‖ ^ 2) ≤
      ENNReal.ofReal (2 ^ 2 * (∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)))
        + 2 ^ 2 * max B 0) := by
  have hD := decay_nonneg hd hq
  have hK : 0 ≤ ∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
    integral_decay_nonneg _ _ (by positivity)
  refine (lintegral_norm_add_pow_le (b := G σ) (continuous_decay _ _) 2
    (profile_grad_sq hd hq σ)).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num)]
  gcongr
  · exact lintegral_le_of_decay (by positivity) (by norm_num)
  · exact (hB σ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem secondDeriv_finite_of_period (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {H : SecondField} (hH : periodLIntegral (fun σ y => ‖H σ y‖ ^ 2) < ⊤) :
    (∫⁻ σ in Set.Icc 0 1, ∫⁻ y,
      ENNReal.ofReal (‖d.profileSecondDeriv q σ y + H σ y‖ ^ 2)) < ⊤ := by
  have hD := decay_nonneg hd hq
  have hslice : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖d.profileSecondDeriv q σ y + H σ y‖ ^ 2)
      ≤ ENNReal.ofReal (2 ^ 2) * ENNReal.ofReal (∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(6 : ℝ)))
        + ENNReal.ofReal (2 ^ 2) * ∫⁻ y, ENNReal.ofReal (‖H σ y‖ ^ 2) := by
    intro σ
    refine (lintegral_norm_add_pow_le (b := H σ) (continuous_decay _ _) 2
      (profile_secondDeriv_sq hd hq σ)).trans ?_
    gcongr
    exact lintegral_le_of_decay (by positivity) (by norm_num)
  refine (lintegral_mono hslice).trans_lt ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Real.volume_Icc]
  exact ENNReal.add_lt_top.2 ⟨by simp [ENNReal.mul_lt_top],
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH⟩

theorem weak_secondDeriv_sum (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {G : GradField} {H : SecondField} (σ : ℝ) (hσ : ∀ j : Fin 3,
      IsWeakGradient (fun y => G σ y (unitVector j)) (fun y => (H σ y).flip (unitVector j)))
    (j : Fin 3) :
    IsWeakGradient (fun y => (fderiv ℝ (d.profile q σ) y + G σ y) (unitVector j))
      (fun y => (d.profileSecondDeriv q σ y + H σ y).flip (unitVector j)) := by
  have e : (fun y => (d.profileSecondDeriv q σ y + H σ y).flip (unitVector j)) =
      fun y => (d.profileSecondDeriv q σ y).flip (unitVector j)
        + (H σ y).flip (unitVector j) := by
    funext y
    rw [ContinuousLinearMap.flip_add, add_apply]
  have e' : (fun y => (fderiv ℝ (d.profile q σ) y + G σ y) (unitVector j)) =
      fun y => fderiv ℝ (d.profile q σ) y (unitVector j) + G σ y (unitVector j) := by
    funext y
    rw [add_apply]
  rw [e, e']
  exact isWeakGradient_add (hd.profileSecondDeriv_weak q hq σ j) (hσ j)

theorem divergence_sum (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {G : GradField} (σ : ℝ) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0) :
    ∀ᵐ y, ∑ i : Fin 3, ((fderiv ℝ (d.profile q σ) y + G σ y) (unitVector i)) i = 0 := by
  filter_upwards [hdiv] with y hy
  have h0 := hd.profile_divergence q hq σ y
  unfold divergenceAt at h0
  have e : ∀ i : Fin 3, ((fderiv ℝ (d.profile q σ) y + G σ y) (unitVector i)) i =
      (fderiv ℝ (d.profile q σ) y (unitVector i)) i + (G σ y (unitVector i)) i := fun i => by
    rw [add_apply, PiLp.add_apply]
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, h0, hy, add_zero]

end Internal.ExtendedSigmaProfileOfHeld

open Internal.ExtendedSigmaProfileOfHeld in
theorem extendedSigmaProfileOfHeldHolds_of (h1 : SliceReadingHolds)
    (h2 : ExtendedHeldWeakEquationHolds) (h3 : ExtendedHeldNonzeroHolds) :
    ExtendedSigmaProfileOfHeldHolds := by
  intro k d hd q hq f κ hf hκ
  obtain ⟨v, G, H, hr, hgrad, hdiv, ⟨B, hB⟩, hH⟩ := h1 (d.period q) (hd.period_pos q hq) f
  refine ⟨d.period q, fun σ y => d.profile q σ y + v σ y,
    fun σ y => fderiv ℝ (d.profile q σ) y + G σ y,
    fun σ y => d.profileSecondDeriv q σ y + H σ y,
    max (2 ^ 6 * (∫ y : Space, d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ))) + 2 ^ 6 * max B 0)
      (2 ^ 2 * (∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) + 2 ^ 2 * max B 0), ?_⟩
  exact
    { period_pos := hd.period_pos q hq
      measurable_velocity :=
        (profile_joint hd q).continuous.aestronglyMeasurable.add hr.measurable_velocity
      measurable_gradient := (measurable_fderiv_with_param ℝ (f := d.profile q)
        (profile_joint hd q).continuous).aestronglyMeasurable.add hr.measurable_gradient
      measurable_secondDeriv :=
        (hd.profileSecondDeriv_measurable q hq).add hr.measurable_second
      periodic := fun σ y => by
        rw [hd.profile_periodic q σ y, hr.periodic_velocity σ y]
      weak_gradient := fun σ => isWeakGradient_add
        (isWeakGradient_of_contDiff (profile_slice hd q σ)) (hgrad σ)
      weak_secondDeriv := by
        filter_upwards [hr.weak_second] with σ hσ j
        exact weak_secondDeriv_sum hd hq σ hσ j
      divergence_free := fun σ => divergence_sum hd hq σ (hdiv σ)
      sixth_power := fun σ =>
        (sixth_bound hd hq (fun σ => (hB σ).1) σ).trans
          (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      gradient_bound := fun σ =>
        (grad_bound hd hq (fun σ => (hB σ).2) σ).trans
          (ENNReal.ofReal_le_ofReal (le_max_right _ _))
      secondDeriv_finite := secondDeriv_finite_of_period hd hq hH
      weak_equation := fun φ hφ => h2 d hd q hq f κ hf hκ v G H hr φ hφ
      nonzero := h3 d hd q hq f κ hf v G H hr }

end Breakdown.Cert

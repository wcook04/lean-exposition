import Breakdown.Cert.CoercivePieceDensityPassageRight

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PassageCommon

theorem isWeakGradient_sub {f₁ f₂ : Space → Space} {g₁ g₂ : Space → (Space →L[ℝ] Space)}
    (h₁ : IsWeakGradient f₁ g₁) (h₂ : IsWeakGradient f₂ g₂) :
    IsWeakGradient (fun y => f₁ y - f₂ y) (fun y => g₁ y - g₂ y) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, fun φ hφ i => ?_⟩
  have hc : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) := hφ.2.fderiv_apply (𝕜 := ℝ) _
  have i1 : Integrable (fun y => φ y • g₁ y (unitVector i)) volume :=
    (Internal.PerturbationFacts.apply_locallyIntegrable h₁.2.1 i).integrable_smul_left_of_hasCompactSupport
      hφ.1.continuous hφ.2
  have i2 : Integrable (fun y => φ y • g₂ y (unitVector i)) volume :=
    (Internal.PerturbationFacts.apply_locallyIntegrable h₂.2.1 i).integrable_smul_left_of_hasCompactSupport
      hφ.1.continuous hφ.2
  have j1 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f₁ y) volume :=
    h₁.1.integrable_smul_left_of_hasCompactSupport hc hcs
  have j2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f₂ y) volume :=
    h₂.1.integrable_smul_left_of_hasCompactSupport hc hcs
  have e1 : (fun y => φ y • (g₁ y - g₂ y) (unitVector i)) =
      fun y => φ y • g₁ y (unitVector i) - φ y • g₂ y (unitVector i) := by
    funext y; rw [ContinuousLinearMap.sub_apply, smul_sub]
  have e2 : (fun y => fderiv ℝ φ y (unitVector i) • (f₁ y - f₂ y)) =
      fun y => fderiv ℝ φ y (unitVector i) • f₁ y - fderiv ℝ φ y (unitVector i) • f₂ y := by
    funext y; rw [smul_sub]
  rw [e1, e2, integral_sub i1 i2, integral_sub j1 j2, h₁.2.2 φ hφ i, h₂.2.2 φ hφ i]
  abel

theorem norm_sub_pow_six_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 6 ≤ 64 * ‖x‖ ^ 6 + 64 * ‖y‖ ^ 6 := by
  have h1 : ‖x - y‖ ≤ 2 * max ‖x‖ ‖y‖ :=
    (norm_sub_le x y).trans (by linarith [le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖])
  have h2 : ‖x - y‖ ^ 6 ≤ (2 * max ‖x‖ ‖y‖) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) h1 6
  have h3 : max ‖x‖ ‖y‖ ^ 6 ≤ ‖x‖ ^ 6 + ‖y‖ ^ 6 := by
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg x) 6]
    · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg y) 6]
  calc ‖x - y‖ ^ 6 ≤ (2 * max ‖x‖ ‖y‖) ^ 6 := h2
    _ = 64 * max ‖x‖ ‖y‖ ^ 6 := by ring
    _ ≤ 64 * (‖x‖ ^ 6 + ‖y‖ ^ 6) := by linarith
    _ = 64 * ‖x‖ ^ 6 + 64 * ‖y‖ ^ 6 := by ring

theorem norm_sub_sq_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_sub_le x y
  have h0 := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

theorem periodL2_sub {E : Type*} [NormedAddCommGroup E] {A B : ℝ → Space → E}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤) :
    periodLIntegral (fun σ y => ‖A σ y - B σ y‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (C := 2) (by norm_num)
    (g := fun σ y => ‖A σ y‖ ^ 2 + ‖B σ y‖ ^ 2) fun σ y => norm_sub_sq_le _ _) ?_
  rw [PassageLimit.periodLIntegral_add (hA.norm.aemeasurable.pow_const 2) (hB.norm.aemeasurable.pow_const 2)
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hA2, hB2⟩)

theorem continuous_matSq : Continuous matSq := by
  unfold matSq
  fun_prop

theorem matSq_sub_le (X Y : Space →L[ℝ] Space) : matSq (X - Y) ≤ 2 * (matSq X + matSq Y) := by
  unfold matSq
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [ContinuousLinearMap.sub_apply]; exact norm_sub_sq_le _ _

theorem matSq_nonneg (X : Space →L[ℝ] Space) : 0 ≤ matSq X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem secondDerivTrace_sub (X Y : Space →L[ℝ] Space →L[ℝ] Space) :
    secondDerivTrace (X - Y) = secondDerivTrace X - secondDerivTrace Y := by
  unfold secondDerivTrace
  rw [← Finset.sum_sub_distrib]
  rfl

theorem deriv_time_eq {f : ℝ → Space → Space} (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2))
    (s : ℝ) (y : Space) :
    deriv (fun t => f t y) s = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y) (1, 0) := by
  have hd : HasFDerivAt (fun z : ℝ × Space => f z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y)) (s, y) :=
    (hf.differentiable (by simp) (s, y)).hasFDerivAt
  have hp : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact (hd.comp_hasDerivAt s hp).deriv

theorem fderiv_space_eq {f : ℝ → Space → Space} (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2))
    (s : ℝ) (y w : Space) :
    fderiv ℝ (f s) y w = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y) (0, w) := by
  have hd : HasFDerivAt (fun z : ℝ × Space => f z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y)) (s, y) :=
    (hf.differentiable (by simp) (s, y)).hasFDerivAt
  have hp : HasFDerivAt (fun x : Space => (s, x)) (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    hasFDerivAt_prodMk_right s y
  have h := hd.comp y hp
  rw [show f s = (fun z : ℝ × Space => f z.1 z.2) ∘ (fun x : Space => (s, x)) from rfl, h.fderiv]
  rfl

def transportVector (P : ℝ) (φ : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  -(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2

theorem transportVector_eq {P : ℝ} {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) (z : ℝ × Space) :
    transportVector P φ z = -(1 / P) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (1, 0) - φ z.1 z.2
      - (1 / 2 : ℝ) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (0, z.2) := by
  have h1 : ContDiff ℝ 1 (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.of_le (by simp)
  unfold transportVector
  rw [deriv_time_eq h1, fderiv_space_eq h1]

theorem continuous_transportVector {P : ℝ} {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    Continuous (transportVector P φ) := by
  have hd := hφ.1.continuous_fderiv (by simp)
  rw [show transportVector P φ = fun z => -(1 / P) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (1, 0)
      - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (0, z.2) from
    funext (transportVector_eq hφ)]
  exact (((hd.clm_apply continuous_const).const_smul (-(1 / P))).sub hφ.1.continuous).sub
    ((hd.clm_apply (continuous_const.prodMk continuous_snd)).const_smul (1 / 2 : ℝ))

theorem hasCompactSupport_transportVector {P : ℝ} {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    HasCompactSupport (transportVector P φ) := by
  refine hφ.2.mono' fun z hz => ?_
  by_contra hn
  have h0 : φ z.1 z.2 = 0 := image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => φ z.1 z.2) hn
  have h1 : fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z = 0 := by
    by_contra h2
    exact hn (support_fderiv_subset ℝ h2)
  apply hz
  rw [transportVector_eq hφ, h1, h0]
  simp

theorem integrable_velocity_transport {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestVector φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (transportVector P φ z)) volume := by
  have hloc := Internal.PerturbationFacts.velocity_locallyIntegrable hv
  have hT := continuous_transportVector (P := P) hφ
  have hTs := hasCompactSupport_transportVector (P := P) hφ
  have h : Integrable (fun z : ℝ × Space => ‖transportVector P φ z‖ • v z.1 z.2) volume :=
    hloc.integrable_smul_left_of_hasCompactSupport hT.norm hTs.norm
  refine h.norm.mono' (hv.measurable_velocity.inner hT.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_norm, mul_comm]
  exact abs_real_inner_le_norm _ _

theorem integrable_derivative_test {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestVector φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)) volume :=
  Cert.Internal.CoerciveBordered.integrable_inner_of_periodic hv.measurable_derivative hv.periodic_derivative
    hv.derivative_finite (ψ := fun z : ℝ × Space => φ z.1 z.2) hφ.1.continuous hφ.2

theorem isPerturbation_sub {Γ₁ Γ₂ : Set Symmetry} {P : ℝ} {a b : ℝ → Space → Space}
    {A B : ℝ → Space → (Space →L[ℝ] Space)} {AA BB : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {ga gb : ℝ → Space → Space} (ha : IsPerturbation Γ₁ P a A AA ga) (hb : IsPerturbation Γ₂ P b B BB gb) :
    IsPerturbation ∅ P (fun σ y => a σ y - b σ y) (fun σ y => A σ y - B σ y) (fun σ y => AA σ y - BB σ y)
      (fun σ y => ga σ y - gb σ y) where
  measurable_velocity := ha.measurable_velocity.sub hb.measurable_velocity
  measurable_gradient := ha.measurable_gradient.sub hb.measurable_gradient
  measurable_secondDeriv := ha.measurable_secondDeriv.sub hb.measurable_secondDeriv
  measurable_derivative := ha.measurable_derivative.sub hb.measurable_derivative
  periodic_velocity σ y := by simp only [ha.periodic_velocity σ y, hb.periodic_velocity σ y]
  periodic_gradient σ y := by simp only [ha.periodic_gradient σ y, hb.periodic_gradient σ y]
  periodic_secondDeriv σ y := by simp only [ha.periodic_secondDeriv σ y, hb.periodic_secondDeriv σ y]
  periodic_derivative σ y := by simp only [ha.periodic_derivative σ y, hb.periodic_derivative σ y]
  weak_gradient := by
    filter_upwards [ha.weak_gradient, hb.weak_gradient] with σ h1 h2
    exact isWeakGradient_sub h1 h2
  weak_secondDeriv := by
    filter_upwards [ha.weak_secondDeriv, hb.weak_secondDeriv] with σ h1 h2
    intro j
    have e : (fun y => (AA σ y - BB σ y).flip (unitVector j)) =
        fun y => (AA σ y).flip (unitVector j) - (BB σ y).flip (unitVector j) := by
      funext y; ext x i; simp
    have e' : (fun y => (A σ y - B σ y) (unitVector j)) =
        fun y => A σ y (unitVector j) - B σ y (unitVector j) := by
      funext y; rw [ContinuousLinearMap.sub_apply]
    rw [e, e']
    exact isWeakGradient_sub (h1 j) (h2 j)
  divergence_free := by
    filter_upwards [ha.divergence_free, hb.divergence_free] with σ h1 h2
    filter_upwards [h1, h2] with y e1 e2
    simp only [ContinuousLinearMap.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib, e1, e2, sub_zero]
  sixth_power := by
    filter_upwards [ha.weak_gradient, hb.weak_gradient, ha.sixth_power, hb.sixth_power] with σ h1 h2 h3 h4
    have hm : AEMeasurable (fun y => ENNReal.ofReal (64 * ‖a σ y‖ ^ 6)) volume :=
      ((h1.1.aestronglyMeasurable.norm.aemeasurable.pow_const 6).const_mul 64).ennreal_ofReal
    calc (∫⁻ y, ENNReal.ofReal (‖a σ y - b σ y‖ ^ 6))
        ≤ ∫⁻ y, (ENNReal.ofReal (64 * ‖a σ y‖ ^ 6) + ENNReal.ofReal (64 * ‖b σ y‖ ^ 6)) :=
          lintegral_mono fun y => by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            exact ENNReal.ofReal_le_ofReal (norm_sub_pow_six_le _ _)
      _ = (∫⁻ y, ENNReal.ofReal (64 * ‖a σ y‖ ^ 6)) + ∫⁻ y, ENNReal.ofReal (64 * ‖b σ y‖ ^ 6) :=
          lintegral_add_left' hm _
      _ < ⊤ := by
          simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 64 by norm_num)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top h3,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top h4⟩
  gradient_finite := by
    have hmA : AEMeasurable (fun z : ℝ × Space => matSq (A z.1 z.2)) volume :=
      (continuous_matSq.comp_aestronglyMeasurable ha.measurable_gradient).aemeasurable
    have hmB : AEMeasurable (fun z : ℝ × Space => matSq (B z.1 z.2)) volume :=
      (continuous_matSq.comp_aestronglyMeasurable hb.measurable_gradient).aemeasurable
    refine lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (C := 2) (by norm_num)
      (g := fun σ y => matSq (A σ y) + matSq (B σ y)) fun σ y => matSq_sub_le _ _) ?_
    rw [PassageLimit.periodLIntegral_add hmA hmB (fun _ _ => matSq_nonneg _) (fun _ _ => matSq_nonneg _)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨ha.gradient_finite, hb.gradient_finite⟩)
  sumSecondPartials_finite := by
    have hc := PassageLimit.continuous_secondDerivTrace
    have e : (fun σ y => ‖secondDerivTrace ((fun σ y => AA σ y - BB σ y) σ y)‖ ^ 2) =
        fun σ y => ‖secondDerivTrace (AA σ y) - secondDerivTrace (BB σ y)‖ ^ 2 := by
      funext σ y; simp only [secondDerivTrace_sub]
    rw [e]
    exact periodL2_sub (hc.comp_aestronglyMeasurable ha.measurable_secondDeriv)
      (hc.comp_aestronglyMeasurable hb.measurable_secondDeriv) ha.sumSecondPartials_finite hb.sumSecondPartials_finite
  derivative_finite := periodL2_sub ha.measurable_derivative hb.measurable_derivative
    ha.derivative_finite hb.derivative_finite
  transport φ hφ := by
    have ta := ha.transport φ hφ
    have tb := hb.transport φ hφ
    change ∫ z : ℝ × Space, inner ℝ (a z.1 z.2 - b z.1 z.2) (transportVector P φ z) =
      ∫ z : ℝ × Space, inner ℝ (ga z.1 z.2 - gb z.1 z.2) (φ z.1 z.2)
    change ∫ z : ℝ × Space, inner ℝ (a z.1 z.2) (transportVector P φ z) = _ at ta
    change ∫ z : ℝ × Space, inner ℝ (b z.1 z.2) (transportVector P φ z) = _ at tb
    simp only [inner_sub_left]
    rw [integral_sub (integrable_velocity_transport ha hφ) (integrable_velocity_transport hb hφ),
      integral_sub (integrable_derivative_test ha hφ) (integrable_derivative_test hb hφ), ta, tb]
  invariant γ hγ := absurd hγ (Set.notMem_empty γ)

theorem difference_isPerturbation (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) (n : ℕ) :
    IsPerturbation ∅ P (fun σ y => u n σ y - v σ y) (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y) (fun σ y => transportPart P (u n) σ y - g σ y) :=
  isPerturbation_sub (hSP P (u n) (hu.1 n)) hv


theorem periodLIntegral_mul_le {a b : ℝ → Space → ℝ} (ha0 : ∀ σ y, 0 ≤ a σ y) (hb0 : ∀ σ y, 0 ≤ b σ y)
    (ham : AEMeasurable (fun z : ℝ × Space => a z.1 z.2) volume)
    (hbm : AEMeasurable (fun z : ℝ × Space => b z.1 z.2) volume) :
    periodLIntegral (fun σ y => a σ y * b σ y) ≤
      periodLIntegral (fun σ y => a σ y ^ 2) ^ (1 / (2 : ℝ)) * periodLIntegral (fun σ y => b σ y ^ 2) ^ (1 / (2 : ℝ)) := by
  have hμ : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [PassageLimit.periodLIntegral_eq_prod (ham.mul hbm), PassageLimit.periodLIntegral_eq_prod (ham.pow_const 2),
    PassageLimit.periodLIntegral_eq_prod (hbm.pow_const 2)]
  have hfa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (a z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ]; exact ham.ennreal_ofReal.restrict
  have hfb : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (b z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ]; exact hbm.ennreal_ofReal.restrict
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)
    Real.HolderConjugate.two_two hfa hfb
  have e1 : (fun z : ℝ × Space => ENNReal.ofReal (a z.1 z.2 * b z.1 z.2)) =
      (fun z : ℝ × Space => ENNReal.ofReal (a z.1 z.2)) * (fun z : ℝ × Space => ENNReal.ofReal (b z.1 z.2)) := by
    funext z; simp only [Pi.mul_apply]; rw [ENNReal.ofReal_mul (ha0 _ _)]
  have e2 : ∀ (c : ℝ → Space → ℝ), (∀ σ y, 0 ≤ c σ y) → (fun z : ℝ × Space => ENNReal.ofReal (c z.1 z.2 ^ 2)) =
      fun z : ℝ × Space => ENNReal.ofReal (c z.1 z.2) ^ (2 : ℝ) := by
    intro c hc
    funext z
    rw [ENNReal.ofReal_pow (hc _ _), ← ENNReal.rpow_natCast]
    norm_num
  rw [e1, e2 a ha0, e2 b hb0]
  exact h

theorem periodLIntegral_mul_tendsto_zero {a b : ℕ → ℝ → Space → ℝ} (ha0 : ∀ n σ y, 0 ≤ a n σ y)
    (hb0 : ∀ n σ y, 0 ≤ b n σ y)
    (ham : ∀ n, AEMeasurable (fun z : ℝ × Space => a n z.1 z.2) volume)
    (hbm : ∀ n, AEMeasurable (fun z : ℝ × Space => b n z.1 z.2) volume)
    (ha : Tendsto (fun n => periodLIntegral (fun σ y => a n σ y ^ 2)) atTop (𝓝 0))
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hb : ∀ n, periodLIntegral (fun σ y => b n σ y ^ 2) ≤ B) :
    Tendsto (fun n => periodLIntegral (fun σ y => a n σ y * b n σ y)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => periodLIntegral (fun σ y => a n σ y ^ 2) ^ (1 / (2 : ℝ)) * B ^ (1 / (2 : ℝ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => periodLIntegral (fun σ y => a n σ y ^ 2) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp ha
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      exact this
    have h2 := ENNReal.Tendsto.mul_const h1
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hB))
    rwa [zero_mul] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => by positivity) fun n => ?_
  refine (periodLIntegral_mul_le (ha0 n) (hb0 n) (ham n) (hbm n)).trans ?_
  gcongr
  exact hb n

theorem abs_alternatingSymbol_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem abs_sum_three_le (f : Fin 3 → ℝ) {M : ℝ} (h : ∀ i, |f i| ≤ M) : |∑ i, f i| ≤ 3 * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f i| ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => h i
    _ = 3 * M := by simp

theorem abs_coord_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at this

theorem abs_apply_unit_le (A : Space →L[ℝ] Space) (j l : Fin 3) : |A (unitVector j) l| ≤ ‖A‖ := by
  refine (abs_coord_le _ l).trans ?_
  have := A.le_opNorm (unitVector j)
  rwa [Internal.PerturbationFacts.norm_unitVector_eq, mul_one] at this

theorem abs_apply₂_unit_le (A : Space →L[ℝ] Space →L[ℝ] Space) (m a b : Fin 3) :
    |A (unitVector m) (unitVector a) b| ≤ ‖A‖ := by
  refine (abs_coord_le _ b).trans ?_
  have := A.le_opNorm₂ (unitVector m) (unitVector a)
  simpa only [Internal.PerturbationFacts.norm_unitVector_eq, mul_one] using this

theorem abs_curlVec_le (A : Space →L[ℝ] Space) (i : Fin 3) : |curlVec A i| ≤ 9 * ‖A‖ := by
  unfold curlVec
  have e : (∑ i' : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i' j l * A (unitVector j) l) • unitVector i') i
      = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l := by
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  rw [e]
  have hterm : ∀ j l : Fin 3, |alternatingSymbol i j l * A (unitVector j) l| ≤ ‖A‖ := fun j l => by
    rw [abs_mul]
    calc |alternatingSymbol i j l| * |A (unitVector j) l| ≤ 1 * ‖A‖ :=
          mul_le_mul (abs_alternatingSymbol_le _ _ _) (abs_apply_unit_le _ _ _) (abs_nonneg _) zero_le_one
      _ = ‖A‖ := one_mul _
  have := abs_sum_three_le (fun j => ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l)
    (M := 3 * ‖A‖) fun j => abs_sum_three_le _ fun l => hterm j l
  linarith

theorem abs_vortGrad_le (A : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) : |vortGrad A j m| ≤ 9 * ‖A‖ := by
  unfold vortGrad
  have hterm : ∀ a b : Fin 3, |alternatingSymbol j a b * A (unitVector m) (unitVector a) b| ≤ ‖A‖ := fun a b => by
    rw [abs_mul]
    calc |alternatingSymbol j a b| * |A (unitVector m) (unitVector a) b| ≤ 1 * ‖A‖ :=
          mul_le_mul (abs_alternatingSymbol_le _ _ _) (abs_apply₂_unit_le _ _ _ _) (abs_nonneg _) zero_le_one
      _ = ‖A‖ := one_mul _
  have := abs_sum_three_le (fun a => ∑ b : Fin 3, alternatingSymbol j a b * A (unitVector m) (unitVector a) b)
    (M := 3 * ‖A‖) fun a => abs_sum_three_le _ fun b => hterm a b
  linarith

def stretchPair (A B dW : Space →L[ℝ] Space) (hW : Space →L[ℝ] Space →L[ℝ] Space) (x y : Space) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlVec A i * ((dW (unitVector j) i + dW (unitVector i) j) / 2) * curlVec B j)
    + ∑ j : Fin 3, (∑ m : Fin 3, x m * vortGrad hW j m) * curlVec B j
    + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad hW j m * A (unitVector j) i * y l

theorem abs_stretchPair_le (A B dW : Space →L[ℝ] Space) (hW : Space →L[ℝ] Space →L[ℝ] Space) (x y : Space) :
    |stretchPair A B dW hW x y| ≤ 729 * ‖dW‖ * ‖A‖ * ‖B‖ + 729 * ‖hW‖ * ‖x‖ * ‖B‖
      + 729 * ‖hW‖ * ‖A‖ * ‖y‖ := by
  have hS : ∀ i j : Fin 3, |(dW (unitVector j) i + dW (unitVector i) j) / 2| ≤ ‖dW‖ := by
    intro i j
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := abs_add_le (dW (unitVector j) i) (dW (unitVector i) j)
    linarith [abs_apply_unit_le dW j i, abs_apply_unit_le dW i j]
  have nA := norm_nonneg A
  have nB := norm_nonneg B
  have nd := norm_nonneg dW
  have nh := norm_nonneg hW
  have nx := norm_nonneg x
  have ny := norm_nonneg y
  have u1 : ∀ i j : Fin 3, |curlVec A i * ((dW (unitVector j) i + dW (unitVector i) j) / 2) * curlVec B j|
      ≤ 81 * ‖dW‖ * ‖A‖ * ‖B‖ := fun i j => by
    rw [abs_mul, abs_mul]
    have h1 := abs_curlVec_le A i
    have h2 := abs_curlVec_le B j
    have h3 := hS i j
    calc |curlVec A i| * |(dW (unitVector j) i + dW (unitVector i) j) / 2| * |curlVec B j|
        ≤ (9 * ‖A‖) * ‖dW‖ * (9 * ‖B‖) := by gcongr
      _ = 81 * ‖dW‖ * ‖A‖ * ‖B‖ := by ring
  have t1 := abs_sum_three_le (fun i => ∑ j : Fin 3, curlVec A i * ((dW (unitVector j) i + dW (unitVector i) j) / 2)
      * curlVec B j) (M := 3 * (81 * ‖dW‖ * ‖A‖ * ‖B‖)) fun i => abs_sum_three_le _ fun j => u1 i j
  have u2 : ∀ j : Fin 3, |(∑ m : Fin 3, x m * vortGrad hW j m) * curlVec B j| ≤ 3 * (9 * ‖x‖ * ‖hW‖) * (9 * ‖B‖) :=
    fun j => by
      rw [abs_mul]
      have hin : |∑ m : Fin 3, x m * vortGrad hW j m| ≤ 3 * (9 * ‖x‖ * ‖hW‖) :=
        abs_sum_three_le _ fun m => by
          rw [abs_mul]
          calc |x m| * |vortGrad hW j m| ≤ ‖x‖ * (9 * ‖hW‖) :=
                mul_le_mul (abs_coord_le x m) (abs_vortGrad_le hW j m) (abs_nonneg _) nx
            _ = 9 * ‖x‖ * ‖hW‖ := by ring
      exact mul_le_mul hin (abs_curlVec_le B j) (abs_nonneg _) (by positivity)
  have t2 := abs_sum_three_le (fun j => (∑ m : Fin 3, x m * vortGrad hW j m) * curlVec B j) u2
  have u3 : ∀ i m l j : Fin 3, |alternatingSymbol i m l * vortGrad hW j m * A (unitVector j) i * y l|
      ≤ 9 * ‖hW‖ * ‖A‖ * ‖y‖ := fun i m l j => by
    rw [abs_mul, abs_mul, abs_mul]
    have e1 := abs_alternatingSymbol_le i m l
    have e2 := abs_vortGrad_le hW j m
    have e3 := abs_apply_unit_le A j i
    have e4 := abs_coord_le y l
    calc |alternatingSymbol i m l| * |vortGrad hW j m| * |A (unitVector j) i| * |y l|
        ≤ 1 * (9 * ‖hW‖) * ‖A‖ * ‖y‖ := by gcongr
      _ = 9 * ‖hW‖ * ‖A‖ * ‖y‖ := by ring
  have t3 := abs_sum_three_le (fun i => ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
      alternatingSymbol i m l * vortGrad hW j m * A (unitVector j) i * y l)
    (M := 3 * (3 * (3 * (9 * ‖hW‖ * ‖A‖ * ‖y‖)))) fun i =>
      abs_sum_three_le _ fun m => abs_sum_three_le _ fun l => abs_sum_three_le _ fun j => u3 i m l j
  unfold stretchPair
  have hh : |(1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
      alternatingSymbol i m l * vortGrad hW j m * A (unitVector j) i * y l| ≤ 729 * ‖hW‖ * ‖A‖ * ‖y‖ := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_nonneg (∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
      alternatingSymbol i m l * vortGrad hW j m * A (unitVector j) i * y l)
    have : 0 ≤ ‖hW‖ * ‖A‖ * ‖y‖ := by positivity
    linarith
  have := abs_add_three (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec A i * ((dW (unitVector j) i + dW (unitVector i) j) / 2)
      * curlVec B j)) (∑ j : Fin 3, (∑ m : Fin 3, x m * vortGrad hW j m) * curlVec B j)
    ((1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
      alternatingSymbol i m l * vortGrad hW j m * A (unitVector j) i * y l)
  rw [abs_neg] at this
  have : 0 ≤ ‖dW‖ * ‖A‖ * ‖B‖ := by positivity
  have : 0 ≤ ‖hW‖ * ‖x‖ * ‖B‖ := by positivity
  linarith

theorem curlVec_sub (A B : Space →L[ℝ] Space) (i : Fin 3) : curlVec (A - B) i = curlVec A i - curlVec B i := by
  unfold curlVec
  simp only [ContinuousLinearMap.sub_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_smul,
    PiLp.sub_apply]

theorem stretchForm_sub_eq (W v v' : ℝ → Space → Space) (G G' : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    stretchForm W v G σ y - stretchForm W v' G' σ y =
      stretchPair (G σ y - G' σ y) (G σ y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
          (v σ y - v' σ y) (v σ y)
        + stretchPair (G' σ y) (G σ y - G' σ y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
          (v' σ y) (v σ y - v' σ y) := by
  unfold stretchForm stretchPair
  simp only [curlVec_sub, ContinuousLinearMap.sub_apply, PiLp.sub_apply, Fin.sum_univ_three]
  ring

theorem norm_sq_le_matSq (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have h := Internal.PerturbationFacts.opNorm_le_sum_apply A
  unfold matSq
  simp only [Fin.sum_univ_three] at h ⊢
  have h0 := norm_nonneg A
  have := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖), sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖),
    sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖)]

theorem norm_fderiv_le_of_decay {W : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (W σ) y‖ ≤ |D| := by
  have h1 := hD σ y 1 (by norm_num)
  rw [norm_iteratedFDeriv_one] at h1
  have hr : (1 : ℝ) ≤ (1 + ‖y‖) ^ (1 + 1) := one_le_pow₀ (by linarith [norm_nonneg y])
  refine h1.trans ?_
  rcases le_or_gt 0 D with hD0 | hD0
  · exact (div_le_self hD0 hr).trans (le_abs_self D)
  · exact (div_neg_of_neg_of_pos hD0 (by linarith)).le.trans (abs_nonneg D)

theorem norm_secondDeriv_mul_le_of_decay {W : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ * (1 + ‖y‖) ≤ |D| := by
  have h2 := hD σ y 2 (le_refl _)
  have e : ‖iteratedFDeriv ℝ 2 (W σ) y‖ = ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [e] at h2
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr1 : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
  calc ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ * (1 + ‖y‖)
      ≤ D / (1 + ‖y‖) ^ (2 + 1) * (1 + ‖y‖) := mul_le_mul_of_nonneg_right h2 hr.le
    _ = D / (1 + ‖y‖) ^ 2 := by field_simp
    _ ≤ |D| / (1 + ‖y‖) ^ 2 := by gcongr; exact le_abs_self D
    _ ≤ |D| := div_le_self (abs_nonneg D) hr1

theorem abs_stretchForm_le {W v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y : Space) :
    |stretchForm W v G σ y| ≤ 729 * |D| * (6 * matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
  have e : stretchForm W v G σ y = stretchPair (G σ y) (G σ y) (fderiv ℝ (W σ) y)
      (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) (v σ y) (v σ y) := rfl
  rw [e]
  have hb := abs_stretchPair_le (G σ y) (G σ y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
    (v σ y) (v σ y)
  have h1 := norm_fderiv_le_of_decay hD σ y
  have h2 := norm_secondDeriv_mul_le_of_decay hD σ y
  have hf := norm_sq_le_matSq (G σ y)
  set gg := ‖G σ y‖
  set dd := ‖fderiv ℝ (W σ) y‖
  set hh := ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖
  set vv := ‖v σ y‖
  set r := 1 + ‖y‖ with hr
  have hr0 : 0 < r := by rw [hr]; linarith [norm_nonneg y]
  have g0 : 0 ≤ gg := norm_nonneg _
  have d0 : 0 ≤ dd := norm_nonneg _
  have h0 : 0 ≤ hh := norm_nonneg _
  have vfix : 0 ≤ vv := norm_nonneg _
  set q := vv / r with hq
  have q0 : 0 ≤ q := div_nonneg vfix hr0.le
  have hvq : vv = q * r := by rw [hq]; field_simp
  have hhv : hh * vv ≤ |D| * q := by
    rw [hvq, show hh * (q * r) = (hh * r) * q by ring]
    exact mul_le_mul_of_nonneg_right h2 q0
  have t1 : dd * gg * gg ≤ |D| * (gg * gg) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have t2 : hh * vv * gg ≤ |D| * q * gg := mul_le_mul_of_nonneg_right hhv g0
  have t3 : hh * gg * vv ≤ |D| * q * gg := by
    rw [show hh * gg * vv = hh * vv * gg by ring]; exact t2
  have hq2 : q ^ 2 = vv ^ 2 / r ^ 2 := by rw [hq, div_pow]
  have hD0 := abs_nonneg D
  have key : 2 * q * gg ≤ gg ^ 2 + q ^ 2 := by nlinarith [sq_nonneg (gg - q)]
  have k2 := mul_le_mul_of_nonneg_left key hD0
  refine hb.trans ?_
  have s1 : 729 * dd * gg * gg + 729 * hh * vv * gg + 729 * hh * gg * vv ≤ 729 * |D| * (2 * gg ^ 2 + q ^ 2) := by
    nlinarith [t1, t2, t3, k2]
  refine s1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← hq2]
  linarith

theorem abs_stretchForm_sub_le {W u v : ℝ → Space → Space} {Gu G : ℝ → Space → (Space →L[ℝ] Space)} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y : Space) :
    |stretchForm W u Gu σ y - stretchForm W v G σ y| ≤
      729 * |D| * ((‖Gu σ y - G σ y‖ + ‖u σ y - v σ y‖ / (1 + ‖y‖)) ^ 2
        + (‖Gu σ y - G σ y‖ + ‖u σ y - v σ y‖ / (1 + ‖y‖)) * (2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖)))) := by
  rw [stretchForm_sub_eq]
  have hb1 := abs_stretchPair_le (Gu σ y - G σ y) (Gu σ y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
    (u σ y - v σ y) (u σ y)
  have hb2 := abs_stretchPair_le (G σ y) (Gu σ y - G σ y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
    (v σ y) (u σ y - v σ y)
  have h1 := norm_fderiv_le_of_decay hD σ y
  have h2 := norm_secondDeriv_mul_le_of_decay hD σ y
  have hgn : ‖Gu σ y‖ ≤ ‖Gu σ y - G σ y‖ + ‖G σ y‖ := by
    have := norm_add_le (Gu σ y - G σ y) (G σ y); simpa using this
  have hun : ‖u σ y‖ ≤ ‖u σ y - v σ y‖ + ‖v σ y‖ := by
    have := norm_add_le (u σ y - v σ y) (v σ y); simpa using this
  have hab := abs_add_le (stretchPair (Gu σ y - G σ y) (Gu σ y) (fderiv ℝ (W σ) y)
      (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) (u σ y - v σ y) (u σ y))
    (stretchPair (G σ y) (Gu σ y - G σ y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
      (v σ y) (u σ y - v σ y))
  set e := ‖Gu σ y - G σ y‖
  set gn := ‖Gu σ y‖
  set g := ‖G σ y‖
  set dd := ‖fderiv ℝ (W σ) y‖
  set hh := ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖
  set dv := ‖u σ y - v σ y‖
  set nu := ‖u σ y‖
  set nv := ‖v σ y‖
  set r := 1 + ‖y‖ with hr
  have hr0 : 0 < r := by rw [hr]; linarith [norm_nonneg y]
  have e0 : 0 ≤ e := norm_nonneg _
  have g0 : 0 ≤ g := norm_nonneg _
  have gn0 : 0 ≤ gn := norm_nonneg _
  have d0 : 0 ≤ dd := norm_nonneg _
  have h0 : 0 ≤ hh := norm_nonneg _
  have dv0 : 0 ≤ dv := norm_nonneg _
  have nu0 : 0 ≤ nu := norm_nonneg _
  have nv0 : 0 ≤ nv := norm_nonneg _
  have hD0 := abs_nonneg D
  set f := dv / r with hf
  set q := nv / r with hq
  have f0 : 0 ≤ f := div_nonneg dv0 hr0.le
  have q0 : 0 ≤ q := div_nonneg nv0 hr0.le
  have hdv : hh * dv ≤ |D| * f := by
    rw [show hh * dv = (hh * r) * f by rw [hf]; field_simp]
    exact mul_le_mul_of_nonneg_right h2 f0
  have hnv : hh * nv ≤ |D| * q := by
    rw [show hh * nv = (hh * r) * q by rw [hq]; field_simp]
    exact mul_le_mul_of_nonneg_right h2 q0
  have hnu : hh * nu ≤ |D| * (f + q) := by
    have := mul_le_mul_of_nonneg_left hun h0
    linarith
  have a1 : dd * e * gn ≤ |D| * (e * (e + g)) := by
    have := mul_le_mul h1 (mul_le_mul_of_nonneg_left hgn e0) (by positivity) hD0
    nlinarith
  have a2 : hh * dv * gn ≤ |D| * f * (e + g) := mul_le_mul hdv hgn gn0 (by positivity)
  have a3 : hh * e * nu ≤ |D| * (f + q) * e := by
    rw [show hh * e * nu = hh * nu * e by ring]; exact mul_le_mul_of_nonneg_right hnu e0
  have b1 : dd * g * e ≤ |D| * g * e := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have b2 : hh * nv * e ≤ |D| * q * e := mul_le_mul_of_nonneg_right hnv e0
  have b3 : hh * g * dv ≤ |D| * f * g := by
    rw [show hh * g * dv = hh * dv * g by ring]; exact mul_le_mul_of_nonneg_right hdv g0
  have hsum : e * (e + g) + f * (e + g) + (f + q) * e + g * e + q * e + f * g
      ≤ (e + f) ^ 2 + (e + f) * (2 * g + 2 * q) := by nlinarith [mul_nonneg f0 q0, sq_nonneg f]
  have hfin := mul_le_mul_of_nonneg_left hsum hD0
  refine hab.trans ?_
  nlinarith [hb1, hb2, a1, a2, a3, b1, b2, b3, hfin]

theorem stretchForm_finite {Γ : Set Symmetry} {P : ℝ} {W v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤) :
    periodLIntegral (fun σ y => |stretchForm W v G σ y|) < ⊤ := by
  obtain ⟨D, hD⟩ := hWdecay
  refine lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (by positivity) fun σ y => abs_stretchForm_le hD σ y) ?_
  have hm1 : AEMeasurable (fun z : ℝ × Space => 6 * matSq (G z.1 z.2)) volume :=
    ((continuous_matSq.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable).const_mul 6
  have hr : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have hm2 : AEMeasurable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    (hv.measurable_velocity.norm.aemeasurable.pow_const 2).div hr.aemeasurable
  rw [PassageLimit.periodLIntegral_add hm1 hm2 (fun _ _ => mul_nonneg (by norm_num) (matSq_nonneg _))
    (fun _ _ => by positivity)]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, hvw⟩)
  exact lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (C := 6) (by norm_num) (g := fun σ y => matSq (G σ y))
    fun σ y => le_refl _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite)

theorem stretchForm_tendsto (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry} {P : ℝ}
    {W v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    Tendsto (fun n => periodLIntegral (fun σ y =>
      |stretchForm W (u n) (gradField (u n)) σ y - stretchForm W v G σ y|)) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := hWdecay
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hr : Continuous (fun z : ℝ × Space => 1 + ‖z.2‖) := by fun_prop
  have hr2 : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have ha0 : ∀ n σ y, 0 ≤ ‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖) :=
    fun n σ y => by positivity
  have hb0 : ∀ (n : ℕ) σ y, 0 ≤ 2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖)) := fun n σ y => by positivity
  have ham : ∀ n, AEMeasurable (fun z : ℝ × Space =>
      ‖gradField (u n) z.1 z.2 - G z.1 z.2‖ + ‖u n z.1 z.2 - v z.1 z.2‖ / (1 + ‖z.2‖)) volume := fun n =>
    (((hpn n).measurable_gradient.sub hv.measurable_gradient).norm.aemeasurable).add
      ((((hpn n).measurable_velocity.sub hv.measurable_velocity).norm.aemeasurable).div hr.aemeasurable)
  have hbm : AEMeasurable (fun z : ℝ × Space =>
      2 * ‖G z.1 z.2‖ + 2 * (‖v z.1 z.2‖ / (1 + ‖z.2‖))) volume :=
    ((hv.measurable_gradient.norm.aemeasurable).const_mul 2).add
      (((hv.measurable_velocity.norm.aemeasurable).div hr.aemeasurable).const_mul 2)
  have hfm : ∀ n, AEMeasurable (fun z : ℝ × Space => matSq (gradField (u n) z.1 z.2 - G z.1 z.2)) volume :=
    fun n => (continuous_matSq.comp_aestronglyMeasurable
      ((hpn n).measurable_gradient.sub hv.measurable_gradient)).aemeasurable
  have hwm : ∀ n, AEMeasurable (fun z : ℝ × Space => ‖u n z.1 z.2 - v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    fun n => (((hpn n).measurable_velocity.sub hv.measurable_velocity).norm.aemeasurable.pow_const 2).div
      hr2.aemeasurable
  have hsq : Tendsto (fun n => periodLIntegral (fun σ y =>
      (‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖)) ^ 2)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => ENNReal.ofReal 6 * (periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y))
        + periodLIntegral (fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2))) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (hu.2.1.add hu.2.2.2.1) (Or.inr (ENNReal.ofReal_ne_top (r := 6)))
      rwa [add_zero, mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le) fun n => ?_
    rw [← PassageLimit.periodLIntegral_add (f := fun σ y => matSq (gradField (u n) σ y - G σ y))
      (g := fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) (hfm n) (hwm n) (fun _ _ => matSq_nonneg _) (fun _ _ => by positivity)]
    refine PassageLimit.periodLIntegral_le_mul (by norm_num) fun σ y => ?_
    have h1 := norm_sq_le_matSq (gradField (u n) σ y - G σ y)
    have hr0 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
    have e : (‖u n σ y - v σ y‖ / (1 + ‖y‖)) ^ 2 = ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := div_pow _ _ _
    have hw0 : 0 ≤ ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by positivity
    have hf0 := matSq_nonneg (gradField (u n) σ y - G σ y)
    nlinarith [sq_nonneg (‖gradField (u n) σ y - G σ y‖ - ‖u n σ y - v σ y‖ / (1 + ‖y‖))]
  obtain ⟨N, hN⟩ := (hu.2.2.2.1.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
  have hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ := by
    have hum : AEMeasurable (fun z : ℝ × Space => ‖u N z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
      ((hpn N).measurable_velocity.norm.aemeasurable.pow_const 2).div hr2.aemeasurable
    refine lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (C := 2) (by norm_num)
      (g := fun σ y => ‖u N σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 + ‖u N σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) fun σ y => ?_) ?_
    · have h := norm_sub_sq_le (u N σ y) (u N σ y - v σ y)
      rw [sub_sub_cancel] at h
      have hr0 : 0 < (1 + ‖y‖) ^ 2 := by positivity
      rw [← add_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hr0.le
    · rw [PassageLimit.periodLIntegral_add (f := fun σ y => ‖u N σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
        (g := fun σ y => ‖u N σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) (hwm N) hum (fun _ _ => by positivity) (fun _ _ => by positivity)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨hN.trans ENNReal.one_lt_top, (hu.1 N).weighted_finite⟩)
  have hB : periodLIntegral (fun σ y => (2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖))) ^ 2) ≠ ⊤ := by
    have hgm : AEMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
      (continuous_matSq.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable
    have hvm : AEMeasurable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
      (hv.measurable_velocity.norm.aemeasurable.pow_const 2).div hr2.aemeasurable
    refine (lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (C := 24) (by norm_num)
      (g := fun σ y => matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) fun σ y => ?_) ?_).ne
    · have h1 := norm_sq_le_matSq (G σ y)
      have e : (‖v σ y‖ / (1 + ‖y‖)) ^ 2 = ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := div_pow _ _ _
      have hw0 : 0 ≤ ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by positivity
      have hf0 := matSq_nonneg (G σ y)
      nlinarith [sq_nonneg (‖G σ y‖ - ‖v σ y‖ / (1 + ‖y‖))]
    · rw [PassageLimit.periodLIntegral_add (f := fun σ y => matSq (G σ y))
        (g := fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) hgm hvm (fun _ _ => matSq_nonneg _) (fun _ _ => by positivity)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hv.gradient_finite, hvw⟩)
  have hmul := periodLIntegral_mul_tendsto_zero
    (a := fun n σ y => ‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖))
    (b := fun _ σ y => 2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖)))
    ha0 hb0 ham (fun _ => hbm) hsq hB (fun _ => le_refl _)
  have hlim : Tendsto (fun n => ENNReal.ofReal (729 * |D|) *
      (periodLIntegral (fun σ y => (‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖)) ^ 2)
        + periodLIntegral (fun σ y => (‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖))
          * (2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖)))))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (hsq.add hmul) (Or.inr (ENNReal.ofReal_ne_top (r := 729 * |D|)))
    rwa [add_zero, mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) fun n => ?_
  rw [← PassageLimit.periodLIntegral_add
    (f := fun σ y => (‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖)) ^ 2)
    (g := fun σ y => (‖gradField (u n) σ y - G σ y‖ + ‖u n σ y - v σ y‖ / (1 + ‖y‖))
      * (2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖)))) ((ham n).pow_const 2) ((ham n).mul hbm)
    (fun σ y => by positivity) (fun σ y => mul_nonneg (ha0 n σ y) (hb0 n σ y))]
  exact PassageLimit.periodLIntegral_le_mul (by positivity) fun σ y => abs_stretchForm_sub_le hD σ y

theorem ae_subseq_tendsto_zero {E : ℕ → ℕ → ℝ → Space → ℝ≥0∞}
    (hE : ∀ k n, AEMeasurable (fun z : ℝ × Space => E k n z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (h : ∀ k, Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E k n σ y) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      ∀ k, Tendsto (fun n => E k (φ n) σ y) atTop (𝓝 0) := by
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have hI : ∀ k n, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E k n σ y) = ∫⁻ z, E k n z.1 z.2 ∂μ := fun k n =>
    (lintegral_prod _ (hE k n)).symm
  have hev : ∀ j, ∀ᶠ n in atTop, ∀ k ∈ Finset.range (j + 1),
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E k n σ y) < (1 / 2 : ℝ≥0∞) ^ j := by
    intro j
    rw [Filter.eventually_all_finset]
    intro k _
    exact (h k).eventually (gt_mem_nhds (ENNReal.pow_pos (by norm_num) j))
  obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hk : ∀ k, ∀ᵐ z ∂μ, Tendsto (fun n => E k (φ n) z.1 z.2) atTop (𝓝 0) := by
    intro k
    have hb : ∀ j, (∫⁻ z, E k (φ (j + k)) z.1 z.2 ∂μ) ≤ (1 / 2 : ℝ≥0∞) ^ (j + k) := fun j => by
      rw [← hI]
      exact (hφb (j + k) k (Finset.mem_range.2 (by omega))).le
    have hsum : (∫⁻ z, ∑' j, E k (φ (j + k)) z.1 z.2 ∂μ) ≠ ⊤ := by
      rw [lintegral_tsum fun j => hE k (φ (j + k))]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
      have hgeo : (∑' j : ℕ, (1 / 2 : ℝ≥0∞) ^ (j + k)) = (∑' j : ℕ, (1 / 2 : ℝ≥0∞) ^ j) * (1 / 2) ^ k := by
        simp_rw [pow_add]
        exact ENNReal.tsum_mul_right
      have hlt : (1 / 2 : ℝ≥0∞) < 1 := by
        norm_num
      rw [hgeo, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne') (ENNReal.pow_ne_top (by simp))
    have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun j => hE k (φ (j + k))) hsum
    filter_upwards [hae] with z hz
    exact (tendsto_add_atTop_iff_nat k).1 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hz.ne)
  have hall : ∀ᵐ z ∂μ, ∀ k, Tendsto (fun n => E k (φ n) z.1 z.2) atTop (𝓝 0) := ae_all_iff.2 hk
  exact Measure.ae_ae_of_ae_prod hall

theorem tendsto_zero_of_ofReal {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (h : Tendsto (fun n => ENNReal.ofReal (a n)) atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [Function.comp_def, ENNReal.toReal_ofReal (ha0 _), ENNReal.toReal_zero] at this
  exact this

theorem ae_subseq_fields (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    {E : ℕ → ℕ → ℝ → Space → ℝ≥0∞}
    (hE : ∀ k n, AEMeasurable (fun z : ℝ × Space => E k n z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (h : ∀ k, Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E k n σ y) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      (∀ k, Tendsto (fun n => E k (φ n) σ y) atTop (𝓝 0)) ∧
      Tendsto (fun n => u (φ n) σ y) atTop (𝓝 (v σ y)) ∧
      Tendsto (fun n => gradField (u (φ n)) σ y) atTop (𝓝 (G σ y)) ∧
      Tendsto (fun n => secondDerivSq (secondDerivField (u (φ n)) σ y - H σ y)) atTop (𝓝 0) := by
  have hpn := fun n => hSP P (u n) (hu.1 n)
  set a0 : ℕ → ℝ → Space → ℝ := fun n σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 with ha0
  set a1 : ℕ → ℝ → Space → ℝ := fun n σ y => matSq (gradField (u n) σ y - G σ y) with ha1
  set a2 : ℕ → ℝ → Space → ℝ := fun n σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y) with ha2
  set E' : ℕ → ℕ → ℝ → Space → ℝ≥0∞ := fun k n σ y =>
    if k = 0 then ENNReal.ofReal (a0 n σ y) else if k = 1 then ENNReal.ofReal (a1 n σ y)
      else if k = 2 then ENNReal.ofReal (a2 n σ y) else E (k - 3) n σ y with hE'
  have hr : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have m0 : ∀ n, AEMeasurable (fun z : ℝ × Space => a0 n z.1 z.2) volume := fun n =>
    ((((hpn n).measurable_velocity.sub hv.measurable_velocity).norm.aemeasurable.pow_const 2).div hr.aemeasurable)
  have m1 : ∀ n, AEMeasurable (fun z : ℝ × Space => a1 n z.1 z.2) volume := fun n =>
    (continuous_matSq.comp_aestronglyMeasurable ((hpn n).measurable_gradient.sub hv.measurable_gradient)).aemeasurable
  have m2 : ∀ n, AEMeasurable (fun z : ℝ × Space => a2 n z.1 z.2) volume := fun n =>
    (PassageLimit.continuous_secondDerivSq.comp_aestronglyMeasurable
      ((hpn n).measurable_secondDeriv.sub hv.measurable_secondDeriv)).aemeasurable
  have hμ : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have q0 : ∀ n σ y, E' 0 n σ y = ENNReal.ofReal (a0 n σ y) := fun n σ y => by simp [hE']
  have q1 : ∀ n σ y, E' 1 n σ y = ENNReal.ofReal (a1 n σ y) := fun n σ y => by
    simp [hE']
  have q2 : ∀ n σ y, E' 2 n σ y = ENNReal.ofReal (a2 n σ y) := fun n σ y => by
    simp [hE']
  have q3 : ∀ k n σ y, E' (k + 3) n σ y = E k n σ y := fun k n σ y => by
    simp only [hE', if_neg (show k + 3 ≠ 0 by omega), if_neg (show k + 3 ≠ 1 by omega),
      if_neg (show k + 3 ≠ 2 by omega), Nat.add_sub_cancel]
  have hEm : ∀ k n, AEMeasurable (fun z : ℝ × Space => E' k n z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    intro k n
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · simp only [q0]; rw [hμ]; exact (m0 n).ennreal_ofReal.restrict
      · simp only [q1]; rw [hμ]; exact (m1 n).ennreal_ofReal.restrict
      · simp only [q2]; rw [hμ]; exact (m2 n).ennreal_ofReal.restrict
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      simp only [q3]
      exact hE j n
  have hlim : ∀ k, Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E' k n σ y) atTop (𝓝 0) := by
    intro k
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · simp only [q0]; exact hu.2.2.2.1
      · simp only [q1]; exact hu.2.1
      · simp only [q2]; exact hu.2.2.1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      simp only [q3]
      exact h j
  obtain ⟨φ, hφ, hae⟩ := ae_subseq_tendsto_zero hEm hlim
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with σ hσ
  filter_upwards [hσ] with y hy
  have t0 : Tendsto (fun n => a0 (φ n) σ y) atTop (𝓝 0) :=
    tendsto_zero_of_ofReal (fun n => by positivity) (by simpa only [q0] using hy 0)
  have t1 : Tendsto (fun n => a1 (φ n) σ y) atTop (𝓝 0) :=
    tendsto_zero_of_ofReal (fun n => matSq_nonneg _) (by simpa only [q1] using hy 1)
  have t2 : Tendsto (fun n => a2 (φ n) σ y) atTop (𝓝 0) :=
    tendsto_zero_of_ofReal (fun n => PassageLimit.secondDerivSq_nonneg _) (by simpa only [q2] using hy 2)
  refine ⟨fun k => ?_, ?_, ?_, t2⟩
  · simpa only [q3] using hy (k + 3)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hpos : 0 < (1 + ‖y‖) ^ 2 := by positivity
    have hsq : Tendsto (fun n => ‖u (φ n) σ y - v σ y‖ ^ 2) atTop (𝓝 0) := by
      have := t0.mul_const ((1 + ‖y‖) ^ 2)
      rw [zero_mul] at this
      refine this.congr fun n => ?_
      simp only [ha0]
      field_simp
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at this
    exact this
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun n => ‖gradField (u (φ n)) σ y - G σ y‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sq_nonneg _) (fun n => norm_sq_le_matSq _) ?_
      simpa using t1.const_mul 3
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at this
    exact this

end Internal.PassageCommon

end Coercive

end Breakdown

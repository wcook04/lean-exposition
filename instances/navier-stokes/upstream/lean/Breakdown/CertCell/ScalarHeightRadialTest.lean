import Breakdown.CertCell.ScalarHeightCylinderMeasure

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ScalarHeight

open Internal.ScalarHeight

lemma eq_zero_near_origin {g : ℝ → ℝ} (hg0 : tsupport g ⊆ Ioi 0) :
    ∃ ε > 0, ∀ r, r < ε → g r = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport g := fun h => lt_irrefl (0 : ℝ) (hg0 h)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport g).isOpen_compl 0 h0
  refine ⟨ε, hε, fun r hr => ?_⟩
  by_cases hr0 : r ≤ 0
  · exact image_eq_zero_of_notMem_tsupport fun h => not_lt.2 hr0 (hg0 h)
  · refine image_eq_zero_of_notMem_tsupport (hball ?_)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (not_le.mp hr0)]
    exact hr

lemma contDiff_radial {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : tsupport g ⊆ Ioi 0) :
    ContDiff ℝ ∞ (fun y : Space => g (planeRadius y)) := by
  have hs : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    ((contDiff_coord 0).pow 2).add ((contDiff_coord 1).pow 2)
  obtain ⟨ε, hε, hzero⟩ := eq_zero_near_origin hg0
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y 0 ^ 2 + y 1 ^ 2 = 0
  · have hev : ∀ᶠ w in 𝓝 y, w 0 ^ 2 + w 1 ^ 2 < ε ^ 2 :=
      hs.continuous.continuousAt.eventually (gt_mem_nhds (by simp only []; rw [hy]; positivity))
    have heq : (fun w : Space => g (planeRadius w)) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with w hw
      refine hzero _ ?_
      rw [planeRadius, Real.sqrt_lt' hε]
      exact hw
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact hg.contDiffAt.comp y ((Real.contDiffAt_sqrt hy).comp y hs.contDiffAt)

lemma fderiv_height {A : Space → ℝ} {ψ : ℝ → ℝ} (hA : Differentiable ℝ A) (hψ : Differentiable ℝ ψ)
    (hinv : ∀ (y : Space) (t : ℝ), A (y + t • unitVector 2) = A y) (y : Space) :
    fderiv ℝ (fun y => A y * ψ (y 2)) y (unitVector 2) = A y * deriv ψ (y 2) := by
  have hc2 : Differentiable ℝ (fun y : Space => y 2) := (contDiff_coord 2).differentiable (by simp)
  have hd : DifferentiableAt ℝ (fun y : Space => A y * ψ (y 2)) y :=
    (hA y).mul ((hψ _).comp y (hc2 y))
  have hd' : HasFDerivAt (fun y : Space => A y * ψ (y 2)) (fderiv ℝ (fun y => A y * ψ (y 2)) y)
      (y + (0 : ℝ) • unitVector 2) := by
    rw [zero_smul, add_zero]
    exact hd.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • unitVector 2) (unitVector 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVector 2)).const_add y
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hl
  have e : ((fun y : Space => A y * ψ (y 2)) ∘ fun t : ℝ => y + t • unitVector 2) =
      fun t => A y * ψ (y 2 + t) := by
    funext t
    simp only [Function.comp_apply, hinv, shift_apply, if_true]
  rw [e] at h1
  have h2 : HasDerivAt (fun t : ℝ => A y * ψ (y 2 + t)) (A y * deriv ψ (y 2)) 0 := by
    have := ((hψ (y 2 + 0)).hasDerivAt.comp_const_add (y 2) 0).const_mul (A y)
    simpa using this
  exact h1.unique h2

lemma locallyIntegrable_value {f : Space → ℝ}
    (h : LocallyIntegrable (fun y => f y • unitVector 0)) : LocallyIntegrable f := fun x => by
  obtain ⟨U, hU, hi⟩ := h x
  refine ⟨U, hU, ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).integrable_comp hi).congr
    (Eventually.of_forall fun y => ?_)⟩
  simp [unitVector]

lemma locallyIntegrable_height {df : Space → Space}
    (h : LocallyIntegrable (fun y => (innerSL ℝ (df y)).smulRight (unitVector 0))) :
    LocallyIntegrable (fun y => df y 2) := fun x => by
  obtain ⟨U, hU, hi⟩ := h x
  refine ⟨U, hU, (((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector 2))).integrable_comp hi).congr
    (Eventually.of_forall fun y => ?_)⟩
  simp [unitVector, EuclideanSpace.inner_single_right]

lemma weak_height_real {f : Space → ℝ} {df : Space → Space}
    (hw : IsWeakGradient (fun y => f y • unitVector 0) (fun y => (innerSL ℝ (df y)).smulRight (unitVector 0)))
    (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, φ y * df y 2 = -∫ y, fderiv ℝ φ y (unitVector 2) * f y := by
  have h := hw.2.2 φ ⟨hφ, hφc⟩ 2
  have e1 : ∀ y, φ y • ((innerSL ℝ (df y)).smulRight (unitVector 0)) (unitVector 2) =
      (φ y * df y 2) • unitVector 0 := by
    intro y
    rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    simp [unitVector, EuclideanSpace.inner_single_right]
  have e2 : ∀ y, fderiv ℝ φ y (unitVector 2) • (f y • unitVector 0) =
      (fderiv ℝ φ y (unitVector 2) * f y) • unitVector 0 := fun y => smul_smul _ _ _
  simp_rw [e1, e2, integral_smul_const] at h
  have h0 := congrArg (fun v : Space => v 0) h
  simpa [unitVector] using h0

lemma tsupport_subset_Icc {ψ : ℝ → ℝ} {N : ℝ} (hψN : ∀ z, N < |z| → ψ z = 0) :
    tsupport ψ ⊆ Icc (-N) N := by
  refine closure_minimal (fun z hz => ?_) isClosed_Icc
  by_contra h
  refine hz (hψN z ?_)
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs z)
  · exact lt_of_lt_of_le h (le_abs_self z)

lemma deriv_eq_zero_of_far {ψ : ℝ → ℝ} {N : ℝ} (hψN : ∀ z, N < |z| → ψ z = 0) :
    ∀ z, N < |z| → deriv ψ z = 0 := by
  intro z hz
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := tsupport_subset_Icc hψN (tsupport_deriv_subset h)
  rw [mem_Icc] at this
  have := abs_le.2 this
  linarith

lemma weak_height_part {f : Space → ℝ} {df : Space → Space}
    (hw : IsWeakGradient (fun y => f y • unitVector 0) (fun y => (innerSL ℝ (df y)).smulRight (unitVector 0)))
    {X : Space → ℝ} (hX : ContDiff ℝ ∞ X) (hXinv : ∀ (y : Space) (t : ℝ), X (y + t • unitVector 2) = X y)
    {B N : ℝ} (hXB : ∀ y, B < planeRadius y → X y = 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψN : ∀ z, N < |z| → ψ z = 0) :
    Integrable (fun y => X y * ψ (y 2) * df y 2 + X y * deriv ψ (y 2) * f y) ∧
      ∫ y, (X y * ψ (y 2) * df y 2 + X y * deriv ψ (y 2) * f y) = 0 := by
  have hc2 : ContDiff ℝ ∞ (fun y : Space => y 2) := contDiff_coord 2
  have hφ : ContDiff ℝ ∞ (fun y => X y * ψ (y 2)) := hX.mul (hψ.comp hc2)
  have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hfar : ∀ y : Space, B + N < ‖y‖ → B < planeRadius y ∨ N < |y 2| := by
    intro y hy
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    linarith [norm_le_planeRadius_add y]
  have hφc : HasCompactSupport (fun y => X y * ψ (y 2)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (B + N)) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    rcases hfar y hy with h | h
    · rw [hXB y h, zero_mul]
    · rw [hψN _ h, mul_zero]
  have hφ'c : HasCompactSupport (fun y => X y * deriv ψ (y 2)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (B + N)) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    rcases hfar y hy with h | h
    · rw [hXB y h, zero_mul]
    · rw [deriv_eq_zero_of_far hψN _ h, mul_zero]
  have key := weak_height_real hw _ hφ hφc
  have hfd : ∀ y, fderiv ℝ (fun y => X y * ψ (y 2)) y (unitVector 2) = X y * deriv ψ (y 2) :=
    fderiv_height (hX.differentiable (by simp)) (hψ.differentiable (by simp)) hXinv
  simp_rw [hfd] at key
  have I1 : Integrable (fun y => X y * ψ (y 2) * df y 2) :=
    (locallyIntegrable_height hw.2.1).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have I2 : Integrable (fun y => X y * deriv ψ (y 2) * f y) :=
    (locallyIntegrable_value hw.1).integrable_smul_left_of_hasCompactSupport
      (hX.continuous.mul (hdψ.comp hc2.continuous)) hφ'c
  exact ⟨I1.add I2, by rw [integral_add I1 I2, key, neg_add_cancel]⟩

def timeFactor (j : ℤ) (τ : ℝ) : ℂ := Complex.exp (-(((2 * Real.pi * j * τ : ℝ) : ℂ) * Complex.I))

def modeFactor (ξ : ℤ × ℤ) (τ θ : ℝ) : ℂ :=
  Complex.exp (-(((2 * Real.pi * ξ.1 * τ + ξ.2 * θ : ℝ) : ℂ) * Complex.I))

lemma norm_timeFactor (j : ℤ) (τ : ℝ) : ‖timeFactor j τ‖ = 1 := by
  rw [timeFactor, show -(((2 * Real.pi * j * τ : ℝ) : ℂ) * Complex.I) =
    ((-(2 * Real.pi * j * τ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_modeFactor (ξ : ℤ × ℤ) (τ θ : ℝ) : ‖modeFactor ξ τ θ‖ = 1 := by
  rw [modeFactor, show -(((2 * Real.pi * ξ.1 * τ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) =
    ((-(2 * Real.pi * ξ.1 * τ + ξ.2 * θ)) : ℝ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_timeFactor (j : ℤ) : Continuous (timeFactor j) := by
  unfold timeFactor
  fun_prop

lemma continuous_modeFactor (ξ : ℤ × ℤ) : Continuous (fun p : ℝ × ℝ => modeFactor ξ p.1 p.2) := by
  unfold modeFactor
  fun_prop

lemma timeFactor_mul_turn (ξ : ℤ × ℤ) (τ θ : ℝ) :
    timeFactor ξ.1 τ * Complex.exp (-(((ξ.2 * θ : ℝ) : ℂ) * Complex.I)) = modeFactor ξ τ θ := by
  rw [timeFactor, modeFactor, ← Complex.exp_add]
  congr 1
  push_cast
  ring

def radialIntegrand (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space) (ξ : ℤ × ℤ) (m ψ : ℝ → ℝ)
    (p : ℝ × Space) : ℂ :=
  timeFactor ξ.1 p.1 * ((m (planeRadius p.2) : ℂ) * turnPoly ξ.2 p.2) *
    ((q p.1 p.2 : ℂ) * ((deriv ψ (p.2 2) : ℝ) : ℂ) + (dq p.1 p.2 2 : ℂ) * (ψ (p.2 2) : ℂ))

def lineMoment (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space) (ξ : ℤ × ℤ) (ψ : ℝ → ℝ) (r : ℝ) : ℂ :=
  ∫ u, modeFactor ξ u.1.1 u.1.2 *
    ((q u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) * ((deriv ψ u.2 : ℝ) : ℂ) +
      (dq u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) 2 : ℂ) * (ψ u.2 : ℂ)) ∂boxMeasure

lemma weak_height_complex {f : Space → ℝ} {df : Space → Space}
    (hw : IsWeakGradient (fun y => f y • unitVector 0) (fun y => (innerSL ℝ (df y)).smulRight (unitVector 0)))
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : tsupport g ⊆ Ioi 0) {B N : ℝ} (hgB : ∀ r, B < r → g r = 0)
    (k : ℤ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψN : ∀ z, N < |z| → ψ z = 0) :
    ∫ y, ((g (planeRadius y) : ℂ) * turnPoly k y) *
      ((f y : ℂ) * ((deriv ψ (y 2) : ℝ) : ℂ) + (df y 2 : ℂ) * (ψ (y 2) : ℂ)) = 0 := by
  set A : Space → ℂ := fun y => (g (planeRadius y) : ℂ) * turnPoly k y with hAdef
  have hA : ContDiff ℝ ∞ A :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_radial hg hg0)).mul (contDiff_turnPoly k)
  have hAinv : ∀ (y : Space) (t : ℝ), A (y + t • unitVector 2) = A y := fun y t => by
    simp only [hAdef, planeRadius_shift, turnPoly_shift]
  have hAB : ∀ y, B < planeRadius y → A y = 0 := fun y h => by
    simp only [hAdef, hgB _ h, Complex.ofReal_zero, zero_mul]
  have hre := weak_height_part hw (X := fun y => (A y).re) (B := B) (Complex.reCLM.contDiff.comp hA)
    (fun y t => by simp only [hAinv]) (fun y (h : B < planeRadius y) => by simp only [hAB y h, Complex.zero_re])
    hψ hψN
  have him := weak_height_part hw (X := fun y => (A y).im) (B := B) (Complex.imCLM.contDiff.comp hA)
    (fun y t => by simp only [hAinv]) (fun y (h : B < planeRadius y) => by simp only [hAB y h, Complex.zero_im])
    hψ hψN
  show ∫ y, A y * ((f y : ℂ) * ((deriv ψ (y 2) : ℝ) : ℂ) + (df y 2 : ℂ) * (ψ (y 2) : ℂ)) = 0
  have e : ∀ y, A y * ((f y : ℂ) * ((deriv ψ (y 2) : ℝ) : ℂ) + (df y 2 : ℂ) * (ψ (y 2) : ℂ)) =
      (((A y).re * ψ (y 2) * df y 2 + (A y).re * deriv ψ (y 2) * f y : ℝ) : ℂ) +
      (((A y).im * ψ (y 2) * df y 2 + (A y).im * deriv ψ (y 2) * f y : ℝ) : ℂ) * Complex.I := by
    intro y
    conv_lhs => rw [← Complex.re_add_im (A y)]
    push_cast
    ring
  simp_rw [e]
  rw [integral_add hre.1.ofReal (him.1.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, hre.2, him.2]
  simp

lemma integral_radialIntegrand_eq_zero {q : ℝ → Space → ℝ} {dq : ℝ → Space → Space}
    (hw : ∀ᵐ σ, IsWeakGradient (fun y => q σ y • unitVector 0)
      (fun y => (innerSL ℝ (dq σ y)).smulRight (unitVector 0)))
    (ξ : ℤ × ℤ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : tsupport g ⊆ Ioi 0) {B N : ℝ}
    (hgB : ∀ r, B < r → g r = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψN : ∀ z, N < |z| → ψ z = 0)
    (hint : Integrable (radialIntegrand q dq ξ g ψ) slabMeasure) :
    ∫ p, radialIntegrand q dq ξ g ψ p ∂slabMeasure = 0 := by
  rw [slabMeasure, integral_prod _ hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_of_ae hw] with τ hτ
  have e : ∀ y, radialIntegrand q dq ξ g ψ (τ, y) = timeFactor ξ.1 τ *
      (((g (planeRadius y) : ℂ) * turnPoly ξ.2 y) *
        ((q τ y : ℂ) * ((deriv ψ (y 2) : ℝ) : ℂ) + (dq τ y 2 : ℂ) * (ψ (y 2) : ℂ))) := fun y => by
    simp only [radialIntegrand]
    ring
  simp_rw [e]
  rw [integral_const_mul, weak_height_complex hτ hg hg0 hgB ξ.2 hψ hψN, mul_zero]
  rfl

lemma exists_support_bound {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ N, 0 ≤ N ∧ ∀ z, N < |z| → ψ z = 0 := by
  obtain ⟨N, hN⟩ := (HasCompactSupport.isCompact hψc).isBounded.subset_closedBall 0
  refine ⟨max N 0, le_max_right _ _, fun z hz => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have h1 := hN h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  linarith [le_max_left N 0]

lemma hasCompactSupport_of_far {ψ : ℝ → ℝ} {N : ℝ} (hψN : ∀ z, N < |z| → ψ z = 0) :
    HasCompactSupport ψ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -N) (b := N)) fun z hz => hψN z ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hz
  rcases hz with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs z)
  · exact lt_of_lt_of_le h (le_abs_self z)

lemma integrable_radialIntegrand {q : ℝ → Space → ℝ} {dq : ℝ → Space → Space}
    (hq : AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume)
    (hdq : AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume)
    (hL : ∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤)
    (ξ : ℤ × ℤ) {m : ℝ → ℝ} (hm : Measurable m) {Cm B : ℝ} (hmC : ∀ r, |m r| ≤ Cm) (hB : 0 ≤ B)
    (hmB : ∀ r, B < r → m r = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ z, N < |z| → ψ z = 0) :
    Integrable (radialIntegrand q dq ξ m ψ) slabMeasure := by
  have hψc : HasCompactSupport ψ := hasCompactSupport_of_far hψN
  obtain ⟨C0, hC0⟩ := hψc.exists_bound_of_continuous hψ.continuous
  obtain ⟨C1, hC1⟩ := hψc.deriv.exists_bound_of_continuous (hψ.continuous_deriv (by simp))
  have hCm : 0 ≤ Cm := (abs_nonneg _).trans (hmC 0)
  have hC0' : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0)
  have hC1' : 0 ≤ C1 := (norm_nonneg _).trans (hC1 0)
  have hR : 0 ≤ B + N := by linarith
  set w : ℝ × Space → ℂ := fun p => timeFactor ξ.1 p.1 * ((m (planeRadius p.2) : ℂ) * turnPoly ξ.2 p.2)
    with hwdef
  have hwm : Measurable w :=
    ((continuous_timeFactor _).measurable.comp measurable_fst).mul
      ((Complex.measurable_ofReal.comp (hm.comp (continuous_planeRadius.measurable.comp measurable_snd))).mul
        ((contDiff_turnPoly _).continuous.measurable.comp measurable_snd))
  have hwC : ∀ p : ℝ × Space, ‖p.2‖ ≤ B + N → ‖w p‖ ≤ Cm * (2 * (B + N)) ^ ξ.2.natAbs := by
    intro p hp
    rw [hwdef, norm_mul, norm_mul, norm_timeFactor, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hmC _) ((norm_turnPoly_le _ _).trans (pow_le_pow_left₀ (by positivity) (by linarith) _))
      (norm_nonneg _) hCm
  have hfar : ∀ p : ℝ × Space, B + N < ‖p.2‖ → w p = 0 ∨ (ψ (p.2 2) = 0 ∧ deriv ψ (p.2 2) = 0) := by
    intro p hp
    by_cases h : B < planeRadius p.2
    · left
      rw [hwdef]
      simp only [hmB _ h, Complex.ofReal_zero, zero_mul, mul_zero]
    · right
      have h2 : N < |p.2 2| := by linarith [norm_le_planeRadius_add p.2, not_lt.mp h]
      exact ⟨hψN _ h2, deriv_eq_zero_of_far hψN _ h2⟩
  have he : radialIntegrand q dq ξ m ψ = fun p => (w p * ((deriv ψ (p.2 2) : ℝ) : ℂ)) * (q p.1 p.2 : ℂ) +
      (w p * (ψ (p.2 2) : ℂ)) * (dq p.1 p.2 2 : ℂ) := by
    funext p
    simp only [radialIntegrand, hwdef]
    ring
  rw [he]
  have hc2 : Continuous (fun p : ℝ × Space => p.2 2) := (contDiff_coord 2).continuous.comp continuous_snd
  refine integrable_slab_mul hq hdq hL (C := Cm * (2 * (B + N)) ^ ξ.2.natAbs * (C0 + C1)) (R := B + N)
    (hwm.mul (Complex.measurable_ofReal.comp ((hψ.continuous_deriv (by simp)).measurable.comp
      hc2.measurable))).aestronglyMeasurable
    (hwm.mul (Complex.measurable_ofReal.comp (hψ.continuous.measurable.comp hc2.measurable))).aestronglyMeasurable
    (fun p => ?_) (fun p => ?_) (fun p hp => ?_) (fun p hp => ?_)
  · by_cases hp : ‖p.2‖ ≤ B + N
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hwC p hp) ((hC1 _).trans (by linarith)) (norm_nonneg _) (by positivity)
    · rcases hfar p (not_le.mp hp) with h | h
      · rw [h, zero_mul, norm_zero]; positivity
      · rw [h.2, Complex.ofReal_zero, mul_zero, norm_zero]; positivity
  · by_cases hp : ‖p.2‖ ≤ B + N
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hwC p hp) ((hC0 _).trans (by linarith)) (norm_nonneg _) (by positivity)
    · rcases hfar p (not_le.mp hp) with h | h
      · rw [h, zero_mul, norm_zero]; positivity
      · rw [h.1, Complex.ofReal_zero, mul_zero, norm_zero]; positivity
  · rcases hfar p hp with h | h
    · rw [h, zero_mul]
    · rw [h.2, Complex.ofReal_zero, mul_zero]
  · rcases hfar p hp with h | h
    · rw [h, zero_mul]
    · rw [h.1, Complex.ofReal_zero, mul_zero]

lemma radialIntegrand_cellMap (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space) (ξ : ℤ × ℤ) (m ψ : ℝ → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (u : (ℝ × ℝ) × ℝ) :
    radialIntegrand q dq ξ m ψ (cellMap (r, u)) = ((m r * r ^ ξ.2.natAbs : ℝ) : ℂ) *
      (modeFactor ξ u.1.1 u.1.2 * ((q u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) *
        ((deriv ψ u.2 : ℝ) : ℂ) + (dq u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) 2 : ℂ) * (ψ u.2 : ℂ))) := by
  simp only [radialIntegrand, cellMap, planeRadius_cylPoint hr, turnPoly_cylPoint, cylPoint_apply_two]
  rw [← timeFactor_mul_turn]
  push_cast
  ring

lemma integral_cell_radialIntegrand (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space) (ξ : ℤ × ℤ)
    (m ψ : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ u, radialIntegrand q dq ξ m ψ (cellMap (r, u)) ∂boxMeasure =
      ((m r * r ^ ξ.2.natAbs : ℝ) : ℂ) * lineMoment q dq ξ ψ r := by
  simp_rw [radialIntegrand_cellMap q dq ξ m ψ hr]
  exact integral_const_mul _ _

lemma ae_lineMoment_eq_zero {q : ℝ → Space → ℝ} {dq : ℝ → Space → Space}
    (hq : AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume)
    (hdq : AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume)
    (hL : ∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤)
    (hw : ∀ᵐ σ, IsWeakGradient (fun y => q σ y • unitVector 0)
      (fun y => (innerSL ℝ (dq σ y)).smulRight (unitVector 0)))
    (ξ : ℤ × ℤ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {N : ℝ} (hN : 0 ≤ N) (hψN : ∀ z, N < |z| → ψ z = 0) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), lineMoment q dq ξ ψ r = 0 := by
  set f : ℝ → ℂ := fun r => ((r * r ^ ξ.2.natAbs : ℝ) : ℂ) * lineMoment q dq ξ ψ r with hf
  have hslab : ∀ m : ℝ → ℝ, Measurable m → ∀ Cm B : ℝ, (∀ r, |m r| ≤ Cm) → 0 ≤ B → (∀ r, B < r → m r = 0) →
      Integrable (fun r => m r • f r) (volume.restrict (Ioi 0)) ∧
      ∫ p, radialIntegrand q dq ξ m ψ p ∂slabMeasure = ∫ r in Ioi 0, m r • f r := by
    intro m hm Cm B hmC hB hmB
    have hI := integrable_radialIntegrand hq hdq hL ξ hm hmC hB hmB hψ hN hψN
    have hpt : ∀ r ∈ Ioi (0 : ℝ), r • ∫ u, radialIntegrand q dq ξ m ψ (cellMap (r, u)) ∂boxMeasure =
        m r • f r := by
      intro r hr
      rw [integral_cell_radialIntegrand q dq ξ m ψ (le_of_lt hr), hf]
      simp only [Complex.real_smul]
      push_cast
      ring
    refine ⟨(integrable_slab_iter hI).congr ((ae_restrict_mem measurableSet_Ioi).mono hpt), ?_⟩
    rw [integral_slab_iter hI]
    exact setIntegral_congr_fun measurableSet_Ioi hpt
  have hloc : LocallyIntegrableOn f (Ioi 0) volume := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    refine ⟨Icc (x / 2) (2 * x), nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
    have h := (hslab ((Icc (x / 2) (2 * x)).indicator 1) (measurable_one.indicator measurableSet_Icc) 1 (2 * x)
      (fun r => by by_cases hr : r ∈ Icc (x / 2) (2 * x) <;> simp [hr]) (by linarith)
      (fun r hr => indicator_of_notMem (fun h => not_le.mpr hr h.2) _)).1
    have h2 : Integrable ((Icc (x / 2) (2 * x)).indicator f) (volume.restrict (Ioi 0)) :=
      h.congr (Eventually.of_forall fun r => by by_cases hr : r ∈ Icc (x / 2) (2 * x) <;> simp [hr])
    rw [integrable_indicator_iff measurableSet_Icc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 (show Icc (x / 2) (2 * x) ⊆ Ioi 0 from
        fun r hr => lt_of_lt_of_le (by linarith) hr.1)] at h2
    exact h2
  have key := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [key] with r hr hr0
    have h1 := hr hr0
    have hne : ((r * r ^ ξ.2.natAbs : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (show (0 : ℝ) < r from hr0) (pow_pos hr0 _)).ne'
    exact (mul_eq_zero.1 h1).resolve_left hne
  · intro g hg hgc hgs
    obtain ⟨B, hB, hgB⟩ := exists_support_bound hgc
    obtain ⟨Cg, hCg⟩ := hgc.exists_bound_of_continuous hg.continuous
    have hgB' : ∀ r, B < r → g r = 0 := fun r hr => hgB r (lt_of_lt_of_le hr (le_abs_self r))
    have hgC : ∀ r, |g r| ≤ Cg := fun r => by simpa using hCg r
    have hs := hslab g hg.continuous.measurable Cg B hgC hB hgB'
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) (fun r hr => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hr (hgs h)), zero_smul]), ← hs.2]
    exact integral_radialIntegrand_eq_zero hw ξ hg hgs hgB' hψ hψN
      (integrable_radialIntegrand hq hdq hL ξ hg.continuous.measurable hgC hB hgB' hψ hN hψN)

end Internal.ScalarHeight

end Bridge

end CertCell

end Breakdown

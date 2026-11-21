import Breakdown.Cert.CoerciveSmoothMuMeasure
import Breakdown.Cert.CoerciveField

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.ModeCalc

def rotZ (x : Fin 3 → ℂ) : Fin 3 → ℂ := ![-x 1, x 0, 0]

def timeField (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := deriv (fun s => v s y) σ

def azimField (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  fderiv ℝ (v σ) y (-(y 1) • unitVector 0 + y 0 • unitVector 1)

theorem rot_zero (φ : ℝ) (y : Space) : axialRot φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := by
  simp [axialRot, unitVector]

theorem rot_one (φ : ℝ) (y : Space) : axialRot φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := by
  simp [axialRot, unitVector]

theorem rot_two (φ : ℝ) (y : Space) : axialRot φ y 2 = y 2 := by
  simp [axialRot, unitVector]

def rotCoord (φ : ℝ) (i : Fin 3) : Space →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => axialRot φ w i
      map_add' := fun a c => by simp [Internal.Field.axialRot_add]
      map_smul' := fun a c => by simp [Internal.Field.axialRot_smul] }

theorem rotCoord_apply (φ : ℝ) (i : Fin 3) (w : Space) : rotCoord φ i w = axialRot φ w i := rfl

theorem box_swap (F : ℝ → ℝ → ℂ) (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ τ in a..b, ∫ φ in c..d, F τ φ = ∫ φ in c..d, ∫ τ in a..b, F τ φ := by
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ((hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self))
  exact integral_integral_swap hi

theorem exp_hasDerivAt (c d t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(((c * s + d : ℝ) : ℂ) * Complex.I)))
      (-((c : ℂ) * Complex.I) * Complex.exp (-(((c * t + d : ℝ) : ℂ) * Complex.I))) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s + d) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).add_const d
  have h2 : HasDerivAt (fun s : ℝ => -(((c * s + d : ℝ) : ℂ) * Complex.I)) (-((c : ℂ) * Complex.I)) t :=
    ((h1.ofReal_comp).mul_const Complex.I).neg
  convert h2.cexp using 1
  ring

theorem time_hasDerivAt (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) (x : Space)
    (φ : ℝ) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => axialRot (-φ) (v (σ + s) x) i) (axialRot (-φ) (timeField v (σ + t) x) i) t := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.differentiable (by simp)
  have h0 : DifferentiableAt ℝ (fun s => v s x) (σ + t) :=
    (hd.comp (differentiable_id.prodMk (differentiable_const x))) (σ + t)
  have h1 : HasDerivAt (fun s => v (σ + s) x) (timeField v (σ + t) x) t :=
    h0.hasDerivAt.comp_const_add σ t
  exact (rotCoord (-φ) i).hasFDerivAt.comp_hasDerivAt t h1

theorem tau_ibp (F G E : ℝ → ℂ) (k : ℝ) (hE : ∀ t, HasDerivAt E (-(k * Complex.I) * E t) t)
    (hF : ∀ t, HasDerivAt F (G t) t) (hEc : Continuous E) (hGc : Continuous G)
    {a b : ℝ} (hper : E b * F b = E a * F a) :
    ∫ t in a..b, E t * G t = (k * Complex.I) * ∫ t in a..b, E t * F t := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hE t) (fun t _ => hF t)
    ((continuous_const.mul hEc).intervalIntegrable _ _) (hGc.intervalIntegrable _ _), hper, sub_self,
    zero_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  congr 1
  funext t
  ring

theorem modeAverage_tau_ibp {β : Type*} (ι : ℤ × ℤ) (F G : ℝ → ℝ → β → ℝ) (b : β)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2 b)) (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2 b))
    (hd : ∀ τ φ, HasDerivAt (fun t => F t φ b) (G τ φ b) τ) (hper : ∀ φ, F 1 φ b = F 0 φ b) :
    modeAverage ι G b = ((2 * Real.pi * ι.1 : ℝ) * Complex.I) * modeAverage ι F b := by
  have cE : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) := by fun_prop
  have hin : ∀ φ : ℝ, ∫ τ in (0 : ℝ)..1, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((G τ φ b : ℝ) : ℂ)
      = ((2 * Real.pi * ι.1 : ℝ) * Complex.I) * ∫ τ in (0 : ℝ)..1,
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F τ φ b : ℝ) : ℂ) := by
    intro φ
    have hE : ∀ t : ℝ, HasDerivAt
        (fun s : ℝ => Complex.exp (-(((2 * Real.pi * ι.1 * s + ι.2 * φ : ℝ) : ℂ) * Complex.I)))
        (-(((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-(((2 * Real.pi * ι.1 * t + ι.2 * φ : ℝ) : ℂ) * Complex.I))) t :=
      fun t => exp_hasDerivAt (2 * Real.pi * ι.1) (ι.2 * φ) t
    have c1 : Continuous (fun t : ℝ => F t φ b) := hF.comp (Continuous.prodMk continuous_id continuous_const)
    have c2 : Continuous (fun t : ℝ => G t φ b) := hG.comp (Continuous.prodMk continuous_id continuous_const)
    refine tau_ibp (fun t => ((F t φ b : ℝ) : ℂ)) (fun t => ((G t φ b : ℝ) : ℂ))
      (fun s => Complex.exp (-(((2 * Real.pi * ι.1 * s + ι.2 * φ : ℝ) : ℂ) * Complex.I)))
      (2 * Real.pi * ι.1) hE (fun t => (hd t φ).ofReal_comp)
      (by fun_prop) (Complex.continuous_ofReal.comp c2) ?_
    have h2 : Complex.exp (-(((2 * Real.pi * ι.1 * 1 + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        = Complex.exp (-(((2 * Real.pi * ι.1 * 0 + ι.2 * φ : ℝ) : ℂ) * Complex.I)) := by
      have : -(((2 * Real.pi * ι.1 * 1 + ι.2 * φ : ℝ) : ℂ) * Complex.I)
          = -(((2 * Real.pi * ι.1 * 0 + ι.2 * φ : ℝ) : ℂ) * Complex.I)
            + ((-ι.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    show Complex.exp (-(((2 * Real.pi * ι.1 * 1 + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F 1 φ b : ℝ) : ℂ)
      = Complex.exp (-(((2 * Real.pi * ι.1 * 0 + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F 0 φ b : ℝ) : ℂ)
    rw [h2, hper φ]
  have s1 := box_swap (fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * ((G τ φ b : ℝ) : ℂ)) (cE.mul (Complex.continuous_ofReal.comp hG)) zero_le_one Real.two_pi_pos.le
  have s2 := box_swap (fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * ((F τ φ b : ℝ) : ℂ)) (cE.mul (Complex.continuous_ofReal.comp hF)) zero_le_one Real.two_pi_pos.le
  unfold modeAverage
  rw [s1, s2, intervalIntegral.integral_congr (fun φ _ => hin φ), intervalIntegral.integral_const_mul]
  ring

theorem time_mode (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    modeVel ι (timeField v) σ y = fun i => ((2 * Real.pi * ι.1 : ℝ) * Complex.I) * modeVel ι v σ y i := by
  funext i
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hTc : Continuous (fun z : ℝ × Space => timeField v z.1 z.2) := by
    have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.differentiable (by simp)
    have e : (fun z : ℝ × Space => timeField v z.1 z.2)
        = fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) := by
      funext z
      unfold timeField
      have h := (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1
        ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
      exact h.deriv
    rw [e]
    exact ((hv.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  refine modeAverage_tau_ibp ι (fun τ φ j => axialRot (-φ) (v (σ + τ) (axialRot φ y)) j)
    (fun τ φ j => axialRot (-φ) (timeField v (σ + τ) (axialRot φ y)) j) i
    (Internal.Field.mode_integrand_continuous hvc σ y i)
    (Internal.Field.mode_integrand_continuous hTc σ y i)
    (fun τ φ => time_hasDerivAt P v hv σ (axialRot φ y) φ i τ) ?_
  intro φ
  show axialRot (-φ) (v (σ + 1) (axialRot φ y)) i = axialRot (-φ) (v (σ + 0) (axialRot φ y)) i
  rw [add_zero, hv.periodic σ]

theorem exp_hasDerivAt' (c d t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(((d + c * s : ℝ) : ℂ) * Complex.I)))
      (-((c : ℂ) * Complex.I) * Complex.exp (-(((d + c * t : ℝ) : ℂ) * Complex.I))) t := by
  have h1 : HasDerivAt (fun s : ℝ => d + c * s) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_add d
  have h2 : HasDerivAt (fun s : ℝ => -(((d + c * s : ℝ) : ℂ) * Complex.I)) (-((c : ℂ) * Complex.I)) t :=
    ((h1.ofReal_comp).mul_const Complex.I).neg
  convert h2.cexp using 1
  ring

theorem modeAverage_phi_ibp {β : Type*} (ι : ℤ × ℤ) (F G : ℝ → ℝ → β → ℝ) (b : β)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2 b)) (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2 b))
    (hd : ∀ τ φ, HasDerivAt (fun t => F τ t b) (G τ φ b) φ) (hper : ∀ τ, F τ (2 * Real.pi) b = F τ 0 b) :
    modeAverage ι G b = ((ι.2 : ℝ) * Complex.I) * modeAverage ι F b := by
  have hin : ∀ τ : ℝ, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((G τ φ b : ℝ) : ℂ)
      = ((ι.2 : ℝ) * Complex.I) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F τ φ b : ℝ) : ℂ) := by
    intro τ
    have hE : ∀ t : ℝ, HasDerivAt
        (fun s : ℝ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * s : ℝ) : ℂ) * Complex.I)))
        (-(((ι.2 : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * t : ℝ) : ℂ) * Complex.I))) t :=
      fun t => exp_hasDerivAt' (ι.2) (2 * Real.pi * ι.1 * τ) t
    have c1 : Continuous (fun t : ℝ => F τ t b) := hF.comp (Continuous.prodMk continuous_const continuous_id)
    have c2 : Continuous (fun t : ℝ => G τ t b) := hG.comp (Continuous.prodMk continuous_const continuous_id)
    refine tau_ibp (fun t => ((F τ t b : ℝ) : ℂ)) (fun t => ((G τ t b : ℝ) : ℂ))
      (fun s => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * s : ℝ) : ℂ) * Complex.I)))
      (ι.2) hE (fun t => (hd τ t).ofReal_comp)
      (by fun_prop) (Complex.continuous_ofReal.comp c2) ?_
    have h2 : Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * (2 * Real.pi) : ℝ) : ℂ) * Complex.I))
        = Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * 0 : ℝ) : ℂ) * Complex.I)) := by
      have : -(((2 * Real.pi * ι.1 * τ + ι.2 * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
          = -(((2 * Real.pi * ι.1 * τ + ι.2 * 0 : ℝ) : ℂ) * Complex.I)
            + ((-ι.2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    show Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * (2 * Real.pi) : ℝ) : ℂ) * Complex.I))
        * ((F τ (2 * Real.pi) b : ℝ) : ℂ)
      = Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * 0 : ℝ) : ℂ) * Complex.I)) * ((F τ 0 b : ℝ) : ℂ)
    rw [h2, hper τ]
  unfold modeAverage
  rw [intervalIntegral.integral_congr (fun τ _ => hin τ), intervalIntegral.integral_const_mul]
  ring

theorem rot_hasDerivAt (y : Space) (φ : ℝ) :
    HasDerivAt (fun t => axialRot t y) (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1) φ := by
  have hc : HasDerivAt (fun t => Real.cos t * y 0 - Real.sin t * y 1) (-Real.sin φ * y 0 - Real.cos φ * y 1) φ :=
    ((Real.hasDerivAt_cos φ).mul_const (y 0)).sub ((Real.hasDerivAt_sin φ).mul_const (y 1))
  have hs : HasDerivAt (fun t => Real.sin t * y 0 + Real.cos t * y 1) (Real.cos φ * y 0 + -Real.sin φ * y 1) φ :=
    ((Real.hasDerivAt_sin φ).mul_const (y 0)).add ((Real.hasDerivAt_cos φ).mul_const (y 1))
  have h : HasDerivAt (fun t => axialRot t y)
      ((-Real.sin φ * y 0 - Real.cos φ * y 1) • (unitVector 0 : Space)
        + (Real.cos φ * y 0 + -Real.sin φ * y 1) • (unitVector 1 : Space)) φ :=
    ((hc.smul_const (unitVector 0 : Space)).add (hs.smul_const (unitVector 1 : Space))).add_const
      (y 2 • (unitVector 2 : Space))
  convert h using 1
  ext j
  fin_cases j <;> simp [axialRot, unitVector] <;> ring

theorem field_hasDerivAt (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (s : ℝ) (y : Space)
    (φ : ℝ) :
    HasDerivAt (fun t => v s (axialRot t y)) (azimField v s (axialRot φ y)) φ := by
  have hd : Differentiable ℝ (v s) :=
    (hv.smooth.comp (contDiff_prodMk_right s)).differentiable (by simp)
  exact (hd (axialRot φ y)).hasFDerivAt.comp_hasDerivAt φ (rot_hasDerivAt y φ)

theorem coord_hasDerivAt {u : ℝ → Space} {u' : Space} {φ : ℝ} (h : HasDerivAt u u' φ) (j : Fin 3) :
    HasDerivAt (fun t => u t j) (u' j) φ :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt φ h

theorem azim_deriv0 (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (s : ℝ) (y : Space)
    (φ : ℝ) :
    HasDerivAt (fun t => axialRot (-t) (v s (axialRot t y)) 0) (axialRot (-φ) (azimField v s (axialRot φ y)) 0 + axialRot (-φ) (v s (axialRot φ y)) 1) φ := by
  have hu := field_hasDerivAt P v hv s y φ
  have h0 := coord_hasDerivAt hu 0
  have h1 := coord_hasDerivAt hu 1
  have h2 := coord_hasDerivAt hu 2
  have e : (fun t => axialRot (-t) (v s (axialRot t y)) 0)
      = fun t => Real.cos t * v s (axialRot t y) 0 + Real.sin t * v s (axialRot t y) 1 := by
    funext t
    rw [rot_zero, Real.cos_neg, Real.sin_neg]
    ring
  rw [e]
  refine HasDerivAt.congr_deriv (((Real.hasDerivAt_cos φ).mul h0).add ((Real.hasDerivAt_sin φ).mul h1)) ?_
  simp only [rot_zero, rot_one, Real.cos_neg, Real.sin_neg]
  ring

theorem azim_deriv1 (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (s : ℝ) (y : Space)
    (φ : ℝ) :
    HasDerivAt (fun t => axialRot (-t) (v s (axialRot t y)) 1) (axialRot (-φ) (azimField v s (axialRot φ y)) 1 - axialRot (-φ) (v s (axialRot φ y)) 0) φ := by
  have hu := field_hasDerivAt P v hv s y φ
  have h0 := coord_hasDerivAt hu 0
  have h1 := coord_hasDerivAt hu 1
  have h2 := coord_hasDerivAt hu 2
  have e : (fun t => axialRot (-t) (v s (axialRot t y)) 1)
      = fun t => -Real.sin t * v s (axialRot t y) 0 + Real.cos t * v s (axialRot t y) 1 := by
    funext t
    rw [rot_one, Real.cos_neg, Real.sin_neg]
  rw [e]
  refine HasDerivAt.congr_deriv ((((Real.hasDerivAt_sin φ).neg).mul h0).add ((Real.hasDerivAt_cos φ).mul h1)) ?_
  simp only [rot_zero, rot_one, Real.cos_neg, Real.sin_neg, Pi.neg_apply]
  ring

theorem azim_deriv2 (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (s : ℝ) (y : Space)
    (φ : ℝ) :
    HasDerivAt (fun t => axialRot (-t) (v s (axialRot t y)) 2) (axialRot (-φ) (azimField v s (axialRot φ y)) 2) φ := by
  have hu := field_hasDerivAt P v hv s y φ
  have h0 := coord_hasDerivAt hu 0
  have h1 := coord_hasDerivAt hu 1
  have h2 := coord_hasDerivAt hu 2
  have e : (fun t => axialRot (-t) (v s (axialRot t y)) 2) = fun t => v s (axialRot t y) 2 := by
    funext t
    rw [rot_two]
  rw [e]
  refine HasDerivAt.congr_deriv h2 ?_
  rw [rot_two]

theorem modeAverage_congr_point {β γ : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (g : ℝ → ℝ → γ → ℝ) (b : β) (c : γ)
    (h : ∀ τ φ, f τ φ b = g τ φ c) : modeAverage ι f b = modeAverage ι g c := by
  unfold modeAverage
  simp_rw [h]

theorem mode_shift_coord (ι : ℤ × ℤ) (g A : ℝ → ℝ → Fin 3 → ℝ) (k l : Fin 3) (c : ℝ)
    (hg : ∀ j, Continuous fun p : ℝ × ℝ => g p.1 p.2 j) (hA : ∀ j, Continuous fun p : ℝ × ℝ => A p.1 p.2 j)
    (hd : ∀ τ φ, HasDerivAt (fun t => g τ t k) (A τ φ k + c * g τ φ l) φ)
    (hper : ∀ τ j, g τ (2 * Real.pi) j = g τ 0 j) :
    modeAverage ι A k = ((ι.2 : ℝ) * Complex.I) * modeAverage ι g k - (c : ℂ) * modeAverage ι g l := by
  have e1 : modeAverage ι A k = modeAverage ι (fun τ φ (_ : Unit) => (A τ φ k + c * g τ φ l) + (-c) * g τ φ l) () :=
    modeAverage_congr_point ι _ _ k () fun τ φ => by ring
  have e2 := Internal.Field.modeAverage_add ι (fun τ φ (_ : Unit) => A τ φ k + c * g τ φ l) (fun τ φ (_ : Unit) => (-c) * g τ φ l) ()
    ((hA k).add (continuous_const.mul (hg l))) (continuous_const.mul (hg l))
  have e3 := modeAverage_phi_ibp ι (fun τ φ (_ : Unit) => g τ φ k) (fun τ φ (_ : Unit) => A τ φ k + c * g τ φ l) ()
    (hg k) ((hA k).add (continuous_const.mul (hg l))) hd (fun τ => hper τ k)
  have e4 := Internal.Field.modeAverage_const_mul ι (-c) (fun τ φ (_ : Unit) => g τ φ l) ()
  have e5 : modeAverage ι (fun τ φ (_ : Unit) => g τ φ k) () = modeAverage ι g k :=
    modeAverage_congr_point ι _ _ () k fun τ φ => rfl
  have e6 : modeAverage ι (fun τ φ (_ : Unit) => g τ φ l) () = modeAverage ι g l :=
    modeAverage_congr_point ι _ _ () l fun τ φ => rfl
  rw [e1, e2, e3, e4, e5, e6]
  push_cast
  ring

theorem rot_period (y : Space) : axialRot (2 * Real.pi) y = y := by
  ext j
  fin_cases j <;> simp [axialRot, unitVector]

theorem rot_neg_period (y : Space) : axialRot (-(2 * Real.pi)) y = y := by
  ext j
  fin_cases j <;> simp [axialRot, unitVector]

theorem rot_zero_angle (y : Space) : axialRot 0 y = y := by
  ext j
  fin_cases j <;> simp [axialRot, unitVector]

theorem azimField_continuous (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => azimField v z.1 z.2) := by
  have hG : Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous
  have hJ : Continuous (fun z : ℝ × Space => -(z.2 1) • (unitVector 0 : Space) + z.2 0 • (unitVector 1 : Space)) := by
    fun_prop
  exact hG.clm_apply hJ

theorem azim_mode (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    modeVel ι (azimField v) σ y = fun i => ((ι.2 : ℝ) * Complex.I) * modeVel ι v σ y i + rotZ (modeVel ι v σ y) i := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hg := fun j => Internal.Field.mode_integrand_continuous hvc σ y j
  have hA := fun j => Internal.Field.mode_integrand_continuous (azimField_continuous P v hv) σ y j
  have hper : ∀ τ j, axialRot (-(2 * Real.pi)) (v (σ + τ) (axialRot (2 * Real.pi) y)) j
      = axialRot (-0) (v (σ + τ) (axialRot 0 y)) j := fun τ j => by
    rw [rot_period, rot_neg_period, neg_zero, rot_zero_angle, rot_zero_angle]
  funext i
  fin_cases i
  · have h := mode_shift_coord ι (fun τ φ j => axialRot (-φ) (v (σ + τ) (axialRot φ y)) j)
      (fun τ φ j => axialRot (-φ) (azimField v (σ + τ) (axialRot φ y)) j) 0 1 1 hg hA
      (fun τ φ => by simpa using azim_deriv0 P v hv (σ + τ) y φ) hper
    have h' : modeVel ι (azimField v) σ y 0 = ((ι.2 : ℝ) : ℂ) * Complex.I * modeVel ι v σ y 0
        - ((1 : ℝ) : ℂ) * modeVel ι v σ y 1 := h
    have hr : rotZ (modeVel ι v σ y) 0 = -(modeVel ι v σ y 1) := rfl
    change modeVel ι (azimField v) σ y 0 = ((ι.2 : ℝ) * Complex.I) * modeVel ι v σ y 0 + rotZ (modeVel ι v σ y) 0
    rw [h', hr]
    push_cast
    ring
  · have h := mode_shift_coord ι (fun τ φ j => axialRot (-φ) (v (σ + τ) (axialRot φ y)) j)
      (fun τ φ j => axialRot (-φ) (azimField v (σ + τ) (axialRot φ y)) j) 1 0 (-1) hg hA
      (fun τ φ => by simpa [sub_eq_add_neg] using azim_deriv1 P v hv (σ + τ) y φ) hper
    have h' : modeVel ι (azimField v) σ y 1 = ((ι.2 : ℝ) : ℂ) * Complex.I * modeVel ι v σ y 1
        - (((-1) : ℝ) : ℂ) * modeVel ι v σ y 0 := h
    have hr : rotZ (modeVel ι v σ y) 1 = modeVel ι v σ y 0 := rfl
    change modeVel ι (azimField v) σ y 1 = ((ι.2 : ℝ) * Complex.I) * modeVel ι v σ y 1 + rotZ (modeVel ι v σ y) 1
    rw [h', hr]
    push_cast
    ring
  · have h := mode_shift_coord ι (fun τ φ j => axialRot (-φ) (v (σ + τ) (axialRot φ y)) j)
      (fun τ φ j => axialRot (-φ) (azimField v (σ + τ) (axialRot φ y)) j) 2 2 0 hg hA
      (fun τ φ => by simpa using azim_deriv2 P v hv (σ + τ) y φ) hper
    have h' : modeVel ι (azimField v) σ y 2 = ((ι.2 : ℝ) : ℂ) * Complex.I * modeVel ι v σ y 2
        - ((0 : ℝ) : ℂ) * modeVel ι v σ y 2 := h
    have hr : rotZ (modeVel ι v σ y) 2 = 0 := rfl
    change modeVel ι (azimField v) σ y 2 = ((ι.2 : ℝ) * Complex.I) * modeVel ι v σ y 2 + rotZ (modeVel ι v σ y) 2
    rw [h', hr]
    push_cast
    ring

end Internal.ModeCalc

end Coercive

end Breakdown

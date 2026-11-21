import Breakdown.Uniqueness.PressureMollifyAux
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.Internal

private theorem idt_contDiff_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) (a : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y a) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

private theorem idt_differentiable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

private theorem idt_iteratedFDeriv_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) (a x : Space) :
    iteratedFDeriv ℝ 2 f x ![a, a] = fderiv ℝ (fun y => fderiv ℝ f y a) x a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (idt_differentiable (contDiff_infty_iff_fderiv.1 hf).2) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

private theorem idt_sumSecondPartialsAt_eq {w : Space → Space} (hw : ContDiff ℝ ∞ w) (x : Space) :
    sumSecondPartialsAt w x = ∑ i, fderiv ℝ (fun y => fderiv ℝ w y (unitVector i)) x (unitVector i) := by
  unfold sumSecondPartialsAt
  exact Finset.sum_congr rfl fun i _ => idt_iteratedFDeriv_two hw _ x

private theorem idt_sum_coord (y : Space) : ∑ i, y i • unitVector i = y := by
  ext j
  simp [unitVector, Pi.single_apply]

private theorem idt_integrable {F : Space → ℝ} (hF : Continuous F) {Φ : Space → Space}
    (hc : HasCompactSupport Φ) (h : ∀ x, x ∉ tsupport Φ → F x = 0) : Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hc h)

private theorem idt_integral_fderiv_eq_zero {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (a : Space) : ∫ x, fderiv ℝ h x a = 0 := by
  have := PressureMollify.integral_mul_fderiv (f := fun _ => (1 : ℝ)) contDiff_const hh hc a
  simpa using this

private theorem idt_integral_sum_fderiv_eq_zero {h : Fin 3 → Space → ℝ}
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    ∫ x, ∑ i, fderiv ℝ (h i) x (unitVector i) = 0 := by
  rw [integral_finsetSum _ fun i _ => ((PressureMollify.contDiff_fderiv_apply (hh i) _).continuous
    ).integrable_of_hasCompactSupport (PressureMollify.hasCompactSupport_fderiv_apply (hc i) _)]
  simp [idt_integral_fderiv_eq_zero (hh _) (hc _)]

private theorem idt_vanish {Φ : Space → Space} {x : Space} (hx : x ∉ tsupport Φ) :
    Φ x = 0 ∧ fderiv ℝ Φ x = 0 ∧ iteratedFDeriv ℝ 2 Φ x = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx,
    Function.notMem_support.1 fun h => hx (support_iteratedFDeriv_subset 2 h)⟩

private theorem idt_sumSecondPartials_identity {w Φ : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    ∫ x, inner ℝ (sumSecondPartialsAt w x) (Φ x) = ∫ x, inner ℝ (w x) (sumSecondPartialsAt Φ x) := by
  set k : Fin 3 → Space → ℝ := fun i y =>
    inner ℝ (fderiv ℝ w y (unitVector i)) (Φ y) - inner ℝ (w y) (fderiv ℝ Φ y (unitVector i))
    with hk
  have hks : ∀ i, ContDiff ℝ ∞ (k i) := fun i =>
    ((idt_contDiff_fderiv_apply hw _).inner ℝ hΦ).sub (hw.inner ℝ (idt_contDiff_fderiv_apply hΦ _))
  have hkc : ∀ i, HasCompactSupport (k i) := fun i => HasCompactSupport.intro hc fun x hx => by
    obtain ⟨h1, h2, -⟩ := idt_vanish hx
    simp [hk, h1, h2]
  have hpt : ∀ x, inner ℝ (sumSecondPartialsAt w x) (Φ x) - inner ℝ (w x) (sumSecondPartialsAt Φ x) =
      ∑ i, fderiv ℝ (k i) x (unitVector i) := by
    intro x
    rw [idt_sumSecondPartialsAt_eq hw, idt_sumSecondPartialsAt_eq hΦ, sum_inner, inner_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : k i = fun y => inner ℝ (fderiv ℝ w y (unitVector i)) (Φ y) -
        inner ℝ (w y) (fderiv ℝ Φ y (unitVector i)) := rfl
    rw [e, fderiv_fun_sub, sub_apply, fderiv_inner_apply, fderiv_inner_apply]
    · ring
    all_goals first
      | exact (idt_differentiable (idt_contDiff_fderiv_apply hw _)) x
      | exact (idt_differentiable (idt_contDiff_fderiv_apply hΦ _)) x
      | exact (idt_differentiable hw) x
      | exact (idt_differentiable hΦ) x
      | exact ((idt_differentiable (idt_contDiff_fderiv_apply hw _)) x).inner ℝ ((idt_differentiable hΦ) x)
      | exact ((idt_differentiable hw) x).inner ℝ ((idt_differentiable (idt_contDiff_fderiv_apply hΦ _)) x)
  have hsspc : ∀ {u : Space → Space}, ContDiff ℝ ∞ u → Continuous (sumSecondPartialsAt u) := by
    intro u hu
    have e : sumSecondPartialsAt u = fun x =>
        ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (unitVector i)) x (unitVector i) :=
      funext (idt_sumSecondPartialsAt_eq hu)
    rw [e]
    exact continuous_finsetSum _ fun i _ =>
      (idt_contDiff_fderiv_apply (idt_contDiff_fderiv_apply hu _) _).continuous
  have hI1 : Integrable (fun x => inner ℝ (sumSecondPartialsAt w x) (Φ x)) :=
    idt_integrable ((hsspc hw).inner hΦ.continuous) hc fun x hx => by
      simp [(idt_vanish hx).1]
  have hI2 : Integrable (fun x => inner ℝ (w x) (sumSecondPartialsAt Φ x)) :=
    idt_integrable (hw.continuous.inner (hsspc hΦ)) hc fun x hx => by
      simp [sumSecondPartialsAt, (idt_vanish hx).2.2]
  have h0 := idt_integral_sum_fderiv_eq_zero hks hkc
  have h1 : ∫ x, (inner ℝ (sumSecondPartialsAt w x) (Φ x) - inner ℝ (w x) (sumSecondPartialsAt Φ x)) = 0 := by
    rw [show (fun x => inner ℝ (sumSecondPartialsAt w x) (Φ x) - inner ℝ (w x) (sumSecondPartialsAt Φ x)) =
      fun x => ∑ i, fderiv ℝ (k i) x (unitVector i) from funext hpt]
    exact h0
  rw [integral_sub hI1 hI2] at h1
  linarith

private theorem idt_advection_identity {w Φ : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x, divergenceAt w x = 0) (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    ∫ x, inner ℝ (advectionAt w x) (Φ x) =
      -∫ x, ∑ i, ∑ j, w x i * w x j * fderiv ℝ Φ x (unitVector i) j := by
  set h : Fin 3 → Space → ℝ := fun i y => w y i * inner ℝ (w y) (Φ y) with hh
  have hhs : ∀ i, ContDiff ℝ ∞ (h i) := fun i =>
    (PressureMollify.contDiff_component hw i).mul (hw.inner ℝ hΦ)
  have hhc : ∀ i, HasCompactSupport (h i) := fun i => HasCompactSupport.intro hc fun x hx => by
    simp [hh, (idt_vanish hx).1]
  have hadv : ∀ x, inner ℝ (advectionAt w x) (Φ x) =
      ∑ i, w x i * inner ℝ (fderiv ℝ w x (unitVector i)) (Φ x) := by
    intro x
    have e : advectionAt w x = ∑ i, w x i • fderiv ℝ w x (unitVector i) := by
      unfold advectionAt
      conv_lhs => rw [← idt_sum_coord (w x)]
      simp [map_sum, map_smul]
    rw [e, sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  have hpt : ∀ x, inner ℝ (advectionAt w x) (Φ x) +
      ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i)) =
      ∑ i, fderiv ℝ (h i) x (unitVector i) := by
    intro x
    have hd : ∀ i, fderiv ℝ (h i) x (unitVector i) =
        w x i * (inner ℝ (w x) (fderiv ℝ Φ x (unitVector i)) +
          inner ℝ (fderiv ℝ w x (unitVector i)) (Φ x)) +
        inner ℝ (w x) (Φ x) * fderiv ℝ w x (unitVector i) i := by
      intro i
      have e : h i = fun y => w y i * inner ℝ (w y) (Φ y) := rfl
      rw [e, fderiv_fun_mul ((idt_differentiable (PressureMollify.contDiff_component hw i)) x)
        (((idt_differentiable hw) x).inner ℝ ((idt_differentiable hΦ) x))]
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [fderiv_inner_apply ℝ ((idt_differentiable hw) x) ((idt_differentiable hΦ) x),
        PressureMollify.fderiv_component hw i x]
    simp only [hd]
    have hdv := hdiv x
    unfold divergenceAt at hdv
    rw [hadv]
    have e2 : ∑ i, inner ℝ (w x) (Φ x) * fderiv ℝ w x (unitVector i) i = 0 := by
      rw [← Finset.mul_sum, hdv, mul_zero]
    rw [Finset.sum_add_distrib, e2, add_zero]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hadvc : Continuous (advectionAt w) :=
    ((contDiff_infty_iff_fderiv.1 hw).2.continuous).clm_apply hw.continuous
  have hI1 : Integrable (fun x => inner ℝ (advectionAt w x) (Φ x)) :=
    idt_integrable (hadvc.inner hΦ.continuous) hc fun x hx => by simp [(idt_vanish hx).1]
  have hI2 : Integrable (fun x => ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) :=
    idt_integrable (continuous_finsetSum _ fun i _ =>
      (PressureMollify.continuous_component hw.continuous i).mul
        (hw.continuous.inner (idt_contDiff_fderiv_apply hΦ _).continuous)) hc fun x hx => by
      simp [(idt_vanish hx).2.1]
  have h1 : ∫ x, (inner ℝ (advectionAt w x) (Φ x) +
      ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) = 0 := by
    rw [show (fun x => inner ℝ (advectionAt w x) (Φ x) +
      ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) =
      fun x => ∑ i, fderiv ℝ (h i) x (unitVector i) from funext hpt]
    exact idt_integral_sum_fderiv_eq_zero hhs hhc
  rw [integral_add hI1 hI2] at h1
  have e3 : (fun x => ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) =
      fun x => ∑ i, ∑ j, w x i * w x j * fderiv ℝ Φ x (unitVector i) j := by
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [e3] at h1
  linarith

theorem integral_time_derivative_add_pressureDefect {T : ℝ} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hv : IsSolutionOn T v q) {t : ℝ} (ht : t ∈ Ioo 0 T)
    {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) + pressureDefect v q t Φ =
      (∫ x, inner ℝ (v t x) (sumSecondPartialsAt Φ x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ Φ x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt Φ)) := by
  have hvt : ContDiff ℝ ∞ (v t) :=
    CutoffEnergy.contDiff_slice hv.smooth_velocity (Ioo_subset_Icc_self ht)
  have hqt : ContDiff ℝ ∞ (q t) :=
    CutoffEnergy.contDiff_slice hv.smooth_pressure (Ioo_subset_Icc_self ht)
  have hmom : ∀ x, deriv (fun τ => v τ x) t =
      sumSecondPartialsAt (v t) x - gradientAt (q t) x - advectionAt (v t) x :=
    fun x => eq_sub_of_add_eq (hv.momentum t ht x)
  have hdiv : ∀ x, divergenceAt (v t) x = 0 := hv.incompressible t (Ioo_subset_Icc_self ht)
  have hL := idt_sumSecondPartials_identity hvt hΦ hc
  have hA := idt_advection_identity hvt hdiv hΦ hc
  have hsspc : Continuous (sumSecondPartialsAt (v t)) := by
    have e : sumSecondPartialsAt (v t) = fun x =>
        ∑ i, fderiv ℝ (fun y => fderiv ℝ (v t) y (unitVector i)) x (unitVector i) :=
      funext (idt_sumSecondPartialsAt_eq hvt)
    rw [e]
    exact continuous_finsetSum _ fun i _ =>
      (idt_contDiff_fderiv_apply (idt_contDiff_fderiv_apply hvt _) _).continuous
  have hgc : Continuous (gradientAt (q t)) := by
    show Continuous (fun x => ∑ i : Fin 3, fderiv ℝ (q t) x (unitVector i) • unitVector i)
    exact continuous_finsetSum _ fun i _ =>
      (idt_contDiff_fderiv_apply hqt _).continuous.smul continuous_const
  have hadvc : Continuous (advectionAt (v t)) :=
    ((contDiff_infty_iff_fderiv.1 hvt).2.continuous).clm_apply hvt.continuous
  have hI1 : Integrable (fun x => inner ℝ (sumSecondPartialsAt (v t) x) (Φ x)) :=
    idt_integrable (hsspc.inner hΦ.continuous) hc fun x hx => by simp [(idt_vanish hx).1]
  have hI2 : Integrable (fun x => inner ℝ (gradientAt (q t) x) (Φ x)) :=
    idt_integrable (hgc.inner hΦ.continuous) hc fun x hx => by simp [(idt_vanish hx).1]
  have hI3 : Integrable (fun x => inner ℝ (advectionAt (v t) x) (Φ x)) :=
    idt_integrable (hadvc.inner hΦ.continuous) hc fun x hx => by simp [(idt_vanish hx).1]
  have hD : (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) =
      (∫ x, inner ℝ (sumSecondPartialsAt (v t) x) (Φ x)) - (∫ x, inner ℝ (gradientAt (q t) x) (Φ x)) -
        ∫ x, inner ℝ (advectionAt (v t) x) (Φ x) := by
    simp only [hmom, inner_sub_left]
    have hI12 : Integrable (fun x => inner ℝ (sumSecondPartialsAt (v t) x) (Φ x) -
        inner ℝ (gradientAt (q t) x) (Φ x)) := hI1.sub hI2
    rw [integral_sub hI12 hI3, integral_sub hI1 hI2]
  unfold pressureDefect
  rw [hD, hL, hA]
  ring

end Breakdown.Internal

import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace ShiftRotateTensorInternal

open Breakdown.Coercive.RotationInternal

private theorem axialRot_add_two_pi (θ : ℝ) (y : Space) : axialRot (θ + 2 * Real.pi) y = axialRot θ y := by
  apply space_ext
  · simp only [axialRot_apply_zero, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · simp only [axialRot_apply_one, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · simp only [axialRot_apply_two]

private theorem axialRot_neg_add_two_pi (θ : ℝ) (y : Space) :
    axialRot (-(θ + 2 * Real.pi)) y = axialRot (-θ) y := by
  apply space_ext
  · simp only [axialRot_apply_zero, neg_add, Real.cos_sub_two_pi, Real.sin_sub_two_pi,
      ← sub_eq_add_neg]
  · simp only [axialRot_apply_one, neg_add, Real.cos_sub_two_pi, Real.sin_sub_two_pi,
      ← sub_eq_add_neg]
  · simp only [axialRot_apply_two]

private theorem axialRot_component_expand (θ : ℝ) (v : Space) (i : Fin 3) :
    axialRot θ v i = ∑ a : Fin 3, axialRot θ (unitVector a) i * v a := by
  fin_cases i <;>
    simp [Fin.sum_univ_three, axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two,
      unitVector]
  all_goals ring

private theorem continuous_axialRot_component (v : Space) (i : Fin 3) :
    Continuous (fun θ : ℝ => axialRot θ v i) := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, axialRot_apply_zero]
    fun_prop
  · simp only [Fin.mk_one, Fin.isValue, axialRot_apply_one]
    fun_prop
  · simp only [Fin.reduceFinMk, Fin.isValue, axialRot_apply_two]
    fun_prop

private theorem axialRot_unit_recombine (φ ψ : ℝ) (j : Fin 3) :
    axialRot ψ (unitVector j) =
      ∑ b : Fin 3, axialRot φ (unitVector b) j • axialRot (ψ + φ) (unitVector b) := by
  apply space_ext <;> fin_cases j <;>
    simp [Fin.sum_univ_three, axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two,
      unitVector, Real.cos_add, Real.sin_add] <;>
    first
      | linear_combination (-Real.cos ψ) * Real.sin_sq_add_cos_sq φ
      | linear_combination (Real.sin ψ) * Real.sin_sq_add_cos_sq φ
      | linear_combination (-Real.sin ψ) * Real.sin_sq_add_cos_sq φ

private theorem axialRot_neg_split (φ ψ : ℝ) (x : Space) :
    axialRot (-ψ) x = axialRot φ (axialRot (-(ψ + φ)) x) := by
  rw [← axialRot_add]
  congr 1
  ring

private theorem phase_shift (ι : ℤ × ℤ) (τ ψ s φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((2 * Real.pi * ι.1 * s + ι.2 * φ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(((2 * Real.pi * ι.1 * (τ + s) + ι.2 * (ψ + φ) : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_time_period (ι : ℤ × ℤ) (τ ψ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * (τ + 1) + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) := by
  have h : -(((2 * Real.pi * ι.1 * (τ + 1) + ι.2 * ψ : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)
        + ((-ι.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem phase_angle_period (ι : ℤ × ℤ) (τ ψ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * (ψ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) := by
  have h : -(((2 * Real.pi * ι.1 * τ + ι.2 * (ψ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)
        + ((-ι.2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem modeAverage_shift {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) (s φ : ℝ)
    (hτ : ∀ τ ψ, f (τ + 1) ψ b = f τ ψ b) (hψ : ∀ τ ψ, f τ (ψ + 2 * Real.pi) b = f τ ψ b) :
    modeAverage ι (fun τ ψ c => f (τ + s) (ψ + φ) c) b =
      Complex.exp (((2 * Real.pi * ι.1 * s + ι.2 * φ : ℝ) : ℂ) * Complex.I) * modeAverage ι f b := by
  set g : ℝ → ℝ → ℂ := fun τ ψ =>
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) * ((f τ ψ b : ℝ) : ℂ)
    with hg
  have hgψ : ∀ τ, Function.Periodic (g τ) (2 * Real.pi) := fun τ ψ => by
    simp only [hg, phase_angle_period, hψ]
  have hgτ : Function.Periodic (fun τ => ∫ ψ in (0 : ℝ)..(2 * Real.pi), g τ ψ) 1 := fun τ => by
    simp only [hg, phase_time_period, hτ]
  have hin : ∀ t, ∫ ψ in (0 : ℝ)..(2 * Real.pi), g t (ψ + φ) = ∫ ψ in (0 : ℝ)..(2 * Real.pi), g t ψ := by
    intro t
    rw [intervalIntegral.integral_comp_add_right (g t) φ, zero_add, add_comm (2 * Real.pi) φ]
    simpa using (hgψ t).intervalIntegral_add_eq φ 0
  have hout : ∫ τ in (0 : ℝ)..1, ∫ ψ in (0 : ℝ)..(2 * Real.pi), g (τ + s) ψ
      = ∫ τ in (0 : ℝ)..1, ∫ ψ in (0 : ℝ)..(2 * Real.pi), g τ ψ := by
    rw [intervalIntegral.integral_comp_add_right (fun τ => ∫ ψ in (0 : ℝ)..(2 * Real.pi), g τ ψ) s,
      zero_add, add_comm (1 : ℝ) s]
    simpa using hgτ.intervalIntegral_add_eq s 0
  have hpt : ∀ τ ψ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I))
      * ((f (τ + s) (ψ + φ) b : ℝ) : ℂ)
      = Complex.exp (((2 * Real.pi * ι.1 * s + ι.2 * φ : ℝ) : ℂ) * Complex.I) * g (τ + s) (ψ + φ) := by
    intro τ ψ
    rw [hg, phase_shift ι τ ψ s φ]
    ring
  simp only [modeAverage]
  simp_rw [hpt, intervalIntegral.integral_const_mul, hin, hout]
  simp only [hg]
  ring

private theorem iterated_eq_set (F : ℝ → ℝ → ℂ)
    (hF : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) :
    ∫ τ in (0 : ℝ)..1, ∫ ψ in (0 : ℝ)..(2 * Real.pi), F τ ψ
      = ∫ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi), F p.1 p.2 := by
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [setIntegral_prod (fun p : ℝ × ℝ => F p.1 p.2) hF, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  funext τ
  rw [intervalIntegral.integral_of_le h2, ← integral_Icc_eq_integral_Ioc]

private theorem modeAverage_linear {β γ : Type*} [Fintype γ] (ι : ℤ × ℤ) (r : β → γ → ℝ)
    (k : ℝ → ℝ → γ → ℝ) (b : β)
    (hk : ∀ c, IntegrableOn (fun p : ℝ × ℝ => k p.1 p.2 c)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) :
    modeAverage ι (fun τ ψ b => ∑ c, r b c * k τ ψ c) b = ∑ c, (r b c : ℂ) * modeAverage ι k c := by
  have hS : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have he : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) := by
    fun_prop
  have hF : ∀ c, IntegrableOn (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
        * ((k p.1 p.2 c : ℝ) : ℂ)) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    fun c => IntegrableOn.continuousOn_mul he.continuousOn (hk c).ofReal hS
  have hpt : (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
        * ((∑ c, r b c * k p.1 p.2 c : ℝ) : ℂ)) = fun p => ∑ c, (r b c : ℂ) *
      (Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
        * ((k p.1 p.2 c : ℝ) : ℂ)) := by
    funext p
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hsum : IntegrableOn (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
        * ((∑ c, r b c * k p.1 p.2 c : ℝ) : ℂ)) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    rw [hpt]
    exact integrable_finsetSum _ fun c _ => (hF c).const_mul _
  have hL := iterated_eq_set (fun τ ψ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I))
        * ((∑ c, r b c * k τ ψ c : ℝ) : ℂ)) hsum
  have hR : ∀ c, ∫ τ in (0 : ℝ)..1, ∫ ψ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) * ((k τ ψ c : ℝ) : ℂ)
      = ∫ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
          * ((k p.1 p.2 c : ℝ) : ℂ) := fun c =>
    iterated_eq_set (fun τ ψ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) * ((k τ ψ c : ℝ) : ℂ))
      (hF c)
  simp only [modeAverage]
  rw [hL]
  simp_rw [hR]
  rw [hpt, integral_finsetSum _ fun c _ => (hF c).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_const_mul]
  ring

private theorem rotated_component_integrableOn (W : ℝ × ℝ → Space)
    (hW : IntegrableOn W (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => axialRot (-p.2) (W p) a)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  have hS : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have h : (fun p : ℝ × ℝ => axialRot (-p.2) (W p) a)
      = fun p => ∑ c : Fin 3, axialRot (-p.2) (unitVector c) a * W p c :=
    funext fun p => axialRot_component_expand _ _ _
  rw [h]
  refine integrable_finsetSum _ fun c _ => ?_
  have hc : IntegrableOn (fun p => W p c) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    exact (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp hW
  have hcont : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (unitVector c) a) :=
    (continuous_axialRot_component (unitVector c) a).comp continuous_snd.neg
  exact IntegrableOn.continuousOn_mul hcont.continuousOn hc hS

private theorem grad_pointwise (L : Space →L[ℝ] Space) (φ ψ : ℝ) (i j : Fin 3) :
    axialRot (-ψ) (L (axialRot ψ (unitVector j))) i =
      ∑ c : Fin 3 × Fin 3, (axialRot φ (unitVector c.1) i * axialRot φ (unitVector c.2) j) *
        axialRot (-(ψ + φ)) (L (axialRot (ψ + φ) (unitVector c.2))) c.1 := by
  rw [axialRot_unit_recombine φ ψ j, axialRot_neg_split φ ψ, axialRot_component_expand φ]
  simp only [Fin.sum_univ_three, Fintype.sum_prod_type, map_add, map_smul, axialRot_map_add,
    axialRot_map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem secondDeriv_pointwise (B : Space →L[ℝ] Space →L[ℝ] Space) (φ ψ : ℝ) (i j l : Fin 3) :
    axialRot (-ψ) (B (axialRot ψ (unitVector j)) (axialRot ψ (unitVector l))) i =
      ∑ c : Fin 3 × Fin 3 × Fin 3, (axialRot φ (unitVector c.1) i * axialRot φ (unitVector c.2.1) j
          * axialRot φ (unitVector c.2.2) l) *
        axialRot (-(ψ + φ)) (B (axialRot (ψ + φ) (unitVector c.2.1))
          (axialRot (ψ + φ) (unitVector c.2.2))) c.1 := by
  rw [axialRot_unit_recombine φ ψ j, axialRot_unit_recombine φ ψ l, axialRot_neg_split φ ψ,
    axialRot_component_expand φ]
  simp only [Fin.sum_univ_three, Fintype.sum_prod_type, map_add, map_smul, axialRot_map_add,
    _root_.add_apply, _root_.smul_apply,
    axialRot_map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end ShiftRotateTensorInternal

open Breakdown.Coercive.RotationInternal ShiftRotateTensorInternal in
theorem modeShiftRotateTensor : ModeShiftRotateTensorHolds := by
  refine ⟨fun G hG ξ σ s φ y hint => ?_, fun H hH ξ σ s φ y hint => ?_⟩
  · set k : ℝ → ℝ → Fin 3 × Fin 3 → ℝ := fun τ ψ ab =>
      axialRot (-ψ) (G (σ + τ) (axialRot ψ y) (axialRot ψ (unitVector ab.2))) ab.1 with hk
    set r : Fin 3 × Fin 3 → Fin 3 × Fin 3 → ℝ := fun ij c =>
      axialRot φ (unitVector c.1) ij.1 * axialRot φ (unitVector c.2) ij.2 with hr
    have hL : modeGrad ξ G (σ + s) (axialRot φ y) = modeAverage ξ (fun τ ψ ij =>
        (fun τ ψ ij => ∑ c, r ij c * k τ ψ c) (τ + s) (ψ + φ) ij) := by
      unfold modeGrad
      congr 1
      funext τ ψ ij
      rw [show σ + s + τ = σ + (τ + s) by ring, ← axialRot_add ψ φ y]
      exact grad_pointwise _ φ ψ ij.1 ij.2
    have hkτ : ∀ τ ψ c, k (τ + 1) ψ c = k τ ψ c := by
      intro τ ψ c
      simp only [hk, show σ + (τ + 1) = σ + τ + 1 by ring, hG (σ + τ) (axialRot ψ y)]
    have hkψ : ∀ τ ψ c, k τ (ψ + 2 * Real.pi) c = k τ ψ c := by
      intro τ ψ c
      simp only [hk, axialRot_add_two_pi, axialRot_neg_add_two_pi]
    have hki : ∀ c, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => k p.1 p.2 c)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := fun c =>
      rotated_component_integrableOn _ (hint c.2) c.1
    funext ij
    rw [hL, modeAverage_shift ξ (fun τ ψ ij => ∑ c, r ij c * k τ ψ c) ij s φ
        (fun τ ψ => by simp only [hkτ]) (fun τ ψ => by simp only [hkψ]),
      modeAverage_linear ξ r k ij hki, Fintype.sum_prod_type]
    rfl
  · set k : ℝ → ℝ → Fin 3 × Fin 3 × Fin 3 → ℝ := fun τ ψ abc =>
      axialRot (-ψ) (H (σ + τ) (axialRot ψ y) (axialRot ψ (unitVector abc.2.1))
        (axialRot ψ (unitVector abc.2.2))) abc.1 with hk
    set r : Fin 3 × Fin 3 × Fin 3 → Fin 3 × Fin 3 × Fin 3 → ℝ := fun ijl c =>
      axialRot φ (unitVector c.1) ijl.1 * axialRot φ (unitVector c.2.1) ijl.2.1
        * axialRot φ (unitVector c.2.2) ijl.2.2 with hr
    have hL : modeSecondDeriv ξ H (σ + s) (axialRot φ y) = modeAverage ξ (fun τ ψ ijl =>
        (fun τ ψ ijl => ∑ c, r ijl c * k τ ψ c) (τ + s) (ψ + φ) ijl) := by
      unfold modeSecondDeriv
      congr 1
      funext τ ψ ijl
      rw [show σ + s + τ = σ + (τ + s) by ring, ← axialRot_add ψ φ y]
      exact secondDeriv_pointwise _ φ ψ ijl.1 ijl.2.1 ijl.2.2
    have hkτ : ∀ τ ψ c, k (τ + 1) ψ c = k τ ψ c := by
      intro τ ψ c
      simp only [hk, show σ + (τ + 1) = σ + τ + 1 by ring, hH (σ + τ) (axialRot ψ y)]
    have hkψ : ∀ τ ψ c, k τ (ψ + 2 * Real.pi) c = k τ ψ c := by
      intro τ ψ c
      simp only [hk, axialRot_add_two_pi, axialRot_neg_add_two_pi]
    have hki : ∀ c, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => k p.1 p.2 c)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := fun c =>
      rotated_component_integrableOn _ (hint c.2.1 c.2.2) c.1
    funext ijl
    rw [hL, modeAverage_shift ξ (fun τ ψ ijl => ∑ c, r ijl c * k τ ψ c) ijl s φ
        (fun τ ψ => by simp only [hkτ]) (fun τ ψ => by simp only [hkψ]),
      modeAverage_linear ξ r k ijl hki]
    simp only [Fintype.sum_prod_type]
    rfl

end Bridge

end CertCell

end Breakdown

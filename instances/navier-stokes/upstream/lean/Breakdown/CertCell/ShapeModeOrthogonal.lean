import Breakdown.Cert.CoerciveStatement

open MeasureTheory

namespace Breakdown

namespace Internal.ModeOrthogonal

private lemma circle_integral (l : ℤ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((((l : ℝ) * φ : ℝ) : ℂ) * Complex.I)) =
      if l = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hl
  · subst hl
    simp
  · have hc : (l : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hl) Complex.I_ne_zero
    have hrw : ∀ φ : ℝ, Complex.exp ((((l : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((l : ℂ) * Complex.I * (φ : ℂ)) := by
      intro φ
      congr 1
      push_cast
      ring
    simp_rw [hrw]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((l : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I l]
      congr 1
      push_cast
      ring
    rw [h2]
    simp

private lemma line_integral (m : ℤ) :
    (∫ τ in (0 : ℝ)..1, Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm
    simp
  · have hc : (2 * Real.pi * (m : ℂ)) * Complex.I ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) (by exact_mod_cast hm))
        Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have hrw : ∀ τ : ℝ, Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((2 * Real.pi * (m : ℂ)) * Complex.I * (τ : ℂ)) := by
      intro τ
      congr 1
      push_cast
      ring
    simp_rw [hrw]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * (m : ℂ)) * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I m]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

private lemma inner_term (c : ℂ) (m l : ℤ) (τ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
        c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ + (l : ℝ) * φ : ℝ) : ℂ) * Complex.I)) =
      (c * if l = 0 then (2 * Real.pi : ℂ) else 0) *
        Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I) := by
  have hrw : ∀ φ : ℝ,
      c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ + (l : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        (c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((l : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
    intro φ
    rw [mul_assoc c, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, circle_integral]
  ring

private lemma outer_term (c : ℂ) (m : ℤ) :
    (∫ τ in (0 : ℝ)..1, c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I)) =
      if m = 0 then c else 0 := by
  rw [intervalIntegral.integral_const_mul, line_integral]
  split_ifs <;> simp

private lemma double_sum {α : Type*} (t : Finset α) (m l m' l' : α → ℤ) (c d : α → ℂ) :
    (∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ j ∈ t, (c j * Complex.exp
            (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
          d j * Complex.exp
            (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) * Complex.I))) =
      ∑ j ∈ t, ((if m j = 0 then c j * (if l j = 0 then (2 * Real.pi : ℂ) else 0) else 0) +
        (if m' j = 0 then d j * (if l' j = 0 then (2 * Real.pi : ℂ) else 0) else 0)) := by
  have hinner : ∀ τ : ℝ, (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ j ∈ t, (c j * Complex.exp
            (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
          d j * Complex.exp
            (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) * Complex.I))) =
      ∑ j ∈ t, ((c j * if l j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m j : ℝ) * τ : ℝ) : ℂ) * Complex.I) +
        (d j * if l' j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m' j : ℝ) * τ : ℝ) : ℂ) * Complex.I)) := by
    intro τ
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_add, inner_term, inner_term]
      · exact (by fun_prop : Continuous fun φ : ℝ => c j * Complex.exp
          (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun φ : ℝ => d j * Complex.exp
          (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
    · intro j _
      exact (by fun_prop : Continuous fun φ : ℝ => c j * Complex.exp
          (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
          d j * Complex.exp
          (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
  simp only [hinner]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_add, outer_term, outer_term]
    · exact (by fun_prop : Continuous fun τ : ℝ => (c j * if l j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m j : ℝ) * τ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun τ : ℝ => (d j * if l' j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m' j : ℝ) * τ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
  · intro j _
    exact (by fun_prop : Continuous fun τ : ℝ => (c j * if l j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m j : ℝ) * τ : ℝ) : ℂ) * Complex.I) +
        (d j * if l' j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m' j : ℝ) * τ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _

private lemma pointwise_split (ξ ν : ℤ × ℤ) (w : ℂ) (τ φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) *
        (((Complex.exp (((2 * Real.pi * (ν.1 : ℝ) * τ + (ν.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I) * w).re
          : ℝ) : ℂ) =
      (w / 2) * Complex.exp (((2 * Real.pi * ((ν.1 - ξ.1 : ℤ) : ℝ) * τ +
          ((ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
        (starRingEnd ℂ w / 2) * Complex.exp (((2 * Real.pi * ((-ν.1 - ξ.1 : ℤ) : ℝ) * τ +
          ((-ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
  set θ : ℝ := 2 * Real.pi * (ν.1 : ℝ) * τ + (ν.2 : ℝ) * φ with hθ
  set θ₀ : ℝ := 2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ with hθ₀
  have h1 : Complex.exp (((2 * Real.pi * ((ν.1 - ξ.1 : ℤ) : ℝ) * τ +
      ((ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ₀ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add, hθ, hθ₀]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (((2 * Real.pi * ((-ν.1 - ξ.1 : ℤ) : ℝ) * τ +
      ((-ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp (-((θ₀ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add, hθ, hθ₀]
    congr 1
    push_cast
    ring
  have h3 : starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [Complex.re_eq_add_conj, map_mul, h3, h1, h2]
  ring

private lemma ite_two_pi (x : ℂ) (a b : ℤ) :
    (if a = 0 then x * (if b = 0 then (2 * Real.pi : ℂ) else 0) else 0) =
      (if a = 0 ∧ b = 0 then x else 0) * (2 * Real.pi : ℂ) := by
  split_ifs <;> simp_all

end Internal.ModeOrthogonal

open Internal.ModeOrthogonal in
theorem modeAverage_of_waveSum {α β : Type*} (s : Finset α) (ν : α → ℤ × ℤ) (w : α → ℂ)
    (f : ℝ → ℝ → β → ℝ) (b : β)
    (hf : ∀ τ φ : ℝ, f τ φ b = ∑ a ∈ s,
      (Complex.exp (((2 * Real.pi * ((ν a).1 : ℝ) * τ + ((ν a).2 : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        w a).re)
    (ξ : ℤ × ℤ) :
    modeAverage ξ f b = ∑ a ∈ s, ((if ξ = ν a then w a / 2 else 0) +
      (if ξ = -ν a then starRingEnd ℂ (w a) / 2 else 0)) := by
  have hpt : ∀ τ φ : ℝ,
      Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) *
        ((f τ φ b : ℝ) : ℂ) =
      ∑ a ∈ s, ((w a / 2) * Complex.exp (((2 * Real.pi * (((ν a).1 - ξ.1 : ℤ) : ℝ) * τ +
          (((ν a).2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
        (starRingEnd ℂ (w a) / 2) * Complex.exp (((2 * Real.pi * ((-(ν a).1 - ξ.1 : ℤ) : ℝ) * τ +
          ((-(ν a).2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I)) := by
    intro τ φ
    rw [hf, Complex.ofReal_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => pointwise_split ξ (ν a) (w a) τ φ
  unfold modeAverage
  have hI : (∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) *
        ((f τ φ b : ℝ) : ℂ)) =
      ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ a ∈ s, ((w a / 2) * Complex.exp (((2 * Real.pi * (((ν a).1 - ξ.1 : ℤ) : ℝ) * τ +
          (((ν a).2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
        (starRingEnd ℂ (w a) / 2) * Complex.exp (((2 * Real.pi * ((-(ν a).1 - ξ.1 : ℤ) : ℝ) * τ +
          ((-(ν a).2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr fun τ _ => intervalIntegral.integral_congr fun φ _ => hpt τ φ
  rw [hI, double_sum, Finset.mul_sum]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  refine Finset.sum_congr rfl fun a _ => ?_
  generalize ν a = v
  obtain ⟨n, k⟩ := v
  obtain ⟨p, q⟩ := ξ
  rw [ite_two_pi, ite_two_pi, ← add_mul, one_div, mul_comm, mul_assoc, mul_inv_cancel₀ hpi, mul_one]
  congr 1 <;> split_ifs <;> first | rfl | (exfalso; simp only [Prod.mk.injEq, Prod.neg_mk] at *; omega)

theorem modeAverage_of_wave {β : Type*} (ν : ℤ × ℤ) (w : ℂ) (f : ℝ → ℝ → β → ℝ) (b : β)
    (hf : ∀ τ φ : ℝ, f τ φ b = (Complex.exp (((2 * Real.pi * ((ν.1) : ℝ) * τ + ((ν.2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) * w).re)
    (ξ : ℤ × ℤ) :
    modeAverage ξ f b = (if ξ = ν then w / 2 else 0) +
      (if ξ = -ν then starRingEnd ℂ w / 2 else 0) := by
  have h := modeAverage_of_waveSum ({()} : Finset Unit) (fun _ => ν) (fun _ => w) f b
    (fun τ φ => by rw [Finset.sum_singleton]; exact hf τ φ) ξ
  rw [h, Finset.sum_singleton]

theorem modeVel_of_waveSum {α : Type*} (s : Finset α) (ν : α → ℤ × ℤ) (w : α → Fin 3 → ℂ)
    (v : ℝ → Space → Space) (σ : ℝ) (y : Space)
    (hv : ∀ (τ φ : ℝ) (i : Fin 3), axialRot (-φ) (v (σ + τ) (axialRot φ y)) i = ∑ a ∈ s,
      (Complex.exp (((2 * Real.pi * (((ν a).1) : ℝ) * τ + (((ν a).2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) * w a i).re)
    (ξ : ℤ × ℤ) :
    modeVel ξ v σ y = fun i => ∑ a ∈ s, ((if ξ = ν a then w a i / 2 else 0) +
      (if ξ = -ν a then starRingEnd ℂ (w a i) / 2 else 0)) := by
  funext i
  exact modeAverage_of_waveSum s ν (fun a => w a i) _ i (fun τ φ => hv τ φ i) ξ

theorem modeGrad_of_waveSum {α : Type*} (s : Finset α) (ν : α → ℤ × ℤ)
    (w : α → Fin 3 × Fin 3 → ℂ) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (hG : ∀ (τ φ : ℝ) (ij : Fin 3 × Fin 3),
      axialRot (-φ) (G (σ + τ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1 = ∑ a ∈ s,
        (Complex.exp (((2 * Real.pi * (((ν a).1) : ℝ) * τ + (((ν a).2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) * w a ij).re)
    (ξ : ℤ × ℤ) :
    modeGrad ξ G σ y = fun ij => ∑ a ∈ s, ((if ξ = ν a then w a ij / 2 else 0) +
      (if ξ = -ν a then starRingEnd ℂ (w a ij) / 2 else 0)) := by
  funext ij
  exact modeAverage_of_waveSum s ν (fun a => w a ij) _ ij (fun τ φ => hG τ φ ij) ξ

theorem modeSecondDeriv_of_waveSum {α : Type*} (s : Finset α) (ν : α → ℤ × ℤ)
    (w : α → Fin 3 × Fin 3 × Fin 3 → ℂ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space)
    (hH : ∀ (τ φ : ℝ) (ijl : Fin 3 × Fin 3 × Fin 3),
      axialRot (-φ) (H (σ + τ) (axialRot φ y) (axialRot φ (unitVector ijl.2.1))
        (axialRot φ (unitVector ijl.2.2))) ijl.1 = ∑ a ∈ s,
        (Complex.exp (((2 * Real.pi * (((ν a).1) : ℝ) * τ + (((ν a).2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) * w a ijl).re)
    (ξ : ℤ × ℤ) :
    modeSecondDeriv ξ H σ y = fun ijl => ∑ a ∈ s, ((if ξ = ν a then w a ijl / 2 else 0) +
      (if ξ = -ν a then starRingEnd ℂ (w a ijl) / 2 else 0)) := by
  funext ijl
  exact modeAverage_of_waveSum s ν (fun a => w a ijl) _ ijl (fun τ φ => hH τ φ ijl) ξ

end Breakdown

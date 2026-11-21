import Breakdown.CertCell.ShapeTypeTwoDecayChart

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem radialPhase_derivs {F : ℝ → ℝ} (hF : IsRadialPhase F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 < u →
      HasDerivAt F (deriv F u) u ∧ HasDerivAt (deriv F) (deriv (deriv F) u) u ∧
      HasDerivAt (deriv (deriv F)) (deriv (deriv (deriv F)) u) u ∧
      |u * deriv F u| ≤ B ∧ |u ^ 2 * deriv (deriv F) u| ≤ B ∧ |u ^ 3 * deriv (deriv (deriv F)) u| ≤ B := by
  obtain ⟨δ, hδ, hC⟩ := hF.smooth
  obtain ⟨B, hB⟩ := hF.scaled_bounded
  have hs : IsOpen (Set.Ioi (-δ)) := isOpen_Ioi
  have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
  have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
  have e1 : ((0 : WithTop ℕ∞) + 1) = 1 := by norm_num
  have h3 : ContDiffOn ℝ (2 + 1) F (Set.Ioi (-δ)) := by rw [e3]; exact hC
  obtain ⟨d0, -, h2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hs).1 h3
  have h2' : ContDiffOn ℝ (1 + 1) (deriv F) (Set.Ioi (-δ)) := by rw [e2]; exact h2
  obtain ⟨d1, -, h1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hs).1 h2'
  have h1' : ContDiffOn ℝ (0 + 1) (deriv (deriv F)) (Set.Ioi (-δ)) := by rw [e1]; exact h1
  obtain ⟨d2, -, -⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hs).1 h1'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl).1
  have i2 : iteratedDeriv 2 F = deriv (deriv F) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have i3 : iteratedDeriv 3 F = deriv (deriv (deriv F)) := by rw [iteratedDeriv_succ, i2]
  refine ⟨B, hB0, fun u hu => ?_⟩
  have hu' : u ∈ Set.Ioi (-δ) := by
    show -δ < u
    linarith
  obtain ⟨b1, b2, b3⟩ := hB u hu.le
  rw [i2] at b2
  rw [i3] at b3
  refine ⟨((d0 u hu').differentiableAt (hs.mem_nhds hu')).hasDerivAt,
    ((d1 u hu').differentiableAt (hs.mem_nhds hu')).hasDerivAt,
    ((d2 u hu').differentiableAt (hs.mem_nhds hu')).hasDerivAt, b1, b2, b3⟩

theorem comp_sq_hasDerivAt {f f' : ℝ → ℝ} {s : ℝ} (h : HasDerivAt f (f' (s ^ 2)) (s ^ 2)) :
    HasDerivAt (fun x : ℝ => f (x ^ 2)) (f' (s ^ 2) * (2 * s)) s := by
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
  exact HasDerivAt.comp (h := fun x : ℝ => x ^ 2) s h h2

theorem abs_const_mul_le {c a B : ℝ} (hc : 0 ≤ c) (h : |a| ≤ B) : |c * a| ≤ c * B := by
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left h hc

theorem chartRadius_chartCoord (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    chartRadius P (chartCoord P y) = ‖y‖ := by
  have h1 : 0 < ‖y‖ + P.chartLength := by positivity
  rw [chartRadius, one_sub_chartCoord P hL y, chartCoord]
  field_simp

theorem farBound_phaseSlope (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) :
    FarBound (fun y => (((j : ℝ) * phaseSlope P (chartCoord P y) : ℝ) : ℂ)) 0 := by
  obtain ⟨B, hB0, hF⟩ := radialPhase_derivs hP.phase
  set F := P.radialPhase
  set F1 := deriv F
  set F2 := deriv F1
  set F3 := deriv F2
  have hsq : ∀ s : ℝ, 1 ≤ s → 0 < s ^ 2 := fun s hs => by positivity
  have hG1 : ∀ s : ℝ, 1 ≤ s → HasDerivAt (fun x : ℝ => F1 (x ^ 2)) (F2 (s ^ 2) * (2 * s)) s :=
    fun s hs => comp_sq_hasDerivAt (hF _ (hsq s hs)).2.1
  have hG2 : ∀ s : ℝ, 1 ≤ s → HasDerivAt (fun x : ℝ => F2 (x ^ 2)) (F3 (s ^ 2) * (2 * s)) s :=
    fun s hs => comp_sq_hasDerivAt (hF _ (hsq s hs)).2.2.1
  have hp : ∀ (n : ℕ) (s : ℝ), HasDerivAt (fun x : ℝ => x ^ n) (n * s ^ (n - 1)) s := fun n s => hasDerivAt_pow n s
  have h := farBound_radial (ρ := fun s : ℝ => (((j : ℝ) * (2 * s ^ 2 * F1 (s ^ 2)) : ℝ) : ℂ))
    (ρ1 := fun s => (((j : ℝ) * (4 * s * F1 (s ^ 2) + 4 * s ^ 3 * F2 (s ^ 2)) : ℝ) : ℂ))
    (ρ2 := fun s => (((j : ℝ) * (4 * F1 (s ^ 2) + 20 * s ^ 2 * F2 (s ^ 2) + 8 * s ^ 4 * F3 (s ^ 2)) : ℝ) : ℂ))
    (a := 0) (R0 := 1) (C := 32 * |(j : ℝ)| * B) le_rfl (by positivity) (fun s hs => ?_) (fun s hs => ?_)
    (fun s hs => ?_)
  · refine h.congr (R0 := 0) fun y _ => ?_
    rw [phaseSlope, chartRadius_chartCoord P hP.chartLength_pos y]
  · refine HasDerivAt.ofReal_comp ?_
    have := (((hp 2 s).const_mul 2).mul (hG1 s hs)).const_mul (j : ℝ)
    refine this.congr_deriv ?_
    push_cast
    ring
  · refine HasDerivAt.ofReal_comp ?_
    have := ((((hasDerivAt_id' s).const_mul 4).mul (hG1 s hs)).add (((hp 3 s).const_mul 4).mul (hG2 s hs))).const_mul (j : ℝ)
    refine this.congr_deriv ?_
    push_cast
    ring
  · have hs0 : 0 < s := by linarith
    obtain ⟨-, -, -, b1, b2, b3⟩ := hF (s ^ 2) (hsq s hs)
    set X := s ^ 2 * F1 (s ^ 2)
    set Y := (s ^ 2) ^ 2 * F2 (s ^ 2)
    set Z := (s ^ 2) ^ 3 * F3 (s ^ 2)
    have hj := abs_nonneg (j : ℝ)
    have hjB : 0 ≤ |(j : ℝ)| * B := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, pow_zero, div_one,
        show (j : ℝ) * (2 * s ^ 2 * F1 (s ^ 2)) = 2 * ((j : ℝ) * X) by ring, abs_mul, abs_mul, abs_two]
      have := mul_le_mul_of_nonneg_left b1 hj
      nlinarith
    · have e : (j : ℝ) * (4 * s * F1 (s ^ 2) + 4 * s ^ 3 * F2 (s ^ 2)) = (j : ℝ) * (4 * X + 4 * Y) / s := by
        simp only [X, Y]
        field_simp
        try ring
      rw [Complex.norm_real, Real.norm_eq_abs, e, abs_div, abs_of_pos hs0, zero_add, pow_one]
      refine div_le_div_of_nonneg_right ?_ hs0.le
      rw [abs_mul]
      have h4 : |4 * X + 4 * Y| ≤ 8 * B := by
        have := abs_add_le (4 * X) (4 * Y)
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 4) b1
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 4) b2
        linarith
      have := mul_le_mul_of_nonneg_left h4 hj
      nlinarith
    · have e : (j : ℝ) * (4 * F1 (s ^ 2) + 20 * s ^ 2 * F2 (s ^ 2) + 8 * s ^ 4 * F3 (s ^ 2)) =
          (j : ℝ) * (4 * X + 20 * Y + 8 * Z) / s ^ 2 := by
        simp only [X, Y, Z]
        field_simp
        try ring
      rw [Complex.norm_real, Real.norm_eq_abs, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2),
        zero_add]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [abs_mul]
      have h4 : |4 * X + 20 * Y + 8 * Z| ≤ 32 * B := by
        have h1 := abs_add_le (4 * X + 20 * Y) (8 * Z)
        have h2 := abs_add_le (4 * X) (20 * Y)
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 4) b1
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 20) b2
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 8) b3
        linarith
      have := mul_le_mul_of_nonneg_left h4 hj
      nlinarith

theorem keyPhase_typeTwo (P : ShapeParams) (κ : FieldKey) (h0 : κ.label.1 = 0) (σ : ℝ) (y : Space) :
    keyPhase P κ σ y = Complex.exp ((((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2)) : ℝ) : ℂ) * Complex.I) := by
  simp [keyPhase, labelAzimuth, h0]

theorem farBound_keyPhase (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (h0 : κ.label.1 = 0)
    (σ : ℝ) : FarBound (fun y => keyPhase P κ σ y) 0 := by
  obtain ⟨B, hB0, hF⟩ := radialPhase_derivs hP.phase
  set F := P.radialPhase
  set F1 := deriv F
  set F2 := deriv F1
  set c : ℝ := 2 * Real.pi * (labelTime κ.label : ℝ) * σ
  set j : ℝ := (κ.phaseIndex : ℝ)
  have hsq : ∀ s : ℝ, 1 ≤ s → 0 < s ^ 2 := fun s hs => by positivity
  have hG0 : ∀ s : ℝ, 1 ≤ s → HasDerivAt (fun x : ℝ => F (x ^ 2)) (F1 (s ^ 2) * (2 * s)) s :=
    fun s hs => comp_sq_hasDerivAt (hF _ (hsq s hs)).1
  have hG1 : ∀ s : ℝ, 1 ≤ s → HasDerivAt (fun x : ℝ => F1 (x ^ 2)) (F2 (s ^ 2) * (2 * s)) s :=
    fun s hs => comp_sq_hasDerivAt (hF _ (hsq s hs)).2.1
  set ρ : ℝ → ℂ := fun s => Complex.exp ((((c + j * F (s ^ 2)) : ℝ) : ℂ) * Complex.I) with hρ
  set k : ℝ → ℝ := fun s => j * (2 * s * F1 (s ^ 2)) with hk
  set k1 : ℝ → ℝ := fun s => j * (2 * F1 (s ^ 2) + 4 * s ^ 2 * F2 (s ^ 2)) with hk1
  have hρd : ∀ s : ℝ, 1 ≤ s → HasDerivAt ρ (ρ s * ((k s : ℂ) * Complex.I)) s := by
    intro s hs
    have h1 : HasDerivAt (fun x : ℝ => c + j * F (x ^ 2)) (k s) s := by
      have := ((hG0 s hs).const_mul j).const_add c
      refine this.congr_deriv ?_
      simp only [hk]
      ring
    have h2 := (h1.ofReal_comp.mul_const Complex.I).cexp
    exact h2
  have hkd : ∀ s : ℝ, 1 ≤ s → HasDerivAt k (k1 s) s := by
    intro s hs
    have := ((((hasDerivAt_id s).const_mul 2).mul (hG1 s hs))).const_mul j
    refine this.congr_deriv ?_
    simp only [hk1, id]
    ring
  have h := farBound_radial (ρ := ρ) (ρ1 := fun s => ρ s * ((k s : ℂ) * Complex.I))
    (ρ2 := fun s => ρ s * ((k s : ℂ) * Complex.I) * ((k s : ℂ) * Complex.I) + ρ s * ((k1 s : ℂ) * Complex.I))
    (a := 0) (R0 := 1) (C := 1 + 2 * |j| * B + 4 * (|j| * B) ^ 2 + 6 * |j| * B) le_rfl (by positivity)
    hρd (fun s hs => ?_) (fun s hs => ?_)
  · refine h.congr (R0 := 0) fun y _ => ?_
    rw [keyPhase_typeTwo P κ h0 σ y]
  · exact (hρd s hs).mul ((hkd s hs).ofReal_comp.mul_const Complex.I)
  · have hs0 : 0 < s := by linarith
    obtain ⟨-, -, -, b1, b2, -⟩ := hF (s ^ 2) (hsq s hs)
    have hρn : ‖ρ s‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hj := abs_nonneg j
    have hjB : 0 ≤ |j| * B := by positivity
    have hkb : |k s| ≤ 2 * |j| * B / s := by
      have e : k s = 2 * j * (s ^ 2 * F1 (s ^ 2)) / s := by
        simp only [hk]
        field_simp
      rw [e, abs_div, abs_of_pos hs0, abs_mul, abs_mul, abs_two]
      refine div_le_div_of_nonneg_right ?_ hs0.le
      have := mul_le_mul_of_nonneg_left b1 hj
      nlinarith
    have hk1b : |k1 s| ≤ 6 * |j| * B / s ^ 2 := by
      have e : k1 s = j * (2 * (s ^ 2 * F1 (s ^ 2)) + 4 * ((s ^ 2) ^ 2 * F2 (s ^ 2))) / s ^ 2 := by
        simp only [hk1]
        field_simp
        try ring
      rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2), abs_mul]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h4 : |2 * (s ^ 2 * F1 (s ^ 2)) + 4 * ((s ^ 2) ^ 2 * F2 (s ^ 2))| ≤ 6 * B := by
        have := abs_add_le (2 * (s ^ 2 * F1 (s ^ 2))) (4 * ((s ^ 2) ^ 2 * F2 (s ^ 2)))
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 2) b1
        have := abs_const_mul_le (by norm_num : (0 : ℝ) ≤ 4) b2
        linarith
      have := mul_le_mul_of_nonneg_left h4 hj
      nlinarith
    have hkI : ‖(k s : ℂ) * Complex.I‖ = |k s| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hk1I : ‖(k1 s : ℂ) * Complex.I‖ = |k1 s| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have e1 : ‖ρ s * ((k s : ℂ) * Complex.I) * ((k s : ℂ) * Complex.I)‖ = |k s| * |k s| := by
      rw [norm_mul, norm_mul (ρ s), hρn, one_mul, hkI]
    have e2 : ‖ρ s * ((k1 s : ℂ) * Complex.I)‖ = |k1 s| := by
      rw [norm_mul (ρ s), hρn, one_mul, hk1I]
    have hCp : 0 ≤ 4 * (|j| * B) ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [hρn, pow_zero, div_one]
      nlinarith
    · rw [norm_mul, hρn, one_mul, hkI, zero_add, pow_one]
      refine hkb.trans (div_le_div_of_nonneg_right ?_ hs0.le)
      nlinarith
    · refine (norm_add_le _ _).trans ?_
      rw [e1, e2, zero_add]
      have hsq1 : |k s| * |k s| ≤ 4 * (|j| * B) ^ 2 / s ^ 2 := by
        have h0' : 0 ≤ |k s| := abs_nonneg _
        have := mul_le_mul hkb hkb h0' (by positivity)
        refine this.trans (le_of_eq ?_)
        field_simp
        try ring
      have : |k s| * |k s| + |k1 s| ≤ (4 * (|j| * B) ^ 2 + 6 * |j| * B) / s ^ 2 := by
        rw [add_div]
        linarith
      refine this.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      nlinarith

end Internal

end GivenShape

end CertCell

end Breakdown

import Breakdown.FracCell.GivenAuxDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem turn_zero (m : ℕ) (y : Space) :
    turnStep m y 0 = Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1 := by
  simp [turnStep]

private theorem turn_one (m : ℕ) (y : Space) :
    turnStep m y 1 = Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1 := by
  simp [turnStep]

private theorem turn_two (m : ℕ) (y : Space) : turnStep m y 2 = y 2 := by
  simp [turnStep]

private theorem turn_norm (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, turn_zero, turn_one, turn_two]
  have h := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * h

private theorem turn_angle (m : ℕ) (y : Space) :
    ∃ j : ℤ, angleOf (turnStep m y) = angleOf y + 2 * Real.pi / m + 2 * Real.pi * j ∨
      angleOf (turnStep m y) = angleOf y := by
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = 2 * Real.pi / m := ⟨_, rfl⟩
  have hz : (⟨turnStep m y 0, turnStep m y 1⟩ : ℂ) =
      (⟨y 0, y 1⟩ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, turn_zero, turn_one, hθ] <;> ring
  by_cases h0 : (⟨y 0, y 1⟩ : ℂ) = 0
  · refine ⟨0, Or.inr ?_⟩
    unfold angleOf
    rw [hz, h0, zero_mul]
  · have hw : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im, mul_zero,
        sub_zero, add_zero, mul_one, zero_add] at h1 h2
      have := Real.sin_sq_add_cos_sq θ
      rw [h1, h2] at this
      norm_num at this
    have ha := Complex.arg_mul_coe_angle h0 hw
    have hw' : (Complex.arg ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) : Real.Angle) = θ := by
      have := Complex.arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle)
      rwa [Real.Angle.cos_coe, Real.Angle.sin_coe] at this
    rw [hw', ← hz, ← Real.Angle.coe_add] at ha
    obtain ⟨j, hj⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 ha
    refine ⟨j, Or.inl ?_⟩
    unfold angleOf
    rw [← hθ]
    linarith

private theorem turn_phase (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) (y : Space) :
    modePhase P n β (turnStep P.m y) = modePhase P n β y := by
  have hN := turn_norm P.m y
  have hL : logPhase P (turnStep P.m y) = logPhase P y := by simp [logPhase, hN]
  obtain ⟨j, hj | hj⟩ := turn_angle P.m y
  · unfold modePhase
    rw [hL, hj]
    have hm : (P.m : ℂ) ≠ 0 := by exact_mod_cast hP.m_pos.ne'
    have : Complex.I * ((((n * P.m : ℤ) : ℝ) * (angleOf y + 2 * Real.pi / P.m + 2 * Real.pi * j) +
        n * β * logPhase P y : ℝ) : ℂ) =
        Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y + n * β * logPhase P y : ℝ) : ℂ) +
          ((n + n * P.m * j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · unfold modePhase
    rw [hL, hj]

private def frameCoef (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space) (k : Fin 3) : ℂ :=
  (decayFactor P y : ℂ) * ∑ n ∈ D.modes, modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) k

private theorem fieldOf_frame (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space) :
    fieldOf P D β y = ofComponents (fun i => (frameCoef P D β y 0).re * radialVec y i +
      (frameCoef P D β y 1).re * polarVecQ y i + (frameCoef P D β y 2).re * azimVecQ y i) := by
  have hre : ∀ (a b c : ℂ) (r : ℝ), (a * (b * (c * (r : ℂ)))).re = (a * (b * c)).re * r := by
    intro a b c r
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold fieldOf frameCoef
  congr 1
  funext i
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, Complex.add_re, Complex.re_sum, Finset.sum_mul, hre]

private theorem turn_fieldOf (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ) (y : Space) :
    fieldOf P D β (turnStep P.m y) = turnStep P.m (fieldOf P D β y) := by
  have hN := turn_norm P.m y
  have hH : heightRatio (turnStep P.m y) = heightRatio y := by simp only [heightRatio, turn_two, hN]
  have hT : chartT P (turnStep P.m y) = chartT P y := by simp only [chartT, hN]
  have hD : decayFactor P (turnStep P.m y) = decayFactor P y := by simp only [decayFactor, chartS, hT]
  have hA : ∀ k, frameCoef P D β (turnStep P.m y) k = frameCoef P D β y k := by
    intro k
    simp only [frameCoef, hT, hH, hD, turn_phase P hP]
  rw [fieldOf_frame, fieldOf_frame, hA 0, hA 1, hA 2]
  ext j
  fin_cases j <;>
    simp [ofComponents, turn_zero, turn_one, turn_two, hN, hH, radialVec, polarVecQ, azimVecQ, qOf] <;> ring

private theorem eval_even_neg (S : Spline) (t x : ℝ) : S.eval false t (-x) = S.eval false t x := by
  simp [Spline.eval]

private theorem eval_odd_neg (S : Spline) (t x : ℝ) (hx : x ≠ 0) : S.eval true t (-x) = -S.eval true t x := by
  unfold Spline.eval
  rcases lt_or_gt_of_ne hx with h | h
  · have h' : ¬ (-x < 0) := by linarith
    simp [h, h', abs_neg]
  · have h' : -x < 0 := by linarith
    have h'' : ¬ (x < 0) := by linarith
    simp [h', h'', abs_neg]

private theorem twisted_even (P : ChartParams) (n : ℤ) (β : ℝ) (f : ℝ → ℝ → ℂ) (t x : ℝ)
    (hf : ∀ t', f t' (-x) = f t' x) : twistedScale P n β f t (-x) = twistedScale P n β f t x := by
  unfold twistedScale radialScale
  rw [show (fun t' => f t' (-x)) = fun t' => f t' x from funext hf, hf t]

private theorem twisted_odd (P : ChartParams) (n : ℤ) (β : ℝ) (f : ℝ → ℝ → ℂ) (t x : ℝ)
    (hf : ∀ t', f t' (-x) = -f t' x) : twistedScale P n β f t (-x) = -twistedScale P n β f t x := by
  unfold twistedScale radialScale
  rw [show (fun t' => f t' (-x)) = fun t' => -f t' x from funext hf, hf t, deriv.fun_neg]
  ring

private theorem height_even_of_odd (f : ℝ → ℝ → ℂ) (t x : ℝ) (hx : x ≠ 0)
    (hf : ∀ x', x' ≠ 0 → f t (-x') = -f t x') : heightDeriv f t (-x) = heightDeriv f t x := by
  unfold heightDeriv
  have hev : (fun x' => f t x') =ᶠ[nhds (-x)] (fun x' => -f t (-x')) := by
    filter_upwards [isOpen_ne.mem_nhds (neg_ne_zero.2 hx)] with x' hx'
    rw [hf x' hx', neg_neg]
  rw [hev.deriv_eq, deriv.fun_neg, deriv_comp_neg (f := fun x' => f t x'), neg_neg, neg_neg]

private theorem reducedField_mirror (P : ChartParams) (D : FieldData) (n : ℤ) (β t x : ℝ) (hx : x ≠ 0) :
    reducedField P D n β t (-x) 0 = reducedField P D n β t x 0 ∧
      reducedField P D n β t (-x) 1 = -reducedField P D n β t x 1 ∧
      reducedField P D n β t (-x) 2 = reducedField P D n β t x 2 := by
  by_cases h0 : n = 0
  · subst h0
    have h1 := height_even_of_odd (fun t' x'' => ((1 - x'' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x'')
      t x hx (fun x' hx' => by simp only [eval_odd_neg _ _ _ hx', neg_sq]; ring)
    have h2 := twisted_odd P 0 β (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') t x
      (fun t' => by simp only [eval_odd_neg _ _ _ hx]; ring)
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at h1 h2
    unfold reducedField
    simp only
    refine ⟨?_, ?_, ?_⟩
    · simp [h1]
    · simp [h2, eval_odd_neg _ _ _ hx]
      ring
    · simp [eval_even_neg]
  · have h2 := twisted_even P n β (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x') t x
      (fun t' => by simp only [eval_even_neg, neg_sq])
    have h1 := height_even_of_odd (fun t' x'' => ((1 - x'' ^ 2 : ℝ) : ℂ) *
        (weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x'' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          (D.amp n).polarAmp.eval true t' x'')) t x hx
      (fun x' hx' => by simp only [eval_odd_neg _ _ _ hx', neg_sq]; ring)
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at h1 h2
    unfold reducedField
    simp only [if_neg h0]
    refine ⟨?_, ?_, ?_⟩
    · simp [eval_even_neg]
    · simp [eval_odd_neg _ _ _ hx]
    · simp [h1, h2, eval_even_neg]

private theorem mirror_zero (y : Space) : mirror y 0 = y 0 := by simp [mirror]

private theorem mirror_one (y : Space) : mirror y 1 = y 1 := by simp [mirror]

private theorem mirror_two (y : Space) : mirror y 2 = -y 2 := by simp [mirror]

private theorem mirror_norm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, mirror_zero, mirror_one, mirror_two, neg_sq]

private theorem mirror_fieldOf (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space) (hy : y 2 ≠ 0) :
    fieldOf P D β (mirror y) = mirror (fieldOf P D β y) := by
  have hN := mirror_norm y
  have hy0 : ‖y‖ ≠ 0 := by
    intro h
    rw [norm_eq_zero] at h
    exact hy (by rw [h]; rfl)
  have hx : heightRatio y ≠ 0 := div_ne_zero hy hy0
  have hH : heightRatio (mirror y) = -heightRatio y := by
    simp only [heightRatio, mirror_two, hN, neg_div]
  have hT : chartT P (mirror y) = chartT P y := by simp only [chartT, hN]
  have hD : decayFactor P (mirror y) = decayFactor P y := by simp only [decayFactor, chartS, hT]
  have hAng : angleOf (mirror y) = angleOf y := by simp only [angleOf, mirror_zero, mirror_one]
  have hPh : ∀ n, modePhase P n β (mirror y) = modePhase P n β y := by
    intro n
    simp only [modePhase, hAng, logPhase, hN]
  have hA0 : frameCoef P D β (mirror y) 0 = frameCoef P D β y 0 := by
    simp only [frameCoef, hT, hH, hD, hPh, (reducedField_mirror P D _ β _ _ hx).1]
  have hA1 : frameCoef P D β (mirror y) 1 = -frameCoef P D β y 1 := by
    simp only [frameCoef, hT, hH, hD, hPh, (reducedField_mirror P D _ β _ _ hx).2.1, mul_neg,
      Finset.sum_neg_distrib]
  have hA2 : frameCoef P D β (mirror y) 2 = frameCoef P D β y 2 := by
    simp only [frameCoef, hT, hH, hD, hPh, (reducedField_mirror P D _ β _ _ hx).2.2]
  rw [fieldOf_frame, fieldOf_frame, hA0, hA1, hA2]
  ext j
  fin_cases j <;>
    simp [ofComponents, mirror_zero, mirror_one, mirror_two, hN, hH, radialVec, polarVecQ, azimVecQ, qOf] <;> ring

private theorem ae_height_ne : ∀ᵐ y ∂(volume : Measure Space), y 2 ≠ 0 := by
  let L : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L] at this
  have h0 := Measure.addHaar_submodule (volume : Measure Space) (LinearMap.ker L) hne
  rw [ae_iff]
  convert h0 using 2
  ext y
  simp [L]

theorem fieldOf_class (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ) :
    IsClassField P.m (fieldOf P D β) :=
  ⟨Filter.Eventually.of_forall (turn_fieldOf P hP D β),
    ae_height_ne.mono (fun y hy => mirror_fieldOf P D β y hy)⟩

end GivenFields

end CellCert

end Breakdown

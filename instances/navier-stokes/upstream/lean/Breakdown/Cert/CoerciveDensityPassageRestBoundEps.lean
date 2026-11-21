import Breakdown.Cert.CoerciveDensityPassageRestBound
import Breakdown.Cert.CoerciveSmoothEpsTail

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageRestBound

theorem abs_le_of_nonneg_le {a M : ℝ} (h0 : 0 ≤ a) (h : a ≤ M) : |a| ≤ M := by
  rw [abs_of_nonneg h0]
  exact h

theorem eps_coeff_bounded {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (ha : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ι y,
      m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y ≤ M ∧
      m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|) ≤ M ∧
      m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (1 + ‖y‖) ≤ M ∧
      m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ M ∧
      ∀ σ, ∀ α ∈ m.waves, m.eps ι y * velAmp W α σ y ≤ M ∧ m.eps ι y * gradAmp (gradField W) α σ y ≤ M ∧
        m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖) ≤ M ∧
        m.eps ι y * vortAmp (gradField W) α σ y ≤ M := by
  obtain ⟨D, hD⟩ := hWdec
  obtain ⟨B', hB'0, hB'⟩ := Internal.SmoothEpsTailDeriv.meanField_curl_bounds hWs hWp hD
  have hD0 : 0 ≤ D := by
    have h := hD 0 0 0 (by norm_num)
    have : 0 ≤ D / (1 + ‖(0 : Space)‖) ^ (0 + 1) := (norm_nonneg _).trans h
    simpa using this
  set B := B' + 9 * D with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ y, ‖meanField W y‖ ≤ B ∧ ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ B ∧
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ ≤ B := fun y =>
    ⟨by linarith [SmoothEpsInternal.norm_meanField_le W hD y], by linarith [(hB' y).1],
      by linarith [(hB' y).2]⟩
  obtain ⟨Be, hBe⟩ := ha.epsW_decay
  obtain ⟨Br, hBr⟩ := ha.rate_bounded
  have hE : ∀ ι y, m.eps ι y ≤ epsSup := fun ι y => ha.epsW_le _ _
  have hE0 : ∀ ι y, 0 ≤ m.eps ι y := fun ι y => abs_nonneg _
  have hEs : 0 ≤ epsSup := (hE0 (0, 0) 0).trans (hE (0, 0) 0)
  have hEy : ∀ ι y, ‖y‖ * m.eps ι y ≤ Be := fun ι y => hBe _ _
  have hBe0 : 0 ≤ Be := (mul_nonneg (norm_nonneg (0 : Space)) (hE0 (0, 0) 0)).trans (hEy (0, 0) 0)
  have hBr0 : 0 ≤ Br := (abs_nonneg _).trans (hBr (m.classOf (0, 0)) 0)
  have hEg : ∀ ι y, m.epsGrad ι y ≤ epsGradSup := fun ι y => ha.epsW_grad_le _ _
  have hEg0 : 0 ≤ epsGradSup := (norm_nonneg _).trans (hEg (0, 0) 0)
  set M := (epsSup * B + 1 / 2 * Be + 2 * (Br * Be) + epsGradSup) + epsSup * (1 / 2 * B + Br)
    + B * (epsSup + Be) + epsSup * B + epsSup * (729 * D) with hM
  have q1 : 0 ≤ epsSup * B + 1 / 2 * Be + 2 * (Br * Be) + epsGradSup := by positivity
  have q2 : 0 ≤ epsSup * (1 / 2 * B + Br) := by positivity
  have q3 : 0 ≤ B * (epsSup + Be) := by positivity
  have q4 : 0 ≤ epsSup * B := by positivity
  have q5 : 0 ≤ epsSup * (729 * D) := by positivity
  refine ⟨M, by positivity, fun ι y => ⟨?_, ?_, ?_, ?_, fun σ α _ => ⟨?_, ?_, ?_, ?_⟩⟩⟩
  · have r1 := SmoothEpsInternal.norm_relativeVelocity_le W (m.rate (m.classOf ι)) y
    have p1 : m.eps ι y * ‖meanField W y‖ ≤ epsSup * B := mul_le_mul (hE ι y) (hB y).1 (norm_nonneg _) hEs
    have p2 : |m.rate (m.classOf ι) y| * (‖y‖ * m.eps ι y) ≤ Br * Be :=
      mul_le_mul (hBr _ _) (hEy ι y) (mul_nonneg (norm_nonneg _) (hE0 ι y)) hBr0
    have p3 := hEy ι y
    calc m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y
        ≤ m.eps ι y * (‖meanField W y‖ + 1 / 2 * ‖y‖ + |m.rate (m.classOf ι) y| * (2 * ‖y‖)) + epsGradSup :=
          add_le_add (mul_le_mul_of_nonneg_left r1 (hE0 ι y)) (hEg ι y)
      _ = m.eps ι y * ‖meanField W y‖ + 1 / 2 * (‖y‖ * m.eps ι y)
          + 2 * (|m.rate (m.classOf ι) y| * (‖y‖ * m.eps ι y)) + epsGradSup := by ring
      _ ≤ epsSup * B + 1 / 2 * Be + 2 * (Br * Be) + epsGradSup := by linarith
      _ ≤ M := by linarith
  · have : m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|)
        ≤ epsSup * (1 / 2 * B + Br) :=
      mul_le_mul (hE ι y) (by linarith [(hB y).2.1, hBr (m.classOf ι) y]) (by positivity) hEs
    linarith
  · have : m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (1 + ‖y‖)
        = ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (m.eps ι y + ‖y‖ * m.eps ι y) := by ring
    rw [this]
    have : ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (m.eps ι y + ‖y‖ * m.eps ι y)
        ≤ B * (epsSup + Be) :=
      mul_le_mul (hB y).2.2 (add_le_add (hE ι y) (hEy ι y))
        (add_nonneg (hE0 ι y) (mul_nonneg (norm_nonneg _) (hE0 ι y))) hB0
    linarith
  · have : m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ epsSup * B :=
      mul_le_mul (hE ι y) (hB y).2.1 (norm_nonneg _) hEs
    linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h1 := Internal.SmoothPieceEps.velAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ≤ D := div_le_self hD0 hy1
    have : m.eps ι y * velAmp W α σ y ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) (by linarith) (Real.sqrt_nonneg _) hEs
    linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h1 := Internal.SmoothPieceEps.gradAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ hy1)
    have : m.eps ι y * gradAmp (gradField W) α σ y ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) (by linarith) (Real.sqrt_nonneg _) hEs
    linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have hyp : 0 < 1 + ‖y‖ := by positivity
    have h1 := Internal.SmoothPieceEps.vortGradAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ≤ D := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (le_self_pow₀ hy1 (by norm_num)) hD0
    have h3 : vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖) ≤ 729 * D := by
      have := mul_le_mul_of_nonneg_right h1 hyp.le
      nlinarith [this, h2]
    have : m.eps ι y * (vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)) ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) h3 (mul_nonneg (Real.sqrt_nonneg _) hyp.le) hEs
    calc m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)
        = m.eps ι y * (vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)) := by ring
      _ ≤ M := by linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h1 := Internal.SmoothPieceEps.vortAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ hy1)
    have : m.eps ι y * vortAmp (gradField W) α σ y ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) (by linarith) (Real.sqrt_nonneg _) hEs
    linarith

theorem epsRest_bound {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => modeEpsRest m W v G H ι σ y) v G H := by
  obtain ⟨M, hM0, hM⟩ := eps_coeff_bounded hA hWs hWp hWdec
  have e0 : ∀ ι y, 0 ≤ m.eps ι y := fun ι y => abs_nonneg _
  have hy : ∀ y : Space, 0 < 1 + ‖y‖ := fun y => by positivity
  have b1 := isRestBound_prod isAmp_vortGrad isAmp_vort
    (fun ι _ y => m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y) hM0
    (fun ι σ y => by
      exact abs_le_of_nonneg_le (add_nonneg (mul_nonneg (e0 ι y) (norm_nonneg _)) (norm_nonneg _)) (hM ι y).1) 0 0 v G H
  have b2 := isRestBound_prod isAmp_vort isAmp_vort
    (fun ι _ y => m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|)) hM0
    (fun ι σ y => by
      exact abs_le_of_nonneg_le (mul_nonneg (e0 ι y) (by positivity)) (hM ι y).2.1) 0 0 v G H
  have b3 := isRestBound_prod isAmp_vel isAmp_vort
    (fun ι _ y => m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (1 + ‖y‖)) hM0
    (fun ι σ y => by
      exact abs_le_of_nonneg_le (mul_nonneg (mul_nonneg (e0 ι y) (norm_nonneg _)) (hy y).le) (hM ι y).2.2.1) 0 0 v G H
  have b4 := isRestBound_prod isAmp_grad isAmp_vort
    (fun ι _ y => m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖) hM0
    (fun ι σ y => by
      exact abs_le_of_nonneg_le (mul_nonneg (e0 ι y) (norm_nonneg _)) (hM ι y).2.2.2.1) 0 0 v G H
  have b5 : ∀ α ∈ m.waves, IsRestBound (fun v G H ι σ y =>
      (m.eps ι y * velAmp W α σ y) * (vortGradAmp H (ι - α) σ y * vortAmp G (ι - 0) σ y)
      + ((m.eps ι y * gradAmp (gradField W) α σ y) * (vortAmp G (ι - α) σ y * vortAmp G (ι - 0) σ y)
      + ((m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖))
          * (velAmp v (ι - α) σ y / (1 + ‖y‖) * vortAmp G (ι - 0) σ y)
      + (m.eps ι y * vortAmp (gradField W) α σ y) * (gradAmp G (ι - α) σ y * vortAmp G (ι - 0) σ y)))) v G H := by
    intro α hα
    have c1 := isRestBound_prod isAmp_vortGrad isAmp_vort (fun ι σ y => m.eps ι y * velAmp W α σ y) hM0
      (fun ι σ y => by
        exact abs_le_of_nonneg_le (mul_nonneg (e0 ι y) (Real.sqrt_nonneg _)) ((hM ι y).2.2.2.2 σ α hα).1) α 0 v G H
    have c2 := isRestBound_prod isAmp_vort isAmp_vort (fun ι σ y => m.eps ι y * gradAmp (gradField W) α σ y) hM0
      (fun ι σ y => by
        exact abs_le_of_nonneg_le (mul_nonneg (e0 ι y) (Real.sqrt_nonneg _)) ((hM ι y).2.2.2.2 σ α hα).2.1) α 0 v G H
    have c3 := isRestBound_prod isAmp_vel isAmp_vort
      (fun ι σ y => m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)) hM0
      (fun ι σ y => by
        exact abs_le_of_nonneg_le (mul_nonneg (mul_nonneg (e0 ι y) (Real.sqrt_nonneg _)) (hy y).le) ((hM ι y).2.2.2.2 σ α hα).2.2.1) α 0 v G H
    have c4 := isRestBound_prod isAmp_grad isAmp_vort (fun ι σ y => m.eps ι y * vortAmp (gradField W) α σ y) hM0
      (fun ι σ y => by
        exact abs_le_of_nonneg_le (mul_nonneg (e0 ι y) (Real.sqrt_nonneg _)) ((hM ι y).2.2.2.2 σ α hα).2.2.2) α 0 v G H
    exact c1.add (c2.add (c3.add c4))
  have b6 := isRestBound_finsetSum m.waves b5
  have ball := b1.neg.add (b2.neg.add (b3.neg.add (b4.neg.add b6.neg)))
  have e : (fun (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) ι σ y => modeEpsRest m W v G H ι σ y) =
      fun v G H ι σ y =>
        -((m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y)
          * (vortGradAmp H (ι - 0) σ y * vortAmp G (ι - 0) σ y))
        + (-((m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|))
          * (vortAmp G (ι - 0) σ y * vortAmp G (ι - 0) σ y))
        + (-((m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (1 + ‖y‖))
          * (velAmp v (ι - 0) σ y / (1 + ‖y‖) * vortAmp G (ι - 0) σ y))
        + (-((m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖) * (gradAmp G (ι - 0) σ y * vortAmp G (ι - 0) σ y))
        + -(∑ α ∈ m.waves, ((m.eps ι y * velAmp W α σ y) * (vortGradAmp H (ι - α) σ y * vortAmp G (ι - 0) σ y)
          + ((m.eps ι y * gradAmp (gradField W) α σ y) * (vortAmp G (ι - α) σ y * vortAmp G (ι - 0) σ y)
          + ((m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖))
            * (velAmp v (ι - α) σ y / (1 + ‖y‖) * vortAmp G (ι - 0) σ y)
          + (m.eps ι y * vortAmp (gradField W) α σ y) * (gradAmp G (ι - α) σ y * vortAmp G (ι - 0) σ y)))))))) := by
    funext v G H ι σ y
    have hy0 : (1 + ‖y‖) ≠ 0 := (hy y).ne'
    simp only [sub_zero]
    have key : m.eps ι y * vortAmp G ι σ y * ∑ α ∈ m.waves,
        (velAmp W α σ y * vortGradAmp H (ι - α) σ y + gradAmp (gradField W) α σ y * vortAmp G (ι - α) σ y
          + vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y
          + vortAmp (gradField W) α σ y * gradAmp G (ι - α) σ y)
        = ∑ α ∈ m.waves, ((m.eps ι y * velAmp W α σ y) * (vortGradAmp H (ι - α) σ y * vortAmp G ι σ y)
          + ((m.eps ι y * gradAmp (gradField W) α σ y) * (vortAmp G (ι - α) σ y * vortAmp G ι σ y)
          + ((m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖))
            * (velAmp v (ι - α) σ y / (1 + ‖y‖) * vortAmp G ι σ y)
          + (m.eps ι y * vortAmp (gradField W) α σ y) * (gradAmp G (ι - α) σ y * vortAmp G ι σ y)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      field_simp
      ring
    unfold modeEpsRest
    rw [key]
    field_simp
    ring
  rw [e]
  exact ball

end Internal.DensityPassageRestBound

end Coercive

end Breakdown

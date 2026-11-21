import Breakdown.Cert.CoerciveSmoothPieceDensityBase

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageRestBase

private theorem abs_coef_sq_le {a A x : ℝ} (h : |a| ≤ A) : |a * x ^ 2| ≤ A * x ^ 2 := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg x)

private theorem base_abs_le {cD c cZ hD hZ wv x2 xc xo x1 x0 r Bd Bz K1 Bw : ℝ} (hcD : |cD| ≤ Bd)
    (hcZ : |cZ| ≤ Bz) (hD0 : 0 ≤ hD) (hD1 : hD ≤ K1) (hZ0 : 0 ≤ hZ) (hZr : (1 + r) ^ 2 * hZ ≤ Bz)
    (hr : 0 < 1 + r) (hc : 0 < c) (hw0 : 0 ≤ wv) (hwB : wv ≤ Bw) :
    |(cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) * x1 ^ 2 - hZ * x0 ^ 2|
      ≤ (Bd + c + (1 + Bd) + (1 / 4 + Bz) + (Bz + K1 + c * Bw) + Bz)
        * (x2 ^ 2 + xc ^ 2 + x1 ^ 2 + xo ^ 2 + (x0 / (1 + r)) ^ 2) := by
  have a1 := abs_le.1 hcD
  have a2 := abs_le.1 hcZ
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans hcD
  have hBz : 0 ≤ Bz := (abs_nonneg _).trans hcZ
  have hK1 : 0 ≤ K1 := hD0.trans hD1
  have hcw : c * wv ≤ c * Bw := mul_le_mul_of_nonneg_left hwB hc.le
  have hcw0 : 0 ≤ c * wv := mul_nonneg hc.le hw0
  have t1 : |(cD - c) * x2 ^ 2| ≤ (Bd + c) * x2 ^ 2 := abs_coef_sq_le (abs_le.2 ⟨by linarith, by linarith⟩)
  have t2 : |(1 - cD) * xc ^ 2| ≤ (1 + Bd) * xc ^ 2 := abs_coef_sq_le (abs_le.2 ⟨by linarith, by linarith⟩)
  have t3 : |(1 / 4 - cZ) * xo ^ 2| ≤ (1 / 4 + Bz) * xo ^ 2 := abs_coef_sq_le (abs_le.2 ⟨by linarith, by linarith⟩)
  have t4 : |(cZ - hD - c * wv) * x1 ^ 2| ≤ (Bz + K1 + c * Bw) * x1 ^ 2 :=
    abs_coef_sq_le (abs_le.2 ⟨by linarith, by linarith⟩)
  have e5 : hZ * x0 ^ 2 = ((1 + r) ^ 2 * hZ) * (x0 / (1 + r)) ^ 2 := by
    field_simp
  have t5 : |hZ * x0 ^ 2| ≤ Bz * (x0 / (1 + r)) ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hZ0 (sq_nonneg x0)), e5]
    exact mul_le_mul_of_nonneg_right hZr (sq_nonneg _)
  have tri : |(cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) * x1 ^ 2
      - hZ * x0 ^ 2| ≤ |(cD - c) * x2 ^ 2| + |(1 - cD) * xc ^ 2| + |(1 / 4 - cZ) * xo ^ 2|
        + |(cZ - hD - c * wv) * x1 ^ 2| + |hZ * x0 ^ 2| := by
    have h1 := abs_sub ((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2
      + (cZ - hD - c * wv) * x1 ^ 2) (hZ * x0 ^ 2)
    have h2 := abs_add_le ((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2)
      ((cZ - hD - c * wv) * x1 ^ 2)
    have h3 := abs_add_le ((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2) ((1 / 4 - cZ) * xo ^ 2)
    have h4 := abs_add_le ((cD - c) * x2 ^ 2) ((1 - cD) * xc ^ 2)
    linarith
  set K := Bd + c + (1 + Bd) + (1 / 4 + Bz) + (Bz + K1 + c * Bw) + Bz with hK
  have s2 := sq_nonneg x2
  have sc := sq_nonneg xc
  have s1 := sq_nonneg x1
  have so := sq_nonneg xo
  have s0 := sq_nonneg (x0 / (1 + r))
  have hcB : 0 ≤ c * Bw := hcw0.trans hcw
  have k2 : (Bd + c) * x2 ^ 2 ≤ K * x2 ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s2
  have kc : (1 + Bd) * xc ^ 2 ≤ K * xc ^ 2 := mul_le_mul_of_nonneg_right (by linarith) sc
  have ko : (1 / 4 + Bz) * xo ^ 2 ≤ K * xo ^ 2 := mul_le_mul_of_nonneg_right (by linarith) so
  have k1 : (Bz + K1 + c * Bw) * x1 ^ 2 ≤ K * x1 ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s1
  have k0 : Bz * (x0 / (1 + r)) ^ 2 ≤ K * (x0 / (1 + r)) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s0
  have ex : K * (x2 ^ 2 + xc ^ 2 + x1 ^ 2 + xo ^ 2 + (x0 / (1 + r)) ^ 2)
      = K * x2 ^ 2 + K * xc ^ 2 + K * x1 ^ 2 + K * xo ^ 2 + K * (x0 / (1 + r)) ^ 2 := by ring
  rw [ex]
  linarith

theorem base_pointwise {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (hwb : ∃ B, ∀ y, w y ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space),
      |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)| ≤
        K * (secondDerivAmp H ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortAmp G ι σ y ^ 2
          + (velAmp v ι σ y / (1 + ‖y‖)) ^ 2) := by
  obtain ⟨Bd, hBd⟩ := hm.convD_decay
  obtain ⟨Bz, hBz⟩ := hm.convZ_decay
  obtain ⟨Bw, hBw⟩ := hwb
  obtain ⟨K1, hK10, hK1⟩ := Internal.SmoothPieceDensity.secondDerivNorm_convD_bound_base m P h w W hm
  have hBd0 : 0 ≤ Bd := le_trans (by positivity) (hBd (m.classOf 0) 0 0 (by norm_num))
  have hBz0 : 0 ≤ Bz := le_trans (by positivity) (hBz (m.classOf 0) 0 0 (by norm_num))
  have hBw0 : 0 ≤ Bw := le_trans (hm.weight_pos.le.trans (hm.weight_lower 0)) (hBw 0)
  have hcD : ∀ c y, |m.convD c y| ≤ Bd := fun c y => by
    have := hBd c y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hcZ : ∀ c y, |m.convZ c y| ≤ Bz := fun c y => by
    have := hBz c y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hc := hm.c_pos
  refine ⟨Bd + m.c + (1 + Bd) + (1 / 4 + Bz) + (Bz + K1 + m.c * Bw) + Bz, by positivity, ?_⟩
  intro v G H ι σ y
  unfold modeVals baseDensity
  exact base_abs_le (hcD (m.classOf ι) y) (hcZ (m.classOf ι) y) (norm_nonneg _) (hK1 (m.classOf ι) y)
    (norm_nonneg _) (by simpa [ModeWeights.secondDerivNorm] using hBz (m.classOf ι) y 2 le_rfl)
    (by positivity) hc (hm.weight_pos.le.trans (hm.weight_lower y)) (hBw y)

end Internal.PieceDensityPassageRestBase

end Coercive

end Breakdown

import Breakdown.FracCert.Defs

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace WeakPairingInternal

theorem tendsto_inner_of_dense {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {D : Set E}
    (hD : Dense D) {x : ℕ → E} {x₀ : E} {B : ℝ} (hB : ∀ n, ‖x n‖ ≤ B)
    (h : ∀ z ∈ D, Tendsto (fun n => inner ℝ (x n) z) atTop (nhds (inner ℝ x₀ z))) (z : E) :
    Tendsto (fun n => inner ℝ (x n) z) atTop (nhds (inner ℝ x₀ z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB0 : 0 ≤ B := (norm_nonneg (x 0)).trans (hB 0)
  set K := B + ‖x₀‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨w, hwD, hzw⟩ := hD.exists_dist_lt z (show 0 < ε / (2 * K) by positivity)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (h w hwD) (ε / 2) (by positivity)
  refine ⟨M, fun n hn => ?_⟩
  have h1 := hM n hn
  rw [Real.dist_eq] at h1 ⊢
  rw [dist_eq_norm] at hzw
  have e : inner ℝ (x n) z - inner ℝ x₀ z =
      (inner ℝ (x n) w - inner ℝ x₀ w) + inner ℝ (x n) (z - w) - inner ℝ x₀ (z - w) := by
    rw [inner_sub_right, inner_sub_right]
    ring
  have a1 : |inner ℝ (x n) (z - w)| ≤ B * ‖z - w‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))
  have a2 : |inner ℝ x₀ (z - w)| ≤ ‖x₀‖ * ‖z - w‖ := abs_real_inner_le_norm _ _
  have a3 : (B + ‖x₀‖) * ‖z - w‖ ≤ K * (ε / (2 * K)) := by
    apply mul_le_mul (by linarith) hzw.le (norm_nonneg _) hK0.le
  have a4 : K * (ε / (2 * K)) = ε / 2 := by field_simp
  rw [e]
  calc |inner ℝ (x n) w - inner ℝ x₀ w + inner ℝ (x n) (z - w) - inner ℝ x₀ (z - w)|
      ≤ |inner ℝ (x n) w - inner ℝ x₀ w| + |inner ℝ (x n) (z - w)| + |inner ℝ x₀ (z - w)| := by
        have := abs_sub (inner ℝ (x n) w - inner ℝ x₀ w + inner ℝ (x n) (z - w)) (inner ℝ x₀ (z - w))
        have := abs_add_le (inner ℝ (x n) w - inner ℝ x₀ w) (inner ℝ (x n) (z - w))
        linarith
    _ < ε := by nlinarith

theorem pair_eq_inner {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ y, inner ℝ (f y) (g y) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem norm_toLp_sq {f : Space → Space} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← pair_eq_inner hf hf]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact real_inner_self_eq_norm_sq _

theorem tendsto_pair_of_tests {f : ℕ → Space → Space} {f₀ : Space → Space} {B : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hB : ∀ n, ∫ y, ‖f n y‖ ^ 2 ≤ B) (hf₀ : MemLp f₀ 2 volume)
    (htest : ∀ ψ : Space → Space, IsTestVectorField ψ →
      Tendsto (fun n => ∫ y, inner ℝ (f n y) (ψ y)) atTop (nhds (∫ y, inner ℝ (f₀ y) (ψ y))))
    {ζ : Space → Space} (hζ : MemLp ζ 2 volume) :
    Tendsto (fun n => ∫ y, inner ℝ (f n y) (ζ y)) atTop (nhds (∫ y, inner ℝ (f₀ y) (ζ y))) := by
  have hD := Lp.dense_hasCompactSupport_contDiff (E := Space) (F := Space) (μ := volume) (p := 2)
    ENNReal.ofNat_ne_top
  have hnB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ Real.sqrt B := by
    intro n
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq]
    exact Real.sqrt_le_sqrt (hB n)
  have key := tendsto_inner_of_dense hD hnB (x₀ := hf₀.toLp f₀) ?_ (hζ.toLp ζ)
  · simp only [pair_eq_inner (hf _) hζ, pair_eq_inner hf₀ hζ]
    exact key
  · rintro Z ⟨ψ, hZψ, hψs, hψd⟩
    have hψ : IsTestVectorField ψ := ⟨hψd, hψs⟩
    have hψ2 : MemLp ψ 2 volume := hψd.continuous.memLp_of_hasCompactSupport hψs
    have e : ∀ g : Space → Space, ∀ hg : MemLp g 2 volume,
        inner ℝ (hg.toLp g) Z = ∫ y, inner ℝ (g y) (ψ y) := by
      intro g hg
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp, hZψ] with y h1 h2
      rw [h1, h2]
    simp only [e]
    exact htest ψ hψ

end WeakPairingInternal

end SteadyCert

end Breakdown

import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxAtomSlopeLeaves

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem slope_w_eq {r : ℝ} (hr : 0 < r) :
    r⁻¹ * (1 + r) ^ (-(3 : ℝ)) = (r * (1 + r) ^ 3)⁻¹ := by
  rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_inv]

private theorem slope_ball_norm {y z : Space} (hz : z ∈ Metric.ball y (‖y‖ / 2)) :
    ‖y‖ / 2 < ‖z‖ ∧ ‖z‖ < 3 * ‖y‖ / 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := norm_sub_norm_le y z
  have h2 := norm_sub_norm_le z y
  rw [norm_sub_rev y z] at h1
  constructor <;> linarith

private theorem slope_annulus_compact (a b : ℝ) : IsCompact {z : Space | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} := by
  refine (isCompact_closedBall (0 : Space) b).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.2

private theorem slope_bound_of_slope {g : Space → (Space →L[ℝ] ℂ)} {s : Set Space} {X : ℝ}
    (h : ∀ a ∈ s, ∀ b ∈ s, dist (g a) (g b) ≤ X * dist a b) : LipschitzOnWith (Real.toNNReal X) g s :=
  LipschitzOnWith.of_dist_le_mul fun a ha b hb =>
    (h a ha b hb).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal X) dist_nonneg)

private theorem slope_scaled_norm {r : ℝ} (hr : 0 < r) (a : Space) : ‖r⁻¹ • a‖ = ‖a‖ / r := by
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_eq_div]

private theorem slope_scaled_dist {r : ℝ} (hr : 0 < r) (a b : Space) :
    dist (r⁻¹ • a) (r⁻¹ • b) = r⁻¹ * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]

private theorem slope_prod_dist (s : ℝ) (z w : Space) : dist (s, z) (s, w) = dist z w := by
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]

private theorem slope_in_annulus {r : ℝ} (hr : 0 < r) {a : Space} (h1 : r / 2 < ‖a‖) (h2 : ‖a‖ < 3 * r / 2) :
    r⁻¹ • a ∈ {z : Space | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} := by
  refine ⟨?_, ?_⟩
  · rw [slope_scaled_norm hr, le_div_iff₀ hr]
    linarith
  · rw [slope_scaled_norm hr, div_le_iff₀ hr]
    linarith

private theorem slope_glue {g : Space → (Space →L[ℝ] ℂ)}
    (hmid : LocallyLipschitzOn {y : Space | y ≠ 0} g)
    (hnear : ∃ δ : ℝ, 0 < δ ∧ ∃ V : ℝ × Space → (Space →L[ℝ] ℂ),
      LocallyLipschitzOn (Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}) V ∧
      ∀ s : ℝ, 0 < s → s < δ → ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 → g (s • z) = V (s, z))
    (hfar : ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ × Space → (Space →L[ℝ] ℂ),
      LocallyLipschitzOn (Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}) W ∧
      ∀ s : ℝ, 0 < s → s < δ → ∃ c : ℂ, ‖c‖ ≤ s ^ 3 ∧
        ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 → g (s⁻¹ • z) = c • W (s, z)) :
    ∃ C : ℝ, ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal (C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))))) g
      (Metric.ball y (‖y‖ / 2)) := by
  obtain ⟨δ₁, hδ₁, V, hV, hVg⟩ := hnear
  obtain ⟨δ₂, hδ₂, W, hW, hWg⟩ := hfar
  have hA0 : ∀ z ∈ {z : Space | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2}, z ∈ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2} := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨K₁, hK₁⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_Icc (a := (0 : ℝ)) (b := δ₁ / 2)).prod (slope_annulus_compact (1 / 2) (3 / 2)))
    (hV.mono (fun p hp => Set.mem_prod.2 ⟨⟨(Set.mem_prod.1 hp).1.1, by linarith [(Set.mem_prod.1 hp).1.2]⟩,
      hA0 _ (Set.mem_prod.1 hp).2⟩))
  obtain ⟨K₂, hK₂⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_Icc (a := (0 : ℝ)) (b := δ₂ / 2)).prod (slope_annulus_compact (1 / 2) (3 / 2)))
    (hW.mono (fun p hp => Set.mem_prod.2 ⟨⟨(Set.mem_prod.1 hp).1.1, by linarith [(Set.mem_prod.1 hp).1.2]⟩,
      hA0 _ (Set.mem_prod.1 hp).2⟩))
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = δ₁ / 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max 1 (2 / δ₂) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hR1 : 1 ≤ R := hR ▸ le_max_left _ _
  have hR2 : 2 / δ₂ ≤ R := hR ▸ le_max_right _ _
  obtain ⟨K₃, hK₃⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (slope_annulus_compact (d / 2) (3 * R / 2))
    (hmid.mono (fun z hz h0 => by
      have := hz.1
      rw [h0, norm_zero] at this
      linarith))
  have hK₁0 : (0 : ℝ) ≤ K₁ := K₁.2
  have hK₂0 : (0 : ℝ) ≤ K₂ := K₂.2
  have hK₃0 : (0 : ℝ) ≤ K₃ := K₃.2
  refine ⟨K₁ * (1 + d) ^ 3 + 8 * K₂ + K₃ * (R * (1 + R) ^ 3), fun y hy => ?_⟩
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [slope_w_eq hr]
  have hC1 : (K₁ : ℝ) * (1 + d) ^ 3 ≤ K₁ * (1 + d) ^ 3 + 8 * K₂ + K₃ * (R * (1 + R) ^ 3) := by
    have : 0 ≤ (K₃ : ℝ) * (R * (1 + R) ^ 3) := by positivity
    linarith
  have hC2 : 8 * (K₂ : ℝ) ≤ K₁ * (1 + d) ^ 3 + 8 * K₂ + K₃ * (R * (1 + R) ^ 3) := by
    have : 0 ≤ (K₃ : ℝ) * (R * (1 + R) ^ 3) := by positivity
    have : 0 ≤ (K₁ : ℝ) * (1 + d) ^ 3 := by positivity
    linarith
  have hC3 : (K₃ : ℝ) * (R * (1 + R) ^ 3) ≤ K₁ * (1 + d) ^ 3 + 8 * K₂ + K₃ * (R * (1 + R) ^ 3) := by
    have : 0 ≤ (K₁ : ℝ) * (1 + d) ^ 3 := by positivity
    linarith
  have hpos : 0 < ‖y‖ * (1 + ‖y‖) ^ 3 := by positivity
  apply slope_bound_of_slope
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := slope_ball_norm ha
  obtain ⟨hb1, hb2⟩ := slope_ball_norm hb
  have hzaA := slope_in_annulus hr ha1 ha2
  have hzbA := slope_in_annulus hr hb1 hb2
  by_cases h1 : ‖y‖ ≤ d
  · have hlt : ‖y‖ < δ₁ := by rw [hd] at h1; linarith
    have ga : g a = V (‖y‖, ‖y‖⁻¹ • a) := by
      rw [← hVg _ hr hlt _ (hA0 _ hzaA).1 (hA0 _ hzaA).2, smul_inv_smul₀ hr.ne']
    have gb : g b = V (‖y‖, ‖y‖⁻¹ • b) := by
      rw [← hVg _ hr hlt _ (hA0 _ hzbA).1 (hA0 _ hzbA).2, smul_inv_smul₀ hr.ne']
    have hmemA : (‖y‖, ‖y‖⁻¹ • a) ∈ Set.Icc (0 : ℝ) (δ₁ / 2) ×ˢ {z : Space | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} :=
      Set.mem_prod.2 ⟨⟨hr.le, hd ▸ h1⟩, hzaA⟩
    have hmemB : (‖y‖, ‖y‖⁻¹ • b) ∈ Set.Icc (0 : ℝ) (δ₁ / 2) ×ˢ {z : Space | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} :=
      Set.mem_prod.2 ⟨⟨hr.le, hd ▸ h1⟩, hzbA⟩
    have hdist : dist (g a) (g b) ≤ (K₁ * ‖y‖⁻¹) * dist a b := by
      rw [ga, gb]
      calc dist (V (‖y‖, ‖y‖⁻¹ • a)) (V (‖y‖, ‖y‖⁻¹ • b))
          ≤ K₁ * dist (‖y‖, ‖y‖⁻¹ • a) (‖y‖, ‖y‖⁻¹ • b) := hK₁.dist_le_mul _ hmemA _ hmemB
        _ = (K₁ * ‖y‖⁻¹) * dist a b := by
          rw [slope_prod_dist, slope_scaled_dist hr]
          ring
    refine hdist.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hr hpos]
    calc (K₁ : ℝ) * (‖y‖ * (1 + ‖y‖) ^ 3) ≤ K₁ * (‖y‖ * (1 + d) ^ 3) := by gcongr
      _ = (K₁ * (1 + d) ^ 3) * ‖y‖ := by ring
      _ ≤ _ := by gcongr
  by_cases h2 : R ≤ ‖y‖
  · have hs : 0 < ‖y‖⁻¹ := inv_pos.2 hr
    have hsle : ‖y‖⁻¹ ≤ δ₂ / 2 := by
      rw [inv_le_comm₀ hr (by positivity), inv_div]
      linarith
    have hslt : ‖y‖⁻¹ < δ₂ := by linarith
    obtain ⟨c, hc, hcW⟩ := hWg _ hs hslt
    have ga : g a = c • W (‖y‖⁻¹, ‖y‖⁻¹ • a) := by
      rw [← hcW _ (hA0 _ hzaA).1 (hA0 _ hzaA).2, inv_smul_smul₀ hs.ne']
    have gb : g b = c • W (‖y‖⁻¹, ‖y‖⁻¹ • b) := by
      rw [← hcW _ (hA0 _ hzbA).1 (hA0 _ hzbA).2, inv_smul_smul₀ hs.ne']
    have hmemA : (‖y‖⁻¹, ‖y‖⁻¹ • a) ∈ Set.Icc (0 : ℝ) (δ₂ / 2) ×ˢ {z : Space | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} :=
      Set.mem_prod.2 ⟨⟨hs.le, hsle⟩, hzaA⟩
    have hmemB : (‖y‖⁻¹, ‖y‖⁻¹ • b) ∈ Set.Icc (0 : ℝ) (δ₂ / 2) ×ˢ {z : Space | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} :=
      Set.mem_prod.2 ⟨⟨hs.le, hsle⟩, hzbA⟩
    have hdist : dist (g a) (g b) ≤ (K₂ * (‖y‖⁻¹) ^ 4) * dist a b := by
      rw [ga, gb, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm]
      calc ‖c‖ * dist (W (‖y‖⁻¹, ‖y‖⁻¹ • a)) (W (‖y‖⁻¹, ‖y‖⁻¹ • b))
          ≤ (‖y‖⁻¹) ^ 3 * (K₂ * dist (‖y‖⁻¹, ‖y‖⁻¹ • a) (‖y‖⁻¹, ‖y‖⁻¹ • b)) :=
            mul_le_mul hc (hK₂.dist_le_mul _ hmemA _ hmemB) dist_nonneg (by positivity)
        _ = (K₂ * (‖y‖⁻¹) ^ 4) * dist a b := by
          rw [slope_prod_dist, slope_scaled_dist hr]
          ring
    refine hdist.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    have hy1 : 1 ≤ ‖y‖ := hR1.trans h2
    rw [inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hpos]
    calc (K₂ : ℝ) * (‖y‖ * (1 + ‖y‖) ^ 3) ≤ K₂ * (‖y‖ * (2 * ‖y‖) ^ 3) := by gcongr; linarith
      _ = (8 * K₂) * ‖y‖ ^ 4 := by ring
      _ ≤ _ := by gcongr
  · rw [not_le] at h1 h2
    have hmA : a ∈ {z : Space | d / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * R / 2} := ⟨by linarith, by linarith⟩
    have hmB : b ∈ {z : Space | d / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * R / 2} := ⟨by linarith, by linarith⟩
    refine (hK₃.dist_le_mul _ hmA _ hmB).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    calc (K₃ : ℝ) * (‖y‖ * (1 + ‖y‖) ^ 3) ≤ K₃ * (R * (1 + R) ^ 3) := by gcongr
      _ ≤ _ := hC3


theorem atomScalar_slopeBound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ C : ℝ, ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal (C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ)))))
      (fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) (Metric.ball y (‖y‖ / 2)) :=
  slope_glue (atomScalar_fderiv_locallySlopeBound P hP j a M β S ha hS hM)
    (atomScalar_fderiv_nearScaled P hP j a M β S ha hS hM) (atomScalar_fderiv_farScaled P hP j a M β S ha hS hM)

end GivenFields

end CellCert

end Breakdown

import Breakdown.Uniqueness.FundSolPotential

open scoped ContDiff ENNReal
open MeasureTheory Set Real
open Filter Topology Metric

noncomputable section

namespace Breakdown.FundSol

private lemma fderiv_smulConv {g : Space → ℝ} (hg : Continuous g) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Space → E} (hM : ContDiff ℝ ∞ M)
    (hMc : HasCompactSupport M) :
    fderiv ℝ (fun x => ∫ t, g t • M (x - t)) = fun x => ∫ t, g t • fderiv ℝ M (x - t) := by
  funext x
  have h := hMc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    hg.locallyIntegrable (hM.of_le (by simp)) x
  have e1 : (fun x => ∫ t, g t • M (x - t)) = convolution g M (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y; simp [convolution]
  rw [e1, h.fderiv]
  simp only [convolution]
  congr 1

private lemma norm_iteratedFDeriv_smulConv_le {g : Space → ℝ} (hg : Continuous g) (k : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Space → E), ContDiff ℝ ∞ M →
      HasCompactSupport M → ∀ x,
      ‖iteratedFDeriv ℝ k (fun x => ∫ t, g t • M (x - t)) x‖ ≤
        ∫ t, |g t| * ‖iteratedFDeriv ℝ k M (x - t)‖ := by
  induction k with
  | zero =>
    intro E _ _ M hM hMc x
    simp only [norm_iteratedFDeriv_zero]
    calc ‖∫ t, g t • M (x - t)‖ ≤ ∫ t, ‖g t • M (x - t)‖ := norm_integral_le_integral_norm _
      _ = _ := by congr 1; funext t; rw [norm_smul, Real.norm_eq_abs]
  | succ k ih =>
    intro E _ _ M hM hMc x
    rw [← norm_iteratedFDeriv_fderiv, fderiv_smulConv hg hM hMc]
    have := ih (fderiv ℝ M) (contDiff_infty_iff_fderiv.1 hM).2 (hMc.fderiv (𝕜 := ℝ)) x
    simpa only [norm_iteratedFDeriv_fderiv] using this

private lemma exists_cutoff_kernel (ρ : ℝ) (hρ : 1 < ρ) : ∃ M : Space → ℝ, ContDiff ℝ ∞ M ∧
    HasCompactSupport M ∧ ∀ z : Space, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ ρ → M z = kernel z := by
  let φ₁ : ContDiffBump (0 : Space) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let φ₂ : ContDiffBump (0 : Space) := ⟨ρ, ρ + 1, by linarith, by linarith⟩
  refine ⟨fun z => φ₂ z * ((1 - φ₁ z) * kernel z), ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z = 0
    · subst hz
      have h0 : (fun z => φ₂ z * ((1 - φ₁ z) * kernel z)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        filter_upwards [ball_mem_nhds (0 : Space) (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
        have : φ₁ y = 1 := φ₁.one_of_mem_closedBall (ball_subset_closedBall hy)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq h0
    · have hk : ContDiffAt ℝ ∞ kernel z :=
        contDiffOn_kernel.contDiffAt (isOpen_compl_singleton.mem_nhds hz)
      exact φ₂.contDiff.contDiffAt.mul ((contDiffAt_const.sub φ₁.contDiff.contDiffAt).mul hk)
  · exact φ₂.hasCompactSupport.mul_right
  · intro z h1 h2
    have e1 : φ₁ z = 0 := φ₁.zero_of_le_dist (by show (1 / 2 : ℝ) ≤ dist z 0; rw [dist_zero_right]; exact h1)
    have e2 : φ₂ z = 1 := φ₂.one_of_mem_closedBall (by simpa using h2)
    simp [e1, e2]

private lemma decay_each {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, ∀ x : Space, ‖iteratedFDeriv ℝ k (potential g) x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (k + 1) := by
  obtain ⟨R₀, hR₀⟩ : ∃ R : ℝ, ∀ t, g t ≠ 0 → ‖t‖ ≤ R := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Space)
    exact ⟨R, fun t ht => by simpa using hR (subset_tsupport g ht)⟩
  have hR : ∀ t, g t ≠ 0 → ‖t‖ ≤ max R₀ 1 := fun t ht => (hR₀ t ht).trans (le_max_left _ _)
  have hR1 : 1 ≤ max R₀ 1 := le_max_right _ _
  generalize max R₀ 1 = R at hR hR1
  obtain ⟨Ck, hCk⟩ := norm_iteratedFDeriv_kernel_le k
  have hP := contDiff_potential hg hc
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) (2 * R + 1)).exists_bound_of_continuousOn
    ((hP.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn)
  have hgi : Integrable (fun t => |g t|) := (hg.continuous.integrable_of_hasCompactSupport hc).abs
  have hI : 0 ≤ ∫ t, |g t| := integral_nonneg fun t => abs_nonneg _
  refine ⟨|B| * (2 * R + 2) ^ (k + 1) + |Ck| * 2 ^ (k + 1) * ∫ t, |g t|, fun x => ?_⟩
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have hq : 0 ≤ (1 + ‖x‖)⁻¹ ^ (k + 1) := by positivity
  have hBt : 0 ≤ |B| * (2 * R + 2) ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1) := by positivity
  have hFt : 0 ≤ |Ck| * 2 ^ (k + 1) * (∫ t, |g t|) * (1 + ‖x‖)⁻¹ ^ (k + 1) := by positivity
  by_cases hx : ‖x‖ ≤ 2 * R + 1
  · have h1 := hB x (mem_closedBall_zero_iff.2 hx)
    have h2 : 1 ≤ (2 * R + 2) ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1) := by
      rw [← mul_pow, ← div_eq_mul_inv]
      exact one_le_pow₀ ((one_le_div hpos).2 (by linarith))
    have h3 : |B| ≤ |B| * ((2 * R + 2) ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1)) :=
      le_mul_of_one_le_right (abs_nonneg _) h2
    have h4 := le_abs_self B
    nlinarith
  · rw [not_le] at hx
    obtain ⟨Mf, hMs, hMc, hMk⟩ := exists_cutoff_kernel (‖x‖ + R + 1) (by linarith [norm_nonneg x])
    have hEq : potential g =ᶠ[𝓝 x] fun y => ∫ t, g t • Mf (y - t) := by
      filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
      have hyx : ‖y - x‖ < 1 / 2 := by rwa [mem_ball, dist_eq_norm] at hy
      simp only [potential, convolution, ContinuousLinearMap.lsmul_apply]
      congr 1
      funext t
      by_cases ht : g t = 0
      · simp [ht]
      · have h1 := hR t ht
        have ea : x = (x - y) + (y - t) + t := by abel
        have eb : y - t = (y - x) + x - t := by abel
        have hA := norm_add₃_le (a := x - y) (b := y - t) (c := t)
        rw [← ea] at hA
        have hB' : ‖y - t‖ ≤ ‖y - x‖ + ‖x‖ + ‖t‖ := by
          rw [eb]; exact (norm_sub_le _ _).trans (by linarith [norm_add_le (y - x) x])
        rw [norm_sub_rev] at hA
        rw [hMk (y - t) (by linarith) (by linarith)]
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    refine (norm_iteratedFDeriv_smulConv_le hg.continuous k Mf hMs hMc x).trans ?_
    have hpt : ∀ t, |g t| * ‖iteratedFDeriv ℝ k Mf (x - t)‖ ≤
        |g t| * (|Ck| * 2 ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1)) := by
      intro t
      by_cases ht : g t = 0
      · simp [ht]
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h1 := hR t ht
        have hlow : (1 + ‖x‖) / 2 ≤ ‖x - t‖ := by
          have := norm_sub_norm_le x t; linarith
        have hup : ‖x - t‖ < ‖x‖ + R + 1 := by
          have := norm_sub_le x t; linarith
        have hne : x - t ≠ 0 := by
          intro h; rw [h, norm_zero] at hlow; linarith
        have hloc : Mf =ᶠ[𝓝 (x - t)] kernel := by
          have hopen : IsOpen {z : Space | 1 / 2 < ‖z‖ ∧ ‖z‖ < ‖x‖ + R + 1} :=
            (isOpen_lt continuous_const continuous_norm).inter
              (isOpen_lt continuous_norm continuous_const)
          filter_upwards [hopen.mem_nhds ⟨by linarith, hup⟩] with z hz
          exact hMk z hz.1.le hz.2.le
        rw [(hloc.iteratedFDeriv ℝ k).eq_of_nhds]
        refine (hCk _ hne).trans ?_
        have hinv : ‖x - t‖⁻¹ ≤ 2 * (1 + ‖x‖)⁻¹ := by
          calc ‖x - t‖⁻¹ ≤ ((1 + ‖x‖) / 2)⁻¹ := inv_anti₀ (by positivity) hlow
            _ = 2 * (1 + ‖x‖)⁻¹ := by rw [inv_div, div_eq_mul_inv]
        calc Ck * ‖x - t‖⁻¹ ^ (k + 1) ≤ |Ck| * ‖x - t‖⁻¹ ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ |Ck| * (2 * (1 + ‖x‖)⁻¹) ^ (k + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv _) (abs_nonneg _)
          _ = |Ck| * 2 ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1) := by rw [mul_pow]; ring
    have hint : Integrable (fun t => |g t| * (|Ck| * 2 ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1))) :=
      hgi.mul_const _
    calc ∫ t, |g t| * ‖iteratedFDeriv ℝ k Mf (x - t)‖
        ≤ ∫ t, |g t| * (|Ck| * 2 ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity) hint
            (Eventually.of_forall hpt)
      _ = (∫ t, |g t|) * (|Ck| * 2 ^ (k + 1) * (1 + ‖x‖)⁻¹ ^ (k + 1)) := integral_mul_const _ _
      _ ≤ _ := by nlinarith

theorem potential_decay {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ k ≤ 3, ∀ x : Space,
      ‖iteratedFDeriv ℝ k (potential g) x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (k + 1) := by
  choose C hC using decay_each hg hc
  refine ⟨|C 0| + |C 1| + |C 2| + |C 3|, fun k hk x => ?_⟩
  have hq : 0 ≤ (1 + ‖x‖)⁻¹ ^ (k + 1) := by positivity
  have key : C k ≤ |C 0| + |C 1| + |C 2| + |C 3| := by
    have := abs_nonneg (C 0); have := abs_nonneg (C 1); have := abs_nonneg (C 2)
    have := abs_nonneg (C 3)
    interval_cases k
    · linarith [le_abs_self (C 0)]
    · linarith [le_abs_self (C 1)]
    · linarith [le_abs_self (C 2)]
    · linarith [le_abs_self (C 3)]
  exact (hC k x).trans (mul_le_mul_of_nonneg_right key hq)

end Breakdown.FundSol

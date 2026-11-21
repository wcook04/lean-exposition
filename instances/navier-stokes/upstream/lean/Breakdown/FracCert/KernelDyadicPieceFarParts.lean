import Breakdown.FracCert.KernelDyadicPieceFar
import Breakdown.FracCert.KernelDyadicPiece

open scoped ContDiff
open MeasureTheory Real Metric

noncomputable section

namespace Breakdown.FracInternal.KernelDyadicPieceFarParts

open Breakdown.FracCert Breakdown.FracInternal.KernelDyadicPieceFar
  Breakdown.FracInternal.KernelDyadicPiece

theorem natCast_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

theorem cutoff_exists : ∃ ψ : Space → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ u, ‖u‖ ≤ 1 / 4 → ψ u = 1) ∧
    (∀ u, 1 / 2 ≤ ‖u‖ → ψ u = 0) ∧ (∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) ∧
    (∀ i : ℕ, 0 < i → ∀ u, ‖u‖ < 1 / 4 → iteratedFDeriv ℝ i ψ u = 0) ∧
    ∀ i : ℕ, ∃ B : ℝ, ∀ u, ‖iteratedFDeriv ℝ i ψ u‖ ≤ B := by
  let b : ContDiffBump (0 : Space) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hc : ContDiff ℝ ∞ (b : Space → ℝ) := b.contDiff
  refine ⟨b, hc, fun u hu => ?_, fun u hu => ?_, fun u => ⟨b.nonneg, b.le_one⟩, ?_, fun i => ?_⟩
  · exact b.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hu)
  · exact b.zero_of_le_dist (by rw [dist_zero_right]; exact hu)
  · intro i hi u hu
    have he : (b : Space → ℝ) =ᶠ[nhds u] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hu)] with v hv
      exact b.one_of_mem_closedBall (ball_subset_closedBall (show v ∈ ball (0 : Space) (1 / 4) from hv))
    rw [(he.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hi)]
    rfl
  · have hs : HasCompactSupport (b : Space → ℝ) := b.hasCompactSupport
    exact (hs.iteratedFDeriv i).exists_bound_of_continuous
      (hc.continuous_iteratedFDeriv (by exact_mod_cast le_top))

private theorem exp_identity (l : ℤ) {X : ℝ} (hX : 0 < X) (d β : ℝ) (m n : ℕ) :
    (2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n * X ^ (3 - β) /
        ((2 : ℝ) ^ (l : ℝ) * X) ^ (4 + m + n) =
      (2 : ℝ) ^ ((d - 1 - m) * l) * X ^ (-(1 + β + m + n)) := by
  rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (l : ℝ)) n, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2 : ℝ) ^ (l : ℝ)), ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast X]
  simp only [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hX, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  push_cast
  ring

private theorem ring_supp {σ : Space → ℂ} {θ : Space → ℝ} (hθ : IsRingCutoff θ) :
    ∀ ξ, (θ ξ : ℂ) * σ ξ ≠ 0 → 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4 := by
  intro ξ h
  have hθ0 : θ ξ ≠ 0 := by
    intro h0
    apply h
    simp [h0]
  have := hθ.2.2.1 ξ hθ0
  constructor <;> linarith [this.1, this.2]

theorem inner_est (h1 : PieceKernelStatement) {σ : Space → ℂ} {d β : ℝ} {θ : Space → ℝ}
    (hd : 0 ≤ d) (hβ : 0 < β) (hβ3 : β < 3) (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ)
    {f : Space → ℂ} (hf : IsWeightedSmooth f β) {ψ : Space → ℝ} (hψc : ContDiff ℝ ∞ ψ)
    (hψ0 : ∀ u, 1 / 2 ≤ ‖u‖ → ψ u = 0) (hψr : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) (n : ℕ) :
    ∃ C : ℝ, ∀ (l : ℤ) (x : Space), 2 ≤ ‖x‖ → 1 < (2 : ℝ) ^ (l : ℝ) * ‖x‖ →
      ‖∫ w, (((ψ (‖x‖⁻¹ • w) : ℝ) : ℂ) * f w) • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖ ≤
        C * ((2 : ℝ) ^ ((d - 1 - ⌈d⌉₊) * l) * ‖x‖ ^ (-(1 + β + ⌈d⌉₊ + n))) := by
  set m := ⌈d⌉₊
  set N := 4 + m + n with hN
  obtain ⟨C0, hC0⟩ := h1 N n
  obtain ⟨B, hB⟩ := ring_symbol_bound hσ hθ (N + n + 4)
  have hK := hC0 _ B (ring_symbol_contDiff hσ hθ) (ring_supp hθ) hB
  set K := FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) with hKdef
  have hKc : ContDiff ℝ ∞ K := hK.1
  have hKb : ∀ y, ‖iteratedFDeriv ℝ n K y‖ ≤ C0 * B / (1 + ‖y‖) ^ N := fun y => by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hK.2 y
  have hCB : 0 ≤ C0 * B := by
    have := hK.2 0
    have h0 := norm_nonneg (iteratedFDeriv ℝ n K 0)
    simp only [norm_zero, add_zero, one_pow, one_mul] at this
    linarith
  obtain ⟨Cf, hCf⟩ := hf.2 0
  have hfb : ∀ w, ‖f w‖ ≤ Cf * (1 + ‖w‖) ^ (-β) := by
    intro w
    have h := hCf w
    rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at h
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  have hCf0 : 0 ≤ Cf := by
    have h := hCf 0
    have : 0 ≤ (1 + ‖(0 : Space)‖) ^ (β + ((0 : ℕ) : ℝ)) * ‖iteratedFDeriv ℝ 0 f 0‖ := by positivity
    linarith
  obtain ⟨Q, hQ0, hQ⟩ := near_integral hβ hβ3
  refine ⟨C0 * B * 2 ^ N * Cf * (3 / 2) ^ 4 * Q, fun l x hx hlx => ?_⟩
  set s : ℝ := (2 : ℝ) ^ (l : ℝ) with hs_def
  have hs : 0 < s := by positivity
  set X := ‖x‖ with hX_def
  have hX : 0 < X := by linarith
  set c : ℝ := (2 : ℝ) ^ ((3 + d) * l) with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨hgi, hgle⟩ := hQ X⁻¹ (inv_pos.2 hX) 0
  set K0 := c * s ^ n * (C0 * B * 2 ^ N / (s * X) ^ N) * Cf * (3 / 2) ^ 4 with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have he : dyadicKernel σ θ d l = fun z => (c : ℂ) * K (s • z) := rfl
  have hpt : ∀ w, ‖(((ψ (X⁻¹ • w) : ℝ) : ℂ) * f w) • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖ ≤
      K0 * ((1 + ‖w‖) ^ (-β) * (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ))) := by
    intro w
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hψr _).1]
    by_cases hw : ψ (X⁻¹ • w) = 0
    · rw [hw, zero_mul, zero_mul]
      positivity
    have hw2 : ‖X⁻¹ • w‖ < 1 / 2 := by
      by_contra h
      exact hw (hψ0 _ (not_lt.1 h))
    have hw3 : ‖X⁻¹ • ((0 : Space) - w)‖ < 1 / 2 := by
      rwa [zero_sub, smul_neg, norm_neg]
    have hwX : ‖w‖ < X / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hX).le, inv_mul_lt_iff₀ hX] at hw2
      linarith
    have hxw : X / 2 ≤ ‖x - w‖ := by
      have := norm_sub_norm_le x w
      linarith
    have hkern : ‖iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖ ≤
        c * s ^ n * (C0 * B * 2 ^ N / (s * X) ^ N) := by
      rw [he]
      refine (scaled_deriv_le hKc c hs n (x - w)).trans ?_
      rw [abs_of_pos hc]
      refine mul_le_mul_of_nonneg_left ((hKb _).trans ?_) (by positivity)
      have hpos : 0 < (s * X) ^ N / 2 ^ N := by positivity
      have hle : (s * X) ^ N / 2 ^ N ≤ (1 + ‖s • (x - w)‖) ^ N := by
        rw [← div_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ N
        rw [norm_smul, Real.norm_of_nonneg hs.le]
        have : s * (X / 2) ≤ s * ‖x - w‖ := mul_le_mul_of_nonneg_left hxw hs.le
        linarith
      calc C0 * B / (1 + ‖s • (x - w)‖) ^ N ≤ C0 * B / ((s * X) ^ N / 2 ^ N) :=
            div_le_div_of_nonneg_left hCB hpos hle
        _ = C0 * B * 2 ^ N / (s * X) ^ N := by field_simp
    have hwt : 1 ≤ (3 / 2) ^ 4 * (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ)) := by
      have h32 : ((3 : ℝ) / 2) ^ (-(4 : ℝ)) ≤ (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have hv : ((3 : ℝ) / 2) ^ (-(4 : ℝ)) = 16 / 81 := by
        rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [hv] at h32
      nlinarith
    have hψ1 := (hψr (X⁻¹ • w)).2
    have hf0 := norm_nonneg (f w)
    have hk0 := norm_nonneg (iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w))
    have hwt0 : 0 ≤ (1 + ‖w‖) ^ (-β) := by positivity
    calc ψ (X⁻¹ • w) * ‖f w‖ * ‖iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖
        ≤ 1 * (Cf * (1 + ‖w‖) ^ (-β)) * (c * s ^ n * (C0 * B * 2 ^ N / (s * X) ^ N)) := by
          gcongr
          exact hfb w
      _ ≤ (Cf * (1 + ‖w‖) ^ (-β)) * (c * s ^ n * (C0 * B * 2 ^ N / (s * X) ^ N)) *
            ((3 / 2) ^ 4 * (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ))) := by
          rw [one_mul]
          exact le_mul_of_one_le_right (by positivity) hwt
      _ = K0 * ((1 + ‖w‖) ^ (-β) * (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ))) := by
          rw [hK0]; ring
  calc ‖∫ w, (((ψ (X⁻¹ • w) : ℝ) : ℂ) * f w) • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖
      ≤ ∫ w, K0 * ((1 + ‖w‖) ^ (-β) * (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ))) :=
        norm_integral_le_of_norm_le (hgi.const_mul K0) (Filter.Eventually.of_forall hpt)
    _ = K0 * ∫ w, (1 + ‖w‖) ^ (-β) * (1 + ‖X⁻¹ • ((0 : Space) - w)‖) ^ (-(4 : ℝ)) :=
        integral_const_mul _ _
    _ ≤ K0 * ((X⁻¹) ^ (β - 3) * Q) := mul_le_mul_of_nonneg_left hgle hK00
    _ = C0 * B * 2 ^ N * Cf * (3 / 2) ^ 4 * Q *
          (c * s ^ n * X ^ (3 - β) / (s * X) ^ N) := by
        rw [Real.inv_rpow hX.le, ← Real.rpow_neg hX.le, neg_sub, hK0]
        ring
    _ = C0 * B * 2 ^ N * Cf * (3 / 2) ^ 4 * Q *
          ((2 : ℝ) ^ ((d - 1 - m) * l) * X ^ (-(1 + β + m + n))) := by
        rw [hN, hc_def, hs_def, exp_identity l hX d β m n]

theorem scaled_kernel_decay {K : Space → ℂ} (hK : ContDiff ℝ ∞ K)
    (hKb : ∀ j : ℕ, ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ j K y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ))
    (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun z => (c : ℂ) * K (s • z)) ∧ ∀ j : ℕ, ∃ A : ℝ, ∀ y,
      ‖iteratedFDeriv ℝ j (fun z => (c : ℂ) * K (s • z)) y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ) := by
  refine ⟨contDiff_const.mul (hK.comp (contDiff_const_smul s)), fun j => ?_⟩
  obtain ⟨A, hA⟩ := hKb j
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 0)
    simpa using this
  set t : ℝ := max 1 s⁻¹
  have ht : 0 < t := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨|c| * s ^ j * A * t ^ (4 : ℝ), fun y => ?_⟩
  refine (scaled_deriv_le hK c hs j y).trans ?_
  have hw : (1 + ‖s • y‖) ^ (-4 : ℝ) ≤ t ^ (4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ) := by
    refine rpow_neg_four_le (by positivity) (by positivity) ht ?_
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    have h2t : s⁻¹ ≤ t := le_max_right _ _
    have h1t : 1 ≤ t := le_max_left _ _
    have hy := norm_nonneg y
    have : ‖y‖ ≤ t * (s * ‖y‖) := by
      calc ‖y‖ = s⁻¹ * (s * ‖y‖) := by field_simp
        _ ≤ t * (s * ‖y‖) := mul_le_mul_of_nonneg_right h2t (by positivity)
    nlinarith
  calc |c| * s ^ j * ‖iteratedFDeriv ℝ j K (s • y)‖
      ≤ |c| * s ^ j * (A * (1 + ‖s • y‖) ^ (-4 : ℝ)) := by gcongr; exact hA _
    _ ≤ |c| * s ^ j * (A * (t ^ (4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ))) := by gcongr
    _ = |c| * s ^ j * A * t ^ (4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ) := by ring

theorem dyadic_kernel_decay (h1 : PieceKernelStatement) {σ : Space → ℂ} {d : ℝ}
    {θ : Space → ℝ} (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (l : ℤ) :
    ContDiff ℝ ∞ (dyadicKernel σ θ d l) ∧ ∀ j : ℕ, ∃ A : ℝ, ∀ y,
      ‖iteratedFDeriv ℝ j (dyadicKernel σ θ d l) y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ) := by
  obtain ⟨hK, hKb⟩ := ring_kernel_props h1 hσ hθ
  exact scaled_kernel_decay hK hKb _ (by positivity)

theorem integrable_smul_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopologyEither Space E]
    {g : Space → ℂ} (hg : Continuous g) {B : ℝ} (hgb : ∀ w, ‖g w‖ ≤ B) {k : Space → E}
    (hk : Continuous k) {A : ℝ} (hkb : ∀ y, ‖k y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ)) (x : Space) :
    Integrable (fun w => g w • k (x - w)) := by
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  refine Integrable.mono' ((hw.comp_sub_left x).const_mul (B * A))
    ((hg.smul (hk.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  refine (norm_smul_le _ _).trans ?_
  have h0 : 0 ≤ ‖g w‖ := norm_nonneg _
  calc ‖g w‖ * ‖k (x - w)‖ ≤ B * (A * (1 + ‖x - w‖) ^ (-4 : ℝ)) :=
        mul_le_mul (hgb w) (hkb _) (norm_nonneg _) (h0.trans (hgb w))
    _ = B * A * (1 + ‖x - w‖) ^ (-(4 : ℝ)) := by ring_nf

theorem integrable_decay_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopologyEither Space E]
    {k : Space → ℂ} (hk : Continuous k) {A : ℝ} (hkb : ∀ y, ‖k y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ))
    {g : Space → E} (hg : Continuous g) {B : ℝ} (hgb : ∀ w, ‖g w‖ ≤ B) (x : Space) :
    Integrable (fun z => k z • g (x - z)) := by
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  refine Integrable.mono' (hw.const_mul (A * B))
    ((hk.smul (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  refine (norm_smul_le _ _).trans ?_
  have hA0 : 0 ≤ A * (1 + ‖z‖) ^ (-4 : ℝ) := (norm_nonneg _).trans (hkb z)
  calc ‖k z‖ * ‖g (x - z)‖ ≤ (A * (1 + ‖z‖) ^ (-4 : ℝ)) * B :=
        mul_le_mul (hkb z) (hgb _) (norm_nonneg _) hA0
    _ = A * B * (1 + ‖z‖) ^ (-(4 : ℝ)) := by ring_nf

private def quotSymbol (σ : Space → ℂ) (θ : Space → ℝ) (p : ℕ) (ξ : Space) : ℂ :=
  (θ ξ : ℂ) * σ ξ * (((-(2 * (π : ℂ) * Complex.I)) ^ (2 * p))⁻¹ * (((‖ξ‖ ^ 2) ^ p)⁻¹ : ℝ))

private theorem quot_contDiff {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (p : ℕ) :
    ContDiff ℝ ∞ (quotSymbol σ θ p) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | h0
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : Space) (by norm_num : (0 : ℝ) < 1 / 2)] with η hη
    rw [mem_ball_zero_iff] at hη
    simp [quotSymbol, ring_zero_small hθ hη.le]
  · have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h0)
    have h2 : ContDiffAt ℝ ∞ (fun η : Space => ((‖η‖ ^ 2) ^ p)⁻¹) ξ :=
      (((contDiff_norm_sq ℝ).contDiffAt).pow p).inv (pow_ne_zero _ hn)
    have h3 : ContDiffAt ℝ ∞ (fun η : Space => ((((‖η‖ ^ 2) ^ p)⁻¹ : ℝ) : ℂ)) ξ :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp ξ h2
    exact ((ring_symbol_contDiff hσ hθ).contDiffAt).mul (contDiffAt_const.mul h3)

private theorem quot_supp {σ : Space → ℂ} {θ : Space → ℝ} (hθ : IsRingCutoff θ) (p : ℕ) :
    ∀ ξ, quotSymbol σ θ p ξ ≠ 0 → 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4 := by
  intro ξ h
  have hθ0 : θ ξ ≠ 0 := by
    intro h0
    apply h
    simp [quotSymbol, h0]
  have := hθ.2.2.1 ξ hθ0
  constructor <;> linarith [this.1, this.2]

private theorem quot_hasCompactSupport {σ : Space → ℂ} {θ : Space → ℝ} (hθ : IsRingCutoff θ)
    (p : ℕ) : HasCompactSupport (quotSymbol σ θ p) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 4) (fun ξ hξ => by
    rw [mem_closedBall_zero_iff, not_le] at hξ
    by_contra h
    linarith [(quot_supp hθ p ξ h).2])

private theorem quot_bound {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (p K : ℕ) :
    ∃ B : ℝ, ∀ i ≤ K, ∀ ξ, ‖iteratedFDeriv ℝ i (quotSymbol σ θ p) ξ‖ ≤ B := by
  have hb : ∀ i : ℕ, ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ i (quotSymbol σ θ p) ξ‖ ≤ B := fun i =>
    ((quot_hasCompactSupport hθ p).iteratedFDeriv i).exists_bound_of_continuous
      ((quot_contDiff hσ hθ p).continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose B hB using hb
  refine ⟨∑ i ∈ Finset.range (K + 1), |B i|, fun i hi ξ => ?_⟩
  refine ((hB i ξ).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

private theorem quot_kernel_props (h1 : PieceKernelStatement) {σ : Space → ℂ} {d : ℝ}
    {θ : Space → ℝ} (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (p : ℕ) :
    ContDiff ℝ ∞ (FourierTransform.fourierInv (quotSymbol σ θ p)) ∧
    ∀ j : ℕ, ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ j
      (FourierTransform.fourierInv (quotSymbol σ θ p)) y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ) := by
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨C, hC⟩ := h1 0 0
    obtain ⟨B, hB⟩ := quot_bound hσ hθ p (0 + 0 + 4)
    exact (hC _ B (quot_contDiff hσ hθ p) (quot_supp hθ p) hB).1
  · obtain ⟨C, hC⟩ := h1 4 j
    obtain ⟨B, hB⟩ := quot_bound hσ hθ p (4 + j + 4)
    refine ⟨C * B, fun y => ?_⟩
    have h := (hC _ B (quot_contDiff hσ hθ p) (quot_supp hθ p) hB).2 y
    have hp : 0 < (1 + ‖y‖) ^ 4 := by positivity
    have he : (1 + ‖y‖) ^ (-4 : ℝ) = ((1 + ‖y‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [he, ← div_eq_mul_inv, le_div_iff₀ hp]
    linarith [h]

private theorem sum_prod_coord (p : ℕ) (v : Space) :
    ∑ a : Fin (3 ^ p), ∏ i : Fin (2 * p),
      inner ℝ v (EuclideanSpace.single ((finFunctionFinEquiv.symm a) (finProdFinEquiv.symm i).2) (1 : ℝ)) =
      (‖v‖ ^ 2) ^ p := by
  have hin : ∀ c : Fin 3, inner ℝ v (EuclideanSpace.single c (1 : ℝ)) = v c := by
    intro c
    simp [EuclideanSpace.inner_single_right]
  simp_rw [hin]
  have hprod : ∀ k : Fin p → Fin 3, ∏ i : Fin (2 * p), v (k (finProdFinEquiv.symm i).2) =
      ∏ b : Fin p, v (k b) ^ 2 := by
    intro k
    rw [← finProdFinEquiv.prod_comp]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.prod_prod_type]
    dsimp only
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
  rw [finFunctionFinEquiv.symm.sum_comp (fun k => ∏ i : Fin (2 * p), v (k (finProdFinEquiv.symm i).2))]
  simp_rw [hprod]
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_pow]

private theorem deriv_eq_integral {g : Space → ℂ} (hc : Continuous g) (hcs : HasCompactSupport g)
    (n : ℕ) :
    Integrable (fun v => VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun x => g (-x)) v n) ∧
    iteratedFDeriv ℝ n (FourierTransform.fourierInv g) =
      FourierTransform.fourier (fun v => VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun x => g (-x)) v n) := by
  have hGc : Continuous (fun x => g (-x)) := hc.comp continuous_neg
  have hGs : HasCompactSupport (fun x => g (-x)) := hcs.comp_homeomorph (Homeomorph.neg Space)
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (n : ℕ∞) → Integrable (fun v : Space => ‖v‖ ^ k * ‖g (-v)‖) := by
    intro k _
    exact ((continuous_norm.pow k).mul hGc.norm).integrable_of_hasCompactSupport
      (hGs.norm.mul_left)
  refine ⟨?_, ?_⟩
  · refine (hGc.fourierPowSMulRight (innerSL ℝ) n).integrable_of_hasCompactSupport ?_
    refine hGs.mono (fun v hv => ?_)
    intro h0
    apply hv
    simp only at h0
    ext m
    simp [h0]
  · rw [Real.fourierInv_eq_fourier_comp_neg]
    exact Real.iteratedFDeriv_fourier hint hGc.aestronglyMeasurable (le_refl (n : ℕ∞))

theorem ring_factor (h1 : PieceKernelStatement) {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (p : ℕ) :
    ∃ (r : ℕ) (K : Fin r → Space → ℂ) (v : Fin r → Fin (2 * p) → Space),
      (∀ a, ContDiff ℝ ∞ (K a)) ∧
      (∀ a (j : ℕ), ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (K a) y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ)) ∧
      ∀ z, FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) z =
        ∑ a, iteratedFDeriv ℝ (2 * p) (K a) z (v a) := by
  obtain ⟨hKc, hKb⟩ := quot_kernel_props h1 hσ hθ p
  refine ⟨3 ^ p, fun _ => FourierTransform.fourierInv (quotSymbol σ θ p),
    fun a i => EuclideanSpace.single ((finFunctionFinEquiv.symm a) (finProdFinEquiv.symm i).2) (1 : ℝ),
    fun _ => hKc, fun _ j => hKb j, fun z => ?_⟩
  obtain ⟨hF, hD⟩ := deriv_eq_integral (quot_contDiff hσ hθ p).continuous
    (quot_hasCompactSupport (σ := σ) hθ p) (2 * p)
  have hI := (Real.fourierIntegral_convergent_iff z).2 hF
  simp only [hD]
  rw [Real.fourierInv_eq_fourier_comp_neg]
  simp only [Real.fourier_eq]
  simp only [ContinuousMultilinearMap.integral_apply hI]
  have hIa : ∀ a : Fin (3 ^ p), Integrable (fun w : Space =>
      (Real.fourierChar (-inner ℝ w z) • VectorFourier.fourierPowSMulRight (innerSL ℝ)
        (fun x => quotSymbol σ θ p (-x)) w (2 * p))
        (fun i => EuclideanSpace.single (finFunctionFinEquiv.symm a (finProdFinEquiv.symm i).2) (1 : ℝ))) :=
    fun a => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (2 * p) => Space) ℂ _).integrable_comp hI
  rw [← integral_finsetSum _ (fun a _ => hIa a)]
  congr 1
  funext v
  have hs := sum_prod_coord p v
  simp only [smul_apply, VectorFourier.fourierPowSMulRight_apply,
    Circle.smul_def, smul_eq_mul, Complex.real_smul]
  rw [← Finset.mul_sum]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
  have hs' : ∑ a : Fin (3 ^ p), ∏ i : Fin (2 * p), innerSL ℝ v
      (EuclideanSpace.single (finFunctionFinEquiv.symm a (finProdFinEquiv.symm i).2) (1 : ℝ)) =
      (‖v‖ ^ 2) ^ p := hs
  rw [hs']
  congr 1
  by_cases hq : (θ (-v) : ℂ) * σ (-v) = 0
  · simp [quotSymbol, hq]
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hq
      have : θ 0 = 0 := ring_zero_small hθ (by simp)
      simp [this]
    have hn : (((‖v‖ ^ 2) ^ p : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 hv))
    have hc : ((-(2 * (π : ℂ) * Complex.I)) ^ (2 * p)) ≠ 0 :=
      pow_ne_zero _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
    simp only [quotSymbol, norm_neg, Complex.ofReal_inv]
    field_simp

theorem conv_deriv_right {K F : Space → ℂ} (hK : Continuous K) {A : ℝ}
    (hKb : ∀ y, ‖K y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ)) (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ j : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ B) :
    ContDiff ℝ ∞ (fun x => ∫ z, K z • F (x - z)) ∧ ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun x => ∫ z, K z • F (x - z)) =
        fun x => ∫ z, K z • iteratedFDeriv ℝ n F (x - z) := by
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  have hFc : ∀ j : ℕ, Continuous (iteratedFDeriv ℝ j F) := fun j =>
    hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  choose B hB using hFb
  have hintj : ∀ (j : ℕ) (x : Space), Integrable (fun z => K z • iteratedFDeriv ℝ j F (x - z)) := by
    intro j x
    have : SecondCountableTopologyEither Space
        (ContinuousMultilinearMap ℝ (fun _ : Fin j => Space) ℂ) := ⟨Or.inl inferInstance⟩
    exact integrable_decay_smul hK hKb (hFc j) (hB j) x
  have hd : ∀ (j : ℕ) (x : Space), HasFDerivAt (fun x => ∫ z, K z • iteratedFDeriv ℝ j F (x - z))
      (∫ z, K z • fderiv ℝ (iteratedFDeriv ℝ j F) (x - z)) x := by
    intro j x₀
    have : SecondCountableTopologyEither Space
        (Space →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => Space) ℂ) := ⟨Or.inl inferInstance⟩
    have hc : Continuous (fderiv ℝ (iteratedFDeriv ℝ j F)) := by
      rw [fderiv_iteratedFDeriv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Space) ℂ).continuous.comp
        (hFc (j + 1))
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
      (F' := fun x z => K z • fderiv ℝ (iteratedFDeriv ℝ j F) (x - z))
      (bound := fun z => A * B (j + 1) * (1 + ‖z‖) ^ (-(4 : ℝ))) (ball_mem_nhds x₀ one_pos)
      (Filter.Eventually.of_forall (fun x => (hintj j x).aestronglyMeasurable)) (hintj j x₀) ?_ ?_
      (hw.const_mul _) ?_
    · exact (hK.smul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z x _ => ?_)
      refine (norm_smul_le _ _).trans ?_
      rw [norm_fderiv_iteratedFDeriv]
      have hA0 : 0 ≤ A * (1 + ‖z‖) ^ (-4 : ℝ) := (norm_nonneg _).trans (hKb z)
      calc ‖K z‖ * ‖iteratedFDeriv ℝ (j + 1) F (x - z)‖ ≤ (A * (1 + ‖z‖) ^ (-4 : ℝ)) * B (j + 1) :=
            mul_le_mul (hKb z) (hB _ _) (norm_nonneg _) hA0
        _ = A * B (j + 1) * (1 + ‖z‖) ^ (-(4 : ℝ)) := by ring_nf
    · refine Filter.Eventually.of_forall (fun z x _ => ?_)
      have hdk : HasFDerivAt (iteratedFDeriv ℝ j F) (fderiv ℝ (iteratedFDeriv ℝ j F) (x - z)) (x - z) :=
        ((hF.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) _).hasFDerivAt
      have h2 := (hdk.comp x ((hasFDerivAt_id x).sub_const z)).const_smul (K z)
      simp only [ContinuousLinearMap.comp_id] at h2
      exact h2
  have hform : ∀ n : ℕ, iteratedFDeriv ℝ n (fun x => ∫ z, K z • F (x - z)) =
      fun x => ∫ z, K z • iteratedFDeriv ℝ n F (x - z) := by
    intro n
    induction n with
    | zero =>
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      have : (fun z => K z • iteratedFDeriv ℝ 0 F (x - z)) =
          fun z => (continuousMultilinearCurryFin0 ℝ Space ℂ).symm (K z • F (x - z)) := by
        funext z; ext m; simp
      rw [this, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ Space ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ n ih =>
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd n x).fderiv]
      refine (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm).trans ?_
      congr 1
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun m _ => ?_), hform⟩
  rw [hform m]
  exact fun x => (hd m x).differentiableAt

theorem norm_iter_iter (H : Space → ℂ) (q : ℕ) : ∀ (n : ℕ) (y : Space),
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ q H) y‖ = ‖iteratedFDeriv ℝ (n + q) H y‖ := by
  induction q with
  | zero =>
    intro n y
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.add_zero]
  | succ q ih =>
    intro n y
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih (n + 1) y, show n + 1 + q = n + (q + 1) by omega]

theorem apply_deriv {H : Space → ℂ} (hH : ContDiff ℝ ∞ H) {q : ℕ} (u : Fin q → Space) :
    ContDiff ℝ ∞ (fun w => iteratedFDeriv ℝ q H w u) ∧ ∀ (n : ℕ) (y : Space),
      ‖iteratedFDeriv ℝ n (fun w => iteratedFDeriv ℝ q H w u) y‖ ≤
        ‖iteratedFDeriv ℝ (n + q) H y‖ * ∏ i, ‖u i‖ := by
  set L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Space) ℂ u
  have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ q H) :=
    hH.iteratedFDeriv_right (by exact_mod_cast le_top)
  have he : (fun w => iteratedFDeriv ℝ q H w u) = L ∘ iteratedFDeriv ℝ q H := rfl
  have hL : ‖L‖ ≤ ∏ i, ‖u i‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun M => ?_)
    rw [mul_comm]
    exact M.le_opNorm u
  refine ⟨he ▸ L.contDiff.comp hD, fun n y => ?_⟩
  rw [he]
  refine (L.norm_iteratedFDeriv_comp_left hD.contDiffAt (by exact_mod_cast le_top)).trans ?_
  rw [norm_iter_iter, mul_comm]
  exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)

theorem scale_apply {K : Space → ℂ} (hK : ContDiff ℝ ∞ K) {s : ℝ} (hs : 0 < s) {q : ℕ}
    (y : Space) (u : Fin q → Space) :
    iteratedFDeriv ℝ q K (s • y) u =
      (((s ^ q)⁻¹ : ℝ) : ℂ) * iteratedFDeriv ℝ q (fun z => ((1 : ℝ) : ℂ) * K (s • z)) y u := by
  have he : (fun z => ((1 : ℝ) : ℂ) * K (s • z)) = K ∘ (s • ContinuousLinearMap.id ℝ Space) := by
    funext z
    simp
  rw [he, ContinuousLinearMap.iteratedFDeriv_comp_right _ hK _ (by exact_mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.real_smul]
  have hq : (s : ℂ) ^ q ≠ 0 := pow_ne_zero _ (by exact_mod_cast hs.ne')
  push_cast
  field_simp

theorem outer_core (h1 : PieceKernelStatement) {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℤ) (F : Space → ℂ), ContDiff ℝ ∞ F →
      (∀ j : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ B) →
      ∀ (n : ℕ) (E : ℝ), (∀ y, ‖iteratedFDeriv ℝ (n + 2 * p) F y‖ ≤ E) → ∀ x : Space,
        ‖∫ w, F w • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖ ≤
          C * ((2 : ℝ) ^ ((3 + d) * l) * (((2 : ℝ) ^ (l : ℝ)) ^ (2 * p + 3))⁻¹ * E) := by
  obtain ⟨r, Kt, v, hKtc, hKtb, hfac⟩ := ring_factor h1 hσ hθ p
  have hA : ∀ a, ∃ A : ℝ, ∀ y, ‖Kt a y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ) := fun a => by
    obtain ⟨A, hA⟩ := hKtb a 0
    exact ⟨A, fun y => by simpa [norm_iteratedFDeriv_zero] using hA y⟩
  choose A hA using hA
  set I4 := ∫ y : Space, (1 + ‖y‖) ^ (-(4 : ℝ)) with hI4_def
  have hI4 : 0 ≤ I4 := integral_nonneg (fun _ => by positivity)
  refine ⟨∑ a, |A a| * (∏ i, ‖v a i‖) * I4, by positivity, fun l F hFc hFb n E hE x => ?_⟩
  set s : ℝ := (2 : ℝ) ^ (l : ℝ) with hs_def
  have hs : 0 < s := by positivity
  set c : ℝ := (2 : ℝ) ^ ((3 + d) * l) with hc_def
  have hc : 0 < c := by positivity
  set Ka : Fin r → Space → ℂ := fun a z => ((1 : ℝ) : ℂ) * Kt a (s • z) with hKa_def
  have hKa : ∀ a, ContDiff ℝ ∞ (Ka a) ∧ ∀ j : ℕ, ∃ A' : ℝ, ∀ y,
      ‖iteratedFDeriv ℝ j (Ka a) y‖ ≤ A' * (1 + ‖y‖) ^ (-4 : ℝ) :=
    fun a => scaled_kernel_decay (hKtc a) (hKtb a) 1 hs
  have hKa0 : ∀ a, ∃ A' : ℝ, ∀ y, ‖Ka a y‖ ≤ A' * (1 + ‖y‖) ^ (-4 : ℝ) := fun a => by
    obtain ⟨A', hA'⟩ := (hKa a).2 0
    exact ⟨A', fun y => by simpa [norm_iteratedFDeriv_zero] using hA' y⟩
  choose A0 hA0 using hKa0
  have hKas : ∀ a y, ‖Ka a y‖ ≤ |A a| * (1 + ‖s • y‖) ^ (-4 : ℝ) := by
    intro a y
    simp only [hKa_def, Complex.ofReal_one, one_mul]
    exact (hA a _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hBF' := hFb
  choose BF' hBF' using hBF'
  obtain ⟨BF, hBF⟩ := hFb 0
  have hF0 : ∀ y, ‖F y‖ ≤ BF := fun y => by simpa [norm_iteratedFDeriv_zero] using hBF y
  set Φ : Fin r → Space → ℂ := fun a w => iteratedFDeriv ℝ (2 * p) F w (v a) with hΦ_def
  have hΦ : ∀ a, ContDiff ℝ ∞ (Φ a) := fun a => (apply_deriv hFc (v a)).1
  have hΦb : ∀ a (j : ℕ), ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (Φ a) y‖ ≤ B := by
    intro a j
    obtain ⟨B, hB⟩ := hFb (j + (2 * p))
    exact ⟨B * ∏ i, ‖v a i‖, fun y => ((apply_deriv hFc (v a)).2 j y).trans
      (mul_le_mul_of_nonneg_right (hB y) (by positivity))⟩
  set H : Fin r → Space → ℂ := fun a x' => ∫ z, Ka a z • Φ a (x' - z) with hH_def
  have hH : ∀ a, ContDiff ℝ ∞ (H a) ∧ ∀ n : ℕ, iteratedFDeriv ℝ n (H a) =
      fun x => ∫ z, Ka a z • iteratedFDeriv ℝ n (Φ a) (x - z) :=
    fun a => conv_deriv_right (hKa a).1.continuous (hA0 a) (hΦ a) (hΦb a)
  obtain ⟨hk, hkb⟩ := dyadic_kernel_decay h1 hσ hθ l
  have hG : ∀ x', ∫ w, F w • dyadicKernel σ θ d l (x' - w) =
      ((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) • ∑ a, H a x' := by
    intro x'
    have hker : ∀ y, dyadicKernel σ θ d l y = ((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) *
        ∑ a, iteratedFDeriv ℝ (2 * p) (Ka a) y (v a) := by
      intro y
      show ((c : ℝ) : ℂ) * FourierTransform.fourierInv (fun ξ => (θ ξ : ℂ) * σ ξ) (s • y) = _
      rw [hfac, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [scale_apply (hKtc a) hs, Complex.ofReal_mul, mul_assoc]
    have : SecondCountableTopologyEither Space
        (ContinuousMultilinearMap ℝ (fun _ : Fin (2 * p) => Space) ℂ) := ⟨Or.inl inferInstance⟩
    have hI : ∀ a, Integrable (fun w => F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w)) := by
      intro a
      obtain ⟨A', hA'⟩ := (hKa a).2 (2 * p)
      exact integrable_smul_decay hFc.continuous hF0
        ((hKa a).1.continuous_iteratedFDeriv (natCast_le_infty (2 * p))) hA' x'
    have hIa : ∀ a, Integrable (fun w => F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w) (v a)) :=
      fun a => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (2 * p) => Space) ℂ (v a)).integrable_comp (hI a)
    have hswap : ∀ a, (fun x'' => ∫ w, F w • Ka a (x'' - w)) = fun x'' => ∫ z, Ka a z • F (x'' - z) := by
      intro a
      rw [← kernelConv_eq]
      funext x''
      simp only [kernelConv, smul_eq_mul]
    have hstep : ∀ a, ∫ w, F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w) (v a) = H a x' := by
      intro a
      have hFD : Integrable (fun z => Ka a z • iteratedFDeriv ℝ (2 * p) F (x' - z)) :=
        integrable_decay_smul (hKa a).1.continuous (hA0 a)
          (hFc.continuous_iteratedFDeriv (natCast_le_infty (2 * p))) (hBF' (2 * p)) x'
      calc ∫ w, F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w) (v a)
          = (∫ w, F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w)) (v a) :=
            (ContinuousMultilinearMap.integral_apply (hI a) (v a)).symm
        _ = (iteratedFDeriv ℝ (2 * p) (fun x'' => ∫ w, F w • Ka a (x'' - w)) x') (v a) := by
            rw [congrFun (conv_iteratedFDeriv (hKa a).1 (hKa a).2 hFc.continuous hF0 (2 * p)) x']
        _ = (iteratedFDeriv ℝ (2 * p) (fun x'' => ∫ z, Ka a z • F (x'' - z)) x') (v a) := by
            rw [hswap a]
        _ = (∫ z, Ka a z • iteratedFDeriv ℝ (2 * p) F (x' - z)) (v a) := by
            rw [(conv_deriv_right (hKa a).1.continuous (hA0 a) hFc hFb).2 (2 * p)]
        _ = H a x' := ContinuousMultilinearMap.integral_apply hFD (v a)
    calc ∫ w, F w • dyadicKernel σ θ d l (x' - w)
        = ∫ w, ((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) •
            ∑ a, F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w) (v a) := by
          congr 1
          funext w
          simp only [hker, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
      _ = ((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) •
            ∑ a, ∫ w, F w • iteratedFDeriv ℝ (2 * p) (Ka a) (x' - w) (v a) := by
          rw [integral_smul, integral_finsetSum _ (fun a _ => hIa a)]
      _ = ((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) • ∑ a, H a x' := by
          congr 1
          exact Finset.sum_congr rfl (fun a _ => hstep a)
  have hconv := congrFun (conv_iteratedFDeriv hk hkb hFc.continuous hF0 n) x
  rw [← hconv, show (fun x' => ∫ w, F w • dyadicKernel σ θ d l (x' - w)) =
      fun x' => ((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) • ∑ a, H a x' from funext hG]
  have hsumc : ContDiff ℝ ∞ (fun x' => ∑ a, H a x') :=
    ContDiff.sum (fun a _ => (hH a).1)
  rw [iteratedFDeriv_const_smul_apply' (hsumc.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_fun_sum_apply (fun a _ => (hH a).1.contDiffAt.of_le (by exact_mod_cast le_top))]
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  have hws : Integrable (fun y : Space => (1 + ‖s • y‖) ^ (-(4 : ℝ))) := hw.comp_smul hs.ne'
  have hwsI : ∫ y : Space, (1 + ‖s • y‖) ^ (-(4 : ℝ)) = (s ^ 3)⁻¹ * I4 := by
    rw [Measure.integral_comp_smul (μ := (volume : Measure Space)) (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) s,
      finrank_euclideanSpace_fin, smul_eq_mul, abs_of_pos (by positivity)]
  have hterm : ∀ a, ‖iteratedFDeriv ℝ n (H a) x‖ ≤ |A a| * (∏ i, ‖v a i‖) * E * ((s ^ 3)⁻¹ * I4) := by
    intro a
    rw [(hH a).2 n]
    have hb : ∀ z, ‖Ka a z • iteratedFDeriv ℝ n (Φ a) (x - z)‖ ≤
        (|A a| * (∏ i, ‖v a i‖) * E) * (1 + ‖s • z‖) ^ (-(4 : ℝ)) := by
      intro z
      rw [norm_smul]
      have h2 : ‖iteratedFDeriv ℝ n (Φ a) (x - z)‖ ≤ E * ∏ i, ‖v a i‖ :=
        ((apply_deriv hFc (v a)).2 n (x - z)).trans
          (mul_le_mul_of_nonneg_right (hE _) (by positivity))
      calc ‖Ka a z‖ * ‖iteratedFDeriv ℝ n (Φ a) (x - z)‖
          ≤ (|A a| * (1 + ‖s • z‖) ^ (-4 : ℝ)) * (E * ∏ i, ‖v a i‖) :=
            mul_le_mul (hKas a z) h2 (norm_nonneg _) (by positivity)
        _ = (|A a| * (∏ i, ‖v a i‖) * E) * (1 + ‖s • z‖) ^ (-(4 : ℝ)) := by ring_nf
    refine (norm_integral_le_of_norm_le (hws.const_mul _) (Filter.Eventually.of_forall hb)).trans ?_
    rw [integral_const_mul, hwsI]
  calc ‖((c * (s ^ (2 * p))⁻¹ : ℝ) : ℂ) • ∑ a, iteratedFDeriv ℝ n (H a) x‖
      ≤ (c * (s ^ (2 * p))⁻¹) * ∑ a, ‖iteratedFDeriv ℝ n (H a) x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (c * (s ^ (2 * p))⁻¹) * ∑ a, |A a| * (∏ i, ‖v a i‖) * E * ((s ^ 3)⁻¹ * I4) := by
        gcongr with a
        exact hterm a
    _ = (∑ a, |A a| * (∏ i, ‖v a i‖) * I4) * (c * (s ^ ((2 * p) + 3))⁻¹ * E) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [pow_add, mul_inv]
        ring

private theorem cutoff_identity {X : ℝ} (hX : 0 < X) (β : ℝ) {i j : ℕ} (hij : i ≤ j) :
    (X⁻¹) ^ i / (X / 4) ^ (β + ((j - i : ℕ) : ℝ)) = (4 : ℝ) ^ (β + ((j - i : ℕ) : ℝ)) * X ^ (-(β + j)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (inv_pos.2 hX), Real.log_inv,
    Real.rpow_def_of_pos (by positivity : (0 : ℝ) < X / 4), Real.log_div hX.ne' (by norm_num),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_def_of_pos hX, ← Real.exp_sub,
    ← Real.exp_add]
  congr 1
  rw [Nat.cast_sub hij]
  ring

theorem outer_cutoff {β : ℝ} (hβ : 0 < β) {f : Space → ℂ} (hf : IsWeightedSmooth f β)
    {ψ : Space → ℝ} (hψc : ContDiff ℝ ∞ ψ) (hψ1 : ∀ u, ‖u‖ ≤ 1 / 4 → ψ u = 1)
    (hψd : ∀ i : ℕ, 0 < i → ∀ u, ‖u‖ < 1 / 4 → iteratedFDeriv ℝ i ψ u = 0)
    (hψb : ∀ i : ℕ, ∃ B : ℝ, ∀ u, ‖iteratedFDeriv ℝ i ψ u‖ ≤ B) :
    (∀ x : Space, ContDiff ℝ ∞ (fun w => (((1 - ψ (‖x‖⁻¹ • w)) : ℝ) : ℂ) * f w)) ∧
    ∀ j : ℕ, ∃ C : ℝ, ∀ x : Space, 2 ≤ ‖x‖ → ∀ w,
      ‖iteratedFDeriv ℝ j (fun w => (((1 - ψ (‖x‖⁻¹ • w)) : ℝ) : ℂ) * f w) w‖ ≤
        C * ‖x‖ ^ (-(β + j)) := by
  set K' : Space → ℂ := fun u => (((1 - ψ u) : ℝ) : ℂ) with hK'
  have hgc : ContDiff ℝ ∞ (fun u => 1 - ψ u) := contDiff_const.sub hψc
  have hK'c : ContDiff ℝ ∞ K' := Complex.ofRealCLM.contDiff.comp hgc
  have hK'0 : ∀ (i : ℕ) (u : Space), ‖u‖ < 1 / 4 → iteratedFDeriv ℝ i K' u = 0 := by
    intro i u hu
    have he : K' =ᶠ[nhds u] fun _ => (0 : ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hu)] with v hv
      rw [mem_ball_zero_iff] at hv
      simp [hK', hψ1 v hv.le]
    rw [(he.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_fun_zero]
    rfl
  have hK'b : ∀ i : ℕ, ∃ B : ℝ, ∀ u, ‖iteratedFDeriv ℝ i K' u‖ ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := hψb i
    refine ⟨1 + B, fun u => ?_⟩
    have h1 : ‖iteratedFDeriv ℝ i K' u‖ = ‖iteratedFDeriv ℝ i (fun u => 1 - ψ u) u‖ := by
      have : K' = Complex.ofRealLI ∘ (fun u => 1 - ψ u) := rfl
      rw [this]
      exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hgc.contDiffAt (by exact_mod_cast le_top)
    rw [h1]
    have h2 : iteratedFDeriv ℝ i (fun u => 1 - ψ u) u =
        iteratedFDeriv ℝ i (fun _ => (1 : ℝ)) u - iteratedFDeriv ℝ i ψ u :=
      iteratedFDeriv_sub_apply (f := fun _ => (1 : ℝ)) contDiff_const.contDiffAt
        (hψc.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h2]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hB u))
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [norm_iteratedFDeriv_zero]; simp
    · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hi)]; simp
  refine ⟨fun x => (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.sub (hψc.comp (contDiff_const_smul _)))).mul hf.1, fun j => ?_⟩
  choose Cf hCf using hf.2
  choose B' hB' using hK'b
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |B' i| *
    (|Cf (j - i)| * (4 : ℝ) ^ (β + ((j - i : ℕ) : ℝ))), fun x hx w => ?_⟩
  set X := ‖x‖ with hX_def
  have hX : 0 < X := by linarith
  have hfun : (fun w => (((1 - ψ (X⁻¹ • w)) : ℝ) : ℂ) * f w) =
      fun w => ((((1 : ℝ) : ℂ) * K' (X⁻¹ • w))) * f w := by
    funext w; simp [hK']
  rw [hfun]
  have hχc : ContDiff ℝ ∞ (fun w => (((1 : ℝ) : ℂ) * K' (X⁻¹ • w))) :=
    contDiff_const.mul (hK'c.comp (contDiff_const_smul _))
  refine (norm_iteratedFDeriv_mul_le hχc hf.1 w (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hsc := scaled_deriv_le hK'c 1 (inv_pos.2 hX) i w
  rw [abs_one, one_mul] at hsc
  have hch : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
  have hRHS : 0 ≤ (j.choose i : ℝ) * |B' i| * (|Cf (j - i)| * (4 : ℝ) ^ (β + ((j - i : ℕ) : ℝ))) *
      X ^ (-(β + j)) := by positivity
  by_cases hw : ‖w‖ < X / 4
  · have hw' : ‖X⁻¹ • w‖ < 1 / 4 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hX).le, inv_mul_lt_iff₀ hX]
      linarith
    rw [hK'0 i _ hw', norm_zero, mul_zero] at hsc
    have h0 : ‖iteratedFDeriv ℝ i (fun w => (((1 : ℝ) : ℂ) * K' (X⁻¹ • w))) w‖ = 0 :=
      le_antisymm hsc (norm_nonneg _)
    rw [h0, mul_zero, zero_mul]
    exact hRHS
  · have hw4 : X / 4 ≤ ‖w‖ := not_lt.1 hw
    have hχ : ‖iteratedFDeriv ℝ i (fun w => (((1 : ℝ) : ℂ) * K' (X⁻¹ • w))) w‖ ≤ (X⁻¹) ^ i * |B' i| :=
      hsc.trans (mul_le_mul_of_nonneg_left ((hB' i _).trans (le_abs_self _)) (by positivity))
    have he : (0 : ℝ) < β + ((j - i : ℕ) : ℝ) := by positivity
    have hfd : ‖iteratedFDeriv ℝ (j - i) f w‖ ≤ |Cf (j - i)| / (X / 4) ^ (β + ((j - i : ℕ) : ℝ)) := by
      have h := hCf (j - i) w
      rw [le_div_iff₀ (by positivity)]
      have hmono : (X / 4) ^ (β + ((j - i : ℕ) : ℝ)) ≤ (1 + ‖w‖) ^ (β + ((j - i : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (by linarith) he.le
      have := norm_nonneg (iteratedFDeriv ℝ (j - i) f w)
      calc ‖iteratedFDeriv ℝ (j - i) f w‖ * (X / 4) ^ (β + ((j - i : ℕ) : ℝ))
          ≤ ‖iteratedFDeriv ℝ (j - i) f w‖ * (1 + ‖w‖) ^ (β + ((j - i : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hmono this
        _ = (1 + ‖w‖) ^ (β + ((j - i : ℕ) : ℝ)) * ‖iteratedFDeriv ℝ (j - i) f w‖ := by ring
        _ ≤ Cf (j - i) := h
        _ ≤ |Cf (j - i)| := le_abs_self _
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => (((1 : ℝ) : ℂ) * K' (X⁻¹ • w))) w‖ *
          ‖iteratedFDeriv ℝ (j - i) f w‖
        ≤ (j.choose i : ℝ) * ((X⁻¹) ^ i * |B' i|) *
            (|Cf (j - i)| / (X / 4) ^ (β + ((j - i : ℕ) : ℝ))) := by
          gcongr
      _ = (j.choose i : ℝ) * |B' i| * |Cf (j - i)| *
            ((X⁻¹) ^ i / (X / 4) ^ (β + ((j - i : ℕ) : ℝ))) := by ring
      _ = (j.choose i : ℝ) * |B' i| * (|Cf (j - i)| * (4 : ℝ) ^ (β + ((j - i : ℕ) : ℝ))) *
            X ^ (-(β + j)) := by
          rw [cutoff_identity hX β hij]; ring

private theorem exp_identity_outer (l : ℤ) {X : ℝ} (hX : 0 < X) (d β : ℝ) (m n : ℕ) :
    (2 : ℝ) ^ ((3 + d) * l) * (((2 : ℝ) ^ (l : ℝ)) ^ (2 * (m + 1) + 3))⁻¹ *
        X ^ (-(β + ((n + 2 * (m + 1) : ℕ) : ℝ))) =
      (2 : ℝ) ^ ((d - 1 - m) * l) * X ^ (-(1 + β + m + n)) *
        ((2 : ℝ) ^ (l : ℝ) * X) ^ (-((m : ℝ) + 1)) := by
  rw [Real.mul_rpow (by positivity) hX.le, ← Real.rpow_natCast ((2 : ℝ) ^ (l : ℝ)),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by positivity)]
  simp only [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hX, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem outer_est (h1 : PieceKernelStatement) {σ : Space → ℂ} {d β : ℝ} {θ : Space → ℝ}
    (hd : 0 ≤ d) (hβ : 0 < β) (hβ3 : β < 3) (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ)
    {f : Space → ℂ} (hf : IsWeightedSmooth f β) {ψ : Space → ℝ} (hψc : ContDiff ℝ ∞ ψ)
    (hψ1 : ∀ u, ‖u‖ ≤ 1 / 4 → ψ u = 1) (hψ0 : ∀ u, 1 / 2 ≤ ‖u‖ → ψ u = 0)
    (hψr : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1)
    (hψd : ∀ i : ℕ, 0 < i → ∀ u, ‖u‖ < 1 / 4 → iteratedFDeriv ℝ i ψ u = 0)
    (hψb : ∀ i : ℕ, ∃ B : ℝ, ∀ u, ‖iteratedFDeriv ℝ i ψ u‖ ≤ B) (n : ℕ) :
    ∃ C : ℝ, ∀ (l : ℤ) (x : Space), 2 ≤ ‖x‖ → 1 < (2 : ℝ) ^ (l : ℝ) * ‖x‖ →
      ‖∫ w, (((1 - ψ (‖x‖⁻¹ • w) : ℝ) : ℂ) * f w) •
          iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖ ≤
        C * ((2 : ℝ) ^ ((d - 1 - ⌈d⌉₊) * l) * ‖x‖ ^ (-(1 + β + ⌈d⌉₊ + n))) := by
  set m := ⌈d⌉₊
  obtain ⟨C, hC0, hC⟩ := outer_core h1 hσ hθ (m + 1)
  obtain ⟨hFc, hFb⟩ := outer_cutoff hβ hf hψc hψ1 hψd hψb
  obtain ⟨CF, hCF⟩ := hFb (n + 2 * (m + 1))
  refine ⟨C * CF, fun l x hx hlx => ?_⟩
  have hX : 0 < ‖x‖ := by linarith
  have hbd : ∀ j : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ j
      (fun w => (((1 - ψ (‖x‖⁻¹ • w)) : ℝ) : ℂ) * f w) y‖ ≤ B := fun j => by
    obtain ⟨Cj, hCj⟩ := hFb j
    exact ⟨Cj * ‖x‖ ^ (-(β + j)), hCj x hx⟩
  have h := hC l _ (hFc x) hbd n _ (hCF x hx) x
  have hCF0 : 0 ≤ CF := by
    have h0 := (norm_nonneg _).trans (hCF x hx 0)
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  refine h.trans ?_
  have hid := exp_identity_outer l hX d β m n
  have hle : ((2 : ℝ) ^ (l : ℝ) * ‖x‖) ^ (-((m : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlx.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hT : 0 ≤ (2 : ℝ) ^ ((d - 1 - m) * l) * ‖x‖ ^ (-(1 + β + m + n)) := by positivity
  calc C * ((2 : ℝ) ^ ((3 + d) * l) * (((2 : ℝ) ^ (l : ℝ)) ^ (2 * (m + 1) + 3))⁻¹ *
        (CF * ‖x‖ ^ (-(β + ((n + 2 * (m + 1) : ℕ) : ℝ)))))
      = C * CF * ((2 : ℝ) ^ ((3 + d) * l) * (((2 : ℝ) ^ (l : ℝ)) ^ (2 * (m + 1) + 3))⁻¹ *
        ‖x‖ ^ (-(β + ((n + 2 * (m + 1) : ℕ) : ℝ)))) := by ring
    _ = C * CF * ((2 : ℝ) ^ ((d - 1 - m) * l) * ‖x‖ ^ (-(1 + β + m + n)) *
        ((2 : ℝ) ^ (l : ℝ) * ‖x‖) ^ (-((m : ℝ) + 1))) := by rw [hid]
    _ ≤ C * CF * ((2 : ℝ) ^ ((d - 1 - m) * l) * ‖x‖ ^ (-(1 + β + m + n)) * 1) := by
        gcongr
    _ = C * CF * ((2 : ℝ) ^ ((d - 1 - m) * l) * ‖x‖ ^ (-(1 + β + m + n))) := by ring

end Breakdown.FracInternal.KernelDyadicPieceFarParts

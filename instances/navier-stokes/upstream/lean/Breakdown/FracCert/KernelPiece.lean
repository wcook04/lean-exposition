import Breakdown.FracCert.StKernel
import Mathlib

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown.FracCert

namespace KernelPieceInternal

theorem moment_integrable {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (k n : ℕ) : Integrable (fun v : Space ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) := by
  have hc : Continuous (fun v : Space ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  refine hc.integrable_of_hasCompactSupport ?_
  exact (hs.iteratedFDeriv n).norm.mul_left (f := fun v : Space ↦ ‖v‖ ^ k)

theorem moment_le {f : Space → ℂ} (hsupp : ∀ ξ, f ξ ≠ 0 → ‖ξ‖ ≤ 4) {B : ℝ}
    (q p : ℕ) (hB : ∀ ξ, ‖iteratedFDeriv ℝ q f ξ‖ ≤ B) :
    ∫ v : Space, ‖v‖ ^ p * ‖iteratedFDeriv ℝ q f v‖ ≤
      4 ^ p * volume.real (Metric.closedBall (0 : Space) 4) * B := by
  have hts : tsupport f ⊆ Metric.closedBall (0 : Space) 4 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro ξ hξ
    simpa using hsupp ξ hξ
  have hzero : ∀ v, v ∉ Metric.closedBall (0 : Space) 4 →
      ‖v‖ ^ p * ‖iteratedFDeriv ℝ q f v‖ = 0 := by
    intro v hv
    have : iteratedFDeriv ℝ q f v = 0 := by
      by_contra h
      exact hv (hts (support_iteratedFDeriv_subset q h))
    simp [this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hfin : volume (Metric.closedBall (0 : Space) 4) < ⊤ := measure_closedBall_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (C := 4 ^ p * B) hfin
    (f := fun v : Space ↦ ‖v‖ ^ p * ‖iteratedFDeriv ℝ q f v‖) (by
      intro v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : ‖v‖ ^ p ≤ 4 ^ p := pow_le_pow_left₀ (norm_nonneg _) (by simpa using hv) p
      exact mul_le_mul h1 (hB v) (norm_nonneg _) (by positivity))
  refine (Real.le_norm_self _).trans (hb.trans (le_of_eq (by ring)))

def term (j n : ℕ) : ℝ :=
  (2 * π) ^ j * (2 * (j : ℝ) + 2) ^ n *
    ∑ p ∈ Finset.range (j + 1) ×ˢ Finset.range (n + 1),
      4 ^ p.1 * volume.real (Metric.closedBall (0 : Space) 4)

def const (N j : ℕ) : ℝ := 2 ^ N * (term j 0 + term j N)

theorem term_nonneg (j n : ℕ) : 0 ≤ term j n := by
  unfold term
  have : 0 ≤ volume.real (Metric.closedBall (0 : Space) 4) := measureReal_nonneg
  positivity

theorem transform_bound {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hsupp : ∀ ξ, f ξ ≠ 0 → ‖ξ‖ ≤ 4)
    (N j : ℕ) {B : ℝ} (hB : ∀ i ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ B) (x : Space) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖ ≤ const N j * B := by
  have hs : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 4) ?_
    intro v hv
    by_contra h
    exact hv (by simpa using hsupp v h)
  have hint := moment_integrable hf hs
  have hL : ∀ n ≤ N, ‖x‖ ^ n * ‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖ ≤
      term j n * B := by
    intro n hn
    calc ‖x‖ ^ n * ‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖
        ≤ (2 * π) ^ j * (2 * (j : ℝ) + 2) ^ n *
          ∑ p ∈ Finset.range (j + 1) ×ˢ Finset.range (n + 1),
            ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ :=
          Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤) hf
            (fun k n _ _ => hint k n) le_top le_top x
      _ ≤ (2 * π) ^ j * (2 * (j : ℝ) + 2) ^ n *
          ∑ p ∈ Finset.range (j + 1) ×ˢ Finset.range (n + 1),
            4 ^ p.1 * volume.real (Metric.closedBall (0 : Space) 4) * B := by
          gcongr with p hp
          have hp2 : p.2 < n + 1 := Finset.mem_range.1 (Finset.mem_product.1 hp).2
          exact moment_le hsupp p.2 p.1 (hB p.2 (by omega))
      _ = term j n * B := by
          simp only [term, ← Finset.sum_mul]
          ring
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hT := norm_nonneg (iteratedFDeriv ℝ j (FourierTransform.fourier f) x)
  have h0 := hL 0 (Nat.zero_le _)
  have hN := hL N le_rfl
  simp only [pow_zero, one_mul] at h0
  have key : (1 + ‖x‖) ^ N ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by
    have hx := norm_nonneg x
    rcases le_total ‖x‖ 1 with h | h
    · calc (1 + ‖x‖) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx N])
    · calc (1 + ‖x‖) ^ N ≤ (2 * ‖x‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * ‖x‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by gcongr; linarith
  calc (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖
      ≤ 2 ^ N * (1 + ‖x‖ ^ N) * ‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖ :=
        mul_le_mul_of_nonneg_right key hT
    _ = 2 ^ N * (‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖ +
          ‖x‖ ^ N * ‖iteratedFDeriv ℝ j (FourierTransform.fourier f) x‖) := by ring
    _ ≤ 2 ^ N * (term j 0 * B + term j N * B) := by gcongr
    _ = const N j * B := by simp only [const]; ring

end KernelPieceInternal

open KernelPieceInternal in
theorem pieceKernel : PieceKernelStatement := by
  intro N j
  refine ⟨const N j, fun m B hm hsupp hB => ?_⟩
  have hinv : FourierTransform.fourierInv m =
      FourierTransform.fourier (fun ξ : Space ↦ m (-ξ)) :=
    Real.fourierInv_eq_fourier_comp_neg m
  have hg : ContDiff ℝ ∞ (fun ξ : Space ↦ m (-ξ)) := hm.comp contDiff_neg
  have hgsupp : ∀ ξ : Space, m (-ξ) ≠ 0 → ‖ξ‖ ≤ 4 := by
    intro ξ h
    simpa using (hsupp (-ξ) h).2
  have hgs : HasCompactSupport (fun ξ : Space ↦ m (-ξ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 4) ?_
    intro v hv
    by_contra h
    exact hv (by simpa using hgsupp v h)
  have hgB : ∀ i ≤ N, ∀ ξ : Space, ‖iteratedFDeriv ℝ i (fun ξ : Space ↦ m (-ξ)) ξ‖ ≤ B := by
    intro i hi ξ
    have := (LinearIsometryEquiv.neg ℝ (E := Space)).norm_iteratedFDeriv_comp_right m ξ i
    have e : (m ∘ (LinearIsometryEquiv.neg ℝ (E := Space))) = fun ξ : Space ↦ m (-ξ) := rfl
    rw [e] at this
    rw [this]
    exact hB i (by omega) _
  refine ⟨?_, fun x => ?_⟩
  · rw [hinv]
    refine Real.contDiff_fourier (N := ⊤) (fun n _ => ?_)
    simpa using moment_integrable hg hgs n 0
  · rw [hinv]
    exact transform_bound hg hgsupp N j hgB x

end Breakdown.FracCert

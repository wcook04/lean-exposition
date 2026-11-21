import Breakdown.FracCert.KernelDyadicPieceFar

open scoped ContDiff
open MeasureTheory Real Metric

noncomputable section

namespace Breakdown.FracInternal.KernelDyadicPiece

open Breakdown.FracCert Breakdown.FracInternal.KernelDyadicPieceFar


theorem kernelConv_eq (k f : Space → ℂ) :
    kernelConv k f = fun x => ∫ w, f w • k (x - w) := by
  funext x
  refine (integral_sub_left_eq_self (fun z => k z * f (x - z)) volume x).symm.trans ?_
  congr 1
  funext w
  simp [sub_sub_cancel, mul_comm]

theorem near_bound (h1 : PieceKernelStatement) {σ : Space → ℂ} {d β : ℝ} {θ : Space → ℝ}
    (hβ : 0 < β) (hβ3 : β < 3) (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ)
    {f : Space → ℂ} (hf : IsWeightedSmooth f β) (n : ℕ) :
    ∃ C : ℝ, ∀ (l : ℤ) (x : Space),
      ‖iteratedFDeriv ℝ n (kernelConv (dyadicKernel σ θ d l) f) x‖ ≤
        C * (2 : ℝ) ^ ((d + n + β) * l) := by
  obtain ⟨hK, hKb⟩ := ring_kernel_props h1 hσ hθ
  obtain ⟨A, hA⟩ := hKb n
  obtain ⟨Q, hQ0, hQ⟩ := near_integral hβ hβ3
  obtain ⟨Cf, hCf⟩ := hf.2 0
  have hfb : ∀ y, ‖f y‖ ≤ Cf * (1 + ‖y‖) ^ (-β) := by
    intro y
    have h := hCf y
    rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at h
    have hp : 0 < (1 + ‖y‖) ^ β := by positivity
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hp]
    linarith
  have hCf0 : 0 ≤ Cf := by
    have := hCf 0
    have h0 : 0 ≤ (1 + ‖(0 : Space)‖) ^ (β + ((0 : ℕ) : ℝ)) *
        ‖iteratedFDeriv ℝ 0 f 0‖ := by positivity
    linarith
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 0)
    simpa using this
  have hfb' : ∀ y, ‖f y‖ ≤ Cf := by
    intro y
    refine (hfb y).trans ?_
    have : (1 + ‖y‖) ^ (-β) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)
    nlinarith
  refine ⟨Cf * A * Q, fun l x => ?_⟩
  have hs : 0 < (2 : ℝ) ^ (l : ℝ) := by positivity
  have hc : 0 < (2 : ℝ) ^ ((3 + d) * l) := by positivity
  have hk_eq : dyadicKernel σ θ d l = fun z => (((2 : ℝ) ^ ((3 + d) * l) : ℝ) : ℂ) *
      FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) (((2 : ℝ) ^ (l : ℝ)) • z) := rfl
  have hkc : ContDiff ℝ ∞ (fun z => (((2 : ℝ) ^ ((3 + d) * l) : ℝ) : ℂ) *
      FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) (((2 : ℝ) ^ (l : ℝ)) • z)) :=
    contDiff_const.mul (hK.comp (contDiff_id.const_smul _))
  have hkb : ∀ j : ℕ, ∃ A' : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (fun z => (((2 : ℝ) ^ ((3 + d) * l) : ℝ) : ℂ) *
      FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) (((2 : ℝ) ^ (l : ℝ)) • z)) y‖ ≤
        A' * (1 + ‖y‖) ^ (-4 : ℝ) := by
    intro j
    obtain ⟨Aj, hAj⟩ := hKb j
    have hAj0 : 0 ≤ Aj := by
      have := (norm_nonneg _).trans (hAj 0)
      simpa using this
    refine ⟨|(2 : ℝ) ^ ((3 + d) * l)| * ((2 : ℝ) ^ (l : ℝ)) ^ j * Aj *
      (1 + 1 / (2 : ℝ) ^ (l : ℝ)) ^ (4 : ℝ), fun y => ?_⟩
    have hsh : (1 + ‖((2 : ℝ) ^ (l : ℝ)) • y‖) ^ (-4 : ℝ) ≤
        (1 + 1 / (2 : ℝ) ^ (l : ℝ)) ^ (4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ) := by
      refine rpow_neg_four_le (by positivity) (by positivity) (by positivity) ?_
      rw [norm_smul, Real.norm_of_nonneg hs.le]
      have he : (1 + 1 / (2 : ℝ) ^ (l : ℝ)) * (1 + (2 : ℝ) ^ (l : ℝ) * ‖y‖) =
          1 + ‖y‖ + (2 : ℝ) ^ (l : ℝ) * ‖y‖ + 1 / (2 : ℝ) ^ (l : ℝ) := by
        field_simp
        ring
      rw [he]
      have : 0 ≤ (2 : ℝ) ^ (l : ℝ) * ‖y‖ := by positivity
      have : 0 ≤ 1 / (2 : ℝ) ^ (l : ℝ) := by positivity
      linarith
    calc _ ≤ |(2 : ℝ) ^ ((3 + d) * l)| * ((2 : ℝ) ^ (l : ℝ)) ^ j *
          ‖iteratedFDeriv ℝ j (FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ))
            (((2 : ℝ) ^ (l : ℝ)) • y)‖ := scaled_deriv_le hK _ hs j y
      _ ≤ |(2 : ℝ) ^ ((3 + d) * l)| * ((2 : ℝ) ^ (l : ℝ)) ^ j *
          (Aj * ((1 + 1 / (2 : ℝ) ^ (l : ℝ)) ^ (4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ((hAj _).trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hsh hAj0
      _ = _ := by ring
  rw [hk_eq, kernelConv_eq, conv_iteratedFDeriv hkc hkb hf.1.continuous hfb' n]
  obtain ⟨hgi, hgle⟩ := hQ _ hs x
  have step : ‖∫ w, f w • iteratedFDeriv ℝ n (fun z => (((2 : ℝ) ^ ((3 + d) * l) : ℝ) : ℂ) *
      FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) (((2 : ℝ) ^ (l : ℝ)) • z)) (x - w)‖ ≤
      ∫ w, (Cf * (2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n * A) *
        ((1 + ‖w‖) ^ (-β) * (1 + ‖((2 : ℝ) ^ (l : ℝ)) • (x - w)‖) ^ (-(4 : ℝ))) := by
    refine norm_integral_le_of_norm_le (hgi.const_mul _) (Filter.Eventually.of_forall (fun w => ?_))
    refine (norm_smul_le _ _).trans ?_
    have h2 := scaled_deriv_le hK ((2 : ℝ) ^ ((3 + d) * l)) hs n (x - w)
    rw [abs_of_pos hc] at h2
    have h3 := hA (((2 : ℝ) ^ (l : ℝ)) • (x - w))
    have h4 : ‖iteratedFDeriv ℝ n (fun z => (((2 : ℝ) ^ ((3 + d) * l) : ℝ) : ℂ) *
      FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ) (((2 : ℝ) ^ (l : ℝ)) • z)) (x - w)‖ ≤
        (2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n *
          (A * (1 + ‖((2 : ℝ) ^ (l : ℝ)) • (x - w)‖) ^ (-(4 : ℝ))) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    have h5 := hfb w
    have hb0 : 0 ≤ (1 + ‖w‖) ^ (-β) := by positivity
    calc ‖f w‖ * _ ≤ (Cf * (1 + ‖w‖) ^ (-β)) * ((2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n *
          (A * (1 + ‖((2 : ℝ) ^ (l : ℝ)) • (x - w)‖) ^ (-(4 : ℝ)))) :=
        mul_le_mul h5 h4 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [integral_const_mul] at step
  have hexp : (2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n * ((2 : ℝ) ^ (l : ℝ)) ^ (β - 3) =
      (2 : ℝ) ^ ((d + n + β) * l) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hK0 : 0 ≤ Cf * (2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n * A := by positivity
  calc _ ≤ _ := step
    _ ≤ (Cf * (2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n * A) *
        (((2 : ℝ) ^ (l : ℝ)) ^ (β - 3) * Q) := mul_le_mul_of_nonneg_left hgle hK0
    _ = Cf * A * Q * ((2 : ℝ) ^ ((3 + d) * l) * ((2 : ℝ) ^ (l : ℝ)) ^ n *
        ((2 : ℝ) ^ (l : ℝ)) ^ (β - 3)) := by ring
    _ = _ := by rw [hexp]

end Breakdown.FracInternal.KernelDyadicPiece

namespace Breakdown.FracCert

open Breakdown.FracInternal.KernelDyadicPiece

theorem dyadicPieceBound_of_far (h1 : PieceKernelStatement) (h2 : FarPieceBoundStatement) :
    DyadicPieceBoundStatement := by
  intro σ d β θ hd hβ hβ3 hσ hθ f hf n
  obtain ⟨C1, hC1⟩ := near_bound h1 hβ hβ3 hσ hθ hf n
  obtain ⟨C2, hC2⟩ := h2 σ d β θ hd hβ hβ3 hσ hθ f hf n
  refine ⟨|C1| + |C2|, fun l x hx => ?_⟩
  have hC1' : C1 ≤ |C1| + |C2| := by linarith [le_abs_self C1, abs_nonneg C2]
  have hC2' : C2 ≤ |C1| + |C2| := by linarith [le_abs_self C2, abs_nonneg C1]
  have hCp : 0 ≤ |C1| + |C2| := by positivity
  split_ifs with hnear
  · exact (hC1 l x).trans (mul_le_mul_of_nonneg_right hC1' (by positivity))
  · have h := hC2 l x hx (lt_of_not_ge hnear)
    have ha : 0 ≤ (2 : ℝ) ^ ((d - 2 * (⌈d⌉₊ + 1)) * l) * ‖x‖ ^ (-(β + n + 2 * (⌈d⌉₊ + 1))) := by
      positivity
    have hb : 0 ≤ (2 : ℝ) ^ ((d - 1 - ⌈d⌉₊) * l) * ‖x‖ ^ (-(1 + β + ⌈d⌉₊ + n)) := by positivity
    refine h.trans ((mul_le_mul_of_nonneg_right hC2' hb).trans ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) hCp

end Breakdown.FracCert

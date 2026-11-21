import Breakdown.FracCert.KernelDyadicPieceFarParts

open scoped ContDiff
open MeasureTheory Real Metric

noncomputable section

namespace Breakdown.FracCert

open Breakdown.FracInternal.KernelDyadicPieceFar Breakdown.FracInternal.KernelDyadicPieceFarParts
  Breakdown.FracInternal.KernelDyadicPiece

theorem farPieceBound (h1 : PieceKernelStatement) : FarPieceBoundStatement := by
  intro σ d β θ hd hβ hβ3 hσ hθ f hf n
  obtain ⟨ψ, hψc, hψ1, hψ0, hψr, hψd, hψb⟩ := cutoff_exists
  obtain ⟨C1, hC1⟩ := inner_est h1 hd hβ hβ3 hσ hθ hf hψc hψ0 hψr n
  obtain ⟨C2, hC2⟩ := outer_est h1 hd hβ hβ3 hσ hθ hf hψc hψ1 hψ0 hψr hψd hψb n
  refine ⟨C1 + C2, fun l x hx hlx => ?_⟩
  obtain ⟨hk, hkb⟩ := dyadic_kernel_decay h1 hσ hθ l
  obtain ⟨Cf, hCf⟩ := hf.2 0
  have hfb : ∀ y, ‖f y‖ ≤ Cf := by
    intro y
    have h := hCf y
    rw [norm_iteratedFDeriv_zero] at h
    have h1y : 1 ≤ (1 + ‖y‖) ^ (β + ((0 : ℕ) : ℝ)) :=
      Real.one_le_rpow (by linarith [norm_nonneg y]) (by simp; linarith)
    nlinarith [norm_nonneg (f y)]
  have hfc : Continuous f := hf.1.continuous
  rw [kernelConv_eq, conv_iteratedFDeriv hk hkb hfc hfb n]
  obtain ⟨A, hA⟩ := hkb n
  have hkc : Continuous (iteratedFDeriv ℝ n (dyadicKernel σ θ d l)) :=
    hk.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have : SecondCountableTopologyEither Space (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
    ⟨Or.inl inferInstance⟩
  have hψcont : Continuous (fun w : Space => ψ (‖x‖⁻¹ • w)) :=
    hψc.continuous.comp (continuous_const_smul _)
  have hIG := integrable_smul_decay (g := fun w => (((ψ (‖x‖⁻¹ • w) : ℝ) : ℂ) * f w))
    ((Complex.continuous_ofReal.comp hψcont).mul hfc) (B := Cf) (fun w => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hψr _).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψr _).2).trans (hfb w)) hkc hA x
  have hIF := integrable_smul_decay (g := fun w => (((1 - ψ (‖x‖⁻¹ • w) : ℝ) : ℂ) * f w))
    ((Complex.continuous_ofReal.comp (continuous_const.sub hψcont)).mul hfc) (B := Cf) (fun w => by
      have h0 := hψr (‖x‖⁻¹ • w)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans (hfb w)) hkc hA x
  have hsplit : (fun w => f w • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)) =
      fun w => (((ψ (‖x‖⁻¹ • w) : ℝ) : ℂ) * f w) • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w) +
        (((1 - ψ (‖x‖⁻¹ • w) : ℝ) : ℂ) * f w) • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w) := by
    funext w
    rw [← add_smul]
    congr 1
    push_cast
    ring
  show ‖∫ w, f w • iteratedFDeriv ℝ n (dyadicKernel σ θ d l) (x - w)‖ ≤ _
  rw [hsplit, integral_add hIG hIF]
  refine (norm_add_le _ _).trans ?_
  have e1 := hC1 l x hx hlx
  have e2 := hC2 l x hx hlx
  rw [add_mul]
  exact add_le_add e1 e2

end Breakdown.FracCert

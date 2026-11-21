import Breakdown.Weak.StatementsSlice
import Breakdown.FreqTr.WeakInX
import Breakdown.FreqTr.MildOfWeak

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem lpProd_sixFifths_six : ENNReal.HolderTriple (ENNReal.ofReal (6 / 5)) 6 1 := by
  constructor
  have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 6) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h6, ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private theorem integrable_weight_smul {p q : ℝ≥0∞} [Fact (1 ≤ p)] [ENNReal.HolderTriple q p 1]
    {w : Space → ℝ} (hw : MemLp w q volume) (g : Lp Space p volume) :
    Integrable (fun y => w y • (g : Space → Space) y) volume :=
  memLp_one_iff_integrable.1 ((Lp.memLp g).smul hw)

private theorem norm_integral_weight_smul_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [ENNReal.HolderTriple q p 1]
    {w : Space → ℝ} (hw : MemLp w q volume) (g : Lp Space p volume) :
    ‖∫ y, w y • (g : Space → Space) y‖ ≤ (eLpNorm w q volume).toReal * ‖g‖ := by
  calc ‖∫ y, w y • (g : Space → Space) y‖
      ≤ (∫⁻ y, ENNReal.ofReal ‖w y • (g : Space → Space) y‖).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (w • (g : Space → Space)) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        congr 1
        apply lintegral_congr
        intro y
        simp
    _ ≤ (eLpNorm w q volume * eLpNorm g p volume).toReal := by
        apply ENNReal.toReal_mono (ENNReal.mul_ne_top hw.eLpNorm_ne_top (Lp.eLpNorm_ne_top g))
        exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) hw.1
    _ = (eLpNorm w q volume).toReal * ‖g‖ := by rw [ENNReal.toReal_mul, Lp.norm_def]

private theorem continuous_integral_weight_smul {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [ENNReal.HolderTriple q p 1] {w : Space → ℝ} (hw : MemLp w q volume) :
    Continuous (fun g : Lp Space p volume => ∫ y, w y • (g : Space → Space) y) := by
  have hsub : ∀ g h : Lp Space p volume,
      (∫ y, w y • (g : Space → Space) y) - ∫ y, w y • (h : Space → Space) y =
        ∫ y, w y • ((g - h : Lp Space p volume) : Space → Space) y := by
    intro g h
    rw [← integral_sub (integrable_weight_smul hw g) (integrable_weight_smul hw h)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub g h] with y hy
    rw [hy, Pi.sub_apply, smul_sub]
  apply LipschitzWith.continuous (K := (eLpNorm w q volume).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [dist_eq_norm, dist_eq_norm, hsub]
  exact norm_integral_weight_smul_le hw (g - h)

private theorem byParts_test {φ : Space → ℝ} (hφ : IsTestFunction φ) {ψ : Space → Space}
    (hψ : IsTestField ψ) (j : Fin 3) :
    ∫ y, φ y • fderiv ℝ ψ y (unitVector j) = -∫ y, fderiv ℝ φ y (unitVector j) • ψ y := by
  have h1 := hφ.1
  have h2 := hψ.1
  have cφ : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (h1.continuous_fderiv (by simp)).clm_apply continuous_const
  have cψ : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
    (h2.continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · exact (cφ.smul h2.continuous).integrable_of_hasCompactSupport hψ.2.1.smul_left
  · exact (h1.continuous.smul cψ).integrable_of_hasCompactSupport hφ.2.smul_right
  · exact (h1.continuous.smul h2.continuous).integrable_of_hasCompactSupport hφ.2.smul_right
  · intro y _
    exact (h1.differentiable (by simp)).differentiableAt
  · intro y _
    exact (h2.differentiable (by simp)).differentiableAt

theorem velocityWeakGradient_holds : VelocityWeakGradient := by
  intro x φ hφ j
  have hw2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  have hw6 : MemLp (fun y => fderiv ℝ φ y (unitVector j)) (ENNReal.ofReal (6 / 5)) volume :=
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j))
  have := lpProd_sixFifths_six
  have hL : Continuous (fun z : X => ∫ y, φ y • (partialX j z : Space → Space) y) :=
    (continuous_integral_weight_smul (p := 2) hw2).comp (partialX j).continuous
  have hR : Continuous (fun z : X =>
      -∫ y, fderiv ℝ φ y (unitVector j) • (velocity z : Space → Space) y) :=
    ((continuous_integral_weight_smul (p := 6) hw6).comp velocity.continuous).neg
  have hsub : (testSpan : Set X) ⊆ {z : X | (∫ y, φ y • (partialX j z : Space → Space) y) =
      -∫ y, fderiv ℝ φ y (unitVector j) • (velocity z : Space → Space) y} := by
    intro z hz
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds z hz
    have hd := isDecayField_of_isTestField hψ
    have hp := partial_holds.1 ψ hd j
    have hv := velocityDecay_holds ψ hd
    have e1 : (fun y => φ y • (partialX j (embedX ψ) : Space → Space) y) =ᵐ[volume]
        fun y => φ y • fderiv ℝ ψ y (unitVector j) := by
      filter_upwards [hp] with y hy
      rw [hy]
      rfl
    have e2 : (fun y => fderiv ℝ φ y (unitVector j) • (velocity (embedX ψ) : Space → Space) y)
        =ᵐ[volume] fun y => fderiv ℝ φ y (unitVector j) • ψ y := by
      filter_upwards [hv] with y hy
      rw [hy]
    show _ = _
    rw [integral_congr_ae e1, integral_congr_ae e2]
    exact byParts_test hφ hψ j
  have hcl := closure_minimal hsub (isClosed_eq hL hR)
  rw [testDense_holds.2.closure_eq] at hcl
  exact hcl (mem_univ x)

end Breakdown.WeakProfile

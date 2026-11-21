import Breakdown.Cert.CoerciveGain
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

open GainInternal

theorem cylRadius_sq_le_norm_sq (y : Space) : cylRadius y ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [cylRadius, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  nlinarith [sq_nonneg (y 2)]

theorem cnormSq_neg' {β : Type*} [Fintype β] (x : β → ℂ) : cnormSq (-x) = cnormSq x := by
  simp [cnormSq]

theorem cnormSq_smul_I (k : ℝ) (x : Fin 3 → ℂ) :
    cnormSq (fun b => (k : ℂ) * Complex.I * x b) = k ^ 2 * cnormSq x := by
  simp only [cnormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem contracted_grad_le (M : Fin 3 × Fin 3 → ℂ) (y : Space) :
    cnormSq (fun b => ∑ j, M (b, j) * (azimuthalField y j : ℂ)) ≤ ‖y‖ ^ 2 * cnormSq M := by
  have hrow : ∀ b, ‖∑ j, M (b, j) * (azimuthalField y j : ℂ)‖ ^ 2 ≤
      (∑ j, ‖M (b, j)‖ ^ 2) * cylRadius y ^ 2 := by
    intro b
    have h1 : ‖∑ j, M (b, j) * (azimuthalField y j : ℂ)‖ ≤ ∑ j, ‖M (b, j)‖ * |azimuthalField y j| := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M (b, j)‖)
      (fun j => |azimuthalField y j|)
    simp only [sq_abs] at h2
    rw [azimuthalField_sq y] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hM : cnormSq M = ∑ b, ∑ j, ‖M (b, j)‖ ^ 2 := by
    simp only [cnormSq, Fintype.sum_prod_type]
  have hS : 0 ≤ cnormSq M := by rw [cnormSq]; positivity
  calc cnormSq (fun b => ∑ j, M (b, j) * (azimuthalField y j : ℂ))
      ≤ ∑ b, (∑ j, ‖M (b, j)‖ ^ 2) * cylRadius y ^ 2 := Finset.sum_le_sum fun b _ => hrow b
    _ = cylRadius y ^ 2 * cnormSq M := by rw [hM, ← Finset.sum_mul, mul_comm]
    _ ≤ ‖y‖ ^ 2 * cnormSq M := mul_le_mul_of_nonneg_right (cylRadius_sq_le_norm_sq y) hS

theorem angular_pointwise (w : Fin 3 → ℂ) (M : Fin 3 × Fin 3 → ℂ) (y : Space) (k : ℝ)
    (hid : ∀ b, ∑ j, M (b, j) * (azimuthalField y j : ℂ) =
      (k : ℂ) * Complex.I * w b + ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * w c) :
    k ^ 2 * cnormSq w ≤ 2 * cnormSq w + 2 * ‖y‖ ^ 2 * cnormSq M := by
  set u : Fin 3 → ℂ := fun b => ∑ j, M (b, j) * (azimuthalField y j : ℂ) with hu
  set Bw : Fin 3 → ℂ := fun b => ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * w c with hBw
  have hkw : (fun b => (k : ℂ) * Complex.I * w b) = u + -Bw := by
    funext b
    simp only [Pi.add_apply, Pi.neg_apply, hu, hBw, hid b]
    ring
  have h1 := cnormSq_add_le u (-Bw)
  rw [← hkw, cnormSq_smul_I, cnormSq_neg'] at h1
  have h2 := contracted_grad_le M y
  have h3 := vel_bound w
  rw [one_pow, one_mul] at h3
  rw [← hu] at h2
  linarith

theorem angular_mode_bound (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (ι : ℤ × ℤ) :
    ∀ᵐ z : ℝ × Space, ((ι.2 : ℝ)) ^ 2 * cnormSq (modeVel ι v z.1 z.2) ≤
      2 * cnormSq (modeVel ι v z.1 z.2) + 2 * ‖z.2‖ ^ 2 * cnormSq (modeGrad ι G z.1 z.2) := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hD1, -, -⟩ := hD Γ P v G H g hv ι
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => by positivity
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hR1 := Measure.ae_ae_of_ae_prod (ae_all_iff.2 (fun n => (hR Γ P v G H g hv ι (s n)).1))
  have hslice : ∀ᵐ σ, ∀ᵐ y, ((ι.2 : ℝ)) ^ 2 * cnormSq (modeVel ι v σ y) ≤
      2 * cnormSq (modeVel ι v σ y) + 2 * ‖y‖ ^ 2 * cnormSq (modeGrad ι G σ y) := by
    filter_upwards [hD1, hR1] with σ h1 h3
    obtain ⟨hw1, hg1, hweak1⟩ := weak_components (fun y => modeVel ι v σ y)
      (fun y => modeGrad ι G σ y) h1.1 h1.2
    have hid1 := angular_identity hRot (fun y => modeVel ι v σ y) (fun y b j => modeGrad ι G σ y (b, j))
      (ι.2 : ℝ) (fun ψ b c => ((axialRot ψ (unitVector c) b : ℝ) : ℂ))
      (fun b c => ((azimuthalField (unitVector c) b : ℝ) : ℂ)) hw1 (fun b j => hg1 b j)
      (fun φ hφ b j => hweak1 φ hφ b j)
      (fun b c => by simp only [unit_apply hRot]; split_ifs <;> simp)
      (fun b c => (hasDerivAt_axialRot (unitVector c) b).ofReal_comp) s hs0 hs
      (fun n => by
        filter_upwards [h3] with y hy b
        have := congrFun (hy n) b
        simpa [rotC] using this)
    filter_upwards [hid1] with y hy1
    exact angular_pointwise _ _ y _ hy1
  refine ae_of_ae_ae ?_ hslice
  have hcn : ∀ {β : Type} [Fintype β], Continuous (cnormSq : (β → ℂ) → ℝ) := by
    intro β _
    unfold cnormSq
    fun_prop
  have mV := hcn.comp_aestronglyMeasurable (modeVel_aesm hRot ι v hv.measurable_velocity)
  have mG := hcn.comp_aestronglyMeasurable (modeGrad_aesm hRot ι G hv.measurable_gradient)
  have hy : AEStronglyMeasurable (fun z : ℝ × Space => 2 * ‖z.2‖ ^ 2) volume :=
    (continuous_const.mul ((continuous_norm.comp continuous_snd).pow 2)).aestronglyMeasurable
  exact AEStronglyMeasurable.nullMeasurableSet_le (aestronglyMeasurable_const.mul mV)
    ((aestronglyMeasurable_const.mul mV).add (hy.mul mG))

end Internal

end FrequencySeminorm

end Coercive

end Breakdown

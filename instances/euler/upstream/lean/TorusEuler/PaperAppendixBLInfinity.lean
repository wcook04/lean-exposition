import TorusEuler.PaperAppendixB
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The Appendix B cutoff bound on all essentially bounded torus fields. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ContDiff ENNReal SchwartzMap

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The finite spectral kernel at the chosen evaluation point. -/
def appendixCutoffKernel (ψ : Vec3 → ℝ) (Λ : ℝ) (x z : Labels) : ℂ :=
  ∑ k ∈ frequencyBand (2 * Λ), (ψ (Λ⁻¹ • latticeVector k) : ℂ) * mFourier k x * mFourier (-k) z

theorem continuous_appendixCutoffKernel (ψ : Vec3 → ℝ) (Λ : ℝ) (x : Labels) :
    Continuous (appendixCutoffKernel ψ Λ x) := by
  unfold appendixCutoffKernel
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (mFourier (-k)).continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothFourierCutoff_eq_integral_appendixKernel (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : Labels → E) (hg : Integrable g unitTorusMeasure) (x : Labels) :
    smoothFourierCutoff ψ Λ g x =
      ∫ z, appendixCutoffKernel ψ Λ x z • g z ∂unitTorusMeasure := by
  classical
  unfold smoothFourierCutoff finiteFourierSum appendixCutoffKernel mFourierCoeff
  simp only [Finset.sum_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [← Complex.coe_smul, smul_smul, mul_comm (mFourier k x), ← integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => (mul_smul _ _ _).symm
  · intro k _
    let c : ℂ := (ψ (Λ⁻¹ • latticeVector k) : ℂ) * mFourier k x
    have hBound : ∀ᵐ z ∂unitTorusMeasure, ‖c * mFourier (-k) z‖ ≤ ‖c‖ := by
      refine ae_of_all _ fun z => ?_
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by
        simpa only [mFourier_norm] using (mFourier (-k)).norm_coe_le_norm z)
    exact hg.bdd_smul ‖c‖ (continuous_const.mul (mFourier (-k)).continuous).aestronglyMeasurable hBound

theorem norm_appendixCutoffKernel_integral_le {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (x : Labels) :
    (∫ z, ‖appendixCutoffKernel ψ Λ x z‖ ∂unitTorusMeasure) ≤
      ∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖ := by
  let K := appendixCutoffKernel ψ Λ x
  let C : ℝ := ∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hK : Continuous K := continuous_appendixCutoffKernel ψ Λ x
  apply le_of_forall_pos_le_add
  intro ε hε
  let g : C(Labels, ℂ) := ⟨fun z => (‖K z‖ + ε)⁻¹ • conj (K z),
    ((hK.norm.add continuous_const).inv₀ fun _ => (add_pos_of_nonneg_of_pos (norm_nonneg _) hε).ne').smul
      (Complex.continuous_conj.comp hK)⟩
  have hg : ‖g‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).2 fun z => by
    change ‖(‖K z‖ + ε)⁻¹ • conj (K z)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (add_pos_of_nonneg_of_pos (norm_nonneg _) hε)),
      Complex.norm_conj, ← div_eq_inv_mul]
    exact (div_le_one (add_pos_of_nonneg_of_pos (norm_nonneg _) hε)).2 (le_add_of_nonneg_right hε.le)
  have hKg : Integrable (fun z => K z * g z) unitTorusMeasure :=
    (hK.mul g.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (z : Labels) : ‖K z‖ ≤ (K z * g z).re + ε := by
    let r := ‖K z‖
    have hr : 0 ≤ r := norm_nonneg _
    have hden : 0 < r + ε := add_pos_of_nonneg_of_pos hr hε
    have hid : (K z * g z).re = (r + ε)⁻¹ * r ^ 2 := by
      change (K z * ((r + ε)⁻¹ • conj (K z))).re = _
      rw [mul_smul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.smul_re, Complex.ofReal_re,
        smul_eq_mul]
    rw [hid, ← div_eq_inv_mul]
    rw [← sub_le_iff_le_add]
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg ε]
  have hI : (∫ z, ‖K z‖ ∂unitTorusMeasure) ≤
      (∫ z, K z * g z ∂unitTorusMeasure).re + ε := by
    have hiK : Integrable (fun z => ‖K z‖) unitTorusMeasure :=
      hK.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiRe : Integrable (fun z => (K z * g z).re) unitTorusMeasure :=
      (Complex.continuous_re.comp (hK.mul g.continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := integral_mono hiK (hiRe.add (integrable_const ε)) hpoint
    change _ ≤ ∫ z, (K z * g z).re + ε ∂unitTorusMeasure at h
    rw [integral_add hiRe (integrable_const ε)] at h
    rw [show (∫ z, (K z * g z).re ∂unitTorusMeasure) =
      (∫ z, K z * g z ∂unitTorusMeasure).re from integral_re hKg] at h
    simpa [unitTorusMeasure] using h
  have hConv := smoothFourierCutoff_eq_integral_appendixKernel ψ Λ g
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) x
  change _ = ∫ z, K z * g z ∂unitTorusMeasure at hConv
  have hNorm : ‖smoothFourierCutoff ψ Λ g x‖ ≤ C := by
    obtain ⟨y, rfl⟩ := toUnitTorus_surjective x
    have hB : BddAbove (range fun y => ‖smoothFourierCutoff ψ Λ g (toUnitTorus y)‖) := by
      have hc : Continuous (smoothFourierCutoff ψ Λ g) := by
        unfold smoothFourierCutoff finiteFourierSum
        exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
      obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨M, by rintro _ ⟨q, rfl⟩; exact hM _ (mem_univ _)⟩
    exact (norm_le_spatialSupNorm hB y).trans ((paperLemmaB1_cutoff_sup hsupp hsmooth hΛ g).trans
      (mul_le_of_le_one_right hC hg))
  have hRe : (∫ z, K z * g z ∂unitTorusMeasure).re ≤ C := by
    rw [← hConv]
    exact (Complex.re_le_norm _).trans hNorm
  exact hI.trans (add_le_add hRe le_rfl)

/-- Direct pointwise cutoff control for essentially bounded data, with
the same scale-independent kernel mass as on continuous functions. -/
theorem paperLemmaB1_cutoff_aeBound {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (g : Labels → E) (hg : Integrable g unitTorusMeasure) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ᵐ z ∂unitTorusMeasure, ‖g z‖ ≤ M) (x : Labels) :
    ‖smoothFourierCutoff ψ Λ g x‖ ≤
      (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) * M := by
  let K := appendixCutoffKernel ψ Λ x
  have hK : Continuous K := continuous_appendixCutoffKernel ψ Λ x
  have hKI : Integrable (fun z => ‖K z‖) unitTorusMeasure :=
    hK.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [smoothFourierCutoff_eq_integral_appendixKernel ψ Λ g hg x]
  calc
    _ ≤ ∫ z, ‖K z • g z‖ ∂unitTorusMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖K z‖ * M ∂unitTorusMeasure := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hKI.mul_const M) ?_
      filter_upwards [hbound] with z hz
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = (∫ z, ‖K z‖ ∂unitTorusMeasure) * M := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_appendixCutoffKernel_integral_le hsupp hsmooth hΛ x) hM

/-- The Fourier cutoff acts on measurable representatives modulo almost-everywhere equality. -/
theorem paperLemmaB1_cutoff_congr_ae (ψ : Vec3 → ℝ) (Λ : ℝ) {f g : Labels → E}
    (h : f =ᵐ[unitTorusMeasure] g) :
    smoothFourierCutoff ψ Λ f = smoothFourierCutoff ψ Λ g := by
  have hCoeff (k : Fin 3 → ℤ) : mFourierCoeff f k = mFourierCoeff g k :=
    integral_congr_ae (h.mono fun z hz => congrArg (fun v => mFourier (-k) z • v) hz)
  unfold smoothFourierCutoff
  simp_rw [hCoeff]

/-- Lemma B.1 on the whole strongly measurable essential-supremum space. -/
theorem paperLemmaB1_cutoff_LInfinity {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (g : Labels → E) (hg : MemLp g ∞ unitTorusMeasure) :
    eLpNormEssSup (smoothFourierCutoff ψ Λ g) unitTorusMeasure ≤
      ENNReal.ofReal (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) *
        eLpNormEssSup g unitTorusMeasure := by
  have h := eLpNormEssSup_le_of_ae_bound (ae_of_all unitTorusMeasure (paperLemmaB1_cutoff_aeBound hsupp hsmooth hΛ g
    (hg.integrable (by simp)) (lpNorm_nonneg (f := g) (p := ∞) (μ := unitTorusMeasure)) (ae_le_lpNorm_exponent_top hg)))
  simpa only [ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _),
    ofReal_lpNorm hg, eLpNorm_exponent_top] using h

end

end TorusEuler

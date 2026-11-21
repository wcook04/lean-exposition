import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.GradCompat

open SchwartzMap FourierTransform LineDeriv

theorem decay_bounds {f : Space → Space} (hf : IsDecayField f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖f y‖ ≤ C ∧ ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨-, -, C, hC⟩ := hf
  have hC0 : 0 ≤ C := by
    have := (hC 0).1
    simp at this
    linarith [norm_nonneg (f 0)]
  refine ⟨C, hC0, fun y => ⟨?_, ?_⟩⟩
  · have h1 := (hC y).1
    have hy : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    calc ‖f y‖ ≤ C / (1 + ‖y‖) := h1
      _ ≤ C := div_le_self hC0 hy
  · have h2 := (hC y).2
    have hpos : (0 : ℝ) < 1 + ‖y‖ := by linarith [norm_nonneg y]
    rw [Real.rpow_neg hpos.le, Real.rpow_two, ← div_eq_mul_inv]
    exact h2

theorem memLp_partialField {f : Space → Space} (hf : IsDecayField f) (k : Fin 3) :
    MemLp (partialField f k) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := decay_bounds hf
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    integrable_one_add_norm (by simp; norm_num)
  have hg : MemLp (fun y : Space => (1 + ‖y‖) ^ (-(2 : ℝ))) 2 volume := by
    rw [memLp_two_iff_integrable_sq]
    · refine hint.congr (ae_of_all _ fun y => ?_)
      have hpos : (0 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      simp only
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos]
      norm_num
    · exact (Continuous.rpow_const (by fun_prop) (fun y => Or.inl (by positivity))).aestronglyMeasurable
  have hcont : Continuous (partialField f k) :=
    (hf.1.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (hg.const_mul C).of_le hcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have hpos : (0 : ℝ) < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hu : ‖unitVector k‖ = 1 := by simp [unitVector]
  calc ‖partialField f k y‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVector k‖ := (fderiv ℝ f y).le_opNorm _
    _ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by rw [hu, mul_one]; exact (hC y).2
    _ = ‖C * (1 + ‖y‖) ^ (-(2 : ℝ))‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hpos.le _))]

theorem coe_gradLp {f : Space → Space} (hf : IsDecayField f) (k : Fin 3) :
    (complexify (toLpOrZero 2 (partialField f k)) : Space → CSpace) =ᵐ[volume]
      fun x => complexifyVec (partialField f k x) := by
  have hm := memLp_partialField hf k
  have h1 : toLpOrZero 2 (partialField f k) = hm.toLp _ := by
    simp [toLpOrZero, hm]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec
    (toLpOrZero 2 (partialField f k)), hm.coeFn_toLp] with x hx hx'
  rw [complexify, hx, h1, hx']

theorem pair_freqTr (G : L2C) (ψ : 𝓢(Space, ℂ)) :
    ∫ ξ, ψ ξ • (freqTrL2 G : Space → CSpace) ξ = ∫ x, (𝓕 ψ) x • (G : Space → CSpace) x := by
  rw [← Lp.toTemperedDistribution_apply (freqTrL2 G) ψ, ← Lp.toTemperedDistribution_apply G (𝓕 ψ)]
  have := Lp.fourier_toTemperedDistribution_eq G
  rw [show freqTrL2 G = 𝓕 G from rfl, ← this]
  rfl

theorem snd_symm (Φ : 𝓢(Space, ℂ)) (j k : Fin 3) (x : Space) :
    (∂_{unitVector j} (∂_{unitVector k} Φ)) x = (∂_{unitVector k} (∂_{unitVector j} Φ)) x := by
  have hΦ : ContDiff ℝ ∞ Φ := Φ.smooth ⊤
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have key : ∀ a b : Space, (∂_{a} (∂_{b} Φ)) x = fderiv ℝ (fderiv ℝ Φ) x a b := by
    intro a b
    rw [lineDerivOp_apply_eq_fderiv]
    have : ((∂_{b} Φ : 𝓢(Space, ℂ)) : Space → ℂ) = fun y => fderiv ℝ Φ y b :=
      funext fun y => lineDerivOp_apply_eq_fderiv b Φ y
    rw [this, fderiv_clm_apply hd.differentiableAt (differentiableAt_const _)]
    simp
  rw [key, key]
  have hs : IsSymmSndFDerivAt ℝ Φ x :=
    (hΦ.contDiffAt).isSymmSndFDerivAt (by simp; norm_cast)
  exact hs _ _
theorem ibp_key {f : Space → Space} (hf : IsDecayField f) (θ : 𝓢(Space, ℂ)) (j : Fin 3) :
    ∫ x, θ x • complexifyVec (partialField f j x) =
      -∫ x, (∂_{unitVector j} θ) x • complexifyVec (f x) := by
  obtain ⟨C, hC0, hC⟩ := decay_bounds hf
  have hsm := hf.1
  have hdf : Differentiable ℝ f := hsm.differentiable (by simp)
  set F : Space → CSpace := fun x => complexifyVec (f x) with hFdef
  have hFd : ∀ x v, fderiv ℝ F x v = complexifyVec (fderiv ℝ f x v) := by
    intro x v
    have h := (complexifyVec.hasFDerivAt.comp x (hdf x).hasFDerivAt).fderiv
    rw [show F = complexifyVec ∘ f from rfl, h]
    rfl
  have hFc : Continuous F := complexifyVec.continuous.comp hsm.continuous
  have hFb : ∀ x, ‖F x‖ ≤ ‖complexifyVec‖ * C := fun x =>
    (complexifyVec.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC x).1 (norm_nonneg _))
  set G : Space → CSpace := fun x => complexifyVec (partialField f j x) with hGdef
  have hGc : Continuous G :=
    complexifyVec.continuous.comp ((hsm.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hGb : ∀ x, ‖G x‖ ≤ ‖complexifyVec‖ * (C * ‖unitVector j‖) := by
    intro x
    refine (complexifyVec.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine ((fderiv ℝ f x).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have h1 : (1 + ‖x‖) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by norm_num)
    calc ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ (-(2 : ℝ)) := (hC x).2
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC0
      _ = C := mul_one C
  have hGF : ∀ x, fderiv ℝ F x (unitVector j) = G x := fun x => hFd x _
  set θ' : 𝓢(Space, ℂ) := ∂_{unitVector j} θ with hθ'
  have hθ'x : ∀ x, fderiv ℝ (θ : Space → ℂ) x (unitVector j) = θ' x := fun x =>
    (lineDerivOp_apply_eq_fderiv (unitVector j) θ x).symm
  have i1 : Integrable (fun x => fderiv ℝ (θ : Space → ℂ) x (unitVector j) • F x) := by
    have : Integrable (fun x => θ' x • F x) :=
      θ'.integrable.smul_bdd (f := F) _ hFc.aestronglyMeasurable (ae_of_all _ hFb)
    simpa only [hθ'x] using this
  have i2 : Integrable (fun x => θ x • fderiv ℝ F x (unitVector j)) := by
    have : Integrable (fun x => θ x • G x) :=
      θ.integrable.smul_bdd (f := G) _ hGc.aestronglyMeasurable (ae_of_all _ hGb)
    simpa only [hGF] using this
  have i3 : Integrable (fun x => θ x • F x) :=
    θ.integrable.smul_bdd (f := F) _ hFc.aestronglyMeasurable (ae_of_all _ hFb)
  have hdF : Differentiable ℝ F := complexifyVec.differentiable.comp hdf
  have key := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable i1 i2 i3
    (fun x _ => θ.differentiableAt) (fun x _ => hdF x)
  simp only [hGF, hθ'x] at key
  exact key

theorem ibp_symm {f : Space → Space} (hf : IsDecayField f) (Φ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    ∫ x, (∂_{unitVector k} Φ) x • complexifyVec (partialField f j x) =
      ∫ x, (∂_{unitVector j} Φ) x • complexifyVec (partialField f k x) := by
  rw [ibp_key hf, ibp_key hf]
  simp only [snd_symm Φ j k]
theorem pair_grad {f : Space → Space} (hf : IsDecayField f) (Ψ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    (-(2 * π * Complex.I)) • ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ • (gradHat f j : Space → CSpace) ξ =
      ∫ x, (∂_{unitVector k} (𝓕 Ψ)) x • complexifyVec (partialField f j x) := by
  rw [← integral_smul]
  have h1 : ∀ ξ, (-(2 * π * Complex.I)) • ((smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ •
      (gradHat f j : Space → CSpace) ξ) =
      ((-(2 * π * Complex.I)) • smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ •
        (gradHat f j : Space → CSpace) ξ := by
    intro ξ
    rw [smul_apply, smul_assoc]
  simp only [h1]
  rw [show (gradHat f j : L2C) = freqTrL2 (complexify (toLpOrZero 2 (partialField f j))) from rfl,
    pair_freqTr, ← lineDerivOp_fourier_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_gradLp hf j] with x hx
  rw [hx]

theorem pair_sym {f : Space → Space} (hf : IsDecayField f) (Ψ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ • (gradHat f j : Space → CSpace) ξ =
      ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector j)) Ψ) ξ • (gradHat f k : Space → CSpace) ξ := by
  have hc : (-(2 * π * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply smul_right_injective CSpace hc
  simp only
  rw [pair_grad hf, pair_grad hf, ibp_symm hf]

end Internal.GradCompat

open Internal.GradCompat SchwartzMap in
theorem gradCompatible : GradCompatible := by
  intro f hf j k
  have hL : ∀ j k : Fin 3, LocallyIntegrable (fun ξ : Space => (ξ k : ℝ) • (gradHat f j : L2C) ξ) volume :=
    fun j k => LocallyIntegrable.continuous_smul (by fun_prop)
      ((Lp.memLp (gradHat f j)).locallyIntegrable (by norm_num))
  refine ae_eq_of_integral_contDiff_smul_eq (hL j k) (hL k j) fun g hg hgs => ?_
  have h₁ : HasCompactSupport (fun ξ => (g ξ : ℂ)) := hgs.comp_left Complex.ofReal_zero
  have h₂ : ContDiff ℝ ∞ (fun ξ => (g ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  set Ψ : 𝓢(Space, ℂ) := h₁.toSchwartzMap h₂ with hΨ
  have e : ∀ j k : Fin 3, ∫ ξ, g ξ • ((ξ k : ℝ) • (gradHat f j : L2C) ξ) =
      ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ • (gradHat f j : Space → CSpace) ξ := by
    intro j k
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    have ht : (inner ℝ · (unitVector k) : Space → ℝ).HasTemperateGrowth :=
      ((innerSL ℝ).flip (unitVector k)).hasTemperateGrowth
    dsimp only
    rw [smulLeftCLM_apply_apply ht]
    have hi : inner ℝ ξ (unitVector k) = ξ k := by
      simp [unitVector, EuclideanSpace.inner_single_right]
    have hΨx : Ψ ξ = (g ξ : ℂ) := rfl
    simp only [hi, hΨx]
    rw [smul_smul, ← Complex.coe_smul]
    congr 1
    rw [Complex.real_smul]
    push_cast
    ring
  rw [e, e]
  exact pair_sym hf Ψ j k

end Breakdown.Freq

import Breakdown.Uniqueness.RegPhysAuxProductPart1

open scoped ContDiff ENNReal FourierTransform Topology ComplexConjugate
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal.ConvProduct

theorem integrable_char_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {u : Space → E}
    (hu : Integrable u) (x : Space) :
    Integrable (fun v => ((𝐞 (inner ℝ v x) : Circle) : ℂ) • u v) := by
  refine hu.norm.mono' ?_ ?_
  · exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable.smul
      hu.aestronglyMeasurable
  · filter_upwards with v
    rw [norm_smul, Circle.norm_coe, one_mul]

theorem freqTrInv_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : Space → E)
    (x : Space) : 𝓕⁻ u x = ∫ v, ((𝐞 (inner ℝ v x) : Circle) : ℂ) • u v := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def]

theorem freqTrInv_apply_eq {f : Space → CSpace} (hf : Integrable f) (x : Space) (i : Fin 3) :
    (𝓕⁻ f x) i = 𝓕⁻ (fun ξ => f ξ i) x := by
  rw [freqTrInv_eq_integral, freqTrInv_eq_integral]
  have h := (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integral_comp_comm (integrable_char_smul hf x)
  simpa using h.symm

theorem freqTrInv_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {φ : Fin 3 → Space → E}
    (hφ : ∀ j, Integrable (φ j)) (x : Space) :
    𝓕⁻ (fun ξ => ∑ j, φ j ξ) x = ∑ j, 𝓕⁻ (φ j) x := by
  simp only [freqTrInv_eq_integral, Finset.smul_sum]
  exact integral_finsetSum _ fun j _ => integrable_char_smul (hφ j) x

theorem freqTrInv_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ)
    (φ : Space → E) (x : Space) : 𝓕⁻ (fun ξ => c • φ ξ) x = c • 𝓕⁻ φ x := by
  simp only [freqTrInv_eq_integral]
  rw [← integral_smul]
  congr 1
  funext v
  rw [smul_comm]

theorem freqTrInv_convC {a b : Space → ℂ} (ha : Integrable a) (hb : Integrable b) (x : Space) :
    𝓕⁻ (convC a b) x = 𝓕⁻ a x * 𝓕⁻ b x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
    convC_eq_convolution]
  exact Real.fourier_mul_convolution_eq ha hb (-x)

theorem freqTrInv_conj_symm {g : Space → ℂ} (hg : ∀ ξ, g (-ξ) = conj (g ξ)) (x : Space) :
    conj (𝓕⁻ g x) = 𝓕⁻ g x := by
  have key : ∀ v : Space, conj (((𝐞 (inner ℝ (-v) x) : Circle) : ℂ) • g (-v)) =
      ((𝐞 (inner ℝ v x) : Circle) : ℂ) • g v := by
    intro v
    rw [inner_neg_left, hg, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_conj,
      AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, Complex.conj_conj]
  calc conj (𝓕⁻ g x) = ∫ v, conj (((𝐞 (inner ℝ v x) : Circle) : ℂ) • g v) := by
        rw [freqTrInv_eq_integral, integral_conj]
    _ = ∫ v, conj (((𝐞 (inner ℝ (-v) x) : Circle) : ℂ) • g (-v)) :=
        (integral_neg_eq_self (fun v => conj (((𝐞 (inner ℝ v x) : Circle) : ℂ) • g v)) volume).symm
    _ = ∫ v, ((𝐞 (inner ℝ v x) : Circle) : ℂ) • g v := by
        congr 1
        funext v
        exact key v
    _ = 𝓕⁻ g x := (freqTrInv_eq_integral g x).symm

theorem physField_freqInner_eq {f : Space → CSpace} (hf : ∀ k, MemLp f 1 (polyWeight k))
    (hsol : IsSolenoidalSymbol f) (x : Space) :
    physField (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (physField f x) : ℝ) : ℂ)) • f ξ) x =
      physField (advectionSymbol f) x := by
  set h := physField f x with hhdef
  have hfi : Integrable f := integrable_of_memLp_polyWeight (hf 0)
  have hfj : ∀ j, Integrable (fun η => f η j) := fun j =>
    integrable_of_memLp_polyWeight (memLp_polyWeight_apply (hf 0) j)
  have hphi : ∀ j, Integrable (fun η : Space => (2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) • f η) :=
    fun j => integrable_of_memLp_polyWeight (memLp_freq_smul (hf 1) j)
  have hb : ∀ j i, Integrable (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) :=
    fun j i => integrable_of_memLp_polyWeight (memLp_freq_smul (memLp_polyWeight_apply (hf 1) i) j)
  have hconv : ∀ j i, Integrable (convC (fun η => f η j)
      (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i)) := fun j i =>
    integrable_of_memLp_polyWeight (memLp_convC (memLp_polyWeight_apply (hf 0) j)
      (memLp_freq_smul (memLp_polyWeight_apply (hf 1) i) j))
  have hadv : Integrable (advectionSymbol f) :=
    integrable_of_memLp_polyWeight (memLp_advectionSymbol_aux hf 0)
  have hreal : ∀ j, (𝓕⁻ (fun η => f η j) x).im = 0 := by
    intro j
    refine Complex.conj_eq_iff_im.mp (freqTrInv_conj_symm (fun ξ => ?_) x)
    rw [(hsol ξ).2]
    rfl
  have hh : ∀ j, h j = (𝓕⁻ (fun η => f η j) x).re := by
    intro j
    rw [← freqTrInv_apply_eq hfi]
    rfl
  have hF : (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) =
      fun ξ => ∑ j, ((h j : ℝ) : ℂ) • ((2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • f ξ) := by
    funext ξ
    simp only [smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  have hL : 𝓕⁻ (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) x =
      ∑ j, ((h j : ℝ) : ℂ) • 𝓕⁻ (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • f ξ) x := by
    rw [hF, freqTrInv_sum (φ := fun j ξ => ((h j : ℝ) : ℂ) • ((2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • f ξ))
      (fun j => by exact (hphi j).smul ((h j : ℝ) : ℂ))]
    exact Finset.sum_congr rfl fun j _ => freqTrInv_const_smul _ _ x
  ext i
  change (𝓕⁻ (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) x i).re =
    (𝓕⁻ (advectionSymbol f) x i).re
  rw [hL, freqTrInv_apply_eq hadv]
  have hR : (fun ξ => advectionSymbol f ξ i) = fun ξ => ∑ j, convC (fun η => f η j)
      (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) ξ := by
    funext ξ
    exact advectionSymbol_apply f ξ i
  rw [hR, freqTrInv_sum (φ := fun j => convC (fun η => f η j)
      (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i)) (fun j => hconv j i)]
  have hc : ∀ j, (𝓕⁻ (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ)) • f ξ) x) i =
      𝓕⁻ (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) x := by
    intro j
    rw [freqTrInv_apply_eq (hphi j)]
    rfl
  rw [WithLp.ofLp_sum, Finset.sum_apply, Complex.re_sum, Complex.re_sum]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  simp only [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [freqTrInv_convC (hfj j) (hb j i), Complex.mul_re, Complex.mul_re, hreal j, Complex.ofReal_re,
    Complex.ofReal_im, hh j]

end Internal.ConvProduct

end Breakdown.SmoothFlow

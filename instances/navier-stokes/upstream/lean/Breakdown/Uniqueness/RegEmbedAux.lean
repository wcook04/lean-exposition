import Breakdown.Uniqueness.RegToolkit
import Breakdown.FreqTr.StatementsBilinFormula
import Breakdown.FreqTr.FreqTrL1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow.Internal.RegEmbed

open Breakdown.Freq

def dmul (k : Fin 3) (g : Space → CSpace) : Space → CSpace :=
  fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ k : ℝ) : ℂ)) • g ξ

theorem abs_coord_le (ξ : Space) (k : Fin 3) : |ξ k| ≤ ‖ξ‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ k

theorem norm_dmul_le (k : Fin 3) (g : Space → CSpace) (ξ : Space) :
    ‖dmul k g ξ‖ ≤ 2 * π * ‖ξ‖ * ‖g ξ‖ := by
  unfold dmul
  rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Complex.norm_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
  gcongr
  exact abs_coord_le ξ k

def HasMoments (g : Space → CSpace) : Prop :=
  AEStronglyMeasurable g volume ∧ ∀ n : ℕ, Integrable (fun ξ : Space => ‖ξ‖ ^ n * ‖g ξ‖) volume

theorem hasMoments_of {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) : HasMoments f := by
  refine ⟨hm, fun n => ?_⟩
  obtain ⟨C, hC⟩ := weightedFreqL1_le n
  refine ⟨(continuous_norm.pow n).aestronglyMeasurable.mul hm.norm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 : ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ n) * ‖f ξ‖ₑ < ⊤ :=
    (hC f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hf (n + 2)).ne))
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) h1
  rw [enorm_mul, Real.enorm_eq_ofReal (by positivity), enorm_norm]
  gcongr
  linarith [norm_nonneg ξ]

theorem HasMoments.integrable {g : Space → CSpace} (h : HasMoments g) : Integrable g volume := by
  have := h.2 0
  simp only [pow_zero, one_mul] at this
  exact (integrable_norm_iff h.1).1 this

theorem HasMoments.integrable_one {g : Space → CSpace} (h : HasMoments g) :
    Integrable (fun ξ : Space => ‖ξ‖ * ‖g ξ‖) volume := by
  simpa using h.2 1

theorem hasMoments_dmul {g : Space → CSpace} (h : HasMoments g) (k : Fin 3) :
    HasMoments (dmul k g) := by
  have hc : Continuous fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((ξ k : ℝ) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable (dmul k g) volume := hc.aestronglyMeasurable.smul h.1
  refine ⟨hm, fun n => ?_⟩
  refine ((h.2 (n + 1)).const_mul (2 * π)).mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul hm.norm) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖ξ‖ ^ n * ‖dmul k g ξ‖ ≤ ‖ξ‖ ^ n * (2 * π * ‖ξ‖ * ‖g ξ‖) := by
        gcongr
        exact norm_dmul_le k g ξ
    _ = 2 * π * (‖ξ‖ ^ (n + 1) * ‖g ξ‖) := by ring

theorem inner_unitVector (v : Space) (k : Fin 3) : inner ℝ v (unitVector k) = v k := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem fderiv_freqTrInv {g : Space → CSpace} (h0 : Integrable g volume)
    (h1 : Integrable (fun v : Space => ‖v‖ * ‖g v‖) volume) (x : Space) (k : Fin 3) :
    HasFDerivAt (𝓕⁻ g) (fderiv ℝ (𝓕⁻ g) x) x ∧
      fderiv ℝ (𝓕⁻ g) x (unitVector k) = 𝓕⁻ (dmul k g) x := by
  have e1 : 𝓕⁻ g = 𝓕 (fun v => g (-v)) := Real.fourierInv_eq_fourier_comp_neg g
  have h0' : Integrable (fun v : Space => g (-v)) volume := h0.comp_neg
  have h1' : Integrable (fun v : Space => ‖v‖ * ‖g (-v)‖) volume := by
    simpa [norm_neg] using h1.comp_neg
  have hd := Real.hasFDerivAt_fourier h0' h1' x
  rw [e1]
  refine ⟨hd.differentiableAt.hasFDerivAt, ?_⟩
  have hint : Integrable (fun v : Space => 𝐞 (-inner ℝ v x) •
      VectorFourier.fourierSMulRight (innerSL ℝ) (fun v => g (-v)) v) volume := by
    rw [Real.fourierIntegral_convergent_iff]
    refine (h1'.const_mul (2 * π * ‖(innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ)‖)).mono'
      h0'.1.fourierSMulRight (Eventually.of_forall fun v => ?_)
    have := VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) (fun v => g (-v)) v
    linarith
  rw [hd.fderiv, Real.fourier_eq, ContinuousLinearMap.integral_apply hint, Real.fourierInv_eq,
    ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [inner_neg_left, dmul, neg_neg, Circle.smul_def, _root_.smul_apply,
    VectorFourier.fourierSMulRight_apply]
  congr 1
  have hi : (innerSL ℝ (-v) (unitVector k) : ℝ) = -(v k) := by
    rw [innerSL_apply_apply, inner_neg_left, inner_unitVector]
  rw [hi]
  ext i
  simp [Complex.real_smul]
  ring

theorem conjVec_conjVec (z : CSpace) : conjVec (conjVec z) = z := by
  ext i
  simp [conjVec]

theorem conjVec_smul (c : ℂ) (z : CSpace) : conjVec (c • z) = star c • conjVec z := by
  ext i
  simp [conjVec]

theorem integrable_char_smul {g : Space → CSpace} (h : Integrable g volume) (x : Space) :
    Integrable (fun v : Space => 𝐞 (inner ℝ v x) • g v) volume := by
  have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := g) (-x)).2 h
  simpa [inner_neg_right] using this

theorem star_char (t : ℝ) : star ((𝐞 t : Circle) : ℂ) = ((𝐞 (-t) : Circle) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

theorem conjVec_freqTrInv {g : Space → CSpace} (h0 : Integrable g volume)
    (hg : ∀ ξ, g (-ξ) = conjVec (g ξ)) (x : Space) : conjVec (𝓕⁻ g x) = 𝓕⁻ g x := by
  rw [Real.fourierInv_eq, ← ContinuousLinearMap.integral_comp_comm conjVec (integrable_char_smul h0 x)]
  rw [← integral_neg_eq_self (fun v : Space => 𝐞 (inner ℝ v x) • g v)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, conjVec_smul, star_char, inner_neg_left, hg]

theorem complexifyVec_realVec {z : CSpace} (h : conjVec z = z) : complexifyVec (realVec z) = z := by
  ext i
  have := congrArg (fun w : CSpace => w i) h
  simp only [conjVec, realVec, complexifyVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk] at this ⊢
  exact Complex.conj_eq_iff_re.1 this

theorem conjSym_dmul {g : Space → CSpace} (hg : ∀ ξ, g (-ξ) = conjVec (g ξ)) (k : Fin 3) (ξ : Space) :
    dmul k g (-ξ) = conjVec (dmul k g ξ) := by
  simp only [dmul, hg, conjVec_smul, PiLp.neg_apply]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]

theorem contDiff_freqTrInv {g : Space → CSpace} (h : HasMoments g) : ContDiff ℝ ∞ (𝓕⁻ g) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  refine Real.contDiff_fourier (N := ⊤) fun n _ => ?_
  simpa [norm_neg] using (h.2 n).comp_neg

theorem partialField_physField {f : Space → CSpace} (h : HasMoments f) (k : Fin 3) :
    partialField (physField f) k = fun x => realVec (𝓕⁻ (dmul k f) x) := by
  funext x
  obtain ⟨hd, he⟩ := fderiv_freqTrInv h.integrable h.integrable_one x k
  have : HasFDerivAt (physField f) (realVec.comp (fderiv ℝ (𝓕⁻ f) x)) x :=
    realVec.hasFDerivAt.comp x hd
  simp only [partialField, this.fderiv, ContinuousLinearMap.comp_apply, he]

theorem sum_freqTrInv_dmul {f : Space → CSpace} (h : HasMoments f) (hs : IsSolenoidalSymbol f)
    (x : Space) : ∑ i : Fin 3, 𝓕⁻ (dmul i f) x i = 0 := by
  have hint : ∀ i : Fin 3, Integrable (fun v : Space => 𝐞 (inner ℝ v x) • dmul i f v) volume :=
    fun i => integrable_char_smul (hasMoments_dmul h i).integrable x
  have e : ∀ i : Fin 3, 𝓕⁻ (dmul i f) x i =
      ∫ v, (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ) (𝐞 (inner ℝ v x) • dmul i f v) := by
    intro i
    rw [Real.fourierInv_eq]
    exact ((EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integral_comp_comm (hint i)).symm
  simp_rw [e]
  rw [← integral_finsetSum _ (fun i _ =>
    ((EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integrable_comp (hint i)))]
  refine (integral_congr_ae (Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
  have h1 := (hs v).1
  simp only [EuclideanSpace.proj, PiLp.proj_apply, Circle.smul_def, dmul, PiLp.smul_apply, smul_eq_mul]
  calc ∑ i : Fin 3, ((𝐞 (inner ℝ v x) : Circle) : ℂ) * (2 * (π : ℂ) * Complex.I * ((v i : ℝ) : ℂ) * f v i)
      = ((𝐞 (inner ℝ v x) : Circle) : ℂ) * (2 * (π : ℂ) * Complex.I) * ∑ i, ((v i : ℝ) : ℂ) * f v i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [h1, mul_zero]

theorem memLp_two_of_le {g f : Space → CSpace} (hg : AEStronglyMeasurable g volume) (m : ℕ) (c : ℝ)
    (hb : ∀ ξ, ‖g ξ‖ₑ ^ 2 ≤ ENNReal.ofReal c * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2))
    (hf : hsNormSq m f < ⊤) : MemLp g 2 volume := by
  refine ⟨hg, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

theorem memLp_self {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) : MemLp f 2 volume :=
  memLp_two_of_le hm 0 1 (fun ξ => by simp [hsWeight]) (hf 0)

theorem memLp_dmul {f : Space → CSpace} (h : HasMoments f) (hf : ∀ m, hsNormSq m f < ⊤) (k : Fin 3) :
    MemLp (dmul k f) 2 volume := by
  refine memLp_two_of_le (hasMoments_dmul h k).1 1 (4 * π ^ 2) (fun ξ => ?_) (hf 1)
  calc ‖dmul k f ξ‖ₑ ^ 2 ≤ (ENNReal.ofReal (2 * π * ‖ξ‖) * ‖f ξ‖ₑ) ^ 2 := by
        gcongr
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (norm_dmul_le k f ξ)
    _ = ENNReal.ofReal ((2 * π * ‖ξ‖) ^ 2) * ‖f ξ‖ₑ ^ 2 := by
        rw [mul_pow, ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (4 * π ^ 2) * (ENNReal.ofReal (hsWeight 1 ξ) * ‖f ξ‖ₑ ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        gcongr
        simp only [hsWeight, pow_one]
        nlinarith [sq_nonneg ‖ξ‖, pi_pos, sq_nonneg π]

theorem freqTrInv_ae {g : Space → CSpace} (h1 : Integrable g volume) (h2 : MemLp g 2 volume) :
    (𝓕⁻ g) =ᵐ[volume] (freqTrL2.symm (toLpOrZero 2 g) : Space → CSpace) :=
  (freqTrL1L2.2 g (memLp_one_iff_integrable.2 h1) h2).symm

theorem memLp_realVec_freqTrInv {g : Space → CSpace} (h1 : Integrable g volume)
    (h2 : MemLp g 2 volume) : MemLp (fun x => realVec (𝓕⁻ g x)) 2 volume :=
  realVec.comp_memLp' ((Lp.memLp _).ae_eq (freqTrInv_ae h1 h2).symm)

end Breakdown.SmoothFlow.Internal.RegEmbed

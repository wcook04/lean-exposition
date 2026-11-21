import Breakdown.FracCert.WeakRegularParts
import Breakdown.FreqTr.NiceDense
import Breakdown.FreqTr.Realization
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.Uniqueness.RegPhysAuxBasic
import Breakdown.Uniqueness.RegPhysAuxPressure
import Breakdown.Uniqueness.RegPhysAuxSmooth
import Breakdown.Frac.RegPowerPhysPower
import Breakdown.Frac.TorusPlaneWave
import Breakdown.Frac.OpExports
import Breakdown.Uniqueness.RegEmbedAux
import Breakdown.FracCert.InverseSquare

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.SteadyCert

namespace WeakRegularInternal

theorem conjVec_invol (z : CSpace) : conjVec (conjVec z) = z := by
  ext i
  simp [conjVec]

def goodSet (f : Space → CSpace) : Set Space :=
  {ξ | f (-ξ) = conjVec (f ξ) ∧ ∑ i, ((ξ i : ℝ) : ℂ) * f ξ i = 0 ∧
    ∑ i, (((-ξ) i : ℝ) : ℂ) * f (-ξ) i = 0}

open Classical in
def cleanSymbol (f : Space → CSpace) (ξ : Space) : CSpace := if ξ ∈ goodSet f then f ξ else 0

theorem neg_mem_goodSet {f : Space → CSpace} {ξ : Space} (h : ξ ∈ goodSet f) : -ξ ∈ goodSet f := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h3, ?_⟩
  · rw [neg_neg, h1, conjVec_invol]
  · rw [neg_neg]; exact h2

theorem cleanSymbol_conjSym (f : Space → CSpace) (ξ : Space) :
    cleanSymbol f (-ξ) = conjVec (cleanSymbol f ξ) := by
  by_cases h : ξ ∈ goodSet f
  · simp only [cleanSymbol, if_pos h, if_pos (neg_mem_goodSet h)]
    exact h.1
  · have h' : -ξ ∉ goodSet f := fun h' => h (by simpa using neg_mem_goodSet h')
    simp only [cleanSymbol, if_neg h, if_neg h', map_zero]

theorem cleanSymbol_div (f : Space → CSpace) (ξ : Space) :
    ∑ i, ((ξ i : ℝ) : ℂ) * cleanSymbol f ξ i = 0 := by
  by_cases h : ξ ∈ goodSet f
  · simp only [cleanSymbol, if_pos h]
    exact h.2.1
  · simp [cleanSymbol, if_neg h]

theorem cleanSymbol_ae {f : Space → CSpace} (h : ∀ᵐ ξ ∂volume, ξ ∈ goodSet f) :
    cleanSymbol f =ᵐ[volume] f := by
  filter_upwards [h] with ξ hξ
  simp only [cleanSymbol, if_pos hξ]

theorem symbolX_ae (U : X) : ∀ᵐ ξ ∂volume,
    symbolX U (-ξ) = conjVec (symbolX U ξ) ∧ ∑ i, ((ξ i : ℝ) : ℂ) * symbolX U ξ i = 0 := by
  obtain ⟨hA, hB⟩ := Internal.NiceDense.sig_ae fieldOpRealized_holds U
  filter_upwards [hA, hB] with ξ h1 h2
  constructor
  · have e : (U : L2C) (-ξ) = conjVec ((U : L2C) ξ) := by
      rw [← h1, conjVec_invol]
    simp only [symbolX, norm_neg, e, map_smul]
  · by_cases hξ : ξ = 0
    · simp [hξ]
    · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
      have hv : freqVec ξ ≠ 0 := by
        intro h0
        apply hξ
        ext i
        have := congrArg (fun z : CSpace => (z i).re) h0
        simpa [freqVec, complexifyVec] using this
      simp only [longitudinal, smul_apply, ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at h2
      have hc : inner ℂ (freqVec ξ) ((U : L2C) ξ) = 0 := by
        rcases smul_eq_zero.1 h2 with h | h
        · exact absurd h (inv_ne_zero (pow_ne_zero 2 hn))
        · exact (smul_eq_zero.1 h).resolve_right hv
      have hs : ∑ i, ((ξ i : ℝ) : ℂ) * (U : L2C) ξ i = 0 := by
        rw [← hc]
        simp [PiLp.inner_apply, freqVec, complexifyVec, mul_comm]
      simp only [symbolX, PiLp.smul_apply, Complex.real_smul]
      rw [Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _, ← Finset.mul_sum, hs, mul_zero]

theorem goodSet_ae (U : X) : ∀ᵐ ξ ∂volume, ξ ∈ goodSet (symbolX U) := by
  have h := symbolX_ae U
  have hn : ∀ᵐ ξ ∂volume, symbolX U (-(-ξ)) = conjVec (symbolX U (-ξ)) ∧
      ∑ i, (((-ξ) i : ℝ) : ℂ) * symbolX U (-ξ) i = 0 :=
    (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae h
  filter_upwards [h, hn] with ξ h1 h2
  exact ⟨h1.1, h1.2, h2.2⟩

theorem physField_clean (U : X) : physField (cleanSymbol (symbolX U)) = physField (symbolX U) := by
  funext x
  simp only [physField]
  rw [Real.fourierInv_congr_ae (cleanSymbol_ae (goodSet_ae U)) x]

theorem moments_clean (U : X) (h : HasAllSymbolL1Moments (symbolX U)) :
    HasAllSymbolL1Moments (cleanSymbol (symbolX U)) := by
  intro j
  refine (h j).congr ?_
  filter_upwards [cleanSymbol_ae (goodSet_ae U)] with ξ hξ
  rw [hξ]

theorem aesm_symbolX (U : X) : AEStronglyMeasurable (symbolX U) volume := by
  have hc : Measurable (fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ)) := by fun_prop
  exact hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)

theorem memLp_clean (U : X) (h : HasAllSymbolL1Moments (symbolX U)) (k : ℕ) :
    MemLp (cleanSymbol (symbolX U)) 1 (weightL1Measure k) := by
  have hae := cleanSymbol_ae (goodSet_ae U)
  have hm : AEStronglyMeasurable (cleanSymbol (symbolX U)) volume :=
    (aesm_symbolX U).congr hae.symm
  rw [memLp_weight_iff hm]
  have hi := (moments_clean U h k).hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hi
  refine lintegral_congr fun ξ => ?_
  have h0 : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ k := by positivity
  rw [enorm_mul, Real.enorm_of_nonneg h0, enorm_norm]

theorem advection_congr {f g : Space → CSpace} (h : g =ᵐ[volume] f) :
    advectionSymbol g = advectionSymbol f := by
  funext ξ
  simp only [advectionSymbol, advectionBilin, convC]
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : ∀ᵐ η ∂(volume : Measure Space), g (ξ - η) = f (ξ - η) :=
    (Measure.measurePreserving_sub_left (volume : Measure Space) ξ).quasiMeasurePreserving.ae h
  refine integral_congr_ae ?_
  filter_upwards [h, hs] with η h1 h2
  rw [h1, h2]

theorem pressure_clean (U : X) :
    pressureSymbol (cleanSymbol (symbolX U)) = pressureSymbol (symbolX U) := by
  funext ξ
  simp only [pressureSymbol, advection_congr (cleanSymbol_ae (goodSet_ae U))]

theorem inverseTransform_smul_single (p : Space → ℂ) (x : Space) :
    𝓕⁻ (fun ξ => p ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) x =
      (𝓕⁻ p x) • EuclideanSpace.single (0 : Fin 3) (1 : ℂ) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  simp only [smul_smul]
  exact integral_smul_const _ _

def pressureField (U : X) (ξ : Space) : CSpace :=
  pressureSymbol (cleanSymbol (symbolX U)) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)

theorem contDiff_pressureField (U : X) (h : HasAllSymbolL1Moments (symbolX U)) :
    ContDiff ℝ ∞ (fun x : Space => 𝓕⁻ (pressureField U) x) := by
  have hsol : IsSolenoidalSymbol (cleanSymbol (symbolX U)) :=
    fun ξ => ⟨cleanSymbol_div _ ξ, cleanSymbol_conjSym _ ξ⟩
  have hc : ∀ k, MemLp (pressureField U) 1 (weightL1Measure k) :=
    memLp_pressureSymbol_single (memLp_clean U h) hsol
  have hC := contDiffOn_freqTrInv_curve (c := fun _ => pressureField U) one_pos
    (fun _ _ k => hc k) (fun k n => contDiffOn_const)
  have hi : ContDiff ℝ ∞ (fun x : Space => ((0 : ℝ), x)) := contDiff_const.prodMk contDiff_id
  have e : (fun x : Space => 𝓕⁻ (pressureField U) x) =
      (fun z : ℝ × Space => 𝓕⁻ ((fun _ : ℝ => pressureField U) z.1) z.2) ∘
        (fun x : Space => ((0 : ℝ), x)) := rfl
  rw [e, ← contDiffOn_univ]
  exact hC.comp hi.contDiffOn fun x _ => ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩

end WeakRegularInternal

open WeakRegularInternal in
theorem pressureSmooth_of (h1 : SymbolL1OfMomentsStatement) : PressureSmoothStatement := by
  intro U hM
  have hD := contDiff_pressureField U (h1 U hM).1
  have hP : profilePressure U = fun x => Complex.reCLM
      ((EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).restrictScalars ℝ (𝓕⁻ (pressureField U) x)) := by
    funext x
    have e : 𝓕⁻ (pressureField U) x =
        (𝓕⁻ (pressureSymbol (cleanSymbol (symbolX U))) x) • EuclideanSpace.single (0 : Fin 3) (1 : ℂ) :=
      inverseTransform_smul_single _ x
    simp only [ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, e,
      pressure_clean U, profilePressure, physScalar]
    simp
  rw [hP]
  exact Complex.reCLM.contDiff.comp
    (((EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hD)

namespace WeakRegularInternal

theorem norm_realVec_le' (z : CSpace) : ‖realVec z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have e : (realVec z) i = (z i).re := rfl
  rw [e, Real.norm_eq_abs, sq_abs]
  have h := Complex.abs_re_le_norm (z i)
  nlinarith [abs_nonneg (z i).re, sq_abs (z i).re]

theorem integrable_pairing {Θ : Space → Space} (hc : Continuous Θ)
    (hΘ : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume) (ψ : 𝓢(Space, CSpace)) :
    Integrable (fun y => inner ℝ (Θ y) (realVec (ψ y))) := by
  set C := 2 ^ 3 * (Finset.Iic ((3 : ℕ), (0 : ℕ))).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ
  have hb : ∀ y, (1 + ‖y‖) ^ 3 * ‖ψ y‖ ≤ C := fun y => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((3 : ℕ), (0 : ℕ))) (k := 3) (n := 0)
      le_rfl le_rfl ψ y
    rwa [norm_iteratedFDeriv_zero] at h
  have hw : MemLp (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume := by
    have hm : AEStronglyMeasurable (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) volume := by
      apply Measurable.aestronglyMeasurable; fun_prop
    rw [memLp_two_iff_integrable_sq hm]
    refine (integrable_one_add_norm (E := Space) (μ := volume) (r := 4) (by simp; norm_num)).congr
      (ae_of_all _ fun y => ?_)
    have hp : 0 < 1 + ‖y‖ := by positivity
    simp only
    rw [sq, ← Real.rpow_add hp]
    norm_num
  have hI := hΘ.norm.integrable_mul hw
  refine (hI.const_mul C).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact (hc.inner (realVec.continuous.comp ψ.continuous)).aestronglyMeasurable
  · have ht : 0 < 1 + ‖y‖ := by positivity
    have h1 : |inner ℝ (Θ y) (realVec (ψ y))| ≤ ‖Θ y‖ * ‖ψ y‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_realVec_le' _) (norm_nonneg _))
    have h2 : ‖ψ y‖ ≤ C / (1 + ‖y‖) ^ 3 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hb y]
    rw [Real.norm_eq_abs]
    refine h1.trans ?_
    simp only [Pi.mul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    rw [Real.rpow_neg ht.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have ha := norm_nonneg (Θ y)
    calc ‖Θ y‖ * ‖ψ y‖ ≤ ‖Θ y‖ * (C / (1 + ‖y‖) ^ 3) := mul_le_mul_of_nonneg_left h2 ha
      _ = C * ((1 + ‖y‖)⁻¹ * ‖Θ y‖ * ((1 + ‖y‖) ^ 2)⁻¹) := by field_simp

theorem longitudinal_conjSym (ξ : Space) (z : CSpace) :
    conjVec (longitudinal (-ξ) (conjVec z)) = longitudinal ξ z := by
  ext i
  simp [longitudinal, conjVec, freqVec, complexifyVec, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem sub_symField_projField {m : Space → CSpace} (hh : ∀ ξ, m (-ξ) = conjVec (m ξ)) (ξ : Space) :
    m ξ - Internal.NiceDense.symField (Internal.NiceDense.projField m) ξ = longitudinal ξ (m ξ) := by
  have e : conjVec (longitudinal (-ξ) (conjVec (m ξ))) = longitudinal ξ (m ξ) := longitudinal_conjSym ξ (m ξ)
  simp only [Internal.NiceDense.symField, Internal.NiceDense.projField, map_sub, hh, conjVec_invol]
  rw [e, ← two_smul ℝ (m ξ - longitudinal ξ (m ξ)), smul_smul]
  norm_num

theorem physField_of_rapid {s : Space → CSpace} (M : 𝓢(Space, CSpace)) (hM : ⇑M = s) :
    physField s = fun y => realVec ((𝓕⁻ M) y) := by
  funext y
  rw [physField, SchwartzMap.fourierInv_coe, hM]


theorem continuous_physField_of {h : Space → CSpace} (hh : Integrable h) : Continuous (physField h) := by
  have hm : MemLp h 1 volume := memLp_one_iff_integrable.2 hh
  have e : physField h = fun x => realVec ((Real.Lp.fourierTransformInv hm.toLp) x) := by
    funext x
    rw [Real.Lp.fourierTransformInv_toLp hm]
    rfl
  rw [e]
  exact realVec.continuous.comp (Real.Lp.fourierTransformInv hm.toLp).continuous

theorem continuous_axialTurn : Continuous axialTurn := by
  have e : axialTurn = fun y : Space => (-(y 1)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (y 0) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
    funext y
    ext i
    fin_cases i <;> simp [axialTurn]
  rw [e]
  fun_prop

theorem integrable_powerSymbol {α : ℝ} (hα : 0 < α) (hα2 : α < 3 / 2) {g : Space → CSpace}
    (hm : AEStronglyMeasurable g volume) (hi : Integrable (fun ξ => (1 + ‖ξ‖) ^ 3 * ‖g ξ‖)) :
    Integrable (powerSymbol α g) := by
  refine (hi.const_mul ((2 * π) ^ 3)).mono' ?_ (ae_of_all _ fun ξ => ?_)
  · exact (Complex.measurable_ofReal.comp
      (by fun_prop : Measurable fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α))).aestronglyMeasurable.smul hm
  · have h0 : 0 ≤ 2 * π * ‖ξ‖ := by positivity
    rw [powerSymbol, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : 1 ≤ 2 * π * (1 + ‖ξ‖) := by nlinarith [Real.pi_gt_three, norm_nonneg ξ]
    have h1 : (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 := by
      calc (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π * (1 + ‖ξ‖)) ^ (2 * α) :=
            Real.rpow_le_rpow h0 (by nlinarith [Real.pi_gt_three]) (by linarith)
        _ ≤ (2 * π * (1 + ‖ξ‖)) ^ ((3 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb (by push_cast; linarith)
        _ = (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 := by rw [Real.rpow_natCast, mul_pow]
    calc (2 * π * ‖ξ‖) ^ (2 * α) * ‖g ξ‖ ≤ (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 * ‖g ξ‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (2 * π) ^ 3 * ((1 + ‖ξ‖) ^ 3 * ‖g ξ‖) := by ring


theorem norm_axialTurn_le (y : Space) : ‖axialTurn y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.sum_univ_three]
  simp [axialTurn]
  nlinarith [sq_nonneg (y 2)]


theorem memLp_of_homNormSq {f : Space → CSpace} (hm : AEStronglyMeasurable f volume) (k : ℕ)
    (h : homNormSq k f < ⊤) : MemLp (fun ξ => (‖ξ‖ ^ k : ℝ) • f ξ) 2 volume := by
  have hm' : AEStronglyMeasurable (fun ξ => (‖ξ‖ ^ k : ℝ) • f ξ) volume :=
    (by fun_prop : Continuous fun ξ : Space => ‖ξ‖ ^ k).aestronglyMeasurable.smul hm
  rw [memLp_two_iff_integrable_sq_norm hm']
  have hA : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖f ξ‖ₑ ^ 2) volume :=
    (by fun_prop : Measurable fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * k))).aemeasurable.mul
      (hm.enorm.pow_const 2)
  refine (integrable_toReal_of_lintegral_ne_top hA h.ne).congr (ae_of_all _ fun ξ => ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ (2 * k)),
    ENNReal.toReal_pow, toReal_enorm, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ k)]
  ring

theorem rpow_le_add {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    r ^ s ≤ r ^ (1 : ℕ) + r ^ (3 : ℕ) := by
  rcases hr.eq_or_lt with h | h
  · subst h; rw [Real.zero_rpow (by linarith)]; simp
  rcases le_total r 1 with hle | hle
  · have := Real.rpow_le_rpow_of_exponent_ge h hle h1
    rw [Real.rpow_one] at this
    have : 0 ≤ r ^ (3 : ℕ) := by positivity
    simp only [pow_one]; linarith
  · have := Real.rpow_le_rpow_of_exponent_le hle h3
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have : 0 ≤ r ^ (1 : ℕ) := by positivity
    linarith


theorem opNorm_le_sum_basis (L : Space →L[ℝ] Space) : ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ i : Fin 3, v i • unitVector i := by
    ext j
    fin_cases j <;> simp [unitVector, Fin.sum_univ_three]
  have hle : ∀ i : Fin 3, |v i| ≤ ‖v‖ := fun i => by
    have := PiLp.norm_apply_le v i
    simpa [Real.norm_eq_abs] using this
  calc ‖L v‖ = ‖∑ i : Fin 3, v i • L (unitVector i)‖ := by
        conv_lhs => rw [hv]
        simp [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • L (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖L (unitVector i)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hle i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (unitVector i)‖) * ‖v‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _


theorem weakGradient_of_smooth {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    IsWeakGradientOf v (fderiv ℝ v) := by
  intro φ hφ j
  obtain ⟨hs, hc⟩ := hφ
  have hφ1 : Differentiable ℝ φ := hs.differentiable (by simp)
  have hv1 : Differentiable ℝ v := hv.differentiable (by simp)
  have cφ' : Continuous fun y => fderiv ℝ φ y (unitVector j) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have cv' : Continuous fun y => fderiv ℝ v y (unitVector j) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • v y) :=
    (cφ'.smul hv.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right)
  have i2 : Integrable (fun y => φ y • fderiv ℝ v y (unitVector j)) :=
    (hs.continuous.smul cv').integrable_of_hasCompactSupport hc.smul_right
  have i3 : Integrable (fun y => φ y • v y) :=
    (hs.continuous.smul hv.continuous).integrable_of_hasCompactSupport hc.smul_right
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable i1 i2 i3
    (fun y _ => hφ1 y) (fun y _ => hv1 y)
  rw [h, neg_neg]

end WeakRegularInternal

open WeakRegularInternal in
theorem residualContinuous_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement)
    (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (U : X) (hM : HasAllMoments U) :
    Continuous (profileResidual α a U) := by
  have hwm := (h1 U hM).1
  have hV : ContDiff ℝ ∞ (physField (symbolX U)) := by
    rw [← physField_clean U]
    exact (h2 _ (moments_clean U hwm) (cleanSymbol_conjSym _)).1
  have hP : ContDiff ℝ ∞ (profilePressure U) := pressureSmooth_of h1 U hM
  have hD : Continuous (fderiv ℝ (physField (symbolX U))) := hV.continuous_fderiv (by simp)
  have hDP : Continuous (fderiv ℝ (profilePressure U)) := hP.continuous_fderiv (by simp)
  have hF : fractionalPowerAt α (physField (symbolX U)) =
      physField (powerSymbol α (cleanSymbol (symbolX U))) := by
    funext x
    rw [← physField_clean U]
    exact powerPhysPower_of α hα (by linarith)
      (Periodic.planeWaveEigen_of α hα (by linarith) (symbolScalar normalizer) normalizer) _
      (memLp_clean U hwm 3) x
  have hFc : Continuous (fractionalPowerAt α (physField (symbolX U))) := by
    rw [hF]
    exact continuous_physField_of (integrable_powerSymbol (by linarith) (by linarith)
      ((aesm_symbolX U).congr (cleanSymbol_ae (goodSet_ae U)).symm) (moments_clean U hwm 3))
  unfold profileResidual rotatingProfileResidual advectionAt gradientAt
  have hc := hV.continuous
  refine ((((Continuous.add ?_ ?_).add ?_).add ?_).add ?_).add ?_
  · have h := hc
    fun_prop
  · have h := hD.clm_apply continuous_id
    fun_prop
  · have h := hD.clm_apply continuous_axialTurn
    have h' := continuous_axialTurn.comp hc
    fun_prop
  · have h := hFc
    fun_prop
  · exact hD.clm_apply hc
  · exact continuous_finsetSum _ fun i _ => (hDP.clm_apply continuous_const).smul continuous_const

theorem residualGrowth_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement)
    (hW : ResidualWeightedStatement) : ResidualGrowthStatement := fun α hα hα2 a U hM =>
  ⟨residualContinuous_of h1 h2 α hα hα2 a U hM, hW α hα hα2 a U hM⟩

open WeakRegularInternal in
theorem residualAnnulus_of (h5 : ResidualGrowthStatement) (hA : ResidualNiceStatement)
    (hB : ResidualGradientStatement) : ResidualAnnulusStatement := by
  intro α hα hα2 a U hW hM m hh hsm hcs hr0
  obtain ⟨r, hr, h0⟩ := hr0
  obtain ⟨hc, hL⟩ := h5 α hα hα2 a U hM
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ ξ, R ≤ ‖ξ‖ → m ξ = 0 := by
    obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R + 1, fun ξ hξ => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    have := hR h
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  obtain ⟨hp, -⟩ := Internal.NiceDense.nice_symField_projField hsm hr h0 hR
  set p := Internal.NiceDense.symField (Internal.NiceDense.projField m) with hpdef
  have hq : ∀ ξ, m ξ - p ξ = longitudinal ξ (m ξ) := sub_symField_projField hh
  set q : Space → CSpace := fun ξ => m ξ - p ξ with hqdef
  have hqh : ∀ ξ, q (-ξ) = conjVec (q ξ) := by
    intro ξ
    simp only [q, map_sub, hh, hp.2.2.2.1]
  have hqs : ContDiff ℝ ∞ q := hsm.sub hp.1
  have hqc : HasCompactSupport q := hcs.sub hp.2.1
  have hq0 : ∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → q ξ = 0 :=
    ⟨r, hr, fun ξ h => by simp only [q]; rw [hq, h0 ξ h, map_zero]⟩
  have hqf : ∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ := by
    refine ⟨fun ξ => (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (freqVec ξ) (m ξ), fun ξ => ?_⟩
    simp only [q]
    rw [hq]
    ext i
    simp [longitudinal]
    ring
  let Mp := hp.2.1.toSchwartzMap hp.1
  let Mq := hqc.toSchwartzMap hqs
  have ep : physField p = fun y => realVec ((𝓕⁻ Mp) y) := physField_of_rapid Mp rfl
  have eq' : physField q = fun y => realVec ((𝓕⁻ Mq) y) := physField_of_rapid Mq rfl
  have em : physField m = fun y => realVec ((𝓕⁻ (Mp + Mq)) y) := by
    refine physField_of_rapid (Mp + Mq) ?_
    funext ξ
    show p ξ + (m ξ - p ξ) = m ξ
    abel
  have hsplit : ∀ y, physField m y = physField p y + physField q y := by
    intro y
    rw [em, ep, eq']
    simp only [FourierTransform.fourierInv_add, add_apply, map_add]
  have i1 : Integrable (fun y => inner ℝ (profileResidual α a U y) (physField p y)) := by
    rw [ep]; exact integrable_pairing hc hL _
  have i2 : Integrable (fun y => inner ℝ (profileResidual α a U y) (physField q y)) := by
    rw [eq']; exact integrable_pairing hc hL _
  have e1 : ∫ y, inner ℝ (profileResidual α a U y) (physField p y) = 0 :=
    hA α hα hα2 a U hW hM (niceField p) ⟨p, hp, rfl⟩
  have e2 := hB α hα hα2 a U hM q hqh hqs hqc hq0 hqf
  simp_rw [hsplit, inner_add_right]
  rw [integral_add i1 i2, e1, e2, add_zero]

open WeakRegularInternal in
theorem residualWeighted_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement)
    (t1 : VelocityInverseWeightStatement) (t2 : VelocityGradientSquareStatement)
    (t3 : PowerSquareStatement) (t4 : AdvectionSquareStatement)
    (t5 : PressureGradientSquareStatement) : ResidualWeightedStatement := by
  intro α hα hα2 a U hM
  have hc := residualContinuous_of h1 h2 α hα hα2 a U hM
  set V := physField (symbolX U) with hVdef
  have A1 := t1 U hM
  have A2 := t2 U hM
  have A3 := t3 α hα hα2 U hM
  have A4 := t4 U hM
  have A5 := t5 U hM
  set c0 := |1 - 1 / (2 * α)| + |1 / (2 * α)| + 2 * |a|
  have S : MemLp (fun y => (c0 * ‖(1 + ‖y‖)⁻¹ • V y‖ + (|1 / (2 * α)| + |a|) * ‖fderiv ℝ V y‖) +
      (‖fractionalPowerAt α V y‖ + ‖advectionAt V y‖ + ‖gradientAt (profilePressure U) y‖)) 2 volume :=
    ((A1.norm.const_mul c0).add (A2.const_mul _)).add ((A3.norm.add A4.norm).add A5.norm)
  have hinv : Continuous (fun y : Space => (1 + ‖y‖)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun y => by positivity)
  refine S.of_le (hinv.smul hc).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have ht0 : 0 < (1 + ‖y‖)⁻¹ := by positivity
  have hty : (1 + ‖y‖)⁻¹ * ‖y‖ ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity)]; linarith
  have ht1 : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
  set t := (1 + ‖y‖)⁻¹ with htdef
  set D := fderiv ℝ V y
  have eV : ‖t • V y‖ = t * ‖V y‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
  have hD1 : ‖D y‖ ≤ ‖D‖ * ‖y‖ := D.le_opNorm y
  have hD2 : ‖D (axialTurn y)‖ ≤ ‖D‖ * ‖y‖ :=
    (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_axialTurn_le y) (norm_nonneg _))
  have hT : ‖axialTurn (V y)‖ ≤ ‖V y‖ := norm_axialTurn_le _
  have hk : t * (‖D‖ * ‖y‖) ≤ ‖D‖ := by
    have := mul_le_mul_of_nonneg_left hty (norm_nonneg D)
    nlinarith
  set F := fractionalPowerAt α V y
  set Ad := advectionAt V y
  set G := gradientAt (profilePressure U) y
  have hΘ : profileResidual α a U y = (1 - 1 / (2 * α)) • V y + (1 / (2 * α)) • D y
      + a • (D (axialTurn y) - axialTurn (V y)) + (1 : ℝ) • F + Ad + G := rfl
  have n1 : ‖(1 - 1 / (2 * α)) • V y‖ = |1 - 1 / (2 * α)| * ‖V y‖ := by rw [norm_smul, Real.norm_eq_abs]
  have n2 : ‖(1 / (2 * α)) • D y‖ = |1 / (2 * α)| * ‖D y‖ := by rw [norm_smul, Real.norm_eq_abs]
  have n3 : ‖a • (D (axialTurn y) - axialTurn (V y))‖ ≤ |a| * (‖D‖ * ‖y‖ + ‖V y‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hD2 hT)) (abs_nonneg a)
  have n4 : ‖(1 : ℝ) • F‖ = ‖F‖ := by rw [one_smul]
  have hsum : ‖profileResidual α a U y‖ ≤ |1 - 1 / (2 * α)| * ‖V y‖ + |1 / (2 * α)| * (‖D‖ * ‖y‖) +
      |a| * (‖D‖ * ‖y‖ + ‖V y‖) + ‖F‖ + ‖Ad‖ + ‖G‖ := by
    rw [hΘ]
    have e1 := norm_add_le ((1 - 1 / (2 * α)) • V y + (1 / (2 * α)) • D y
      + a • (D (axialTurn y) - axialTurn (V y)) + (1 : ℝ) • F + Ad) G
    have e2 := norm_add_le ((1 - 1 / (2 * α)) • V y + (1 / (2 * α)) • D y
      + a • (D (axialTurn y) - axialTurn (V y)) + (1 : ℝ) • F) Ad
    have e3 := norm_add_le ((1 - 1 / (2 * α)) • V y + (1 / (2 * α)) • D y
      + a • (D (axialTurn y) - axialTurn (V y))) ((1 : ℝ) • F)
    have e4 := norm_add_le ((1 - 1 / (2 * α)) • V y + (1 / (2 * α)) • D y)
      (a • (D (axialTurn y) - axialTurn (V y)))
    have e5 := norm_add_le ((1 - 1 / (2 * α)) • V y) ((1 / (2 * α)) • D y)
    have m2 : |1 / (2 * α)| * ‖D y‖ ≤ |1 / (2 * α)| * (‖D‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left hD1 (abs_nonneg _)
    linarith
  rw [norm_smul, Real.norm_of_nonneg ht0.le, Real.norm_of_nonneg (by positivity)]
  have hF0 := norm_nonneg F
  have hA0 := norm_nonneg Ad
  have hG0 := norm_nonneg G
  have hVpos := norm_nonneg (V y)
  have hD0 := norm_nonneg D
  have hy0 := norm_nonneg y
  have ha := abs_nonneg a
  have hb := abs_nonneg (1 / (2 * α))
  have hc1 := abs_nonneg (1 - 1 / (2 * α))
  calc t * ‖profileResidual α a U y‖
      ≤ t * (|1 - 1 / (2 * α)| * ‖V y‖ + |1 / (2 * α)| * (‖D‖ * ‖y‖) +
        |a| * (‖D‖ * ‖y‖ + ‖V y‖) + ‖F‖ + ‖Ad‖ + ‖G‖) := mul_le_mul_of_nonneg_left hsum ht0.le
    _ = (|1 - 1 / (2 * α)| + |a|) * (t * ‖V y‖) + (|1 / (2 * α)| + |a|) * (t * (‖D‖ * ‖y‖)) +
        t * (‖F‖ + ‖Ad‖ + ‖G‖) := by ring
    _ ≤ c0 * (t * ‖V y‖) + (|1 / (2 * α)| + |a|) * ‖D‖ + (‖F‖ + ‖Ad‖ + ‖G‖) := by
        gcongr
        · simp only [c0]; linarith
        · calc t * (‖F‖ + ‖Ad‖ + ‖G‖) ≤ 1 * (‖F‖ + ‖Ad‖ + ‖G‖) :=
                mul_le_mul_of_nonneg_right ht1 (by positivity)
            _ = _ := one_mul _
    _ = _ := by rw [eV]

open WeakRegularInternal in
theorem powerSquare_of (h1 : SymbolL1OfMomentsStatement) : PowerSquareStatement := by
  intro α hα hα2 U hM
  have hwm := (h1 U hM).1
  have hF : fractionalPowerAt α (physField (symbolX U)) =
      physField (powerSymbol α (cleanSymbol (symbolX U))) := by
    funext x
    rw [← physField_clean U]
    exact powerPhysPower_of α hα (by linarith)
      (Periodic.planeWaveEigen_of α hα (by linarith) (symbolScalar normalizer) normalizer) _
      (memLp_clean U hwm 3) x
  have hae := cleanSymbol_ae (goodSet_ae U)
  have hmg : AEStronglyMeasurable (cleanSymbol (symbolX U)) volume := (aesm_symbolX U).congr hae.symm
  have hI := integrable_powerSymbol (α := α) (by linarith) (by linarith) hmg (moments_clean U hwm 3)
  have M1 := memLp_of_homNormSq hmg 1 (by rw [homNormSq, lintegral_congr_ae (by filter_upwards [hae] with ξ h; rw [h])]; exact hM 1 le_rfl)
  have M3 := memLp_of_homNormSq hmg 3 (by rw [homNormSq, lintegral_congr_ae (by filter_upwards [hae] with ξ h; rw [h])]; exact hM 3 (by norm_num))
  have hL2 : MemLp (powerSymbol α (cleanSymbol (symbolX U))) 2 volume := by
    refine ((M1.norm.add M3.norm).const_mul ((2 * π) ^ (3 : ℕ))).of_le hI.aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    have h0 : 0 ≤ 2 * π * ‖ξ‖ := by positivity
    have hp : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    rw [powerSymbol, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.mul_rpow (by positivity) (norm_nonneg _)]
    simp only [Pi.add_apply, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 1),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 3)]
    have e1 : (2 * π) ^ (2 * α) ≤ (2 * π) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hp (by push_cast; linarith)
    have e2 := rpow_le_add (norm_nonneg ξ) (s := 2 * α) (by linarith) (by linarith)
    have hg := norm_nonneg (cleanSymbol (symbolX U) ξ)
    have hq : 0 ≤ ‖ξ‖ ^ (2 * α) := by positivity
    calc (2 * π) ^ (2 * α) * ‖ξ‖ ^ (2 * α) * ‖cleanSymbol (symbolX U) ξ‖
        ≤ (2 * π) ^ (3 : ℕ) * (‖ξ‖ ^ (1 : ℕ) + ‖ξ‖ ^ (3 : ℕ)) * ‖cleanSymbol (symbolX U) ξ‖ := by
          gcongr
      _ = _ := by rw [Real.norm_of_nonneg (by positivity)]; ring
  rw [hF]
  exact Breakdown.SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv hI hL2

open WeakRegularInternal in
theorem advectionSquare_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement)
    (t2 : VelocityGradientSquareStatement) : AdvectionSquareStatement := by
  intro U hM
  have hwm := (h1 U hM).1
  obtain ⟨hV, hB⟩ := h2 _ (moments_clean U hwm) (cleanSymbol_conjSym _)
  rw [physField_clean U] at hV hB
  obtain ⟨C, hC⟩ := hB 0
  have hD : Continuous (fderiv ℝ (physField (symbolX U))) := hV.continuous_fderiv (by simp)
  refine ((t2 U hM).const_mul C).of_le (hD.clm_apply hV.continuous).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  have hy : ‖physField (symbolX U) y‖ ≤ C := by
    have := hC y
    rwa [norm_iteratedFDeriv_zero] at this
  rw [advectionAt, Real.norm_eq_abs, abs_mul, abs_norm]
  calc ‖fderiv ℝ (physField (symbolX U)) y (physField (symbolX U) y)‖
      ≤ ‖fderiv ℝ (physField (symbolX U)) y‖ * ‖physField (symbolX U) y‖ := (fderiv ℝ _ y).le_opNorm _
    _ ≤ ‖fderiv ℝ (physField (symbolX U)) y‖ * C := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = |C| * ‖fderiv ℝ (physField (symbolX U)) y‖ := by
        rw [abs_of_nonneg ((norm_nonneg _).trans hy), mul_comm]

open WeakRegularInternal in
theorem velocityGradientSquare_of (h1 : SymbolL1OfMomentsStatement) : VelocityGradientSquareStatement := by
  intro U hM
  have hwm := (h1 U hM).1
  have hae := cleanSymbol_ae (goodSet_ae U)
  set g := cleanSymbol (symbolX U)
  have hmg : AEStronglyMeasurable g volume := (aesm_symbolX U).congr hae.symm
  have M1 := memLp_of_homNormSq hmg 1
    (by rw [homNormSq, lintegral_congr_ae (by filter_upwards [hae] with ξ h; rw [h])]; exact hM 1 le_rfl)
  have hI1 := moments_clean U hwm 1
  have hpart : ∀ i : Fin 3, MemLp (fun y => fderiv ℝ (physField g) y (unitVector i)) 2 volume := by
    intro i
    have e : (fun y => fderiv ℝ (physField g) y (unitVector i)) = fun y =>
        realVec (𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ)) • g ξ) y) := by
      funext y
      exact fderiv_physField_apply (memLp_clean U hwm 1) y (unitVector i)
    have hb : ∀ ξ : Space, ‖(2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ)) • g ξ‖ ≤
        2 * π * (‖ξ‖ * ‖g ξ‖) := fun ξ => by
      rw [norm_smul]
      have h1' : ‖(2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ))‖ ≤ 2 * π * ‖ξ‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
          Complex.norm_ofNat, Real.norm_of_nonneg pi_pos.le, mul_one]
        have := abs_real_inner_le_norm ξ (unitVector i)
        have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
        rw [hu, mul_one] at this
        rw [Real.norm_eq_abs]
        nlinarith [pi_pos]
      calc _ ≤ 2 * π * ‖ξ‖ * ‖g ξ‖ := mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
        _ = _ := by ring
    have hm : AEStronglyMeasurable (fun ξ =>
        (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ)) • g ξ) volume :=
      (by fun_prop : Continuous fun ξ : Space =>
        (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ))).aestronglyMeasurable.smul hmg
    have hI : Integrable (fun ξ =>
        (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ)) • g ξ) :=
      (hI1.const_mul (2 * π)).mono' hm (ae_of_all _ fun ξ => (hb ξ).trans (by
        have : ‖ξ‖ * ‖g ξ‖ ≤ (1 + ‖ξ‖) ^ 1 * ‖g ξ‖ :=
          mul_le_mul_of_nonneg_right (by simp) (norm_nonneg _)
        nlinarith [pi_pos]))
    have hL : MemLp (fun ξ =>
        (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ (unitVector i) : ℝ) : ℂ)) • g ξ) 2 volume :=
      (M1.norm.const_mul (2 * π)).of_le hm (ae_of_all _ fun ξ => by
        refine (hb ξ).trans (le_of_eq ?_)
        rw [norm_mul, norm_norm, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 1),
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π), pow_one])
    rw [e]
    exact Breakdown.SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv hI hL
  have hS : MemLp (fun y => ∑ i : Fin 3, ‖fderiv ℝ (physField g) y (unitVector i)‖) 2 volume :=
    memLp_finsetSum _ fun i _ => (hpart i).norm
  rw [← physField_clean U]
  refine hS.of_le (measurable_fderiv ℝ (physField g)).norm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [norm_norm, Real.norm_of_nonneg (by positivity)]
  exact opNorm_le_sum_basis _

open WeakRegularInternal in
theorem velocityInverseWeight_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement) :
    VelocityInverseWeightStatement := by
  intro U hM
  obtain ⟨hwm, hvel⟩ := h1 U hM
  have hV : ContDiff ℝ ∞ (physField (symbolX U)) := by
    rw [← physField_clean U]
    exact (h2 _ (moments_clean U hwm) (cleanSymbol_conjSym _)).1
  have h6 : MemLp (physField (symbolX U)) 6 volume := (Lp.memLp (velocity U)).ae_eq hvel
  have hD := velocityGradientSquare_of h1 U hM
  have hm : AEStronglyMeasurable (fun y => ‖fderiv ℝ (physField (symbolX U)) y‖) volume :=
    hD.aestronglyMeasurable
  have hsq := (memLp_two_iff_integrable_sq hm).1 hD
  have hE : Integrable (fun y => entrySq (fderiv ℝ (physField (symbolX U)) y)) := by
    refine (hsq.const_mul 3).mono' ?_ (ae_of_all _ fun y => ?_)
    · simp only [entrySq]
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (((hV.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2).aestronglyMeasurable
    · have hb : ∀ i : Fin 3, ‖fderiv ℝ (physField (symbolX U)) y (unitVector i)‖ ^ 2 ≤
          ‖fderiv ℝ (physField (symbolX U)) y‖ ^ 2 := fun i => by
        have := (fderiv ℝ (physField (symbolX U)) y).le_opNorm (unitVector i)
        have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
        rw [hu, mul_one] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      have hs : 0 ≤ entrySq (fderiv ℝ (physField (symbolX U)) y) :=
        Finset.sum_nonneg fun i _ => by positivity
      rw [Real.norm_of_nonneg hs, entrySq, Fin.sum_univ_three]
      linarith [hb 0, hb 1, hb 2]
  obtain ⟨hi, -⟩ := inverseSquareBound _ _ hV.continuous.aestronglyMeasurable h6 hE
    (weakGradient_of_smooth hV)
  have hcw : Continuous (fun y => (1 + ‖y‖)⁻¹ • physField (symbolX U) y) :=
    (Continuous.inv₀ (f := fun y : Space => 1 + ‖y‖) (by fun_prop) (fun y => by positivity)).smul
      hV.continuous
  rw [memLp_two_iff_integrable_sq_norm hcw.aestronglyMeasurable]
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]; simp
  refine hi.mono' (hcw.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [hne] with y hy
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_of_nonneg (by positivity), mul_pow,
    inv_pow, inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hy0.le (by linarith) 2)

open WeakRegularInternal in
theorem weakProfileRegular_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement)
    (h3 : LowFrequencyRemovalStatement) (t5 : PressureGradientSquareStatement)
    (h6 : ResidualNiceStatement) (h7 : ResidualGradientStatement) :
    WeakProfileRegularStatement := by
  have t1 := velocityInverseWeight_of h1 h2
  have t2 := velocityGradientSquare_of h1
  have h5 := residualGrowth_of h1 h2 (residualWeighted_of h1 h2 t1 t2 (powerSquare_of h1)
    (advectionSquare_of h1 h2 t2) t5)
  intro α hα hα2 a U hW hM
  have hwm := (h1 U hM).1
  have hphys := physField_clean U
  refine ⟨?_, ?_, profilePressure U, pressureSmooth_of h1 U hM, ?_⟩
  · rw [← hphys]
    exact (h2 _ (moments_clean U hwm) (cleanSymbol_conjSym _)).1
  · intro y
    rw [← hphys]
    exact divergenceAt_physField (memLp_clean U hwm 1) (cleanSymbol_div _) y
  · obtain ⟨hc, hL⟩ := h5 α hα hα2 a U hM
    exact h3 _ hc hL (fun m hm1 hm2 hm3 hm4 =>
      residualAnnulus_of h5 h6 h7 α hα hα2 a U hW hM m hm1 hm2 hm3 hm4)

end Breakdown.FracCert

import Breakdown.FracCert.StWeakRegular
import Breakdown.Uniqueness.RegPhysAuxBasic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace WeakLowFrequency.Internal

def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def cbump (ξ : Space) : ℂ := ((bump ξ : ℝ) : ℂ)

theorem cbump_contDiff : ContDiff ℝ ∞ cbump :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem cbump_hasCompactSupport : HasCompactSupport cbump :=
  bump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem cbump_continuous : Continuous cbump := cbump_contDiff.continuous

theorem cbump_integrable : Integrable cbump :=
  cbump_continuous.integrable_of_hasCompactSupport cbump_hasCompactSupport

theorem cbump_neg (ξ : Space) : cbump (-ξ) = cbump ξ := by
  simp [cbump, bump.neg]

theorem cbump_zero : cbump 0 = 1 := by
  simp [cbump, bump.one_of_mem_closedBall (Metric.mem_closedBall_self (zero_le_one))]

theorem cbump_eq_one {ξ : Space} (h : ‖ξ‖ ≤ 1) : cbump ξ = 1 := by
  have : ξ ∈ Metric.closedBall (0 : Space) bump.rIn := by simpa [bump] using h
  simp [cbump, bump.one_of_mem_closedBall this]

def bumpTest : SchwartzMap Space ℂ := cbump_hasCompactSupport.toSchwartzMap cbump_contDiff

def bumpTestInv : SchwartzMap Space ℂ := 𝓕⁻ bumpTest

def bumpTestFwd : SchwartzMap Space ℂ := 𝓕 bumpTest

def kern (z : Space) : ℂ := 𝓕⁻ cbump z

theorem kern_eq_bumpTest : kern = ⇑bumpTestInv := by
  rw [bumpTestInv, SchwartzMap.fourierInv_coe]
  rfl

theorem kern_integrable : Integrable kern := by
  rw [kern_eq_bumpTest]; exact bumpTestInv.integrable

theorem kern_continuous : Continuous kern := by
  rw [kern_eq_bumpTest]; exact bumpTestInv.continuous

theorem kern_apply (z : Space) : kern z = ∫ v, (𝐞 (inner ℝ v z) : ℂ) * cbump v := by
  simp only [kern, Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]

theorem kern_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖kern z‖ ≤ C * ((1 + ‖z‖) ^ 4)⁻¹ := by
  refine ⟨2 ^ 4 * (Finset.Iic (4, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) bumpTestInv,
    by positivity, fun z => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 0)) (k := 4) (n := 0)
    le_rfl le_rfl bumpTestInv z
  rw [norm_iteratedFDeriv_zero, ← kern_eq_bumpTest] at h
  have hp : 0 < (1 + ‖z‖) ^ 4 := by positivity
  rw [le_mul_inv_iff₀ hp, mul_comm]
  exact h

theorem integral_kern : ∫ z, kern z = 1 := by
  have hF : Integrable (𝓕 cbump) := by
    have : 𝓕 cbump = ⇑bumpTestFwd := by rw [bumpTestFwd, SchwartzMap.fourier_coe]; rfl
    rw [this]; exact bumpTestFwd.integrable
  have h := congrFun (cbump_continuous.fourier_fourierInv_eq cbump_integrable hF) 0
  rw [Real.fourier_eq] at h
  simpa [kern, cbump_zero] using h

def rk (z : Space) : ℝ := (kern z).re

theorem rk_continuous : Continuous rk := Complex.continuous_re.comp kern_continuous

theorem rk_integrable : Integrable rk := kern_integrable.re

theorem integral_rk : ∫ z, rk z = 1 := by
  unfold rk
  have h := integral_re kern_integrable
  rw [integral_kern] at h
  simpa using h

theorem rk_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |rk z| ≤ C * ((1 + ‖z‖) ^ 4)⁻¹ := by
  obtain ⟨C, hC, h⟩ := kern_decay
  exact ⟨C, hC, fun z => (Complex.abs_re_le_norm _).trans (h z)⟩

def wave (w η : Space) : ℂ := (𝐞 (inner ℝ η w) : ℂ) * cbump η

theorem kern_eq_wave (w : Space) : kern w = ∫ η, wave w η := kern_apply w

def sym (t : ℝ) (x₀ : Space) (j : Fin 3) (ξ : Space) : CSpace :=
  ((𝐞 (-(inner ℝ ξ x₀)) : ℂ) * cbump (t • ξ)) • EuclideanSpace.single j (1 : ℂ)

def prof (t : ℝ) (x₀ y : Space) : ℝ := (t ^ 3)⁻¹ * rk (t⁻¹ • (y - x₀))

theorem char_mul (a b : ℝ) : (𝐞 a : ℂ) * (𝐞 b : ℂ) = 𝐞 (a + b) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem scaling {t : ℝ} (ht : 0 < t) (x₀ y : Space) :
    ∫ ξ, (𝐞 (inner ℝ ξ y) : ℂ) * ((𝐞 (-(inner ℝ ξ x₀)) : ℂ) * cbump (t • ξ)) =
      (((t ^ 3)⁻¹ : ℝ) : ℂ) * kern (t⁻¹ • (y - x₀)) := by
  have h1 : ∀ ξ : Space, (𝐞 (inner ℝ ξ y) : ℂ) * ((𝐞 (-(inner ℝ ξ x₀)) : ℂ) * cbump (t • ξ)) =
      wave (t⁻¹ • (y - x₀)) (t • ξ) := by
    intro ξ
    rw [wave, ← mul_assoc, char_mul, real_inner_smul_left, real_inner_smul_right, inner_sub_right,
      ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul, sub_eq_add_neg]
  rw [integral_congr_ae (Eventually.of_forall h1), Measure.integral_comp_smul, ← kern_eq_wave,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity), Complex.real_smul]

theorem realVec_smul_single (c : ℂ) (j : Fin 3) :
    realVec (c • EuclideanSpace.single j (1 : ℂ)) = c.re • EuclideanSpace.single j (1 : ℝ) := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [realVec]
  · simp [realVec, hij]

theorem physField_sym {t : ℝ} (ht : 0 < t) (x₀ : Space) (j : Fin 3) (y : Space) :
    physField (sym t x₀ j) y = prof t x₀ y • EuclideanSpace.single j (1 : ℝ) := by
  simp only [physField, Real.fourierInv_eq, sym, Circle.smul_def, smul_smul]
  rw [integral_smul_const, scaling ht, realVec_smul_single, Complex.re_ofReal_mul]
  rfl

theorem star_char (a : ℝ) : star (𝐞 a : ℂ) = 𝐞 (-a) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

theorem sym_conjSym (t : ℝ) (x₀ : Space) (j : Fin 3) (ξ : Space) :
    sym t x₀ j (-ξ) = conjVec (sym t x₀ j ξ) := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [sym, conjVec, smul_neg, cbump, inner_neg_left, bump.neg]
  · simp [sym, conjVec, hij]

theorem char_contDiff (x₀ : Space) :
    ContDiff ℝ ∞ (fun ξ : Space => (𝐞 (-(inner ℝ ξ x₀)) : ℂ)) := by
  simp only [Real.fourierChar_apply]
  have h : ContDiff ℝ ∞ (fun ξ : Space => ((2 * π * -(inner ℝ ξ x₀) : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((contDiff_id.inner ℝ contDiff_const).neg) :
        ContDiff ℝ ∞ (fun ξ : Space => 2 * π * -(inner ℝ ξ x₀)))).mul contDiff_const
  exact Complex.contDiff_exp.comp h

theorem sym_contDiff (t : ℝ) (x₀ : Space) (j : Fin 3) : ContDiff ℝ ∞ (sym t x₀ j) := by
  unfold sym
  exact ((char_contDiff x₀).mul (cbump_contDiff.comp (contDiff_const_smul t))).smul contDiff_const

theorem sym_hasCompactSupport {t : ℝ} (ht : 0 < t) (x₀ : Space) (j : Fin 3) :
    HasCompactSupport (sym t x₀ j) := by
  refine HasCompactSupport.mono (cbump_hasCompactSupport.comp_smul ht.ne') ?_
  intro ξ hξ h0
  apply hξ
  simp [sym, h0]

theorem sym_integrable {t : ℝ} (ht : 0 < t) (x₀ : Space) (j : Fin 3) : Integrable (sym t x₀ j) :=
  (sym_contDiff t x₀ j).continuous.integrable_of_hasCompactSupport (sym_hasCompactSupport ht x₀ j)

theorem sym_eq {t : ℝ} (ht : 0 ≤ t) (x₀ : Space) (j : Fin 3) {ξ : Space} (h : t * ‖ξ‖ ≤ 1) :
    sym t x₀ j ξ = ((𝐞 (-(inner ℝ ξ x₀)) : ℂ)) • EuclideanSpace.single j (1 : ℂ) := by
  have h' : ‖t • ξ‖ ≤ 1 := by rw [norm_smul, Real.norm_of_nonneg ht]; exact h
  simp [sym, cbump_eq_one h']

theorem prof_continuous (t : ℝ) (x₀ : Space) : Continuous (prof t x₀) :=
  continuous_const.mul (rk_continuous.comp (by fun_prop : Continuous fun y : Space => t⁻¹ • (y - x₀)))

theorem inv6_integrable : Integrable (fun z : Space => ((1 + ‖z‖) ^ 6)⁻¹) := by
  have h := integrable_one_add_norm (E := Space) (μ := volume) (r := 6)
    (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem change_var {t : ℝ} (ht : 0 < t) (x₀ : Space) (H : Space → ℝ) :
    ∫ y, H (t⁻¹ • (y - x₀)) = t ^ 3 * ∫ z, H z := by
  rw [integral_sub_right_eq_self (fun y => H (t⁻¹ • y)) x₀, Measure.integral_comp_smul volume H t⁻¹,
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (by positivity), smul_eq_mul]

theorem weight_le (x₀ y : Space) : 1 + ‖y‖ ≤ (1 + ‖x₀‖) * (1 + ‖y - x₀‖) := by
  have h1 := norm_sub_norm_le y x₀
  have h2 := norm_nonneg x₀
  have h3 := norm_nonneg (y - x₀)
  nlinarith

theorem prof_sq_le {C : ℝ} (_hC : 0 ≤ C) (hdec : ∀ z, |rk z| ≤ C * ((1 + ‖z‖) ^ 4)⁻¹)
    {t : ℝ} (ht : 0 < t) (x₀ y : Space) :
    ((1 + ‖y‖) * prof t x₀ y) ^ 2 ≤
      ((1 + ‖x₀‖) * (1 + t) * (t ^ 3)⁻¹ * C) ^ 2 * ((1 + ‖t⁻¹ • (y - x₀)‖) ^ 6)⁻¹ := by
  have hk := hdec (t⁻¹ • (y - x₀))
  set s := ‖t⁻¹ • (y - x₀)‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have hys : ‖y - x₀‖ = t * s := by
    rw [hs, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), ← mul_assoc,
      mul_inv_cancel₀ ht.ne', one_mul]
  have hw : 1 + ‖y‖ ≤ (1 + ‖x₀‖) * (1 + t) * (1 + s) := by
    have h5 := weight_le x₀ y
    rw [hys] at h5
    have h4 : 1 + t * s ≤ (1 + t) * (1 + s) := by nlinarith
    calc 1 + ‖y‖ ≤ (1 + ‖x₀‖) * (1 + t * s) := h5
      _ ≤ (1 + ‖x₀‖) * ((1 + t) * (1 + s)) := by gcongr
      _ = _ := by ring
  have hs1 : 0 < 1 + s := by positivity
  have hab : |(1 + ‖y‖) * prof t x₀ y| ≤
      (1 + ‖x₀‖) * (1 + t) * (t ^ 3)⁻¹ * C * ((1 + s) ^ 3)⁻¹ := by
    rw [prof, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + ‖y‖),
      abs_of_pos (by positivity : (0 : ℝ) < (t ^ 3)⁻¹)]
    calc (1 + ‖y‖) * ((t ^ 3)⁻¹ * |rk (t⁻¹ • (y - x₀))|)
        ≤ ((1 + ‖x₀‖) * (1 + t) * (1 + s)) * ((t ^ 3)⁻¹ * (C * ((1 + s) ^ 4)⁻¹)) := by
          gcongr
      _ = _ := by field_simp
  calc ((1 + ‖y‖) * prof t x₀ y) ^ 2 = |(1 + ‖y‖) * prof t x₀ y| ^ 2 := (sq_abs _).symm
    _ ≤ ((1 + ‖x₀‖) * (1 + t) * (t ^ 3)⁻¹ * C * ((1 + s) ^ 3)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hab 2
    _ = _ := by rw [mul_pow, inv_pow, ← pow_mul]

theorem inv6_comp_integrable {t : ℝ} (ht : 0 < t) (x₀ : Space) :
    Integrable (fun y : Space => ((1 + ‖t⁻¹ • (y - x₀)‖) ^ 6)⁻¹) :=
  (inv6_integrable.comp_smul (inv_ne_zero ht.ne')).comp_sub_right x₀

theorem prof_sq_integrable {C : ℝ} (hC : 0 ≤ C) (hdec : ∀ z, |rk z| ≤ C * ((1 + ‖z‖) ^ 4)⁻¹)
    {t : ℝ} (ht : 0 < t) (x₀ : Space) :
    Integrable (fun y => ((1 + ‖y‖) * prof t x₀ y) ^ 2) := by
  refine ((inv6_comp_integrable ht x₀).const_mul
    (((1 + ‖x₀‖) * (1 + t) * (t ^ 3)⁻¹ * C) ^ 2)).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (((continuous_const.add continuous_norm).mul (prof_continuous t x₀)).pow 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact prof_sq_le hC hdec ht x₀ y

theorem integral_prof_sq_le {C : ℝ} (hC : 0 ≤ C) (hdec : ∀ z, |rk z| ≤ C * ((1 + ‖z‖) ^ 4)⁻¹)
    {t : ℝ} (ht : 0 < t) (x₀ : Space) :
    ∫ y, ((1 + ‖y‖) * prof t x₀ y) ^ 2 ≤
      ((1 + ‖x₀‖) * (1 + t) * (t ^ 3)⁻¹ * C) ^ 2 * (t ^ 3 * ∫ z : Space, ((1 + ‖z‖) ^ 6)⁻¹) := by
  rw [← change_var ht x₀ (fun z : Space => ((1 + ‖z‖) ^ 6)⁻¹), ← integral_const_mul]
  exact integral_mono (prof_sq_integrable hC hdec ht x₀)
    ((inv6_comp_integrable ht x₀).const_mul _) (fun y => prof_sq_le hC hdec ht x₀ y)

theorem weighted_pairing_bound {Θ : Space → Space} (hΘc : Continuous Θ)
    (hΘ : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume) (j : Fin 3) {g : Space → ℝ}
    (hg : AEStronglyMeasurable g volume) (hg2 : Integrable (fun y => ((1 + ‖y‖) * g y) ^ 2)) :
    Integrable (fun y => g y * Θ y j) ∧
      |∫ y, g y * Θ y j| ≤ Real.sqrt (∫ y, ‖(1 + ‖y‖)⁻¹ • Θ y‖ ^ 2) *
        Real.sqrt (∫ y, ((1 + ‖y‖) * g y) ^ 2) := by
  set F : Space → ℝ := fun y => ‖(1 + ‖y‖)⁻¹ • Θ y‖ with hFdef
  set G : Space → ℝ := fun y => |(1 + ‖y‖) * g y| with hGdef
  have hF : MemLp F 2 volume := hΘ.norm
  have hGm : AEStronglyMeasurable G volume :=
    (((continuous_const.add continuous_norm).aestronglyMeasurable).mul hg).norm
  have hG : MemLp G 2 volume := by
    rw [memLp_two_iff_integrable_sq hGm]
    simp only [G, sq_abs]
    exact hg2
  have hFG : Integrable (fun y => F y * G y) := hF.integrable_mul hG
  have hpt : ∀ y, |g y * Θ y j| ≤ F y * G y := by
    intro y
    have hw : 0 < 1 + ‖y‖ := by positivity
    have h1 : |Θ y j| ≤ ‖Θ y‖ := by
      have := PiLp.norm_apply_le (Θ y) j
      rwa [Real.norm_eq_abs] at this
    simp only [F, G, norm_smul, norm_inv, Real.norm_eq_abs, abs_mul, abs_of_pos hw]
    calc |g y| * |Θ y j| ≤ |g y| * ‖Θ y‖ := by gcongr
      _ = (1 + ‖y‖)⁻¹ * ‖Θ y‖ * ((1 + ‖y‖) * |g y|) := by field_simp
  have hθ : Continuous (fun y => Θ y j) := by fun_prop
  have hint : Integrable (fun y => g y * Θ y j) := by
    refine hFG.mono' (hg.mul hθ.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hpt y
  refine ⟨hint, ?_⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun y => norm_nonneg _) (Eventually.of_forall fun y => abs_nonneg _)
    (by simpa using hF) (by simpa using hG)
  calc |∫ y, g y * Θ y j| ≤ ∫ y, |g y * Θ y j| := abs_integral_le_integral_abs
    _ ≤ ∫ y, F y * G y := integral_mono hint.abs hFG hpt
    _ ≤ _ := hH
    _ = _ := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        simp only [Real.rpow_two, sq_abs]

theorem low_limit {Θ : Space → Space} (hΘc : Continuous Θ)
    (hΘ : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume) (x₀ : Space) (j : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ y, prof ε⁻¹ x₀ y * Θ y j) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hdec⟩ := rk_decay
  set M := ∫ y, ‖(1 + ‖y‖)⁻¹ • Θ y‖ ^ 2
  set I := ∫ z : Space, ((1 + ‖z‖) ^ 6)⁻¹ with hI
  clear_value I
  set c := ((1 + ‖x₀‖) * C) ^ 2 * I
  have hbound : ∀ ε : ℝ, 0 < ε →
      |∫ y, prof ε⁻¹ x₀ y * Θ y j| ≤ Real.sqrt M * Real.sqrt (c * ((ε + 1) ^ 2 * ε)) := by
    intro ε hε
    have ht : 0 < ε⁻¹ := inv_pos.2 hε
    obtain ⟨-, hcs⟩ := weighted_pairing_bound hΘc hΘ j (prof_continuous ε⁻¹ x₀).aestronglyMeasurable
      (prof_sq_integrable hC hdec ht x₀)
    refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    refine (integral_prof_sq_le hC hdec ht x₀).trans (le_of_eq ?_)
    rw [← hI]
    simp only [c]
    field_simp
  have hlim : Tendsto (fun ε : ℝ => Real.sqrt M * Real.sqrt (c * ((ε + 1) ^ 2 * ε)))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => Real.sqrt M * Real.sqrt (c * ((ε + 1) ^ 2 * ε))) := by
      fun_prop
    have h0 := hc.tendsto 0
    rw [show Real.sqrt M * Real.sqrt (c * (((0 : ℝ) + 1) ^ 2 * 0)) = 0 by simp] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Real.norm_eq_abs]
  exact hbound ε hε

def tail (δ : ℝ) (x₀ : Space) : Space → ℝ := (Metric.ball x₀ 1)ᶜ.indicator (prof δ x₀)

def hbase (δ : ℝ) (x₀ : Space) : Space → ℝ := (Metric.ball x₀ 1).indicator (prof δ x₀)

theorem tail_measurable (δ : ℝ) (x₀ : Space) : Measurable (tail δ x₀) :=
  (prof_continuous δ x₀).measurable.indicator measurableSet_ball.compl

theorem tail_sq_le_prof (δ : ℝ) (x₀ y : Space) :
    ((1 + ‖y‖) * tail δ x₀ y) ^ 2 ≤ ((1 + ‖y‖) * prof δ x₀ y) ^ 2 := by
  by_cases hy : y ∈ Metric.ball x₀ 1
  · rw [tail, Set.indicator_of_notMem (fun h : y ∈ (Metric.ball x₀ 1)ᶜ => h hy), mul_zero,
      zero_pow two_ne_zero]
    exact sq_nonneg _
  · rw [tail, Set.indicator_of_mem (hy : y ∈ (Metric.ball x₀ 1)ᶜ)]

theorem tail_sq_le {C : ℝ} (hC : 0 ≤ C) (hdec : ∀ z, |rk z| ≤ C * ((1 + ‖z‖) ^ 4)⁻¹)
    {δ : ℝ} (hδ : 0 < δ) (x₀ y : Space) :
    ((1 + ‖y‖) * tail δ x₀ y) ^ 2 ≤
      (16 * C * (1 + ‖x₀‖) * δ) ^ 2 * ((1 + ‖y - x₀‖) ^ 6)⁻¹ := by
  by_cases hy : y ∈ Metric.ball x₀ 1
  · rw [tail, Set.indicator_of_notMem (fun h : y ∈ (Metric.ball x₀ 1)ᶜ => h hy), mul_zero,
      zero_pow two_ne_zero]
    positivity
  · have hy' : y ∈ (Metric.ball x₀ 1)ᶜ := hy
    rw [tail, Set.indicator_of_mem hy']
    have hs1 : 1 ≤ ‖y - x₀‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hk := hdec (δ⁻¹ • (y - x₀))
    set s := ‖y - x₀‖ with hs
    have hn : ‖δ⁻¹ • (y - x₀)‖ = δ⁻¹ * s := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
    rw [hn] at hk
    have hsp : 0 < 1 + s := by positivity
    have h1' : (1 + s) / (2 * δ) ≤ 1 + δ⁻¹ * s := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 + δ⁻¹ * s) * (2 * δ) = 2 * δ + 2 * s := by field_simp
      rw [this]
      linarith
    have hkey : ((1 + δ⁻¹ * s) ^ 4)⁻¹ ≤ (2 * δ) ^ 4 * ((1 + s) ^ 4)⁻¹ := by
      calc ((1 + δ⁻¹ * s) ^ 4)⁻¹ ≤ (((1 + s) / (2 * δ)) ^ 4)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1' 4)
        _ = (2 * δ) ^ 4 * ((1 + s) ^ 4)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]
    have hw : 1 + ‖y‖ ≤ (1 + ‖x₀‖) * (1 + s) := weight_le x₀ y
    have hab : |(1 + ‖y‖) * prof δ x₀ y| ≤ 16 * C * (1 + ‖x₀‖) * δ * ((1 + s) ^ 3)⁻¹ := by
      rw [prof, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + ‖y‖),
        abs_of_pos (by positivity : (0 : ℝ) < (δ ^ 3)⁻¹)]
      calc (1 + ‖y‖) * ((δ ^ 3)⁻¹ * |rk (δ⁻¹ • (y - x₀))|)
          ≤ ((1 + ‖x₀‖) * (1 + s)) * ((δ ^ 3)⁻¹ * (C * ((2 * δ) ^ 4 * ((1 + s) ^ 4)⁻¹))) := by
            gcongr
            exact hk.trans (mul_le_mul_of_nonneg_left hkey hC)
        _ = _ := by field_simp; ring
    calc ((1 + ‖y‖) * prof δ x₀ y) ^ 2 = |(1 + ‖y‖) * prof δ x₀ y| ^ 2 := (sq_abs _).symm
      _ ≤ (16 * C * (1 + ‖x₀‖) * δ * ((1 + s) ^ 3)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hab 2
      _ = _ := by rw [mul_pow, inv_pow, ← pow_mul]

theorem tail_limit {Θ : Space → Space} (hΘc : Continuous Θ)
    (hΘ : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume) (x₀ : Space) (j : Fin 3) :
    Tendsto (fun δ : ℝ => ∫ y, tail δ x₀ y * Θ y j) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hdec⟩ := rk_decay
  set M := ∫ y, ‖(1 + ‖y‖)⁻¹ • Θ y‖ ^ 2
  set I := ∫ z : Space, ((1 + ‖z‖) ^ 6)⁻¹
  have hI' : Integrable (fun y : Space => ((1 + ‖y - x₀‖) ^ 6)⁻¹) :=
    inv6_integrable.comp_sub_right x₀
  have hIeq : ∫ y : Space, ((1 + ‖y - x₀‖) ^ 6)⁻¹ = I :=
    integral_sub_right_eq_self (fun y : Space => ((1 + ‖y‖) ^ 6)⁻¹) x₀
  have hbound : ∀ δ : ℝ, 0 < δ →
      |∫ y, tail δ x₀ y * Θ y j| ≤ Real.sqrt M * Real.sqrt ((16 * C * (1 + ‖x₀‖) * δ) ^ 2 * I) := by
    intro δ hδ
    have hsq : Integrable (fun y => ((1 + ‖y‖) * tail δ x₀ y) ^ 2) := by
      refine (hI'.const_mul ((16 * C * (1 + ‖x₀‖) * δ) ^ 2)).mono' ?_
        (Eventually.of_forall fun y => ?_)
      · exact (((continuous_const.add continuous_norm).measurable.mul
          (tail_measurable δ x₀)).pow_const 2).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact tail_sq_le hC hdec hδ x₀ y
    obtain ⟨-, hcs⟩ := weighted_pairing_bound hΘc hΘ j (tail_measurable δ x₀).aestronglyMeasurable hsq
    refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    rw [← hIeq, ← integral_const_mul]
    exact integral_mono hsq (hI'.const_mul _) (fun y => tail_sq_le hC hdec hδ x₀ y)
  have hlim : Tendsto (fun δ : ℝ => Real.sqrt M * Real.sqrt ((16 * C * (1 + ‖x₀‖) * δ) ^ 2 * I))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous
        (fun δ : ℝ => Real.sqrt M * Real.sqrt ((16 * C * (1 + ‖x₀‖) * δ) ^ 2 * I)) := by
      fun_prop
    have h0 := hc.tendsto 0
    rw [show Real.sqrt M * Real.sqrt ((16 * C * (1 + ‖x₀‖) * 0) ^ 2 * I) = 0 by simp] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [Real.norm_eq_abs]
  exact hbound δ hδ

theorem core_limit {Θ : Space → Space} (hΘc : Continuous Θ) (x₀ : Space) (j : Fin 3) :
    Tendsto (fun δ : ℝ => ∫ y, hbase δ x₀ y * Θ y j) (𝓝[>] 0) (𝓝 (Θ x₀ j)) := by
  set θ : Space → ℝ := fun y => Θ y j with hθdef
  have hθ : Continuous θ := by fun_prop
  set Φ : Space → ℝ := (Metric.ball x₀ 1).indicator θ with hΦdef
  have hΦm : Measurable Φ := hθ.measurable.indicator measurableSet_ball
  obtain ⟨S, hS⟩ := (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn hθ.continuousOn
  have hΦb : ∀ y, |Φ y| ≤ |S| := by
    intro y
    by_cases hy : y ∈ Metric.ball x₀ 1
    · rw [hΦdef, Set.indicator_of_mem hy]
      have := hS y (Metric.ball_subset_closedBall hy)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self S)
    · rw [hΦdef, Set.indicator_of_notMem hy, abs_zero]
      exact abs_nonneg S
  have hΦc : ContinuousAt Φ x₀ := by
    refine hθ.continuousAt.congr ?_
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with y hy
    rw [hΦdef, Set.indicator_of_mem hy]
  have hΦ0 : Φ x₀ = θ x₀ := Set.indicator_of_mem (Metric.mem_ball_self one_pos) θ
  have hrw : ∀ δ : ℝ, 0 < δ → ∫ y, hbase δ x₀ y * Θ y j = ∫ z, rk z * Φ (x₀ + δ • z) := by
    intro δ hδ
    have h1 : ∀ y, hbase δ x₀ y * Θ y j =
        (δ ^ 3)⁻¹ * (rk (δ⁻¹ • (y - x₀)) * Φ (x₀ + δ • (δ⁻¹ • (y - x₀)))) := by
      intro y
      rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul, add_sub_cancel]
      by_cases hy : y ∈ Metric.ball x₀ 1
      · rw [hbase, hΦdef, Set.indicator_of_mem hy, Set.indicator_of_mem hy, prof]
        ring
      · rw [hbase, hΦdef, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
        ring
    rw [integral_congr_ae (Eventually.of_forall h1),
      change_var hδ x₀ (fun z => (δ ^ 3)⁻¹ * (rk z * Φ (x₀ + δ • z))), integral_const_mul,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hlim : Tendsto (fun δ : ℝ => ∫ z, rk z * Φ (x₀ + δ • z)) (𝓝[>] 0)
      (𝓝 (∫ z, rk z * θ x₀)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => |rk z| * |S|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun δ => rk_continuous.aestronglyMeasurable.mul
        (hΦm.comp (by fun_prop : Measurable fun z : Space => x₀ + δ • z)).aestronglyMeasurable
    · exact Eventually.of_forall fun δ => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hΦb _) (abs_nonneg _)
    · exact rk_integrable.abs.mul_const _
    · refine Eventually.of_forall fun z => ?_
      refine Tendsto.const_mul (rk z) ?_
      rw [← hΦ0]
      have ht : Tendsto (fun δ : ℝ => x₀ + δ • z) (𝓝[>] 0) (𝓝 x₀) := by
        have hc : Continuous (fun δ : ℝ => x₀ + δ • z) := by fun_prop
        have h0 := hc.tendsto 0
        rw [zero_smul, add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      exact hΦc.tendsto.comp ht
  have hval : ∫ z, rk z * θ x₀ = Θ x₀ j := by rw [integral_mul_const, integral_rk, one_mul]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hrw δ hδ).symm

theorem component_zero {Θ : Space → Space} (hΘc : Continuous Θ)
    (hΘ : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume)
    (hm : ∀ m : Space → CSpace, (∀ ξ, m (-ξ) = conjVec (m ξ)) → ContDiff ℝ ∞ m →
      HasCompactSupport m → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → m ξ = 0) →
      ∫ y, inner ℝ (Θ y) (physField m y) = 0) (x₀ : Space) (j : Fin 3) : Θ x₀ j = 0 := by
  obtain ⟨C, hC, hdec⟩ := rk_decay
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun y => prof t x₀ y * Θ y j) := fun t ht =>
    (weighted_pairing_bound hΘc hΘ j (prof_continuous t x₀).aestronglyMeasurable
      (prof_sq_integrable hC hdec ht x₀)).1
  have hEq : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∫ y, prof δ x₀ y * Θ y j = ∫ y, prof ε⁻¹ x₀ y * Θ y j := by
    intro δ hδ ε hε
    have hε' : 0 < ε⁻¹ := inv_pos.2 hε
    have h := hm (fun ξ => sym δ x₀ j ξ - sym ε⁻¹ x₀ j ξ)
      (fun ξ => by
        show sym δ x₀ j (-ξ) - sym ε⁻¹ x₀ j (-ξ) = conjVec (sym δ x₀ j ξ - sym ε⁻¹ x₀ j ξ)
        rw [sym_conjSym, sym_conjSym, map_sub])
      ((sym_contDiff δ x₀ j).sub (sym_contDiff ε⁻¹ x₀ j))
      ((sym_hasCompactSupport hδ x₀ j).sub (sym_hasCompactSupport hε' x₀ j))
      ⟨min ε δ⁻¹, lt_min hε (inv_pos.2 hδ), fun ξ hξ => by
        have h1 : δ * ‖ξ‖ ≤ 1 :=
          (le_div_iff₀' hδ).1 (by rw [one_div]; exact (lt_min_iff.1 hξ).2.le)
        have h2 : ε⁻¹ * ‖ξ‖ ≤ 1 := by
          rw [inv_mul_le_iff₀ hε, mul_one]
          exact (lt_min_iff.1 hξ).1.le
        show sym δ x₀ j ξ - sym ε⁻¹ x₀ j ξ = 0
        rw [sym_eq hδ.le x₀ j h1, sym_eq hε'.le x₀ j h2, sub_self]⟩
    have hpt : ∀ y, inner ℝ (Θ y) (physField (fun ξ => sym δ x₀ j ξ - sym ε⁻¹ x₀ j ξ) y) =
        prof δ x₀ y * Θ y j - prof ε⁻¹ x₀ y * Θ y j := by
      intro y
      rw [physField_sub (sym_integrable hδ x₀ j) (sym_integrable hε' x₀ j), physField_sym hδ,
        physField_sym hε', ← sub_smul, inner_smul_right, EuclideanSpace.inner_single_right]
      simp only [one_mul, conj_trivial]
      ring
    simp_rw [hpt] at h
    rw [integral_sub (hint δ hδ) (hint ε⁻¹ hε')] at h
    linarith
  have hzero : ∀ δ : ℝ, 0 < δ → ∫ y, prof δ x₀ y * Θ y j = 0 := by
    intro δ hδ
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) (low_limit hΘc hΘ x₀ j)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hEq δ hδ ε hε
  have hsplit : ∀ δ : ℝ, 0 < δ → ∫ y, prof δ x₀ y * Θ y j =
      (∫ y, hbase δ x₀ y * Θ y j) + ∫ y, tail δ x₀ y * Θ y j := by
    intro δ hδ
    have ht : Integrable (fun y => tail δ x₀ y * Θ y j) := by
      refine (weighted_pairing_bound hΘc hΘ j (tail_measurable δ x₀).aestronglyMeasurable ?_).1
      refine (prof_sq_integrable hC hdec hδ x₀).mono' ?_ (Eventually.of_forall fun y => ?_)
      · exact (((continuous_const.add continuous_norm).measurable.mul
          (tail_measurable δ x₀)).pow_const 2).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact tail_sq_le_prof δ x₀ y
    have hpt : ∀ y, hbase δ x₀ y * Θ y j = prof δ x₀ y * Θ y j - tail δ x₀ y * Θ y j := by
      intro y
      by_cases hy : y ∈ Metric.ball x₀ 1
      · rw [hbase, tail, Set.indicator_of_mem hy,
          Set.indicator_of_notMem (fun h : y ∈ (Metric.ball x₀ 1)ᶜ => h hy)]
        ring
      · rw [hbase, tail, Set.indicator_of_notMem hy,
          Set.indicator_of_mem (hy : y ∈ (Metric.ball x₀ 1)ᶜ)]
        ring
    have hc : Integrable (fun y => hbase δ x₀ y * Θ y j) :=
      ((hint δ hδ).sub ht).congr (Eventually.of_forall fun y => (hpt y).symm)
    rw [← integral_add hc ht]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hpt]
    ring
  have hlim := (core_limit hΘc x₀ j).add (tail_limit hΘc hΘ x₀ j)
  rw [add_zero] at hlim
  have hlim' : Tendsto (fun δ : ℝ => (∫ y, hbase δ x₀ y * Θ y j) + ∫ y, tail δ x₀ y * Θ y j)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [← hsplit δ hδ, hzero δ hδ]
  exact tendsto_nhds_unique hlim hlim'


end WeakLowFrequency.Internal

theorem lowFrequencyRemoval : LowFrequencyRemovalStatement := by
  intro Θ hΘc hΘ hm y
  ext j
  simpa using WeakLowFrequency.Internal.component_zero hΘc hΘ hm y j

end Breakdown.FracCert

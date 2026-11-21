import Breakdown.CertTorus.RegularStatements
import Breakdown.Uniqueness.RegIdentifyAuxDivFree

open MeasureTheory Set Real Filter
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.VelocityOfSymbol

theorem symX_ae_sig (x : X) :
    ∀ᵐ ξ ∂volume, conjVec (symX x (-ξ)) = symX x ξ ∧ longitudinal ξ (symX x ξ) = 0 := by
  have hx := (Freq.Internal.H1Consistency.mem_sig_iff (x : L2C)).1 x.2
  have h1 := Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds (x : L2C)
  have h2 := Freq.Internal.H1Consistency.longitudinal_ae fieldOpRealized_holds (x : L2C)
  rw [hx.1] at h1
  rw [hx.2] at h2
  filter_upwards [h1, h2, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3
  refine ⟨e1.symm, ?_⟩
  simp only [symX]
  rw [← e2, e3]
  rfl

theorem velSymbol_ae (x : X) :
    velSymbol x =ᵐ[volume] fun ξ => ((2 * π * ‖ξ‖)⁻¹ : ℝ) • symX x ξ := by
  filter_upwards [symX_ae_sig x] with ξ e
  have hh : (1 / 2 : ℝ) • (symX x ξ + symX x ξ) = symX x ξ := by
    rw [← two_smul ℝ (symX x ξ), smul_smul]
    norm_num
  rw [velSymbol, e.1, hh, Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.divFreeC_eq_sub, e.2, sub_zero]

theorem aestronglyMeasurable_velSymbol (x : X) : AEStronglyMeasurable (velSymbol x) volume := by
  have hm : Measurable fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ) := by fun_prop
  exact (hm.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (x : L2C))).congr
    (velSymbol_ae x).symm

theorem integrable_velSymbol (hW : HomWiener) {x : X} (hx : IsSmoothX x) :
    Integrable (velSymbol x) volume := by
  obtain ⟨C, hC⟩ := hW 0
  have hb := hC x
  simp only [pow_zero, ENNReal.ofReal_one, one_mul, zero_add] at hb
  refine ⟨aestronglyMeasurable_velSymbol x, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.2 ⟨hx 0, hx 1⟩).ne

theorem exists_radial_mul (x : X) (c : Space → ℝ) (hc : Measurable c) (C : ℝ)
    (hC : ∀ ξ, |c ξ| ≤ C) (he : ∀ ξ, c (-ξ) = c ξ) :
    ∃ z : X, ((z : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => c ξ • (x : L2C) ξ := by
  have hmem := Freq.Internal.TestDense.memLp_smul_of_bounded (x : L2C) c hc C hC
  refine ⟨⟨hmem.toLp _, ?_⟩, hmem.coeFn_toLp⟩
  exact Freq.Internal.TestDense.mem_sig_of_ae x c he _ hmem.coeFn_toLp

def highFreq (n : ℕ) : Set Space := {ξ | 1 / ((n : ℝ) + 1) ≤ ‖ξ‖}

theorem measurableSet_highFreq (n : ℕ) : MeasurableSet (highFreq n) :=
  measurableSet_le measurable_const measurable_norm

theorem pos_of_mem_highFreq {n : ℕ} {ξ : Space} (h : ξ ∈ highFreq n) : 0 < ‖ξ‖ :=
  lt_of_lt_of_le (by positivity) (h : 1 / ((n : ℝ) + 1) ≤ ‖ξ‖)

theorem neg_mem_highFreq (n : ℕ) (ξ : Space) : -ξ ∈ highFreq n ↔ ξ ∈ highFreq n := by
  show 1 / ((n : ℝ) + 1) ≤ ‖-ξ‖ ↔ 1 / ((n : ℝ) + 1) ≤ ‖ξ‖
  rw [norm_neg]

theorem eventually_mem_highFreq {ξ : Space} (hξ : ξ ≠ 0) : ∀ᶠ n in atTop, ξ ∈ highFreq n := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hξ)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact le_trans (Nat.one_div_le_one_div hn) hN.le

theorem indicator_neg_highFreq (n : ℕ) (f : Space → ℝ) (hf : ∀ ζ, f (-ζ) = f ζ) (ξ : Space) :
    (highFreq n).indicator f (-ξ) = (highFreq n).indicator f ξ := by
  by_cases h : ξ ∈ highFreq n
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((neg_mem_highFreq n ξ).2 h), hf]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun h' => h ((neg_mem_highFreq n ξ).1 h'))]

theorem abs_indicator_inv_le (n : ℕ) (ξ : Space) :
    |(highFreq n).indicator (fun ζ : Space => ((2 * π * ‖ζ‖)⁻¹ : ℝ)) ξ| ≤ (n : ℝ) + 1 := by
  by_cases h : ξ ∈ highFreq n
  · simp only [Set.indicator_of_mem h]
    have hp := pos_of_mem_highFreq h
    have hh : 1 / ((n : ℝ) + 1) ≤ ‖ξ‖ := h
    rw [abs_of_nonneg (by positivity)]
    calc (2 * π * ‖ξ‖)⁻¹ ≤ ‖ξ‖⁻¹ := inv_anti₀ hp (by nlinarith [Real.pi_gt_three])
      _ ≤ (n : ℝ) + 1 := by
        rw [inv_le_comm₀ hp (by positivity)]
        simpa [one_div] using hh
  · simp only [Set.indicator_of_notMem h, abs_zero]
    positivity

theorem tendsto_cut (x : X) (y : ℕ → X)
    (hy : ∀ n, ((y n : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => (highFreq n).indicator (fun _ => (1 : ℝ)) ξ • (x : L2C) ξ) :
    Tendsto y atTop (𝓝 x) := by
  set s : Space → CSpace := ((x : L2C) : Space → CSpace) with hs
  have hd : ∀ n, (((x - y n : X) : L2C) : Space → CSpace) =ᵐ[volume] (highFreq n)ᶜ.indicator s := by
    intro n
    have e0 : ((x - y n : X) : L2C) = (x : L2C) - (y n : L2C) := rfl
    rw [e0]
    filter_upwards [Lp.coeFn_sub (x : L2C) (y n : L2C), hy n] with ξ e1 e2
    rw [e1, Pi.sub_apply, e2]
    by_cases h : ξ ∈ highFreq n
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h), one_smul,
        sub_self]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), zero_smul, sub_zero]
  have hnorm : ∀ n, ‖y n - x‖ = (eLpNorm ((highFreq n)ᶜ.indicator s) 2 volume).toReal := by
    intro n
    rw [norm_sub_rev]
    change ‖((x - y n : X) : L2C)‖ = _
    rw [Lp.norm_def, eLpNorm_congr_ae (hd n)]
  have hs2 : eLpNorm s 2 volume < ⊤ := (Lp.memLp (x : L2C)).eLpNorm_lt_top
  have hfin : ∫⁻ ξ, ‖s ξ‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
      ENNReal.ofNat_ne_top hs2
    simpa using this.ne
  have hlim : Tendsto (fun n => ∫⁻ ξ, ‖(highFreq n)ᶜ.indicator s ξ‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (fun ξ => ‖s ξ‖ₑ ^ (2 : ℝ)) (F := fun n ξ => ‖(highFreq n)ᶜ.indicator s ξ‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0)
      (fun n => (((Lp.aestronglyMeasurable (x : L2C)).indicator
        (measurableSet_highFreq n).compl).enorm).pow_const _)
      (fun n => Eventually.of_forall fun ξ =>
        ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self _ _) (by norm_num))
      hfin
      (by
        filter_upwards [Freq.Internal.H1Consistency.ae_ne_zero] with ξ hξ
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_mem_highFreq hξ] with n hn
        rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hn), enorm_zero,
          ENNReal.zero_rpow_of_pos (by norm_num)])
    simpa using h
  have hL : Tendsto (fun n => eLpNorm ((highFreq n)ᶜ.indicator s) 2 volume) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm ((highFreq n)ᶜ.indicator s) 2 volume =
        (∫⁻ ξ, ‖(highFreq n)ᶜ.indicator s ξ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      intro n
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      norm_num
    simp_rw [e]
    have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    exact hc.comp hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
  rw [ENNReal.toReal_zero] at h
  exact h

theorem physField_cut_tendsto {v : Space → CSpace} (hv : Integrable v volume) (y : Space) :
    Tendsto (fun n => physField ((highFreq n).indicator v) y) atTop (𝓝 (physField v y)) := by
  have h : Tendsto (fun n => 𝓕⁻ ((highFreq n).indicator v) y) atTop (𝓝 (𝓕⁻ v y)) := by
    simp only [Real.fourierInv_eq']
    refine tendsto_integral_of_dominated_convergence (fun ξ => ‖v ξ‖) ?_ hv.norm ?_ ?_
    · intro n
      exact (Continuous.aestronglyMeasurable (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul
          (continuous_id.inner continuous_const))).mul continuous_const))).smul
        (hv.aestronglyMeasurable.indicator (measurableSet_highFreq n))
    · intro n
      refine Eventually.of_forall fun ξ => ?_
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact norm_indicator_le_norm_self _ _
    · filter_upwards [Freq.Internal.H1Consistency.ae_ne_zero] with ξ hξ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_mem_highFreq hξ] with n hn
      rw [Set.indicator_of_mem hn]
  exact (realVec.continuous.tendsto _).comp h

theorem velocity_ae_physField (hW : HomWiener) (x : X) (hx : IsSmoothX x) :
    (velocity x : Space → Space) =ᵐ[volume] physField (velSymbol x) := by
  set v := velSymbol x with hvdef
  have hvi : Integrable v volume := integrable_velSymbol hW hx
  have hva : v =ᵐ[volume] fun ξ => ((2 * π * ‖ξ‖)⁻¹ : ℝ) • symX x ξ := velSymbol_ae x
  have hy : ∀ n, ∃ z : X, ((z : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => (highFreq n).indicator (fun _ => (1 : ℝ)) ξ • (x : L2C) ξ := fun n =>
    exists_radial_mul x _ (measurable_const.indicator (measurableSet_highFreq n)) 1
      (fun ξ => by
        by_cases h : ξ ∈ highFreq n
        · simp only [Set.indicator_of_mem h, abs_one, le_refl]
        · simp only [Set.indicator_of_notMem h, abs_zero, zero_le_one])
      (fun ξ => indicator_neg_highFreq n _ (fun _ => rfl) ξ)
  have hg : ∀ n, ∃ z : X, ((z : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => (highFreq n).indicator (fun ζ : Space => ((2 * π * ‖ζ‖)⁻¹ : ℝ)) ξ • (x : L2C) ξ :=
    fun n => exists_radial_mul x _
      ((by fun_prop : Measurable fun ζ : Space => ((2 * π * ‖ζ‖)⁻¹ : ℝ)).indicator
        (measurableSet_highFreq n)) ((n : ℝ) + 1) (abs_indicator_inv_le n)
      (fun ξ => indicator_neg_highFreq n _ (fun ζ => by simp only [norm_neg]) ξ)
  choose y hy using hy
  choose g hg using hg
  have hhalf : ∀ n, IsHalfSspOf (g n) (y n) := by
    intro n
    unfold IsHalfSspOf
    filter_upwards [hy n, hg n] with ξ e1 e2
    rw [e1, e2, smul_smul]
    congr 1
    by_cases h : ξ ∈ highFreq n
    · simp only [Set.indicator_of_mem h]
      have hp := pos_of_mem_highFreq h
      rw [mul_inv_cancel₀ (mul_pos (by positivity) hp).ne']
    · simp only [Set.indicator_of_notMem h, mul_zero]
  have hgv : ∀ n, ((g n : L2C) : Space → CSpace) =ᵐ[volume] (highFreq n).indicator v := by
    intro n
    filter_upwards [hg n, hva] with ξ e1 e2
    rw [e1]
    by_cases h : ξ ∈ highFreq n
    · simp only [Set.indicator_of_mem h]
      rw [e2]
      rfl
    · simp only [Set.indicator_of_notMem h, zero_smul]
  have hvel : ∀ n, ((velocity (y n) : L6R) : Space → Space) =ᵐ[volume]
      physField ((highFreq n).indicator v) := by
    intro n
    have h1 : MemLp ((highFreq n).indicator v) 1 volume :=
      memLp_one_iff_integrable.2 (hvi.indicator (measurableSet_highFreq n))
    have h2 : MemLp ((highFreq n).indicator v) 2 volume := (Lp.memLp (g n : L2C)).ae_eq (hgv n)
    have e : (g n : L2C) = toLpOrZero 2 ((highFreq n).indicator v) := by
      apply Lp.ext
      rw [toLpOrZero, dif_pos h2]
      exact (hgv n).trans h2.coeFn_toLp.symm
    have e' : toPhys (g n : L2C) = realPart (freqTrL2.symm (g n : L2C)) := rfl
    have h3 : ((freqTrL2.symm (g n : L2C) : L2C) : Space → CSpace) =ᵐ[volume]
        𝓕⁻ ((highFreq n).indicator v) := by
      rw [e]
      exact freqTrL1L2.2 _ h1 h2
    have h4 : ((realPart (freqTrL2.symm (g n : L2C)) : L2R) : Space → Space) =ᵐ[volume]
        fun a => realVec ((freqTrL2.symm (g n : L2C) : L2C) a) :=
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec (freqTrL2.symm (g n : L2C))
    filter_upwards [velocityInverts_holds (g n) (y n) (hhalf n), h4, h3] with ξ e1 e2 e3
    rw [e1, e', e2, e3]
    rfl
  have hconv : Tendsto y atTop (𝓝 x) := tendsto_cut x y hy
  set F : Space → Space := ((velocity x : L6R) : Space → Space) with hF
  have hdiff : ∀ n, (fun ξ => F ξ - physField ((highFreq n).indicator v) ξ) =ᵐ[volume]
      ((velocity (x - y n) : L6R) : Space → Space) := by
    intro n
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (velocity x) (velocity (y n)), hvel n] with ξ e1 e2
    rw [e1, Pi.sub_apply, e2]
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun ξ => F ξ - physField ((highFreq n).indicator v) ξ) volume :=
    fun n => (Lp.aestronglyMeasurable _).congr (hdiff n).symm
  have hlim : ∀ᵐ ξ ∂volume, Tendsto (fun n => F ξ - physField ((highFreq n).indicator v) ξ) atTop
      (𝓝 (F ξ - physField v ξ)) :=
    Eventually.of_forall fun ξ => tendsto_const_nhds.sub (physField_cut_tendsto hvi ξ)
  have hnorm : Tendsto (fun n => eLpNorm (fun ξ => F ξ - physField ((highFreq n).indicator v) ξ)
      6 volume) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (fun ξ => F ξ - physField ((highFreq n).indicator v) ξ) 6 volume =
        ENNReal.ofReal ‖velocity (x - y n)‖ := by
      intro n
      rw [eLpNorm_congr_ae (hdiff n), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    simp_rw [e]
    have hc : Tendsto (fun n => ‖velocity (x - y n)‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => x - y n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := x)).sub hconv
      simpa using ((velocity.continuous.tendsto 0).comp h0).norm
    simpa using ENNReal.tendsto_ofReal hc
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 6) hmeas _ hlim
  have hz : eLpNorm (fun ξ => F ξ - physField v ξ) 6 volume = 0 :=
    le_antisymm (le_of_le_of_eq hle hnorm.liminf_eq) (zero_le)
  rw [eLpNorm_eq_zero_iff (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) (by norm_num)] at hz
  filter_upwards [hz] with ξ hξ
  exact sub_eq_zero.1 hξ

end Internal.VelocityOfSymbol

theorem velocityOfSymbolOfWiener_holds : VelocityOfSymbolOfWiener := fun hW x hx =>
  Internal.VelocityOfSymbol.velocity_ae_physField hW x hx

end Breakdown.FarField

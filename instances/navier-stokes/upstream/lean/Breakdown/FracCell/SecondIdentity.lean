import Breakdown.FracCell.StClauses
import Breakdown.FracCert.SecondSymbol
import Breakdown.FreqTr.EmbedMem

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Internal.SecondIdentity

open Freq

def curlPart (j : Fin 3) : Space →L[ℝ] Space :=
  ∑ i : Fin 3, ∑ l : Fin 3, permSign i j l • (EuclideanSpace.proj l : Space →L[ℝ] ℝ).smulRight (unitVector i)

def curlPartC (j : Fin 3) : CSpace →L[ℂ] CSpace :=
  ∑ i : Fin 3, ∑ l : Fin 3, ((permSign i j l : ℝ) : ℂ) •
    (EuclideanSpace.proj l : CSpace →L[ℂ] ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))

theorem sum_unit_apply (c : Fin 3 → ℝ) (k : Fin 3) : (∑ i : Fin 3, c i • unitVector i) k = c k := by
  simp [unitVector, Fin.sum_univ_three]
  fin_cases k <;> simp

theorem curlPart_sum_apply (w : Fin 3 → Space) (i : Fin 3) :
    (∑ j : Fin 3, curlPart j (w j)) i = ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * w j l := by
  simp [curlPart, unitVector, Fin.sum_univ_three]
  fin_cases i <;> simp

theorem curlPartC_sum_apply (w : Fin 3 → CSpace) (i : Fin 3) :
    (∑ j : Fin 3, curlPartC j (w j)) i = ∑ j : Fin 3, ∑ l : Fin 3, ((permSign i j l : ℝ) : ℂ) * w j l := by
  simp [curlPartC, Fin.sum_univ_three]
  fin_cases i <;> simp

theorem cvec_apply (z : Space) (i : Fin 3) : (complexifyVec z) i = ((z i : ℝ) : ℂ) := rfl

theorem curlPart_compat (j : Fin 3) (w : Space) :
    complexifyVec (curlPart j w) = curlPartC j (complexifyVec w) := by
  ext k
  simp [curlPart, curlPartC, unitVector, Fin.sum_univ_three, cvec_apply]
  fin_cases k <;> simp

theorem curlOf_eq (M : Space →L[ℝ] Space) : curlOf M = ∑ j : Fin 3, curlPart j (M (unitVector j)) := by
  ext k
  rw [curlPart_sum_apply, curlOf, sum_unit_apply]
  rfl

theorem cnorm_sq (z : CSpace) : ‖z‖ ^ 2 = ∑ i : Fin 3, ‖z i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]

theorem curlGradSq_eq (H : Space →L[ℝ] Space →L[ℝ] Space) :
    curlGradSq H = ∑ a : Fin 3, ‖∑ j : Fin 3, curlPart j (H (unitVector a) (unitVector j))‖ ^ 2 := by
  simp only [Freq.Internal.H1Consistency.norm_sq_eq, curlPart_sum_apply, curlGradSq]
  exact Finset.sum_comm


theorem permSign_vals : permSign 0 1 2 = 1 ∧ permSign 1 2 0 = 1 ∧ permSign 2 0 1 = 1 ∧ permSign 0 2 1 = -1 ∧ permSign 2 1 0 = -1 ∧
    permSign 1 0 2 = -1 ∧ (∀ i l, permSign i i l = 0) ∧ (∀ i j, permSign i j j = 0) ∧ (∀ i j, permSign i j i = 0) := by
  refine ⟨by simp [permSign], by simp [permSign], by simp [permSign], by simp [permSign], by simp [permSign], by simp [permSign],
    ?_, ?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [permSign]

theorem curl_norm (ξ : Space) (hξ : ξ ≠ 0) (a : Fin 3 → CSpace)
    (hc : ∀ j k : Fin 3, (ξ k : ℝ) • a j = (ξ j : ℝ) • a k) (hd : ∑ i : Fin 3, a i i = 0) :
    ‖∑ j : Fin 3, curlPartC j (a j)‖ ^ 2 = ∑ j : Fin 3, ‖a j‖ ^ 2 := by
  have hn : ‖ξ‖ ^ 2 = ∑ k, (ξ k) ^ 2 := Freq.Internal.H1Consistency.norm_sq_eq ξ
  have hpos : 0 < ‖ξ‖ ^ 2 := by
    have := norm_pos_iff.2 hξ
    positivity
  set b : CSpace := ((‖ξ‖ ^ 2)⁻¹ : ℝ) • ∑ k, (ξ k : ℝ) • a k with hb
  have hab : ∀ j, a j = (ξ j : ℝ) • b := by
    intro j
    have e : (‖ξ‖ ^ 2 : ℝ) • a j = (ξ j : ℝ) • ∑ k, (ξ k : ℝ) • a k := by
      rw [hn, Finset.sum_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sq, mul_smul, hc j k, smul_comm]
    rw [hb, smul_comm, ← e, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  simp only [hab] at hd ⊢
  have hR := congrArg Complex.re hd
  have hI := congrArg Complex.im hd
  simp only [Fin.sum_univ_three, PiLp.smul_apply, Complex.real_smul, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    Complex.zero_re, Complex.zero_im] at hR hI
  rw [cnorm_sq]
  simp only [curlPartC_sum_apply]
  simp only [norm_smul, mul_pow, cnorm_sq b, Fin.sum_univ_three, permSign_vals.1,
    permSign_vals.2.1, permSign_vals.2.2.1, permSign_vals.2.2.2.1, permSign_vals.2.2.2.2.1, permSign_vals.2.2.2.2.2.1,
    permSign_vals.2.2.2.2.2.2.1, permSign_vals.2.2.2.2.2.2.2.1, permSign_vals.2.2.2.2.2.2.2.2, PiLp.smul_apply,
    Complex.real_smul, Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.zero_re,
    Complex.zero_im, Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg]
  linear_combination
    (-((ξ 0) * (b 0).re + (ξ 1) * (b 1).re + (ξ 2) * (b 2).re)) * hR
      + (-((ξ 0) * (b 0).im + (ξ 1) * (b 1).im + (ξ 2) * (b 2).im)) * hI

theorem hat_sum_map (L : Fin 3 → Space →L[ℝ] Space) (A : Fin 3 → CSpace →L[ℂ] CSpace)
    (hLA : ∀ j z, complexifyVec (L j z) = A j (complexifyVec z)) {f : Fin 3 → Space → Space}
    (hf : ∀ j, MemLp (f j) 2 volume) :
    (SteadyCert.Internal.SecondSymbol.hatOf (fun y => ∑ j, L j (f j y)) : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ j, A j ((SteadyCert.Internal.SecondSymbol.hatOf (f j) : Space → CSpace) ξ) := by
  have hs : MemLp (fun y => ∑ j, L j (f j y)) 2 volume :=
    memLp_finsetSum _ fun j _ => (L j).comp_memLp' (hf j)
  have hC : complexify (toLpOrZero 2 (fun y => ∑ j, L j (f j y))) =
      ∑ j, ContinuousLinearMap.compLpL 2 volume (A j) (complexify (toLpOrZero 2 (f j))) := by
    apply Lp.ext
    filter_upwards [Freq.Internal.H1Consistency.complexify_toLp_ae hs,
      Lp.coeFn_finsetSum Finset.univ
        (fun j => ContinuousLinearMap.compLpL 2 volume (A j) (complexify (toLpOrZero 2 (f j)))),
      ae_all_iff.2 fun j => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) (A j)
        (complexify (toLpOrZero 2 (f j))),
      ae_all_iff.2 fun j => Freq.Internal.H1Consistency.complexify_toLp_ae (hf j)] with x h1 h2 h3 h4
    rw [h1, h2, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h3 j, h4 j, hLA]
  have hH : SteadyCert.Internal.SecondSymbol.hatOf (fun y => ∑ j, L j (f j y)) =
      ∑ j, ContinuousLinearMap.compLpL 2 volume (A j) (SteadyCert.Internal.SecondSymbol.hatOf (f j)) := by
    rw [SteadyCert.Internal.SecondSymbol.hatOf, hC, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Freq.Internal.EmbedMem.freqTrL2_compLpL (A j) _
  rw [hH]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j => ContinuousLinearMap.compLpL 2 volume (A j) (SteadyCert.Internal.SecondSymbol.hatOf (f j))),
    ae_all_iff.2 fun j => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) (A j)
      (SteadyCert.Internal.SecondSymbol.hatOf (f j))] with ξ h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => h2 j

theorem hat_ae_zero {f : Space → Space} (hf : MemLp f 2 volume) (h0 : f =ᵐ[volume] 0) :
    (SteadyCert.Internal.SecondSymbol.hatOf f : Space → CSpace) =ᵐ[volume] 0 := by
  have hz : toLpOrZero 2 f = 0 := by
    apply Lp.ext
    filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hf, h0,
      Lp.coeFn_zero Space 2 (volume : Measure Space)] with x h1 h2 h3
    rw [h1, h2, h3]
  rw [SteadyCert.Internal.SecondSymbol.hatOf, hz, map_zero, map_zero]
  exact Lp.coeFn_zero _ _ _

end Internal.SecondIdentity

open Internal.SecondIdentity SteadyCert.Internal.SecondSymbol Freq in
theorem secondIdentity : SecondIdentityStatement := by
  intro m v G H hv
  obtain ⟨-, -, hfull, htrace⟩ := SteadyCert.secondSymbolEnergy m v G H hv
  have hmG : ∀ i, MemLp (WeakProfile.gradComponent G i) 2 volume :=
    fun i => memLp_comp hv.measurable_gradient hv.gradient_two i
  have hmH : ∀ i j, MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume :=
    fun i j => memLp_second hv.measurable_second hv.second_two i j
  have hloc : LocallyIntegrable G volume := by
    have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖) volume :=
      locallyIntegrable_finsetSum _ fun i _ => (hmG i).norm.locallyIntegrable (by norm_num)
    refine hs.mono hv.measurable_gradient (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (norm_le_sum (G y)).trans (le_abs_self _)
  have hwg : IsWeakGradient v G :=
    ⟨hv.velocity_six.locallyIntegrable (by norm_num), hloc, fun φ hφ i => by
      rw [hv.weak_gradient φ hφ i, neg_neg]⟩
  have hcomp : ∀ j, hatOf (WeakProfile.gradComponent G j) = WeakProfile.Internal.GradientFreqTr.hatComp G j :=
    fun j => rfl
  have hA : ∀ k i, (hatOf (fun y => H y (unitVector k) (unitVector i)) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
        (WeakProfile.Internal.GradientFreqTr.hatComp G i : Space → CSpace) ξ :=
    fun k i => hat_deriv hmG (hmH k i) (fun φ hφ => hv.weak_second φ hφ i k)
  have hB : ∀ j k, ∀ᵐ ξ ∂volume,
      (ξ k : ℝ) • (WeakProfile.Internal.GradientFreqTr.hatComp G j : L2C) ξ =
        (ξ j : ℝ) • (WeakProfile.Internal.GradientFreqTr.hatComp G k : L2C) ξ :=
    fun j k => WeakProfile.Internal.GradientFreqTr.compat hwg hmG j k
  have hS : (SteadyCert.secondSymbol H : Space → CSpace) =ᵐ[volume]
      fun ξ => -∑ k, (hatOf (fun y => H y (unitVector k) (unitVector k)) : Space → CSpace) ξ :=
    hat_negSum (f := fun k y => H y (unitVector k) (unitVector k)) (fun k => hmH k k)
  have hD : ∀ᵐ ξ ∂volume, ∑ i : Fin 3,
      (WeakProfile.Internal.GradientFreqTr.hatComp G i : Space → CSpace) ξ i = 0 := by
    let L : Fin 3 → Space →L[ℝ] Space := fun i =>
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (unitVector 0)
    let A : Fin 3 → CSpace →L[ℂ] CSpace := fun i =>
      (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).smulRight (EuclideanSpace.single 0 (1 : ℂ))
    have hLA : ∀ j z, complexifyVec (L j z) = A j (complexifyVec z) := by
      intro j z
      ext k
      fin_cases k <;> simp [L, A, unitVector, cvec_apply]
    have h1 := hat_sum_map L A hLA hmG
    have h0 : (fun y => ∑ j, L j (WeakProfile.gradComponent G j y)) =ᵐ[volume] 0 := by
      filter_upwards [hv.divergence] with y hy
      have e : ∀ j, inner ℝ (G y (unitVector j)) (unitVector j) = G y (unitVector j) j := fun j => by
        rw [unitVector, EuclideanSpace.inner_single_right]
        simp
      simp only [e] at hy
      have hproj : ∀ i (x : Space), (EuclideanSpace.proj i : Space →L[ℝ] ℝ) x = x i := fun _ _ => rfl
      simp only [L, ContinuousLinearMap.smulRight_apply, ← Finset.sum_smul, Pi.zero_apply,
        WeakProfile.gradComponent, hproj]
      rw [hy, zero_smul]
    have h2 := hat_ae_zero (memLp_finsetSum _ fun j _ => (L j).comp_memLp' (hmG j)) h0
    filter_upwards [h1, h2] with ξ e1 e2
    have e3 := congrArg (fun z : CSpace => z 0) (e1.symm.trans e2)
    simpa [A, hcomp] using e3
  have hcurl : ∀ᵐ ξ ∂volume,
      ‖∑ j, curlPartC j ((WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ)‖ ^ 2 =
        ∑ j, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ‖ ^ 2 := by
    filter_upwards [ae_all_iff.2 fun j => ae_all_iff.2 fun k => hB j k, hD,
      Freq.Internal.H1Consistency.ae_ne_zero] with ξ hb hd hξ
    exact curl_norm ξ hξ _ hb hd
  have hiG : ∀ j, Integrable (fun ξ =>
      ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ‖ ^ 2) volume :=
    fun j => (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hphysG : ∀ j, Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) volume :=
    fun j => (memLp_two_iff_integrable_sq_norm (hmG j).1).1 (hmG j)
  refine ⟨?_, ?_, ?_⟩
  · show (∫ y, SteadyCert.fullSecondSq (H y)) = _
    rw [hfull, htrace]
  · have hmc : ∀ a, MemLp (fun y => ∑ j, curlPart j (H y (unitVector a) (unitVector j))) 2 volume :=
      fun a => memLp_finsetSum _ fun j _ => (curlPart j).comp_memLp' (hmH a j)
    have hic : ∀ a, Integrable (fun y => ‖∑ j, curlPart j (H y (unitVector a) (unitVector j))‖ ^ 2) volume :=
      fun a => (memLp_two_iff_integrable_sq_norm (hmc a).1).1 (hmc a)
    have hih : ∀ a, Integrable (fun ξ => ‖(hatOf (fun y => ∑ j, curlPart j (H y (unitVector a) (unitVector j))) :
        Space → CSpace) ξ‖ ^ 2) volume :=
      fun a => (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
    have hpt : ∀ᵐ ξ ∂volume, ∑ a, ‖(hatOf (fun y => ∑ j, curlPart j (H y (unitVector a) (unitVector j))) :
        Space → CSpace) ξ‖ ^ 2 = ‖(SteadyCert.secondSymbol H : Space → CSpace) ξ‖ ^ 2 := by
      filter_upwards [ae_all_iff.2 fun a => hat_sum_map curlPart curlPartC curlPart_compat (hmH a),
        ae_all_iff.2 fun k => ae_all_iff.2 fun i => hA k i, hS, hcurl,
        ae_all_iff.2 fun j => ae_all_iff.2 fun k => hB j k, Freq.Internal.H1Consistency.ae_ne_zero]
        with ξ hsum ha hs hc hb hξ
      have hs' : (SteadyCert.secondSymbol H : Space → CSpace) ξ = -∑ k : Fin 3,
          ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
            (WeakProfile.Internal.GradientFreqTr.hatComp G k : Space → CSpace) ξ := by
        rw [hs]
        simp only [ha]
      obtain ⟨h1, -⟩ := algebra_id ξ hξ
        (fun j => (WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ) _ hb hs'
      have hfp : 0 < SteadyCert.freqPow 2 ξ := by
        rw [freqPow_two]
        have := norm_pos_iff.2 hξ
        positivity
      have e1 : ∀ a, ‖(hatOf (fun y => ∑ j, curlPart j (H y (unitVector a) (unitVector j))) :
          Space → CSpace) ξ‖ ^ 2 = (2 * π) ^ 2 * (ξ a) ^ 2 *
            ∑ j, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ‖ ^ 2 := by
        intro a
        rw [hsum a]
        simp only [ha, map_smul, ← Finset.smul_sum]
        rw [norm_coef_smul, hc]
      simp only [e1]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Freq.Internal.H1Consistency.norm_sq_eq, ← freqPow_two,
        ← h1]
      field_simp
    calc (∫ y, curlGradSq (H y))
        = ∫ y, ∑ a, ‖∑ j, curlPart j (H y (unitVector a) (unitVector j))‖ ^ 2 := by
          simp only [curlGradSq_eq]
      _ = ∑ a, ∫ y, ‖∑ j, curlPart j (H y (unitVector a) (unitVector j))‖ ^ 2 :=
          integral_finsetSum _ fun a _ => hic a
      _ = ∑ a, ∫ ξ, ‖(hatOf (fun y => ∑ j, curlPart j (H y (unitVector a) (unitVector j))) :
          Space → CSpace) ξ‖ ^ 2 :=
          Finset.sum_congr rfl fun a _ => integral_sq_hat (hmc a)
      _ = ∫ ξ, ∑ a, ‖(hatOf (fun y => ∑ j, curlPart j (H y (unitVector a) (unitVector j))) :
          Space → CSpace) ξ‖ ^ 2 :=
          (integral_finsetSum _ fun a _ => hih a).symm
      _ = ∫ ξ, ‖(SteadyCert.secondSymbol H : Space → CSpace) ξ‖ ^ 2 := integral_congr_ae hpt
      _ = _ := htrace.symm
  · have hc3 : (fun y => curlOf (G y)) =
        fun y => ∑ j, curlPart j (WeakProfile.gradComponent G j y) := funext fun y => curlOf_eq _
    have hmc : MemLp (fun y => ∑ j, curlPart j (WeakProfile.gradComponent G j y)) 2 volume :=
      memLp_finsetSum _ fun j _ => (curlPart j).comp_memLp' (hmG j)
    calc (∫ y, ‖curlOf (G y)‖ ^ 2)
        = ∫ ξ, ‖(hatOf (fun y => ∑ j, curlPart j (WeakProfile.gradComponent G j y)) :
            Space → CSpace) ξ‖ ^ 2 := by
          rw [← integral_sq_hat hmc]
          simp only [curlOf_eq, WeakProfile.gradComponent]
      _ = ∫ ξ, ∑ j, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [hat_sum_map curlPart curlPartC curlPart_compat hmG, hcurl] with ξ h1 h2
          rw [h1]
          simp only [hcomp]
          exact h2
      _ = ∑ j, ∫ ξ, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → CSpace) ξ‖ ^ 2 :=
          integral_finsetSum _ fun j _ => hiG j
      _ = ∑ j, ∫ y, ‖G y (unitVector j)‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => (integral_sq_hat (hmG j)).symm
      _ = ∫ y, SteadyCert.entrySq (G y) := by
          unfold SteadyCert.entrySq
          exact (integral_finsetSum _ fun j _ => hphysG j).symm

end CellCert

end Breakdown

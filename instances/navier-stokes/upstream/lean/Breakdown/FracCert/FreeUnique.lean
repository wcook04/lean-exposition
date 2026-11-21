import Breakdown.FracCert.StFree

open scoped ContDiff ENNReal
open MeasureTheory Real Filter Topology ContinuousLinearMap
open scoped Convolution

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeUnique.Internal

theorem clm_zero_of_unit {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F)
    (h : ∀ j, L (unitVector j) = 0) : L = 0 := by
  have h' : ∀ j, L (EuclideanSpace.single j 1) = 0 := h
  ext1 v
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, h']

theorem conv_deriv_zero (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (hw : IsWeakGradientOf v G) (hG : ∀ᵐ y ∂volume, G y = 0)
    (f : Space → ℝ) (hfs : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (z : Space) (j : Fin 3) :
    ∫ t, (fderiv ℝ f (z - t) (unitVector j)) • v t = 0 := by
  set φ : Space → ℝ := fun t => f (z - t) with hφ
  have hφs : ContDiff ℝ ∞ φ := hfs.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hfc.comp_homeomorph (Homeomorph.subLeft z)
  have hd : ∀ t, fderiv ℝ φ t (unitVector j) = -(fderiv ℝ f (z - t) (unitVector j)) := by
    intro t
    have h1 : HasFDerivAt φ ((fderiv ℝ f (z - t)).comp (0 - ContinuousLinearMap.id ℝ Space)) t :=
      ((hfs.differentiable (by simp)) (z - t)).hasFDerivAt.comp t
        ((hasFDerivAt_const z t).sub (hasFDerivAt_id t))
    rw [h1.fderiv]
    simp
  have key := hw φ ⟨hφs, hφc⟩ j
  have hr : ∫ y, φ y • G y (unitVector j) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hG] with y hy
    simp [hy]
  rw [hr, neg_zero] at key
  simp only [hd, neg_smul, integral_neg, neg_eq_zero] at key
  exact key

theorem conv_const (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (hloc : LocallyIntegrable v volume) (hw : IsWeakGradientOf v G) (hG : ∀ᵐ y ∂volume, G y = 0)
    (ρ : ContDiffBump (0 : Space)) (x : Space) :
    ((ρ.normed volume) ⋆[lsmul ℝ ℝ, volume] v) x = ((ρ.normed volume) ⋆[lsmul ℝ ℝ, volume] v) 0 := by
  have hfs : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hfc : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  have h1 : ContDiff ℝ 1 (ρ.normed volume) := hfs.of_le (by exact_mod_cast le_top)
  rw [← convolution_flip]
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ)
  · intro z
    exact (hfc.hasFDerivAt_convolution_right _ hloc h1 z).differentiableAt
  · intro z
    rw [(hfc.hasFDerivAt_convolution_right _ hloc h1 z).fderiv]
    apply clm_zero_of_unit
    intro j
    have hex := (hfc.fderiv (𝕜 := ℝ)).convolutionExists_right ((lsmul ℝ ℝ).flip.precompR Space) hloc
      (h1.continuous_fderiv (by simp)) z
    rw [convolution_def, ContinuousLinearMap.integral_apply hex]
    simpa using conv_deriv_zero v G hw hG _ hfs hfc z j

theorem velocity_zero (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (hv : MemLp v 6 volume)
    (hw : IsWeakGradientOf v G) (hG : ∀ᵐ y ∂volume, G y = 0) : ∀ᵐ y ∂volume, v y = 0 := by
  have hloc : LocallyIntegrable v volume := hv.locallyIntegrable (by norm_num)
  let ρ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1)), by positivity, by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
  have hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := by
    simpa [ρ] using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (K := 2) hρ
    (Eventually.of_forall fun n => le_refl _) hloc
  have hae' : ∀ᵐ x ∂volume, Tendsto (fun n => ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] v) 0) atTop
      (𝓝 (v x)) := by
    filter_upwards [hae] with x hx
    simpa only [conv_const v G hloc hw hG _ x] using hx
  have : (ae (volume : Measure Space)).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨x0, hx0⟩ := hae'.exists
  have hconst : ∀ᵐ x ∂volume, v x = v x0 := by
    filter_upwards [hae'] with x hx
    exact tendsto_nhds_unique hx hx0
  have hm : MemLp (fun _ : Space => v x0) 6 volume := hv.ae_eq hconst
  rcases (memLp_const_iff (by norm_num) (by norm_num)).1 hm with h | h
  · filter_upwards [hconst] with x hx
    exact hx.trans h
  · rw [measure_univ_of_isAddLeftInvariant] at h
    exact absurd h (lt_irrefl _)

theorem second_zero_of_energy {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h1 : SecondSymbolEnergyStatement)
    (hF : IsSecondOrderField m v G H)
    (hS : ∀ᵐ ξ ∂volume, (secondSymbol H : Space → Freq.CSpace) ξ = 0) :
    (∀ᵐ y ∂volume, G y = 0) ∧ ∀ᵐ y ∂volume, H y = 0 := by
  obtain ⟨-, hGe, hHe, -⟩ := h1 m v G H hF
  have hGi : ∫ y, entrySq (G y) = 0 := by
    rw [hGe]
    apply integral_eq_zero_of_ae
    filter_upwards [hS] with ξ h
    simp [h]
  have hHi : ∫ y, fullSecondSq (H y) = 0 := by
    rw [hHe]
    apply integral_eq_zero_of_ae
    filter_upwards [hS] with ξ h
    simp [h]
  have hGn : ∀ y, 0 ≤ entrySq (G y) := fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hHn : ∀ y, 0 ≤ fullSecondSq (H y) := fun y =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hHint : Integrable (fun y => fullSecondSq (H y)) volume := hF.second_two
  have hGa := (integral_eq_zero_iff_of_nonneg hGn hF.gradient_two).1 hGi
  have hHa := (integral_eq_zero_iff_of_nonneg hHn hHint).1 hHi
  refine ⟨?_, ?_⟩
  · filter_upwards [hGa] with y hy
    have hy' : entrySq (G y) = 0 := hy
    unfold entrySq at hy'
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at hy'
    apply clm_zero_of_unit
    intro i
    simpa using hy' i (Finset.mem_univ _)
  · filter_upwards [hHa] with y hy
    have hy' : fullSecondSq (H y) = 0 := hy
    unfold fullSecondSq at hy'
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)] at hy'
    apply clm_zero_of_unit
    intro i
    apply clm_zero_of_unit
    intro j
    have hi := hy' i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at hi
    simpa using hi j (Finset.mem_univ _)

end FreeUnique.Internal

open FreeUnique.Internal

theorem freeUnique_of (h1 : SecondSymbolEnergyStatement) (h2 : WeakPowerSymbolStatement)
    (h3 : DriftPowerStatement) : FreeUniqueStatement := by
  intro α hα1 hα2 a m v G H P hF hP hD hsum
  obtain ⟨hI, hpair⟩ := h3 α hα1 hα2 a m v G H P hF hP hD
  have hfp : ∀ s ξ, 0 ≤ freqPow s ξ := fun s ξ => Real.rpow_nonneg (by positivity) s
  have hI0 : 0 ≤ ∫ ξ, freqPow (2 * α - 4) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 :=
    integral_nonneg fun ξ => mul_nonneg (hfp _ _) (sq_nonneg _)
  have hc : 0 < 3 / 2 - 5 / (4 * α) := by
    have h4 : 5 / (4 * α) < 5 / 4 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  have hpairP : l2Pair (driftField α a v G) P = -∫ y, ‖P y‖ ^ 2 := by
    unfold l2Pair
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hsum] with y hy
    have hy' : driftField α a v G y = -P y := eq_neg_of_add_eq_zero_left hy
    simp [hy']
  have hPint : Integrable (fun y => ‖P y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hP.1.1).1 hP.1
  have hPn : 0 ≤ ∫ y, ‖P y‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hprod := mul_nonneg hc.le hI0
  have hPsq : ∫ y, ‖P y‖ ^ 2 = 0 := by linarith
  have hIz : ∫ ξ, freqPow (2 * α - 4) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 = 0 := by
    have : (3 / 2 - 5 / (4 * α)) *
        ∫ ξ, freqPow (2 * α - 4) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc.ne'
    · exact h
  have hPz : ∀ᵐ y ∂volume, P y = 0 := by
    have ha := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg ‖P y‖) hPint).1 hPsq
    filter_upwards [ha] with y hy
    simpa using hy
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    rw [ae_iff]
    simp
  have hS : ∀ᵐ ξ ∂volume, (secondSymbol H : Space → Freq.CSpace) ξ = 0 := by
    have ha := (integral_eq_zero_iff_of_nonneg
      (fun ξ => mul_nonneg (hfp (2 * α - 4) ξ) (sq_nonneg ‖(secondSymbol H : Space → Freq.CSpace) ξ‖))
      hI).1 hIz
    filter_upwards [ha, hne] with ξ hξ hξ0
    have hpos : 0 < freqPow (2 * α - 4) ξ := by
      have : 0 < ‖ξ‖ := norm_pos_iff.2 hξ0
      exact Real.rpow_pos_of_pos (by positivity) _
    simp only [Pi.zero_apply] at hξ
    rcases mul_eq_zero.1 hξ with h | h
    · exact absurd h hpos.ne'
    · simpa using h
  obtain ⟨hGz, hHz⟩ := second_zero_of_energy h1 hF hS
  exact ⟨velocity_zero v G hF.velocity_six hF.weak_gradient hGz, hGz, hHz, hPz⟩

end SteadyCert

end Breakdown

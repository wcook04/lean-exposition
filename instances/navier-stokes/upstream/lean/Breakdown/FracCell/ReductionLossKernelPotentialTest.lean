import Breakdown.FracCell.ReductionLossDefs
import Breakdown.Uniqueness.FundSolByParts
import Breakdown.Uniqueness.FundSolPointwiseAux3

open scoped ContDiff ENNReal Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace FracInternal

namespace KernelPotentialTestInternal

open SteadyCert CellCert.Reduction


theorem potential_nonpos (W : Space → ℝ) (hW0 : ∀ y, 0 ≤ W y) (x : Space) :
    FundSol.potential W x ≤ 0 := by
  unfold FundSol.potential
  rw [convolution_def]
  refine integral_nonpos fun t => ?_
  simp only [Pi.zero_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, FundSol.kernel]
  have := hW0 t
  have h2 : 0 ≤ ‖x - t‖⁻¹ := by positivity
  have h3 : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  nlinarith [mul_nonneg this (mul_nonneg h3 h2)]

theorem smoothCase (W : Space → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hW0 : ∀ y, 0 ≤ W y) (Λ : ℝ) (hΨ : ∀ x, -FundSol.potential W x ≤ Λ) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (δ : ℝ) (hδ : 0 < δ) :
    ∫ y, W y * φ y ^ 2 ≤ (Λ + δ) * ∫ y, ∑ j : Fin 3, (fderiv ℝ φ y (unitVector j)) ^ 2 := by
  set P := FundSol.potential W with hPdef
  have hP : ContDiff ℝ ∞ P := FundSol.contDiff_potential hW hWc
  set Ψ : Space → ℝ := fun x => -P x + δ with hΨdef
  have hΨs : ContDiff ℝ ∞ Ψ := hP.neg.add contDiff_const
  have hΨpos : ∀ x, 0 < Ψ x := fun x => by
    have := potential_nonpos W hW0 x
    simp only [hΨdef]
    linarith
  have hΨle : ∀ x, Ψ x ≤ Λ + δ := fun x => by
    have := hΨ x
    simp only [hΨdef]
    linarith
  have hPd : ∀ x, HasFDerivAt P (fderiv ℝ P x) x := fun x =>
    (hP.differentiable (by simp) x).hasFDerivAt
  have hφd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x := fun x =>
    (hφ.differentiable (by simp) x).hasFDerivAt
  have hΨd : ∀ x e, fderiv ℝ Ψ x e = -fderiv ℝ P x e := fun x e => by
    have h : HasFDerivAt Ψ (-fderiv ℝ P x) x := (hPd x).neg.add_const δ
    rw [h.fderiv]
    simp
  set h : Space → ℝ := fun x => φ x ^ 2 * (Ψ x)⁻¹ with hhdef
  have hhs : ContDiff ℝ ∞ h := (hφ.pow 2).mul (hΨs.inv fun x => (hΨpos x).ne')
  have hhc : HasCompactSupport h := hφc.mono fun x hx => by
    intro h0
    apply hx
    simp [hhdef, h0]
  have hhd : ∀ x e, fderiv ℝ h x e =
      2 * φ x * fderiv ℝ φ x e / Ψ x + φ x ^ 2 * fderiv ℝ P x e / Ψ x ^ 2 := fun x e => by
    have hΨx : HasFDerivAt Ψ (fderiv ℝ Ψ x) x := (hΨs.differentiable (by simp) x).hasFDerivAt
    have hne := (hΨpos x).ne'
    have hi : HasFDerivAt (fun y => (Ψ y)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(Ψ x ^ 2)⁻¹)).comp (fderiv ℝ Ψ x)) x :=
      (hasFDerivAt_inv hne).comp x hΨx
    have h1 := ((hφd x).pow 2).mul hi
    rw [show h = (fun y => φ y ^ 2) * (fun y => (Ψ y)⁻¹) from rfl, h1.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, hΨd]
    field_simp
    ring
  set f : Fin 3 → Space → ℝ := fun j x => fderiv ℝ P x (unitVector j) with hfdef
  have hfs : ∀ j, ContDiff ℝ ∞ (f j) := fun j =>
    (hP.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hhdc : ∀ e, HasCompactSupport (fun x => fderiv ℝ h x e) := fun e =>
    hhc.fderiv_apply (𝕜 := ℝ) e
  have hhdcont : ∀ e, Continuous (fun x => fderiv ℝ h x e) := fun e =>
    (hhs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hIBP : ∀ j, ∫ x, f j x * fderiv ℝ h x (unitVector j) =
      -∫ x, FundSol.secondPartial P j j x * h x := by
    intro j
    have hsp : ∀ x, fderiv ℝ (f j) x (unitVector j) = FundSol.secondPartial P j j x := fun x =>
      (FundSol.Internal.secondPartial_eq_dir hP j j x).symm
    have hfdc : Continuous (fun x => fderiv ℝ (f j) x (unitVector j)) :=
      ((hfs j).continuous_fderiv (by simp)).clm_apply continuous_const
    have h1 : Integrable (fun x => fderiv ℝ (f j) x (unitVector j) * h x) :=
      (hfdc.mul hhs.continuous).integrable_of_hasCompactSupport hhc.mul_left
    have h2 : Integrable (fun x => f j x * fderiv ℝ h x (unitVector j)) :=
      ((hfs j).continuous.mul (hhdcont _)).integrable_of_hasCompactSupport (hhdc _).mul_left
    have h3 : Integrable (fun x => f j x * h x) :=
      ((hfs j).continuous.mul hhs.continuous).integrable_of_hasCompactSupport hhc.mul_left
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
      (fun x _ => (hfs j).differentiable (by simp) x) (fun x _ => hhs.differentiable (by simp) x)]
    simp only [hsp]
  have hspI : ∀ j, Integrable (fun x => FundSol.secondPartial P j j x * h x) := fun j =>
    ((FundSol.Internal.continuous_secondPartial hP j j).mul hhs.continuous).integrable_of_hasCompactSupport
      hhc.mul_left
  have hfhI : ∀ j, Integrable (fun x => f j x * fderiv ℝ h x (unitVector j)) := fun j =>
    ((hfs j).continuous.mul (hhdcont _)).integrable_of_hasCompactSupport (hhdc _).mul_left
  have hWh : ∫ x, W x * h x = ∫ x, -∑ j, f j x * fderiv ℝ h x (unitVector j) := by
    rw [integral_neg, integral_finsetSum _ fun j _ => hfhI j]
    simp only [hIBP, Finset.sum_neg_distrib, neg_neg]
    rw [← integral_finsetSum _ fun j _ => hspI j]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Finset.sum_mul]
    have hl := FundSol.scalarSumSecondPartials_potential hW hWc x
    simp only [FundSol.scalarSumSecondPartials] at hl
    rw [hl]
  have hpt : ∀ x, -∑ j, f j x * fderiv ℝ h x (unitVector j) ≤
      ∑ j : Fin 3, (fderiv ℝ φ x (unitVector j)) ^ 2 := by
    intro x
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hhd]
    have hq := hΨpos x
    set t := φ x / Ψ x with ht
    have e1 : -(f j x * (2 * φ x * fderiv ℝ φ x (unitVector j) / Ψ x +
        φ x ^ 2 * fderiv ℝ P x (unitVector j) / Ψ x ^ 2)) =
        -(2 * t * f j x * fderiv ℝ φ x (unitVector j) + t ^ 2 * f j x ^ 2) := by
      simp only [ht, hfdef]
      field_simp
    rw [e1]
    nlinarith [sq_nonneg (fderiv ℝ φ x (unitVector j) + t * f j x)]
  have hgradI : Integrable (fun x => ∑ j : Fin 3, (fderiv ℝ φ x (unitVector j)) ^ 2) :=
    (continuous_finsetSum _ fun j _ =>
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro' hφc.isCompact (isClosed_tsupport φ) fun x hx => by
        have : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
        simp [this])
  have hnegI : Integrable (fun x => -∑ j, f j x * fderiv ℝ h x (unitVector j)) :=
    (integrable_finsetSum _ fun j _ => hfhI j).neg
  have hWhle : ∫ x, W x * h x ≤ ∫ x, ∑ j : Fin 3, (fderiv ℝ φ x (unitVector j)) ^ 2 := by
    rw [hWh]
    exact integral_mono hnegI hgradI hpt
  have hWhI : Integrable (fun x => W x * h x) :=
    (hW.continuous.mul hhs.continuous).integrable_of_hasCompactSupport hhc.mul_left
  have hWφI : Integrable (fun x => W x * φ x ^ 2) :=
    (hW.continuous.mul (hφ.continuous.pow 2)).integrable_of_hasCompactSupport hWc.mul_right
  have hptW : ∀ x, W x * φ x ^ 2 ≤ (Λ + δ) * (W x * h x) := by
    intro x
    have hq := hΨpos x
    have hle := hΨle x
    have hw := hW0 x
    have e2 : W x * φ x ^ 2 = Ψ x * (W x * h x) := by
      simp only [hhdef]
      field_simp
    rw [e2]
    have : 0 ≤ W x * h x := by
      simp only [hhdef]
      positivity
    exact mul_le_mul_of_nonneg_right hle this
  calc ∫ y, W y * φ y ^ 2 ≤ ∫ y, (Λ + δ) * (W y * h y) := integral_mono hWφI (hWhI.const_mul _) hptW
    _ = (Λ + δ) * ∫ y, W y * h y := integral_const_mul _ _
    _ ≤ (Λ + δ) * ∫ y, ∑ j : Fin 3, (fderiv ℝ φ y (unitVector j)) ^ 2 := by
      have : 0 ≤ Λ + δ := le_trans (hΨpos 0).le (hΨle 0)
      exact mul_le_mul_of_nonneg_left hWhle this


theorem mollPotential (V : Space → ℝ) (Λ : ℝ) (hK : KernelBound V Λ) (U : Space → ℝ)
    (hU0 : ∀ y, 0 ≤ U y) (hUV : ∀ y, U y ≤ V y) (hUm : Measurable U) (hUi : Integrable U)
    (ρ : ContDiffBump (0 : Space)) (x : Space) :
    -FundSol.potential (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) x ≤ Λ := by
  have hΛ : 0 ≤ Λ := le_trans (integral_nonneg fun y => by have := hK.1 y; positivity) (hK.2.2 0).2
  set ρn := ρ.normed volume with hρn
  set W := ρn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U with hWdef
  have hWc : Continuous W :=
    (ρ.hasCompactSupport_normed.contDiff_convolution_left (n := 0) _ ρ.contDiff_normed
      hUi.locallyIntegrable).continuous
  have hW : ∀ t, W t = ∫ s, ρn s * U (t - s) := fun t => by
    simp only [hWdef, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hW0 : ∀ t, 0 ≤ W t := fun t => by
    rw [hW]
    exact integral_nonneg fun s => mul_nonneg (ρ.nonneg_normed s) (hU0 _)
  set k : Space → ℝ := fun t => (4 * Real.pi)⁻¹ * ‖x - t‖⁻¹ with hk
  have hk0 : ∀ t, 0 ≤ k t := fun t => by simp only [hk]; positivity
  have hkm : Measurable k := by
    simp only [hk]
    fun_prop
  have hpot : -FundSol.potential W x = ∫ t, W t * k t := by
    unfold FundSol.potential
    rw [convolution_def, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, FundSol.kernel, hk]
    ring
  rw [hpot]
  have hρm : Measurable ρn := ρ.continuous_normed.measurable
  have hWs : ∀ t, ENNReal.ofReal (W t) ≤ ∫⁻ s, ENNReal.ofReal (ρn s) * ENNReal.ofReal (U (t - s)) := by
    intro t
    have hm : AEStronglyMeasurable (fun s => ρn s * U (t - s)) volume :=
      (hρm.mul (hUm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    rw [hW, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s =>
      mul_nonneg (ρ.nonneg_normed s) (hU0 _)) hm]
    refine ENNReal.ofReal_toReal_le.trans (le_of_eq ?_)
    refine lintegral_congr fun s => ?_
    rw [ENNReal.ofReal_mul (ρ.nonneg_normed s)]
  have hinner : ∀ s, ∫⁻ t, ENNReal.ofReal (U (t - s)) * ENNReal.ofReal (k t) ≤ ENNReal.ofReal Λ := by
    intro s
    have htr := lintegral_add_right_eq_self (μ := (volume : Measure Space))
      (fun t => ENNReal.ofReal (U (t - s)) * ENNReal.ofReal (k t)) s
    rw [← htr]
    obtain ⟨hI, hle⟩ := hK.2.2 (x - s)
    have hVn : 0 ≤ᵐ[volume] fun y => V y / (4 * Real.pi * ‖x - s - y‖) :=
      ae_of_all _ fun y => by have := hK.1 y; positivity
    calc ∫⁻ w, ENNReal.ofReal (U (w + s - s)) * ENNReal.ofReal (k (w + s))
        ≤ ∫⁻ w, ENNReal.ofReal (V w / (4 * Real.pi * ‖x - s - w‖)) := by
          refine lintegral_mono fun w => ?_
          rw [← ENNReal.ofReal_mul (hU0 _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : w + s - s = w := by abel
          have e2 : x - (w + s) = x - s - w := by abel
          simp only [e1, hk, e2]
          have e3 : (4 * Real.pi)⁻¹ * ‖x - s - w‖⁻¹ = (4 * Real.pi * ‖x - s - w‖)⁻¹ := (mul_inv _ _).symm
          rw [e3, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hUV w) (by positivity)
      _ = ENNReal.ofReal (∫ y, V y / (4 * Real.pi * ‖x - s - y‖)) :=
          (ofReal_integral_eq_lintegral_ofReal hI hVn).symm
      _ ≤ ENNReal.ofReal Λ := ENNReal.ofReal_le_ofReal hle
  have hmeas : AEMeasurable (Function.uncurry fun t s =>
      ENNReal.ofReal (ρn s) * (ENNReal.ofReal (U (t - s)) * ENNReal.ofReal (k t)))
      ((volume : Measure Space).prod volume) := by
    refine Measurable.aemeasurable ?_
    have h1 : Measurable fun p : Space × Space => U (p.1 - p.2) := hUm.comp (measurable_fst.sub measurable_snd)
    have h2 : Measurable fun p : Space × Space => ρn p.2 := hρm.comp measurable_snd
    have h3 : Measurable fun p : Space × Space => k p.1 := hkm.comp measurable_fst
    exact h2.ennreal_ofReal.mul (h1.ennreal_ofReal.mul h3.ennreal_ofReal)
  have hA : ∫⁻ t, ENNReal.ofReal (W t * k t) ≤ ENNReal.ofReal Λ := by
    calc ∫⁻ t, ENNReal.ofReal (W t * k t)
        ≤ ∫⁻ t, (∫⁻ s, ENNReal.ofReal (ρn s) * ENNReal.ofReal (U (t - s))) * ENNReal.ofReal (k t) := by
          refine lintegral_mono fun t => ?_
          rw [ENNReal.ofReal_mul (hW0 t)]
          exact mul_le_mul_left (hWs t) _
      _ ≤ ∫⁻ t, ∫⁻ s, ENNReal.ofReal (ρn s) * (ENNReal.ofReal (U (t - s)) * ENNReal.ofReal (k t)) := by
          refine lintegral_mono fun t => ?_
          refine (lintegral_mul_const_le _ _).trans (le_of_eq ?_)
          refine lintegral_congr fun s => ?_
          ring
      _ = ∫⁻ s, ∫⁻ t, ENNReal.ofReal (ρn s) * (ENNReal.ofReal (U (t - s)) * ENNReal.ofReal (k t)) :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ s, ENNReal.ofReal (ρn s) * ∫⁻ t, ENNReal.ofReal (U (t - s)) * ENNReal.ofReal (k t) := by
          refine lintegral_congr fun s => ?_
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ s, ENNReal.ofReal (ρn s) * ENNReal.ofReal Λ :=
          lintegral_mono fun s => mul_le_mul_right (hinner s) _
      _ = (∫⁻ s, ENNReal.ofReal (ρn s)) * ENNReal.ofReal Λ :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal Λ := by
          rw [← ofReal_integral_eq_lintegral_ofReal ρ.integrable_normed
            (ae_of_all _ fun s => ρ.nonneg_normed s), ρ.integral_normed]
          simp
  have hWk : AEStronglyMeasurable (fun t => W t * k t) volume :=
    (hWc.measurable.mul hkm).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => mul_nonneg (hW0 t) (hk0 t)) hWk]
  exact ENNReal.toReal_le_of_le_ofReal hΛ hA


theorem mollCase (V : Space → ℝ) (Λ : ℝ) (hK : KernelBound V Λ) (U : Space → ℝ)
    (hU0 : ∀ y, 0 ≤ U y) (hUV : ∀ y, U y ≤ V y) (hUm : Measurable U) (hUi : Integrable U)
    (hUc : HasCompactSupport U) (ρ : ContDiffBump (0 : Space)) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) y * φ y ^ 2 ≤
      Λ * ∫ y, ∑ j : Fin 3, (fderiv ℝ φ y (unitVector j)) ^ 2 := by
  set W := ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U with hWdef
  have hWs : ContDiff ℝ ∞ W :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed hUi.locallyIntegrable
  have hWc : HasCompactSupport W := ρ.hasCompactSupport_normed.convolution _ hUc
  have hW0 : ∀ t, 0 ≤ W t := fun t => by
    simp only [hWdef, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact integral_nonneg fun s => mul_nonneg (ρ.nonneg_normed s) (hU0 _)
  have hP := mollPotential V Λ hK U hU0 hUV hUm hUi ρ
  set Y := ∫ y, ∑ j : Fin 3, (fderiv ℝ φ y (unitVector j)) ^ 2 with hY
  have hY0 : 0 ≤ Y := integral_nonneg fun y => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (Y + 1) := by positivity
  have h := smoothCase W hWs hWc hW0 Λ hP φ hφ hφc (ε / (Y + 1)) hδ
  refine h.trans ?_
  have : ε / (Y + 1) * Y ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem scalarCase (V : Space → ℝ) (Λ : ℝ) (hK : KernelBound V Λ) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun y => V y * φ y ^ 2) ∧
      ∫ y, V y * φ y ^ 2 ≤ Λ * ∫ y, ∑ j : Fin 3, (fderiv ℝ φ y (unitVector j)) ^ 2 := by
  have hΛ : 0 ≤ Λ := le_trans (integral_nonneg fun y => by have := hK.1 y; positivity) (hK.2.2 0).2
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : tsupport φ ⊆ Metric.closedBall 0 R := hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set U := (Metric.closedBall (0 : Space) R).indicator V with hUdef
  have hU0 : ∀ y, 0 ≤ U y := fun y => by
    simp only [hUdef, Set.indicator]
    split_ifs
    · exact hK.1 y
    · exact le_rfl
  have hUV : ∀ y, U y ≤ V y := fun y => by
    simp only [hUdef, Set.indicator]
    split_ifs
    · exact le_rfl
    · exact hK.1 y
  have hUm : Measurable U := hK.2.1.indicator Metric.isClosed_closedBall.measurableSet
  have hUc : HasCompactSupport U := HasCompactSupport.intro (isCompact_closedBall 0 R) fun y hy => by
    simp only [hUdef, Set.indicator_of_notMem hy]
  have hUi : Integrable U := by
    obtain ⟨hI, -⟩ := hK.2.2 0
    refine (hI.const_mul (4 * Real.pi * R)).mono' hUm.aestronglyMeasurable ?_
    have h0 : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
      have : (volume : Measure Space) {(0 : Space)} = 0 := measure_singleton 0
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with y hy
      simpa using hy
    filter_upwards [h0] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hU0 y)]
    have hVy := hK.1 y
    have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hz : ‖(0 : Space) - y‖ = ‖y‖ := by simp
    rw [hz]
    simp only [hUdef, Set.indicator]
    split_ifs with hmem
    · have hyR : ‖y‖ ≤ R := by simpa using hmem
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have : V y * ‖y‖ ≤ V y * R := mul_le_mul_of_nonneg_left hyR hVy
      nlinarith [Real.pi_pos]
    · positivity
  have hUφ : ∀ y, U y * φ y ^ 2 = V y * φ y ^ 2 := fun y => by
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · simp only [hUdef, Set.indicator_of_mem hy]
    · have : φ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hsub h)
      simp [this]
  set Y := ∫ y, ∑ j : Fin 3, (fderiv ℝ φ y (unitVector j)) ^ 2 with hY
  have hY0 : 0 ≤ Y := integral_nonneg fun y => Finset.sum_nonneg fun j _ => sq_nonneg _
  let ρ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith⟩
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun n => ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) y)
      atTop (𝓝 (U y)) := by
    refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := ρ) (K := 2) ?_ ?_
      hUi.locallyIntegrable
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · refine Eventually.of_forall fun n => le_of_eq ?_
      show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
      field_simp
  set f : ℕ → Space → ℝ := fun n y =>
    ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) y * φ y ^ 2 with hf
  have hfc : ∀ n, Continuous (f n) := fun n =>
    ((ρ n).hasCompactSupport_normed.contDiff_convolution_left (n := 0) _ (ρ n).contDiff_normed
      hUi.locallyIntegrable).continuous.mul (hφ.continuous.pow 2)
  have hfi : ∀ n, Integrable (f n) := fun n =>
    (hfc n).integrable_of_hasCompactSupport
      (HasCompactSupport.mono (f' := fun y => φ y ^ 2) hφc fun y hy h0 => hy (by simp [h0])).mul_left
  have hfn : ∀ n y, 0 ≤ f n y := fun n y => by
    simp only [hf, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_nonneg (integral_nonneg fun s => mul_nonneg ((ρ n).nonneg_normed s) (hU0 _)) (sq_nonneg _)
  have hbound : ∀ n, ∫ y, f n y ≤ Λ * Y := fun n =>
    mollCase V Λ hK U hU0 hUV hUm hUi hUc (ρ n) φ hφ hφc
  have hpt : ∀ᵐ y ∂volume, Tendsto (fun n => f n y) atTop (𝓝 (V y * φ y ^ 2)) := by
    filter_upwards [hlim] with y hy
    rw [← hUφ y]
    exact hy.mul_const _
  have hgm : AEStronglyMeasurable (fun y => V y * φ y ^ 2) volume :=
    (hK.2.1.mul (hφ.continuous.measurable.pow_const 2)).aestronglyMeasurable
  have hg0 : 0 ≤ᵐ[volume] fun y => V y * φ y ^ 2 := ae_of_all _ fun y => by
    have := hK.1 y
    positivity
  have hfat : ∫⁻ y, ENNReal.ofReal (V y * φ y ^ 2) ≤ ENNReal.ofReal (Λ * Y) := by
    calc ∫⁻ y, ENNReal.ofReal (V y * φ y ^ 2)
        = ∫⁻ y, liminf (fun n => ENNReal.ofReal (f n y)) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hpt] with y hy
          exact ((ENNReal.tendsto_ofReal hy).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (f n y)) atTop :=
          lintegral_liminf_le' fun n => ((hfc n).measurable.ennreal_ofReal).aemeasurable
      _ ≤ liminf (fun n => ENNReal.ofReal (Λ * Y)) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hfn n))]
          exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = ENNReal.ofReal (Λ * Y) := liminf_const _
  have hint : Integrable (fun y => V y * φ y ^ 2) :=
    ⟨hgm, (hasFiniteIntegral_iff_ofReal hg0).2 (lt_of_le_of_lt hfat ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hΛ hY0) hfat

theorem gradSq_integrable (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => ∑ j : Fin 3, (fderiv ℝ φ x (unitVector j)) ^ 2) :=
  (continuous_finsetSum _ fun j _ =>
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.intro' hφc.isCompact (isClosed_tsupport φ) fun x hx => by
      have : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [this])

end KernelPotentialTestInternal

end FracInternal

namespace CellCert

namespace Reduction

open SteadyCert FracInternal.KernelPotentialTestInternal

theorem kernelPotentialTest (V : Space → ℝ) (Λ : ℝ) (hK : KernelBound V Λ) (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Integrable (fun y => V y * ‖u y‖ ^ 2) ∧
      ∫ y, V y * ‖u y‖ ^ 2 ≤ Λ * ∫ y, entrySq (fderiv ℝ u y) := by
  set φ : Fin 3 → Space → ℝ := fun i y => u y i with hφdef
  have hφs : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hu
  have hφc : ∀ i, HasCompactSupport (φ i) := fun i => hc.comp_left (g := fun v : Space => v i) (by simp)
  have hd : ∀ i y e, fderiv ℝ (φ i) y e = fderiv ℝ u y e i := fun i y e => by
    have h := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y
      ((hu.differentiable (by simp) y).hasFDerivAt))
    rw [show φ i = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ u from rfl, h.fderiv]
    simp
  have hS := fun i => scalarCase V Λ hK (φ i) (hφs i) (hφc i)
  have hnorm : ∀ y, V y * ‖u y‖ ^ 2 = ∑ i : Fin 3, V y * φ i y ^ 2 := fun y => by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  have hentry : ∀ y, entrySq (fderiv ℝ u y) =
      ∑ i : Fin 3, ∑ j : Fin 3, (fderiv ℝ (φ i) y (unitVector j)) ^ 2 := fun y => by
    simp only [entrySq, hd, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_comm
  have hI : Integrable (fun y => V y * ‖u y‖ ^ 2) := by
    simp only [hnorm]
    exact integrable_finsetSum _ fun i _ => (hS i).1
  refine ⟨hI, ?_⟩
  simp only [hnorm, hentry]
  rw [integral_finsetSum _ fun i _ => (hS i).1,
    integral_finsetSum _ fun i _ => gradSq_integrable (φ i) (hφs i) (hφc i), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => (hS i).2

end Reduction

end CellCert

end Breakdown

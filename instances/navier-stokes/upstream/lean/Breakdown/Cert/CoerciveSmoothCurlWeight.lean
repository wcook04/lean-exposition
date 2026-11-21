import Breakdown.Cert.CoerciveCurlWeight

open scoped ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothCurlWeight.Internal

open CurlWeight.Internal

theorem compactSupport_of_vanish {φ g : Space → ℝ} (hφ : HasCompactSupport φ)
    (h : ∀ x ∉ tsupport φ, g x = 0) : HasCompactSupport g :=
  hφ.mono' (fun x hx => by
    by_contra h'
    exact hx (h x h'))

theorem identity_of_compactSupport {φ : Space → ℝ} {u : Space → Space} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hu2 : ContDiff ℝ 2 u) (hdiv : ∀ y, divergenceAt u y = 0) :
    ∫ y, φ y * ‖curlVec (fderiv ℝ u y)‖ ^ 2 =
      (∫ y, φ y * matSq (fderiv ℝ u y)) - ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ φ x) y (unitVector i) (unitVector j) * u y i * u y j := by
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu2.fderiv_right (by norm_num)
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hud : ∀ x, HasFDerivAt u (fderiv ℝ u x) x := fun x =>
    ((hu2.differentiable (by norm_num)) x).hasFDerivAt
  have hDud : ∀ x, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x := fun x =>
    ((hDu.differentiable one_ne_zero) x).hasFDerivAt
  have hφd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x := fun x =>
    ((hφ.differentiable (by norm_num)) x).hasFDerivAt
  have hDφd : ∀ x, HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := fun x =>
    ((hφ1.differentiable one_ne_zero) x).hasFDerivAt
  have hU : ∀ (i : Fin 3) x, HasFDerivAt (fun x => u x i)
      ((coordMap i).comp (fderiv ℝ u x)) x := fun i x =>
    (coordMap i).hasFDerivAt.comp x (hud x)
  have hDU : ∀ (i j : Fin 3) x, HasFDerivAt (fun x => fderiv ℝ u x (unitVector i) j)
      ((coordMap j).comp ((fderiv ℝ (fderiv ℝ u) x).flip (unitVector i))) x := by
    intro i j x
    have h1 := (hDud x).clm_apply (hasFDerivAt_const (unitVector i) x)
    exact ((coordMap j).hasFDerivAt.comp x h1).congr_fderiv (by ext v; simp [coordMap_apply])
  have hDΦ : ∀ (i : Fin 3) x, HasFDerivAt (fun x => fderiv ℝ φ x (unitVector i))
      ((fderiv ℝ (fderiv ℝ φ) x).flip (unitVector i)) x := by
    intro i x
    exact ((hDφd x).clm_apply (hasFDerivAt_const (unitVector i) x)).congr_fderiv (by ext v; simp)
  have hsym : ∀ x, IsSymmSndFDerivAt ℝ u x := fun x =>
    hu2.contDiffAt.isSymmSndFDerivAt (by simp)
  have hdiv1 : ∀ x, ∑ j : Fin 3, fderiv ℝ u x (unitVector j) j = 0 := fun x => by
    simpa [divergenceAt] using hdiv x
  have hdiv2 : ∀ x (i : Fin 3),
      ∑ j : Fin 3, fderiv ℝ (fderiv ℝ u) x (unitVector i) (unitVector j) j = 0 := by
    intro x i
    have hdd : HasFDerivAt (fun x => ∑ j : Fin 3, fderiv ℝ u x (unitVector j) j)
        (∑ j : Fin 3, (coordMap j).comp ((fderiv ℝ (fderiv ℝ u) x).flip (unitVector j))) x :=
      HasFDerivAt.fun_sum (fun j _ => hDU j j x)
    have h0 : HasFDerivAt (fun x => ∑ j : Fin 3, fderiv ℝ u x (unitVector j) j)
        (0 : Space →L[ℝ] ℝ) x := by
      have : (fun x => ∑ j : Fin 3, fderiv ℝ u x (unitVector j) j) = fun _ => 0 :=
        funext hdiv1
      rw [this]
      exact hasFDerivAt_const 0 x
    have := congrArg (fun L => L (unitVector i)) (hdd.unique h0)
    simpa [coordMap_apply, sum_apply] using this
  have hkey : ∀ (j : Fin 3) x, fderiv ℝ (fluxField φ u j) x (unitVector j) =
      ∑ i : Fin 3, (fderiv ℝ φ x (unitVector j) * u x i * fderiv ℝ u x (unitVector i) j
        + φ x * fderiv ℝ u x (unitVector j) i * fderiv ℝ u x (unitVector i) j
        + φ x * u x i * fderiv ℝ (fderiv ℝ u) x (unitVector i) (unitVector j) j
        - (fderiv ℝ (fderiv ℝ φ) x (unitVector j) (unitVector i) * u x i * u x j
          + fderiv ℝ φ x (unitVector i) * fderiv ℝ u x (unitVector j) i * u x j
          + fderiv ℝ φ x (unitVector i) * u x i * fderiv ℝ u x (unitVector j) j)) := by
    intro j x
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (((hφd x).mul (hU i x)).mul (hDU i j x)).sub (((hDΦ i x).mul (hU i x)).mul (hU j x)))
    rw [HasFDerivAt.fderiv (f := fluxField φ u j) h, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [coordMap_apply]
    rw [hsym x (unitVector j) (unitVector i)]
    ring
  have halg : ∀ x, ∑ j : Fin 3, fderiv ℝ (fluxField φ u j) x (unitVector j) =
      φ x * (∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ u x (unitVector j) i * fderiv ℝ u x (unitVector i) j)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun x => fderiv ℝ φ x) x (unitVector i) (unitVector j) * u x i * u x j := by
    intro x
    have e1 := hdiv1 x
    have e20 := hdiv2 x 0
    have e21 := hdiv2 x 1
    have e22 := hdiv2 x 2
    simp only [Fin.sum_univ_three] at e1 e20 e21 e22
    simp only [hkey, Fin.sum_univ_three]
    linear_combination (φ x) * (u x 0 * e20 + u x 1 * e21 + u x 2 * e22)
      - (fderiv ℝ φ x (unitVector 0) * u x 0 + fderiv ℝ φ x (unitVector 1) * u x 1
        + fderiv ℝ φ x (unitVector 2) * u x 2) * e1
  have hz : ∀ x ∉ tsupport φ, φ x = 0 ∧ fderiv ℝ φ x = 0 ∧
      fderiv ℝ (fun x => fderiv ℝ φ x) x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h)),
      image_eq_zero_of_notMem_tsupport
        (fun h => hx (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ h)))⟩
  have cu : ∀ i : Fin 3, Continuous (fun x => u x i) := fun i =>
    (coordMap i).continuous.comp hu2.continuous
  have cDu : ∀ i j : Fin 3, Continuous (fun x => fderiv ℝ u x (unitVector i) j) := fun i j =>
    (coordMap j).continuous.comp (hDu.continuous.clm_apply continuous_const)
  have cD2φ : ∀ i j : Fin 3,
      Continuous (fun x => fderiv ℝ (fun x => fderiv ℝ φ x) x (unitVector i) (unitVector j)) :=
    fun i j => ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply
      continuous_const
  have hflux : ∀ j : Fin 3, Integrable (fun x => fderiv ℝ (fluxField φ u j) x (unitVector j)) ∧
      ∫ x, fderiv ℝ (fluxField φ u j) x (unitVector j) = 0 := by
    intro j
    refine integral_fderiv_eq_zero ?_ ?_ (unitVector j)
    · have cdu : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => u x i) := fun i =>
        (coordMap i).contDiff.comp (hu2.of_le (by norm_num))
      have cdDu : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => fderiv ℝ u x (unitVector i) j) := fun i =>
        (coordMap j).contDiff.comp (hDu.clm_apply contDiff_const)
      have cdDφ : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => fderiv ℝ φ x (unitVector i)) := fun i =>
        hφ1.clm_apply contDiff_const
      unfold fluxField
      exact ContDiff.sum (fun i _ => ((((hφ.of_le (by norm_num)).mul (cdu i)).mul (cdDu i)).sub
        (((cdDφ i).mul (cdu i)).mul (cdu j))))
    · refine compactSupport_of_vanish hφc fun x hx => ?_
      simp [fluxField, (hz x hx).1, (hz x hx).2.1]
  have hT : Integrable (fun x => φ x * ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ u x (unitVector j) i * fderiv ℝ u x (unitVector i) j) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφ.continuous.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => (cDu j i).mul (cDu i j))
    · refine compactSupport_of_vanish hφc fun x hx => ?_
      simp [(hz x hx).1]
  have hB : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ φ x) x (unitVector i) (unitVector j) * u x i * u x j) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => ((cD2φ i j).mul (cu i)).mul (cu j)
    · refine compactSupport_of_vanish hφc fun x hx => ?_
      simp [(hz x hx).2.2]
  have hA : Integrable (fun x => φ x * matSq (fderiv ℝ u x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφ.continuous.mul (continuous_finsetSum _ fun i _ =>
        ((hDu.continuous.clm_apply continuous_const).norm.pow 2))
    · refine compactSupport_of_vanish hφc fun x hx => ?_
      simp [(hz x hx).1]
  have hTB : ∫ x, φ x * (∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ u x (unitVector j) i * fderiv ℝ u x (unitVector i) j) =
      ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ φ x) x (unitVector i) (unitVector j) * u x i * u x j := by
    have h0 : ∫ x, ∑ j : Fin 3, fderiv ℝ (fluxField φ u j) x (unitVector j) = 0 := by
      rw [integral_finsetSum _ fun j _ => (hflux j).1]
      exact Finset.sum_eq_zero fun j _ => (hflux j).2
    simp only [halg] at h0
    rw [integral_sub hT hB] at h0
    exact sub_eq_zero.mp h0
  have hpt : ∀ x, φ x * ‖curlVec (fderiv ℝ u x)‖ ^ 2 = φ x * matSq (fderiv ℝ u x)
      - φ x * (∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ u x (unitVector j) i * fderiv ℝ u x (unitVector i) j) := fun x => by
    rw [curl_norm_sq, mul_sub]
  simp only [hpt]
  rw [integral_sub hA hT, hTB]

def bump : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩

def scaleMap (n : ℕ) : Space →L[ℝ] Space := ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Space

def cutoff (n : ℕ) : Space → ℝ := (bump : Space → ℝ) ∘ scaleMap n

def weighted (φ : Space → ℝ) (n : ℕ) : Space → ℝ := fun z => cutoff n z * φ z

theorem scaleMap_apply (n : ℕ) (y : Space) : scaleMap n y = ((n : ℝ) + 1)⁻¹ • y := rfl

theorem norm_scaleMap_apply (n : ℕ) (y : Space) :
    ‖scaleMap n y‖ = ((n : ℝ) + 1)⁻¹ * ‖y‖ := by
  rw [scaleMap_apply, norm_smul, Real.norm_of_nonneg (by positivity)]

theorem norm_scaleMap_le (n : ℕ) : ‖scaleMap n‖ ≤ ((n : ℝ) + 1)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => by
    rw [norm_scaleMap_apply]

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ 2 (cutoff n) :=
  bump.contDiff.comp (scaleMap n).contDiff

theorem cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * ((n : ℝ) + 1))) ?_
  intro x hx
  show bump (scaleMap n x) = 0
  apply bump.zero_of_le_dist
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  rw [dist_zero_right, norm_scaleMap_apply]
  show (2 : ℝ) ≤ _
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

theorem cutoff_eq_one {n : ℕ} {x : Space} (hx : ‖x‖ ≤ (n : ℝ) + 1) : cutoff n x = 1 := by
  show bump (scaleMap n x) = 1
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_scaleMap_apply]
  show _ ≤ (1 : ℝ)
  rw [inv_mul_eq_div, div_le_one (by positivity)]
  exact hx

theorem abs_cutoff_le (n : ℕ) (x : Space) : |cutoff n x| ≤ 1 := by
  show |bump (scaleMap n x)| ≤ 1
  rw [abs_of_nonneg bump.nonneg]
  exact bump.le_one

theorem cutoff_deriv_bound (i : ℕ) (hi : i ≤ 2) : ∃ K, ∀ (n : ℕ) (y : Space),
    (1 + ‖y‖) ^ i * ‖iteratedFDeriv ℝ i (cutoff n) y‖ ≤ K := by
  have hc : Continuous (fun z : Space =>
      (1 + ‖z‖) ^ i * ‖iteratedFDeriv ℝ i (bump : Space → ℝ) z‖) :=
    ((continuous_const.add continuous_norm).pow i).mul
      ((bump.contDiff (n := 2)).continuous_iteratedFDeriv (by exact_mod_cast hi)).norm
  have hs : HasCompactSupport (fun z : Space =>
      (1 + ‖z‖) ^ i * ‖iteratedFDeriv ℝ i (bump : Space → ℝ) z‖) :=
    (bump.hasCompactSupport.iteratedFDeriv i).norm.mul_left
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨K, fun n y => ?_⟩
  have hK' := hK (scaleMap n y)
  rw [Real.norm_of_nonneg (by positivity)] at hK'
  have heq := (scaleMap n).iteratedFDeriv_comp_right (bump.contDiff (n := 2)) y (i := i)
    (by exact_mod_cast hi)
  have hle : ‖iteratedFDeriv ℝ i (cutoff n) y‖ ≤
      ‖iteratedFDeriv ℝ i (bump : Space → ℝ) (scaleMap n y)‖ * (((n : ℝ) + 1)⁻¹) ^ i := by
    rw [cutoff, heq]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact norm_scaleMap_le n
  have hc1 : (1 + ‖y‖) * ((n : ℝ) + 1)⁻¹ ≤ 1 + ‖scaleMap n y‖ := by
    rw [norm_scaleMap_apply]
    have h1 : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    nlinarith [norm_nonneg y]
  calc (1 + ‖y‖) ^ i * ‖iteratedFDeriv ℝ i (cutoff n) y‖
      ≤ (1 + ‖y‖) ^ i * (‖iteratedFDeriv ℝ i (bump : Space → ℝ) (scaleMap n y)‖
          * (((n : ℝ) + 1)⁻¹) ^ i) := by gcongr
    _ = ((1 + ‖y‖) * ((n : ℝ) + 1)⁻¹) ^ i
          * ‖iteratedFDeriv ℝ i (bump : Space → ℝ) (scaleMap n y)‖ := by rw [mul_pow]; ring
    _ ≤ (1 + ‖scaleMap n y‖) ^ i * ‖iteratedFDeriv ℝ i (bump : Space → ℝ) (scaleMap n y)‖ := by
        gcongr
    _ ≤ K := hK'

theorem norm_secondDeriv_eq (f : Space → ℝ) (y : Space) :
    ‖fderiv ℝ (fun x => fderiv ℝ f x) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
  show ‖fderiv ℝ (fderiv ℝ f) y‖ = _
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem weighted_secondDeriv_bound {φ : Space → ℝ} (hφ : ContDiff ℝ 2 φ) {B : ℝ}
    (hB : ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j φ y‖ ≤ B) :
    ∃ K, ∀ (n : ℕ) (y : Space),
      (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y‖ ≤ K := by
  obtain ⟨K0, h0⟩ := cutoff_deriv_bound 0 (by norm_num)
  obtain ⟨K1, h1⟩ := cutoff_deriv_bound 1 (by norm_num)
  obtain ⟨K2, h2⟩ := cutoff_deriv_bound 2 le_rfl
  refine ⟨K0 * B + 2 * (K1 * B) + K2 * B, fun n y => ?_⟩
  have hm : ‖iteratedFDeriv ℝ 2 (weighted φ n) y‖ ≤ ∑ i ∈ Finset.range (2 + 1),
      ((Nat.choose 2 i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i (cutoff n) y‖
        * ‖iteratedFDeriv ℝ (2 - i) φ y‖ :=
    norm_iteratedFDeriv_mul_le (cutoff_contDiff n) hφ y (n := 2) le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    show Nat.choose 2 0 = 1 from rfl, show Nat.choose 2 1 = 2 from rfl,
    show Nat.choose 2 2 = 1 from rfl, Nat.cast_one, Nat.cast_ofNat] at hm
  rw [norm_secondDeriv_eq]
  have k0 : 0 ≤ K0 := le_trans (by positivity) (h0 n y)
  have k1 : 0 ≤ K1 := le_trans (by positivity) (h1 n y)
  have k2 : 0 ≤ K2 := le_trans (by positivity) (h2 n y)
  have e0 := mul_le_mul (h0 n y) (hB y 2 le_rfl) (by positivity) k0
  have e1 := mul_le_mul (h1 n y) (hB y 1 (by norm_num)) (by positivity) k1
  have e2 := mul_le_mul (h2 n y) (hB y 0 (by norm_num)) (by positivity) k2
  calc (1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ 2 (weighted φ n) y‖
      ≤ (1 + ‖y‖) ^ 2 * (1 * ‖iteratedFDeriv ℝ 0 (cutoff n) y‖ * ‖iteratedFDeriv ℝ 2 φ y‖
        + 2 * ‖iteratedFDeriv ℝ 1 (cutoff n) y‖ * ‖iteratedFDeriv ℝ 1 φ y‖
        + 1 * ‖iteratedFDeriv ℝ 2 (cutoff n) y‖ * ‖iteratedFDeriv ℝ 0 φ y‖) := by gcongr
    _ = ((1 + ‖y‖) ^ 0 * ‖iteratedFDeriv ℝ 0 (cutoff n) y‖)
          * ((1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ 2 φ y‖)
        + 2 * (((1 + ‖y‖) ^ 1 * ‖iteratedFDeriv ℝ 1 (cutoff n) y‖)
          * ((1 + ‖y‖) ^ 1 * ‖iteratedFDeriv ℝ 1 φ y‖))
        + ((1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ 2 (cutoff n) y‖)
          * ((1 + ‖y‖) ^ 0 * ‖iteratedFDeriv ℝ 0 φ y‖) := by ring
    _ ≤ K0 * B + 2 * (K1 * B) + K2 * B := by linarith

theorem weighted_eventuallyEq (φ : Space → ℝ) (y : Space) :
    ∀ᶠ n in atTop, weighted φ n =ᶠ[𝓝 y] φ := by
  obtain ⟨N, hN⟩ := exists_nat_ge (‖y‖ + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  filter_upwards [Metric.ball_mem_nhds y one_pos] with z hz
  have hz' : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have : ‖z‖ ≤ (n : ℝ) + 1 := by linarith
  show cutoff n z * φ z = φ z
  rw [cutoff_eq_one this, one_mul]

theorem curl_sq_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ^ 2 ≤ 2 * matSq G := by
  rw [curl_norm_sq]
  simp only [matSq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  nlinarith [sq_nonneg (G (unitVector 0) 1 + G (unitVector 1) 0),
    sq_nonneg (G (unitVector 0) 2 + G (unitVector 2) 0),
    sq_nonneg (G (unitVector 1) 2 + G (unitVector 2) 1),
    sq_nonneg (G (unitVector 0) 0), sq_nonneg (G (unitVector 1) 1),
    sq_nonneg (G (unitVector 2) 2)]

theorem matSq_nonneg (G : Space →L[ℝ] Space) : 0 ≤ matSq G :=
  Finset.sum_nonneg fun i _ => by positivity

end SmoothCurlWeight.Internal

open CurlWeight.Internal SmoothCurlWeight.Internal

theorem curlWeightIdentityDecayHolds_proof : CurlWeightIdentityDecayHolds := by
  intro φ u hφ hBd hu hdiv hmatSq hweightedSq
  obtain ⟨B, hB⟩ := hBd
  have hφB : ∀ y, |φ y| ≤ B := fun y => by
    have := hB y 0 (by norm_num)
    rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hφB 0)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have cDu : ∀ i j : Fin 3, Continuous (fun x => fderiv ℝ u x (unitVector i) j) := fun i j =>
    (coordMap j).continuous.comp (hDu.continuous.clm_apply continuous_const)
  have cF : Continuous (fun y => matSq (fderiv ℝ u y)) :=
    continuous_finsetSum _ fun i _ => (hDu.continuous.clm_apply continuous_const).norm.pow 2
  have hcurl : (fun y => ‖curlVec (fderiv ℝ u y)‖ ^ 2) = fun y => matSq (fderiv ℝ u y)
      - ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ u y (unitVector j) i * fderiv ℝ u y (unitVector i) j :=
    funext fun y => curl_norm_sq _
  have cC : Continuous (fun y => ‖curlVec (fderiv ℝ u y)‖ ^ 2) := by
    rw [hcurl]
    exact cF.sub (continuous_finsetSum _ fun i _ => continuous_finsetSum _
      fun j _ => (cDu j i).mul (cDu i j))
  have cu : ∀ i : Fin 3, Continuous (fun x => u x i) := fun i =>
    (coordMap i).continuous.comp hu.continuous
  have hFi : Integrable (fun y => matSq (fderiv ℝ u y)) :=
    ⟨cF.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => matSq_nonneg _)).2 hmatSq⟩
  have hHi : Integrable (fun y => ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2) :=
    ⟨((hu.continuous.norm.pow 2).div ((continuous_const.add continuous_norm).pow 2)
        fun y => show ((1 : ℝ) + ‖y‖) ^ 2 ≠ 0 by positivity).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y =>
        show (0 : ℝ) ≤ ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2 by positivity)).2 hweightedSq⟩
  have hψ : ∀ n, ContDiff ℝ 2 (weighted φ n) := fun n => (cutoff_contDiff n).mul hφ
  have hψc : ∀ n, HasCompactSupport (weighted φ n) := fun n =>
    (cutoff_hasCompactSupport n).mul_right
  have cψ : ∀ n, Continuous (weighted φ n) := fun n => (hψ n).continuous
  have hψB : ∀ n y, |weighted φ n y| ≤ B := fun n y => by
    show |cutoff n y * φ y| ≤ B
    rw [abs_mul]
    calc |cutoff n y| * |φ y| ≤ 1 * B :=
          mul_le_mul (abs_cutoff_le n y) (hφB y) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  obtain ⟨K, hK⟩ := weighted_secondDeriv_bound hφ hB
  have T1 : Tendsto (fun n => ∫ y, weighted φ n y * ‖curlVec (fderiv ℝ u y)‖ ^ 2) atTop
      (𝓝 (∫ y, φ y * ‖curlVec (fderiv ℝ u y)‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => B * (2 * matSq (fderiv ℝ u y)))
      (fun n => ((cψ n).mul cC).aestronglyMeasurable) ((hFi.const_mul 2).const_mul B)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖curlVec (fderiv ℝ u y)‖)]
      exact mul_le_mul (hψB n y) (curl_sq_le _) (sq_nonneg _) hB0
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [weighted_eventuallyEq φ y] with n hn
      rw [hn.self_of_nhds]
  have T2 : Tendsto (fun n => ∫ y, weighted φ n y * matSq (fderiv ℝ u y)) atTop
      (𝓝 (∫ y, φ y * matSq (fderiv ℝ u y))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => B * matSq (fderiv ℝ u y))
      (fun n => ((cψ n).mul cF).aestronglyMeasurable) (hFi.const_mul B)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (matSq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hψB n y) (matSq_nonneg _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [weighted_eventuallyEq φ y] with n hn
      rw [hn.self_of_nhds]
  have T3 : Tendsto (fun n => ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y (unitVector i) (unitVector j)
          * u y i * u y j) atTop
      (𝓝 (∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ φ x) y (unitVector i) (unitVector j) * u y i * u y j)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => 9 * K * (‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2))
      (fun n => ?_) (hHi.const_mul (9 * K))
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have h1 : ContDiff ℝ 1 (fderiv ℝ (weighted φ n)) := (hψ n).fderiv_right (by norm_num)
      have c2 : ∀ i j : Fin 3, Continuous (fun x =>
          fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) x (unitVector i) (unitVector j)) :=
        fun i j => ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply
          continuous_const
      exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => ((c2 i j).mul (cu i)).mul (cu j)).aestronglyMeasurable
    · have hij : ∀ i j : Fin 3,
          ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y (unitVector i) (unitVector j)
            * u y i * u y j‖
            ≤ ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y‖ * ‖u y‖ ^ 2 := by
        intro i j
        rw [norm_mul, norm_mul, sq, ← mul_assoc]
        have e1 : ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y (unitVector i)
            (unitVector j)‖ ≤ ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y‖ := by
          have := (fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y).le_opNorm₂
            (unitVector i) (unitVector j)
          simpa [unitVector, PiLp.norm_single] using this
        have e2 := PiLp.norm_apply_le (u y) i
        have e3 := PiLp.norm_apply_le (u y) j
        gcongr
      have hsum : ‖∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y (unitVector i) (unitVector j)
            * u y i * u y j‖
          ≤ 9 * (‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y‖ * ‖u y‖ ^ 2) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j).trans ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        linarith
      have ht : 0 < (1 + ‖y‖) ^ 2 := by positivity
      have hsplit : ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y‖ * ‖u y‖ ^ 2 =
          ((1 + ‖y‖) ^ 2 * ‖fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y‖)
            * (‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
        field_simp
      have hle := mul_le_mul_of_nonneg_right (hK n y)
        (by positivity : (0 : ℝ) ≤ ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)
      calc _ ≤ _ := hsum
        _ ≤ 9 * K * (‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
          rw [hsplit]
          linarith
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [weighted_eventuallyEq φ y] with n hn
      have hh : fderiv ℝ (fun x => fderiv ℝ (weighted φ n) x) y =
          fderiv ℝ (fun x => fderiv ℝ φ x) y := (hn.fderiv (𝕜 := ℝ)).fderiv_eq
      rw [hh]
  have T4 : Tendsto (fun n => ∫ y, weighted φ n y * ‖curlVec (fderiv ℝ u y)‖ ^ 2) atTop
      (𝓝 ((∫ y, φ y * matSq (fderiv ℝ u y)) - ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ φ x) y (unitVector i) (unitVector j) * u y i * u y j)) :=
    (T2.sub T3).congr fun n => (identity_of_compactSupport (hψ n) (hψc n) hu hdiv).symm
  exact tendsto_nhds_unique T1 T4

end Coercive

end Breakdown

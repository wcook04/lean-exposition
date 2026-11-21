import Breakdown.Cert.CoerciveNodes

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal

def coordMap (i : Fin 3) : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

theorem coordMap_apply (i : Fin 3) (w : Space) : coordMap i w = w i := rfl

theorem coord_sum_smul (c : Fin 3 → ℝ) (k : Fin 3) :
    (∑ i : Fin 3, c i • unitVector i) k = c k := by
  fin_cases k <;> simp [unitVector, Fin.sum_univ_three, ]

theorem curl_norm_sq (G : Space →L[ℝ] Space) :
    ‖curlVec G‖ ^ 2 = matSq G
      - ∑ i : Fin 3, ∑ j : Fin 3, G (unitVector j) i * G (unitVector i) j := by
  simp only [EuclideanSpace.real_norm_sq_eq, curlVec, matSq, coord_sum_smul]
  simp only [Fin.sum_univ_three, alternatingSymbol]
  norm_num
  ring

theorem hasCompactSupport_of_vanish {u : Space → Space} {g : Space → ℝ}
    (hu : HasCompactSupport u) (h : ∀ x ∉ tsupport u, g x = 0) : HasCompactSupport g :=
  hu.mono' (fun x hx => by
    by_contra h'
    exact hx (h x h'))

theorem fderiv_eq_zero_of_not_mem {u : Space → Space} {x : Space} (hx : x ∉ tsupport u) :
    fderiv ℝ u x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))

theorem integral_fderiv_eq_zero {S : Space → ℝ} (hS : ContDiff ℝ 1 S) (hc : HasCompactSupport S)
    (v : Space) : Integrable (fun x => fderiv ℝ S x v) ∧ ∫ x, fderiv ℝ S x v = 0 := by
  have hint : Integrable (fun x => fderiv ℝ S x v) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hS.continuous_fderiv one_ne_zero).clm_apply continuous_const) ?_
    refine (hc.fderiv (𝕜 := ℝ)).mono ?_
    intro x hx h0
    exact hx (by simp [h0])
  refine ⟨hint, ?_⟩
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℝ)) (g := S) (v := v) (by simp) (by simpa using hint)
    (by simpa using hS.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hS.differentiable one_ne_zero).differentiableAt)
  simpa using h

def fluxField (φ : Space → ℝ) (u : Space → Space) (j : Fin 3) (x : Space) : ℝ :=
  ∑ i : Fin 3, (φ x * u x i * fderiv ℝ u x (unitVector i) j
    - fderiv ℝ φ x (unitVector i) * u x i * u x j)

end CurlWeight.Internal

open CurlWeight.Internal

theorem curlWeightIdentityHolds_proof : CurlWeightIdentityHolds := by
  intro φ u hφ hu hcu hdiv
  have hu2 : ContDiff ℝ 2 u := contDiff_infty.mp hu 2
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
  have hz : ∀ x ∉ tsupport u, u x = 0 ∧ fderiv ℝ u x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_eq_zero_of_not_mem hx⟩
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
    · refine hasCompactSupport_of_vanish hcu fun x hx => ?_
      simp [fluxField, (hz x hx).1]
  have hT : Integrable (fun x => φ x * ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ u x (unitVector j) i * fderiv ℝ u x (unitVector i) j) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφ.continuous.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => (cDu j i).mul (cDu i j))
    · refine hasCompactSupport_of_vanish hcu fun x hx => ?_
      simp [(hz x hx).2]
  have hB : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ φ x) x (unitVector i) (unitVector j) * u x i * u x j) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => ((cD2φ i j).mul (cu i)).mul (cu j)
    · refine hasCompactSupport_of_vanish hcu fun x hx => ?_
      simp [(hz x hx).1]
  have hA : Integrable (fun x => φ x * matSq (fderiv ℝ u x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφ.continuous.mul (continuous_finsetSum _ fun i _ =>
        ((hDu.continuous.clm_apply continuous_const).norm.pow 2))
    · refine hasCompactSupport_of_vanish hcu fun x hx => ?_
      simp [matSq, (hz x hx).2]
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

end Coercive

end Breakdown

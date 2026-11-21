import Breakdown.Cert.CoerciveEnergyIdentityTools

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace EnergyIdentityInternal

theorem curlVec_apply (G : Space →L[ℝ] Space) (i : Fin 3) :
    curlVec G i = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l := by
  fin_cases i <;> simp [curlVec, unitVector, Fin.sum_univ_three]

theorem mul_deriv (f g : Space → ℝ) (y w : Space) (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (fun x => f x * g x) y w = fderiv ℝ f y w * g y + f y * fderiv ℝ g y w := by
  rw [show (fun x => f x * g x) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem curl_comp_eq (u : Space → Space) (l : Fin 3) :
    (fun x => curlVec (fderiv ℝ u x) l) =
      fun x => ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).comp curlCLM) (fderiv ℝ u x) := rfl

theorem curl_contDiff (u : Space → Space) {m n : WithTop ℕ∞} (hu : ContDiff ℝ m u) (h : n + 1 ≤ m)
    (l : Fin 3) : ContDiff ℝ n (fun x => curlVec (fderiv ℝ u x) l) := by
  rw [curl_comp_eq]
  exact ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).comp curlCLM).contDiff.comp (hu.fderiv_right h)

theorem curl_support (u : Space → Space) (hc : HasCompactSupport u) (l : Fin 3) :
    HasCompactSupport (fun x => curlVec (fderiv ℝ u x) l) := by
  rw [curl_comp_eq]
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

theorem curl_deriv (u : Space → Space) (hu : ContDiff ℝ 2 u) (y : Space) (l j : Fin 3) :
    fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j) =
      ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol l a b *
        fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector a) b := by
  have hdd : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [curl_comp_eq, fderiv_clm_left _ (hdd y)]
  simp only [ContinuousLinearMap.comp_apply, curlCLM_apply]
  exact curlVec_apply _ l

theorem d2_symm_two (u : Space → Space) (hu : ContDiff ℝ 2 u) (y a b : Space) :
    fderiv ℝ (fun x => fderiv ℝ u x) y a b = fderiv ℝ (fun x => fderiv ℝ u x) y b a :=
  (hu.contDiffAt.isSymmSndFDerivAt (by simp)) a b

theorem ibp_sum {ι : Type*} (s : Finset ι) (f g : ι → Space → ℝ) (m : ι → Fin 3)
    (hf : ∀ t ∈ s, ContDiff ℝ 1 (f t)) (hg : ∀ t ∈ s, ContDiff ℝ 1 (g t))
    (hc : ∀ t ∈ s, HasCompactSupport (f t)) :
    ∫ y, ∑ t ∈ s, f t y * fderiv ℝ (g t) y (unitVector (m t)) =
      -∫ y, ∑ t ∈ s, fderiv ℝ (f t) y (unitVector (m t)) * g t y := by
  have i1 : ∀ t ∈ s, Integrable (fun y => f t y * fderiv ℝ (g t) y (unitVector (m t))) := by
    intro t ht
    have c1 := (hf t ht).continuous
    have c2 : Continuous fun y => fderiv ℝ (g t) y (unitVector (m t)) :=
      ((hg t ht).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact cont_intg _ (c1.mul c2) (hc t ht).mul_right
  have i2 : ∀ t ∈ s, Integrable (fun y => fderiv ℝ (f t) y (unitVector (m t)) * g t y) := by
    intro t ht
    have c1 : Continuous fun y => fderiv ℝ (f t) y (unitVector (m t)) :=
      ((hf t ht).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact cont_intg _ (c1.mul (hg t ht).continuous) (((hc t ht).fderiv_apply (𝕜 := ℝ) _).mul_right)
  rw [integral_finsetSum _ i1, integral_finsetSum _ i2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun t ht => ibp _ _ _ (hf t ht) (hg t ht) (hc t ht))

theorem eps_000 : alternatingSymbol 0 0 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_001 : alternatingSymbol 0 0 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_002 : alternatingSymbol 0 0 2 = 0 := by norm_num [alternatingSymbol]
theorem eps_010 : alternatingSymbol 0 1 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_011 : alternatingSymbol 0 1 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_012 : alternatingSymbol 0 1 2 = 1 := by norm_num [alternatingSymbol]
theorem eps_020 : alternatingSymbol 0 2 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_021 : alternatingSymbol 0 2 1 = -1 := by norm_num [alternatingSymbol]
theorem eps_022 : alternatingSymbol 0 2 2 = 0 := by norm_num [alternatingSymbol]
theorem eps_100 : alternatingSymbol 1 0 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_101 : alternatingSymbol 1 0 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_102 : alternatingSymbol 1 0 2 = -1 := by norm_num [alternatingSymbol]
theorem eps_110 : alternatingSymbol 1 1 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_111 : alternatingSymbol 1 1 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_112 : alternatingSymbol 1 1 2 = 0 := by norm_num [alternatingSymbol]
theorem eps_120 : alternatingSymbol 1 2 0 = 1 := by norm_num [alternatingSymbol]
theorem eps_121 : alternatingSymbol 1 2 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_122 : alternatingSymbol 1 2 2 = 0 := by norm_num [alternatingSymbol]
theorem eps_200 : alternatingSymbol 2 0 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_201 : alternatingSymbol 2 0 1 = 1 := by norm_num [alternatingSymbol]
theorem eps_202 : alternatingSymbol 2 0 2 = 0 := by norm_num [alternatingSymbol]
theorem eps_210 : alternatingSymbol 2 1 0 = -1 := by norm_num [alternatingSymbol]
theorem eps_211 : alternatingSymbol 2 1 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_212 : alternatingSymbol 2 1 2 = 0 := by norm_num [alternatingSymbol]
theorem eps_220 : alternatingSymbol 2 2 0 = 0 := by norm_num [alternatingSymbol]
theorem eps_221 : alternatingSymbol 2 2 1 = 0 := by norm_num [alternatingSymbol]
theorem eps_222 : alternatingSymbol 2 2 2 = 0 := by norm_num [alternatingSymbol]

theorem div_deriv_zero_two (u : Space → Space) (hu : ContDiff ℝ 2 u) (hd : ∀ y, divergenceAt u y = 0)
    (y : Space) (j : Fin 3) :
    ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector i) i = 0 := by
  have h1 : ∀ i : Fin 3, DifferentiableAt ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector i)) y := by
    intro i
    have hc : ContDiff ℝ 1 (fun x => fderiv ℝ (fun z => u z i) x (unitVector i)) :=
      ((((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hu).fderiv_right (m := 1)
        (by norm_num)).clm_apply contDiff_const)
    exact (hc.differentiable (by norm_num)) y
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have e : (fun x => ∑ i : Fin 3, fderiv ℝ (fun z => u z i) x (unitVector i)) = fun _ => 0 := by
    funext x
    simp only [fderiv_component u (hdu x)]
    exact hd x
  have h2 : fderiv ℝ (fun x => ∑ i : Fin 3, fderiv ℝ (fun z => u z i) x (unitVector i)) y (unitVector j) =
      ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun z => u z i) x (unitVector i)) y (unitVector j) := by
    rw [fderiv_fun_sum (fun i _ => h1 i)]
    simp
  rw [e] at h2
  simp only [fderiv_second_component u hu y] at h2
  rw [← h2]
  simp

theorem ssp_curl (u : Space → Space) (hu : ContDiff ℝ 2 u) (hd : ∀ y, divergenceAt u y = 0)
    (y : Space) (i : Fin 3) :
    (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) i =
      ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j) := by
  simp only [curl_deriv u hu]
  have t := div_deriv_zero_two u hu hd y
  have t0 := t 0
  have t1 := t 1
  have t2 := t 2
  simp only [Fin.sum_univ_three] at t0 t1 t2
  have s10 := d2_symm_two u hu y (unitVector 1) (unitVector 0)
  have s20 := d2_symm_two u hu y (unitVector 2) (unitVector 0)
  have s21 := d2_symm_two u hu y (unitVector 2) (unitVector 1)
  simp only [s10, s20, s21] at t0 t1 t2
  fin_cases i <;>
  · simp [secondDerivTrace, Fin.sum_univ_three, alternatingSymbol, s10, s20, s21]
    linarith

theorem A_deriv (u W₀ : Space → Space) (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W₀) (y w : Space) :
    fderiv ℝ (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) y w =
      (fderiv ℝ (fun x => fderiv ℝ u x) y w (W₀ y) + fderiv ℝ u y (fderiv ℝ W₀ y w)) +
      (fderiv ℝ (fun x => fderiv ℝ W₀ x) y w (u y) + fderiv ℝ W₀ y (fderiv ℝ u y w)) := by
  have du : Differentiable ℝ u := hu.differentiable (by norm_num)
  have dW : Differentiable ℝ W₀ := hW.differentiable (by norm_num)
  have ddu : Differentiable ℝ (fun x => fderiv ℝ u x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have ddW : Differentiable ℝ (fun x => fderiv ℝ W₀ x) :=
    (hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_fun_add ((ddu y).clm_apply (dW y)) ((ddW y).clm_apply (du y))]
  rw [ContinuousLinearMap.add_apply, fderiv_clm_apply (ddu y) (dW y), fderiv_clm_apply (ddW y) (du y)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  abel

theorem A_deriv_jets (u W₀ : Space → Space) (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W₀) (y : Space)
    (i j : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) y (unitVector j) i =
      ∑ k : Fin 3, (W₀ y k * fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector k) i
        + fderiv ℝ W₀ y (unitVector j) k * fderiv ℝ u y (unitVector k) i
        + u y k * fderiv ℝ (fun x => fderiv ℝ W₀ x) y (unitVector j) (unitVector k) i
        + fderiv ℝ u y (unitVector j) k * fderiv ℝ W₀ y (unitVector k) i) := by
  rw [A_deriv u W₀ hu hW]
  simp only [PiLp.add_apply]
  rw [apply_self (fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j)) (W₀ y) i,
    apply_self (fderiv ℝ u y) (fderiv ℝ W₀ y (unitVector j)) i,
    apply_self (fderiv ℝ (fun x => fderiv ℝ W₀ x) y (unitVector j)) (u y) i,
    apply_self (fderiv ℝ W₀ y) (fderiv ℝ u y (unitVector j)) i]
  simp only [Finset.sum_add_distrib]
  ring

set_option maxHeartbeats 2000000 in
theorem curl_grad_point (u W₀ : Space → Space) (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W₀)
    (hd : ∀ y, divergenceAt u y = 0) (hWd : ∀ y, divergenceAt W₀ y = 0) (y : Space) :
    -∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        fderiv ℝ (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) y (unitVector j) i *
          curlVec (fderiv ℝ u y) l =
      ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)
      + (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j)
      + -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
          curlVec (fderiv ℝ u y) i) := by
  simp only [curl_deriv u hu]
  simp only [A_deriv_jets u W₀ hu hW, curlVec_apply, vortGrad]
  have tu := hd y
  have tW := hWd y
  simp only [divergenceAt, Fin.sum_univ_three] at tu tW
  have eu : fderiv ℝ u y (unitVector 2) 2 = -fderiv ℝ u y (unitVector 0) 0 - fderiv ℝ u y (unitVector 1) 1 := by
    linarith
  have eW : fderiv ℝ W₀ y (unitVector 2) 2 = -fderiv ℝ W₀ y (unitVector 0) 0 - fderiv ℝ W₀ y (unitVector 1) 1 := by
    linarith
  have s10 := d2_symm_two u hu y (unitVector 1) (unitVector 0)
  have s20 := d2_symm_two u hu y (unitVector 2) (unitVector 0)
  have s21 := d2_symm_two u hu y (unitVector 2) (unitVector 1)
  have r10 := d2_symm_two W₀ hW y (unitVector 1) (unitVector 0)
  have r20 := d2_symm_two W₀ hW y (unitVector 2) (unitVector 0)
  have r21 := d2_symm_two W₀ hW y (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three]
  simp only [eps_000, eps_001, eps_002, eps_010, eps_011, eps_012, eps_020, eps_021, eps_022, eps_100, eps_101, eps_102, eps_110, eps_111, eps_112, eps_120, eps_121, eps_122, eps_200, eps_201, eps_202, eps_210, eps_211, eps_212, eps_220, eps_221, eps_222]
  simp only [s10, s20, s21, r10, r20, r21]
  rw [eu, eW]
  ring

theorem vanish_radius (u : Space → Space) (hc : HasCompactSupport u) :
    ∃ R, ∀ y, R < ‖y‖ → u y = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun y hy => ?_⟩
  by_contra h
  have hm : y ∈ Metric.closedBall (0 : Space) R := hR (subset_tsupport _ h)
  simp only [Metric.mem_closedBall, dist_zero_right] at hm
  linarith

theorem const_mul_deriv (c : ℝ) (a : Space → ℝ) (y w : Space) (ha : DifferentiableAt ℝ a y) :
    fderiv ℝ (fun x => c * a x) y w = c * fderiv ℝ a y w := by
  rw [(ha.hasFDerivAt.const_mul c).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem cmul_deriv (c : ℝ) (f g : Space → ℝ) (y w : Space) (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (fun x => c * (f x * g x)) y w = c * (fderiv ℝ f y w * g y + f y * fderiv ℝ g y w) := by
  have h : HasFDerivAt (fun x => c * (f x * g x)) (c • (f y • fderiv ℝ g y + g y • fderiv ℝ f y)) y :=
    (hf.hasFDerivAt.mul hg.hasFDerivAt).const_mul c
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  ring

theorem x_split (u W₀ : Space → Space) (hu : Differentiable ℝ u) (y : Space) :
    -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) := by
  simp only [Fintype.sum_prod_type, fderiv_component u (hu y), curlVec_apply (fderiv ℝ u y)]
  simp only [Fin.sum_univ_three]
  ring

set_option maxHeartbeats 4000000 in
theorem x_expand (u W₀ : Space → Space) (hu : ContDiff ℝ ∞ u) (hW : ContDiff ℝ 2 W₀) (y : Space) :
    -(∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) y (unitVector t.2.2.1) *
          u y t.2.2.2) =
      2 * ((1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l) +
      ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) := by
  have dO : ∀ j, DifferentiableAt ℝ (fun x => curlVec (fderiv ℝ W₀ x) j) y := fun j =>
    ((curl_contDiff W₀ hW (n := 1) (by norm_num) j).differentiable (by norm_num)) y
  have dD : ∀ j i, DifferentiableAt ℝ (fun x => fderiv ℝ u x (unitVector j) i) y := fun j i =>
    ((d1_smooth u hu j i).differentiable (by simp)) y
  simp only [cmul_deriv _ _ _ y _ (dO _) (dD _ _), curl_deriv W₀ hW, d2_eq u hu, vortGrad,
    Fintype.sum_prod_type]
  have s10 := d2_symm u hu y (unitVector 1) (unitVector 0)
  have s20 := d2_symm u hu y (unitVector 2) (unitVector 0)
  have s21 := d2_symm u hu y (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three]
  simp only [s10, s20, s21]
  ring

set_option maxHeartbeats 2000000 in
theorem y_point (u W₀ : Space → Space) (hu : ContDiff ℝ ∞ u) (hW : ContDiff ℝ 2 W₀) (y : Space) :
    ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) y (unitVector t.2.1) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 =
      -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) := by
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have dO : ∀ j, DifferentiableAt ℝ (fun x => curlVec (fderiv ℝ W₀ x) j) y := fun j =>
    ((curl_contDiff W₀ hW (n := 1) (by norm_num) j).differentiable (by norm_num)) y
  have dU : ∀ l, DifferentiableAt ℝ (fun x => u x l) y := fun l =>
    ((comp_smooth u hu l).differentiable (by simp)) y
  simp only [cmul_deriv _ _ _ y _ (dO _) (dU _), curl_deriv W₀ hW, fderiv_component u (hdu y),
    Fintype.sum_prod_type]
  simp only [curlVec_apply]
  have r10 := d2_symm_two W₀ hW y (unitVector 1) (unitVector 0)
  have r20 := d2_symm_two W₀ hW y (unitVector 2) (unitVector 0)
  have r21 := d2_symm_two W₀ hW y (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three]
  simp only [eps_000, eps_001, eps_002, eps_010, eps_011, eps_012, eps_020, eps_021, eps_022, eps_100, eps_101, eps_102, eps_110, eps_111, eps_112, eps_120, eps_121, eps_122, eps_200, eps_201, eps_202, eps_210, eps_211, eps_212, eps_220, eps_221, eps_222]
  simp only [r10, r20, r21]
  ring


theorem cmul_support_right (c : ℝ) (f g : Space → ℝ) (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => c * (f x * g x)) :=
  hg.mono' (fun x hx => subset_tsupport _
    (Function.mem_support.mpr fun h => Function.mem_support.mp hx (by simp [h])))

theorem cmul_support_one (c : ℝ) (g : Space → ℝ) (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => c * g x) :=
  hg.mono' (fun x hx => subset_tsupport _
    (Function.mem_support.mpr fun h => Function.mem_support.mp hx (by simp [h])))

theorem cmul_contDiff (c : ℝ) (f g : Space → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun x => c * (f x * g x)) :=
  contDiff_const.mul (hf.mul hg)

theorem cmul_contDiff_one (c : ℝ) (g : Space → ℝ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun x => c * g x) :=
  contDiff_const.mul hg
theorem x_term (u W₀ : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hW : ContDiff ℝ 2 W₀) :
    ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∫ y, (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l := by
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have cO : ∀ j, ContDiff ℝ 1 (fun x => curlVec (fderiv ℝ W₀ x) j) := fun j =>
    curl_contDiff W₀ hW (by norm_num) j
  obtain ⟨R, z0⟩ := vanish_radius u hc
  have z1 := fderiv_vanish u R z0
  have cu : Continuous u := hu.continuous
  have cdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have cddu : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    (hu.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cddW : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ W₀ x) y) :=
    (hW.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hI : ∀ f : Space → ℝ, Continuous f → (∀ y, R < ‖y‖ → f y = 0) → Integrable f :=
    fun f hf h => cont_intg f hf (compact_of_vanish f R h)
  have iR3 : Integrable (fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l) := by
    apply hI
    · simp only [vortGrad]; fun_prop
    · intro y hy; simp [z0 y hy]
  have iY : Integrable (fun y => ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1)) := by
    apply hI
    · simp only [d2_eq u hu, ← curlCLM_apply]; fun_prop
    · intro y hy; simp [z0 y hy]
  have e1 : ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) := by
    congr 1; funext y; exact x_split u W₀ hdu y
  have e2 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) y (unitVector t.2.2.1) *
          u y t.2.2.2 :=
    ibp_sum _ (fun (t : Fin 3 × Fin 3 × Fin 3 × Fin 3) (x : Space) => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) (fun t x => u x t.2.2.2)
      (fun t => t.2.2.1)
      (fun t _ => cmul_contDiff _ _ _ (cO _) ((d1_smooth u hu _ _).of_le one_le_inf))
      (fun t _ => (comp_smooth u hu _).of_le one_le_inf)
      (fun t _ => cmul_support_right _ _ _ (d1_support u hc _ _))
  have e3 : -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) y (unitVector t.2.2.1) *
          u y t.2.2.2 =
      2 * (∫ y, (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l) +
      ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) := by
    rw [← integral_neg, ← integral_const_mul, ← integral_add (iR3.const_mul 2) iY]
    congr 1; funext y; exact x_expand u W₀ hu hW y
  have e4 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) y (unitVector t.2.1) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 :=
    ibp_sum _ (fun (t : Fin 3 × Fin 3 × Fin 3 × Fin 3) (x : Space) => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) (fun t x => fderiv ℝ u x (unitVector t.2.2.1) t.1)
      (fun t => t.2.1)
      (fun t _ => cmul_contDiff _ _ _ (cO _) ((comp_smooth u hu _).of_le one_le_inf))
      (fun t _ => (d1_smooth u hu _ _).of_le one_le_inf)
      (fun t _ => cmul_support_right _ _ _ (comp_support u hc _))
  have e5 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) y (unitVector t.2.1) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 =
      ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) := by
    congr 1; funext y; exact y_point u W₀ hu hW y
  rw [e4, e5] at e3
  rw [e1, e2, e3]
  rw [← e2, ← e1] at e3
  linarith

theorem A_contDiff (u W₀ : Space → Space) (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W₀) :
    ContDiff ℝ 1 (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) :=
  ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply (hW.of_le (by norm_num))).add
    ((hW.fderiv_right (m := 1) (by norm_num)).clm_apply (hu.of_le (by norm_num)))

theorem A_support (u W₀ : Space → Space) (hc : HasCompactSupport u) :
    HasCompactSupport (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) := by
  refine HasCompactSupport.add ?_ ?_
  · refine (hc.fderiv (𝕜 := ℝ)).mono' (fun x hx => subset_tsupport _ ?_)
    refine Function.mem_support.mpr (fun h => Function.mem_support.mp hx ?_)
    simp [h]
  · refine hc.mono' (fun x hx => subset_tsupport _ ?_)
    refine Function.mem_support.mpr (fun h => Function.mem_support.mp hx ?_)
    simp [h]

theorem stretch_identity (u W₀ : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hd : ∀ y, divergenceAt u y = 0) (hW : ContDiff ℝ 2 W₀) (hWd : ∀ y, divergenceAt W₀ y = 0) :
    ∫ y, inner ℝ (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y))
        (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∫ y, (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j
        + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
            * fderiv ℝ u y (unitVector j) i * u y l) := by
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hA := A_contDiff u W₀ h2 hW
  have hAc := A_support u W₀ hc
  have dA : Differentiable ℝ (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) :=
    hA.differentiable (by norm_num)
  have hAi : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) i) := by
    intro i
    have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hA
    exact h
  obtain ⟨R, z0⟩ := vanish_radius u hc
  have z1 := fderiv_vanish u R z0
  have z2 := fderiv_vanish _ R z1
  have cu : Continuous u := hu.continuous
  have cdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have cddu : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    (hu.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have cW : Continuous W₀ := hW.continuous
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cddW : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ W₀ x) y) :=
    (hW.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hI : ∀ f : Space → ℝ, Continuous f → (∀ y, R < ‖y‖ → f y = 0) → Integrable f :=
    fun f hf h => cont_intg f hf (compact_of_vanish f R h)
  have sa : ∀ y, inner ℝ (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y))
      (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) t.1) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) t.2.2) y (unitVector t.2.1) := by
    intro y
    rw [inner_coord]
    simp only [ssp_curl u h2 hd y, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have sb : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) t.1) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) t.2.2) y (unitVector t.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) t.1) y (unitVector t.2.1) *
          curlVec (fderiv ℝ u y) t.2.2 :=
    ibp_sum _ (fun (t : Fin 3 × Fin 3 × Fin 3) (x : Space) => alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) t.1) (fun t x => curlVec (fderiv ℝ u x) t.2.2)
      (fun t => t.2.1) (fun t _ => cmul_contDiff_one _ _ (hAi _))
      (fun t _ => curl_contDiff u h2 (by norm_num) _)
      (fun t _ => cmul_support_one _ _ (comp_support _ hAc _))
  have sc : ∀ y, -(∑ t : Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) t.1) y (unitVector t.2.1) *
          curlVec (fderiv ℝ u y) t.2.2) =
      ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)
      + (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j)
      + -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
          curlVec (fderiv ℝ u y) i) := by
    intro y
    rw [← curl_grad_point u W₀ h2 hW hd hWd y]
    simp only [const_mul_deriv _ _ y _ ((hAi _).differentiable (by norm_num) y),
      fderiv_component _ (dA y), Fintype.sum_prod_type]
  have iT : ∀ l : Fin 3, Integrable (fun y => ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)) := by
    intro l
    refine integrable_finsetSum _ (fun k _ => cont_intg _ ?_ ((curl_support u hc l).mul_left.mul_right))
    have c1 := (curl_contDiff u hu (n := ∞) (by simp) l)
    have c2 : Continuous fun y => fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) :=
      (c1.continuous_fderiv (by simp)).clm_apply continuous_const
    have c3 : Continuous fun y => W₀ y k := by
      have h := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp cW
      exact h
    exact (c3.mul c1.continuous).mul c2
  have tz : ∫ y, ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) = 0 := by
    rw [integral_finsetSum _ (fun l _ => iT l)]
    exact Finset.sum_eq_zero (fun l _ => transport_zero W₀ (hW.of_le (by norm_num)) hWd _
      (curl_contDiff u hu (n := ∞) (by simp) l) (curl_support u hc l))
  have iR : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j) := by
    apply hI
    · simp only [vortGrad, ← curlCLM_apply]; fun_prop
    · intro y hy; simp [z0 y hy, z1 y hy, ← curlCLM_apply]
  have iX : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j *
      fderiv ℝ u y (unitVector j) i * curlVec (fderiv ℝ u y) i)) := by
    apply hI
    · simp only [← curlCLM_apply]; fun_prop
    · intro y hy; simp [z1 y hy]
  have i3 : Integrable (fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
            * fderiv ℝ u y (unitVector j) i * u y l) := by
    apply hI
    · simp only [vortGrad]; fun_prop
    · intro y hy; simp [z0 y hy]
  have iTs : Integrable (fun y => ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)) := by
    refine integrable_finsetSum _ ?_
    intro l _
    exact iT l
  simp_rw [sa]
  rw [sb, ← integral_neg]
  simp_rw [sc]
  rw [integral_add _ iX, integral_add _ iR, tz, x_term u W₀ hu hc hW, integral_add _ i3]
  all_goals first
    | exact iR
    | exact iTs
    | exact iTs.add iR
    | ring

theorem slice_stretch (W v : ℝ → Space → Space) (σ : ℝ) (hW : ContDiff ℝ 2 (W σ))
    (hWd : ∀ y, divergenceAt (W σ) y = 0) (hu : ContDiff ℝ ∞ (v σ)) (hc : HasCompactSupport (v σ))
    (hd : ∀ y, divergenceAt (v σ) y = 0) :
    ∫ y, inner ℝ (fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y))
        (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ y, stretchForm W v (gradField v) σ y :=
  stretch_identity (v σ) (W σ) hu hc hd hW hWd

end EnergyIdentityInternal

end Coercive

end Breakdown

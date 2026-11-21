import Breakdown.Defs

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal.ConvectionSmooth

theorem fderiv_eq_zero_off {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set Space}
    (hK : IsClosed K) {h : Space → F} (hv : ∀ y ∉ K, h y = 0) (y : Space) (hy : y ∉ K) :
    fderiv ℝ h y = 0 := by
  have hev : h =ᶠ[𝓝 y] fun _ => (0 : F) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz using hv z hz
  rw [hev.fderiv_eq]
  simp

theorem integrable_off {K : Set Space} (hK : IsCompact K) {f : Space → ℝ} (hf : Continuous f)
    (hv : ∀ y ∉ K, f y = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK hv)

theorem integral_fderiv_eq_zero {K : Set Space} (hK : IsCompact K) {h : Space → ℝ}
    (hh : ContDiff ℝ 1 h) (hv : ∀ y ∉ K, h y = 0) (v : Space) :
    ∫ y, fderiv ℝ h y v = 0 := by
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hc : Continuous fun y => fderiv ℝ h y v :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdv : ∀ y ∉ K, fderiv ℝ h y v = 0 := fun y hy => by
    rw [fderiv_eq_zero_off hK.isClosed hv y hy]
    rfl
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℝ)) (g := h) (v := v)
    (by simp)
    (integrable_off hK (continuous_const.mul hc) (fun y hy => by simp [hdv y hy]))
    (integrable_off hK (continuous_const.mul hh.continuous) (fun y hy => by simp [hv y hy]))
    (fun x _ => differentiableAt_const _) (fun x _ => hd x)
  simpa using key

theorem expand (w : Space) : w = ∑ k : Fin 3, w k • unitVector k := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simpa [unitVector, EuclideanSpace.basisFun_apply] using h.symm

theorem sum_inner_mul_inner (x y : Space) :
    ∑ i : Fin 3, inner ℝ x (unitVector i) * inner ℝ (unitVector i) y = inner ℝ x y := by
  simpa [unitVector, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_inner_mul_inner x y

theorem pair_sum (A B : Space →L[ℝ] Space) :
    ∑ j : Fin 3, inner ℝ (A (B (unitVector j))) (A (unitVector j)) =
      ∑ i : Fin 3, inner ℝ (B (ContinuousLinearMap.adjoint A (unitVector i)))
        (ContinuousLinearMap.adjoint A (unitVector i)) := by
  have h1 : ∀ j : Fin 3, inner ℝ (A (B (unitVector j))) (A (unitVector j)) =
      ∑ i : Fin 3, inner ℝ (B (unitVector j)) (ContinuousLinearMap.adjoint A (unitVector i)) *
        inner ℝ (ContinuousLinearMap.adjoint A (unitVector i)) (unitVector j) := by
    intro j
    rw [← sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm (A (unitVector j))]
  have h2 : ∀ i : Fin 3, inner ℝ (B (ContinuousLinearMap.adjoint A (unitVector i)))
      (ContinuousLinearMap.adjoint A (unitVector i)) =
      ∑ j : Fin 3, inner ℝ (B (unitVector j)) (ContinuousLinearMap.adjoint A (unitVector i)) *
        inner ℝ (ContinuousLinearMap.adjoint A (unitVector i)) (unitVector j) := by
    intro i
    set x := ContinuousLinearMap.adjoint A (unitVector i)
    rw [← ContinuousLinearMap.adjoint_inner_right B x x, ← sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, mul_comm]
  simp_rw [h1, h2]
  exact Finset.sum_comm

theorem second_expand (Q : Space →L[ℝ] Space →L[ℝ] Space) (w x : Space) (j : Fin 3) :
    ∑ k : Fin 3, w k * inner ℝ (Q (unitVector k) (unitVector j)) x =
      inner ℝ (Q w (unitVector j)) x := by
  conv_rhs => rw [expand w]
  simp [map_sum, map_smul, sum_inner, real_inner_smul_left]


theorem identity {W u : Space → Space} (hW : ContDiff ℝ 1 W) (hdiv : ∀ y, divergenceAt W y = 0)
    (hu : ContDiff ℝ ∞ u) (hsupp : HasCompactSupport u) :
    (∫ y, inner ℝ (fderiv ℝ u y (W y)) (-sumSecondPartialsAt u y)) =
      ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y (ContinuousLinearMap.adjoint (fderiv ℝ u y) (unitVector i)))
        (ContinuousLinearMap.adjoint (fderiv ℝ u y) (unitVector i)) := by
  have hK : IsCompact (tsupport u) := hsupp
  have hKc : IsClosed (tsupport u) := isClosed_tsupport u
  have hu0 : ∀ y ∉ tsupport u, u y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hDu0 : ∀ y ∉ tsupport u, fderiv ℝ u y = 0 := fderiv_eq_zero_off hKc hu0
  have hDuinf : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.1 hu).2
  have hDu1 : ContDiff ℝ 1 (fderiv ℝ u) := hDuinf.of_le (by exact_mod_cast le_top)
  have hDud : Differentiable ℝ (fderiv ℝ u) := hDu1.differentiable one_ne_zero
  have hDuc : Continuous (fderiv ℝ u) := hDu1.continuous
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hDWc : Continuous (fderiv ℝ W) := hW.continuous_fderiv one_ne_zero
  have hsym : ∀ y v w, fderiv ℝ (fderiv ℝ u) y v w = fderiv ℝ (fderiv ℝ u) y w v := fun y =>
    hu.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)
  set φ : Fin 3 → Space → ℝ := fun j y =>
    inner ℝ (fderiv ℝ u y (W y)) (fderiv ℝ u y (unitVector j)) with hφdef
  have hφ1 : ∀ j, ContDiff ℝ 1 (φ j) := fun j =>
    (hDu1.clm_apply hW).inner ℝ (hDu1.clm_apply contDiff_const)
  have hφ0 : ∀ j, ∀ y ∉ tsupport u, φ j y = 0 := fun j y hy => by simp [φ, hDu0 y hy]
  have hφd : ∀ j y, fderiv ℝ (φ j) y (unitVector j) =
      inner ℝ (fderiv ℝ (fderiv ℝ u) y (unitVector j) (W y)) (fderiv ℝ u y (unitVector j)) +
      inner ℝ (fderiv ℝ u y (fderiv ℝ W y (unitVector j))) (fderiv ℝ u y (unitVector j)) +
      inner ℝ (fderiv ℝ u y (W y)) (fderiv ℝ (fderiv ℝ u) y (unitVector j) (unitVector j)) := by
    intro j y
    have hA := (hDud y).hasFDerivAt.clm_apply (hWd y).hasFDerivAt
    have hB := (hDud y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector j) y)
    rw [(hA.inner ℝ hB).fderiv]
    simp [inner_add_left]
    ring
  set S : Space → ℝ := fun y => ∑ j : Fin 3,
    inner ℝ (fderiv ℝ u y (unitVector j)) (fderiv ℝ u y (unitVector j)) with hSdef
  set θ : Fin 3 → Space → ℝ := fun k y => W y k * S y with hθdef
  have hS1 : ContDiff ℝ 1 S := ContDiff.sum fun j _ =>
    (hDu1.clm_apply contDiff_const).inner ℝ (hDu1.clm_apply contDiff_const)
  have hθ1 : ∀ k, ContDiff ℝ 1 (θ k) := fun k =>
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hW).mul hS1
  have hθ0 : ∀ k, ∀ y ∉ tsupport u, θ k y = 0 := fun k y hy => by simp [θ, S, hDu0 y hy]
  have hθd : ∀ k y, fderiv ℝ (θ k) y (unitVector k) =
      (fderiv ℝ W y (unitVector k)) k * S y + W y k * ∑ j : Fin 3,
        2 * inner ℝ (fderiv ℝ (fderiv ℝ u) y (unitVector k) (unitVector j))
          (fderiv ℝ u y (unitVector j)) := by
    intro k y
    have hc := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hWd y).hasFDerivAt
    have hS : HasFDerivAt S _ y := HasFDerivAt.fun_sum fun j _ =>
      ((hDud y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector j) y)).inner ℝ
        ((hDud y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector j) y))
    have hT : HasFDerivAt (θ k) _ y := hc.mul hS
    rw [hT.fderiv]
    simp [real_inner_comm, Finset.mul_sum]
    simp only [← two_mul]
    ring
  have hpt : ∀ y, inner ℝ (fderiv ℝ u y (W y)) (-sumSecondPartialsAt u y) =
      ∑ j : Fin 3, inner ℝ (fderiv ℝ u y (fderiv ℝ W y (unitVector j))) (fderiv ℝ u y (unitVector j)) +
        ((1 / 2) * ∑ k : Fin 3, fderiv ℝ (θ k) y (unitVector k) -
          ∑ j : Fin 3, fderiv ℝ (φ j) y (unitVector j)) := by
    intro y
    have hlap : sumSecondPartialsAt u y = ∑ j : Fin 3,
        fderiv ℝ (fderiv ℝ u) y (unitVector j) (unitVector j) := by
      simp [sumSecondPartialsAt, iteratedFDeriv_two_apply]
    have F1 : ∑ k : Fin 3, (fderiv ℝ W y (unitVector k)) k = 0 := hdiv y
    have F2 : ∀ j : Fin 3, ∑ k : Fin 3, W y k *
        inner ℝ (fderiv ℝ (fderiv ℝ u) y (unitVector k) (unitVector j)) (fderiv ℝ u y (unitVector j)) =
        inner ℝ (fderiv ℝ (fderiv ℝ u) y (unitVector j) (W y)) (fderiv ℝ u y (unitVector j)) := by
      intro j
      rw [second_expand, hsym]
    have F20 := F2 0
    have F21 := F2 1
    have F22 := F2 2
    simp only [Fin.sum_univ_three] at F1 F20 F21 F22
    simp only [hφd, hθd, hlap, Fin.sum_univ_three, inner_neg_right, inner_add_right]
    linear_combination (-(1 / 2) * S y) * F1 - F20 - F21 - F22
  have iT2 : Integrable (fun y => ∑ j : Fin 3,
      inner ℝ (fderiv ℝ u y (fderiv ℝ W y (unitVector j))) (fderiv ℝ u y (unitVector j))) :=
    integrable_off hK (continuous_finsetSum _ fun j _ =>
      (hDuc.clm_apply (hDWc.clm_apply continuous_const)).inner (hDuc.clm_apply continuous_const))
      (fun y hy => by simp [hDu0 y hy])
  have iθ : ∀ k, Integrable (fun y => fderiv ℝ (θ k) y (unitVector k)) := fun k =>
    integrable_off hK (((hθ1 k).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (fun y hy => by rw [fderiv_eq_zero_off hKc (hθ0 k) y hy]; rfl)
  have iφ : ∀ j, Integrable (fun y => fderiv ℝ (φ j) y (unitVector j)) := fun j =>
    integrable_off hK (((hφ1 j).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (fun y hy => by rw [fderiv_eq_zero_off hKc (hφ0 j) y hy]; rfl)
  have iSθ := integrable_finsetSum Finset.univ fun k _ => iθ k
  have iSφ := integrable_finsetSum Finset.univ fun j _ => iφ j
  have zθ : ∫ y, ∑ k : Fin 3, fderiv ℝ (θ k) y (unitVector k) = 0 := by
    rw [integral_finsetSum _ fun k _ => iθ k]
    exact Finset.sum_eq_zero fun k _ => integral_fderiv_eq_zero hK (hθ1 k) (hθ0 k) _
  have zφ : ∫ y, ∑ j : Fin 3, fderiv ℝ (φ j) y (unitVector j) = 0 := by
    rw [integral_finsetSum _ fun j _ => iφ j]
    exact Finset.sum_eq_zero fun j _ => integral_fderiv_eq_zero hK (hφ1 j) (hφ0 j) _
  calc (∫ y, inner ℝ (fderiv ℝ u y (W y)) (-sumSecondPartialsAt u y))
      = ∫ y, (∑ j : Fin 3,
          inner ℝ (fderiv ℝ u y (fderiv ℝ W y (unitVector j))) (fderiv ℝ u y (unitVector j)) +
          ((1 / 2) * ∑ k : Fin 3, fderiv ℝ (θ k) y (unitVector k) -
            ∑ j : Fin 3, fderiv ℝ (φ j) y (unitVector j))) := by
        congr 1
        funext y
        exact hpt y
    _ = (∫ y, ∑ j : Fin 3,
          inner ℝ (fderiv ℝ u y (fderiv ℝ W y (unitVector j))) (fderiv ℝ u y (unitVector j))) +
          ((1 / 2) * (∫ y, ∑ k : Fin 3, fderiv ℝ (θ k) y (unitVector k)) -
            ∫ y, ∑ j : Fin 3, fderiv ℝ (φ j) y (unitVector j)) := by
        have h1 : Integrable (fun y => (1 / 2) * ∑ k : Fin 3, fderiv ℝ (θ k) y (unitVector k)) :=
          iSθ.const_mul _
        have h2 : Integrable (fun y => (1 / 2) * ∑ k : Fin 3, fderiv ℝ (θ k) y (unitVector k) -
            ∑ j : Fin 3, fderiv ℝ (φ j) y (unitVector j)) := h1.sub iSφ
        rw [integral_add iT2 h2, integral_sub h1 iSφ, integral_const_mul]
    _ = _ := by
        rw [zθ, zφ]
        simp only [mul_zero, sub_zero, add_zero]
        congr 1
        funext y
        exact pair_sum _ _

end Internal.ConvectionSmooth

theorem convectionIdentitySmooth (W u : Space → Space) (C : ℝ) (hW : ContDiff ℝ 1 W)
    (_hWb : ∀ y, ‖W y‖ ≤ C) (_hDW : ∀ y, ‖fderiv ℝ W y‖ ≤ C) (hdiv : ∀ y, divergenceAt W y = 0)
    (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) :
    (∫ y, inner ℝ (fderiv ℝ u y (W y)) (-sumSecondPartialsAt u y)) =
      ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y (ContinuousLinearMap.adjoint (fderiv ℝ u y) (unitVector i)))
        (ContinuousLinearMap.adjoint (fderiv ℝ u y) (unitVector i)) :=
  Internal.ConvectionSmooth.identity hW hdiv hu hs

end CertReduction

end Breakdown

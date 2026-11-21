import Breakdown.FracCell.CellDensityModesMirror

open MeasureTheory Real

noncomputable section

namespace Breakdown.FracInternal.CellDensityModesWeak

open SteadyCert CellCert CellCert.CellAnalysis FracInternal.CellDensityModesMirror

theorem mirror_coe : (⇑LinearSolveCore.mirrorIsometry : Space → Space) = mirror := rfl

theorem mirror_coe' : (⇑LinearSolveCore.mirrorIsometry.toLinearIsometry : Space → Space) = mirror := rfl

theorem mirror_neg (u : Space) : mirror (-u) = -mirror u := by
  ext i; simp [mirror_apply]

theorem mirror_emb : MeasurableEmbedding mirror := by
  rw [← mirror_coe]; exact LinearSolveCore.mirrorIsometry.toHomeomorph.measurableEmbedding

theorem test_comp {φ : Space → ℝ} (hφ : IsTestScalar φ) : IsTestScalar (fun y => φ (mirror y)) := by
  refine ⟨?_, ?_⟩
  · have : (fun y => φ (mirror y)) = φ ∘ (LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv : Space →L[ℝ] Space) := rfl
    rw [this]
    exact hφ.1.comp (ContinuousLinearMap.contDiff _)
  · exact hφ.2.comp_homeomorph LinearSolveCore.mirrorIsometry.toHomeomorph

theorem deriv_comp {φ : Space → ℝ} (hφ : IsTestScalar φ) (w : Space) (j : Fin 3) :
    fderiv ℝ (fun y => φ (mirror y)) w (unitVector j) = sgn j * fderiv ℝ φ (mirror w) (unitVector j) := by
  have hL : (fun y => φ (mirror y)) = φ ∘ (LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv : Space →L[ℝ] Space) := rfl
  rw [hL, fderiv_comp w ((hφ.1.differentiable (by simp)) _)
    (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h1 : (LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv : Space →L[ℝ] Space) (unitVector j)
      = sgn j • unitVector j := mirror_unit j
  have h2 : (LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv : Space →L[ℝ] Space) w = mirror w := rfl
  rw [h1, h2, map_smul, smul_eq_mul]

theorem weak_mirror {f g : Space → Space} (j : Fin 3) (c : ℝ)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g y)
    (hg : MemLp g 2 volume) (hf : ∀ᵐ y ∂volume, f (mirror y) = c • mirror (f y)) :
    ∀ᵐ y ∂volume, g (mirror y) = (c * sgn j) • mirror (g y) := by
  have hmp := LinearSolveCore.mirror_measurePreserving
  have hg1 : LocallyIntegrable (fun y => g (mirror y)) volume :=
    (hg.comp_measurePreserving hmp).locallyIntegrable (by norm_num)
  have hg2 : LocallyIntegrable (fun y => (c * sgn j) • mirror (g y)) volume := by
    have : MemLp (fun y => mirror (g y)) 2 volume := by
      rw [← mirror_coe]
      exact LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hg
    exact (this.const_smul (c * sgn j)).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq hg1 hg2 fun φ hφd hφs => ?_
  have hφ : IsTestScalar φ := ⟨hφd, hφs⟩
  have lhs : (∫ y, φ y • g (mirror y)) = -(sgn j • ∫ y, fderiv ℝ φ y (unitVector j) • f (mirror y)) := by
    have e1 : (∫ y, φ y • g (mirror y)) = ∫ y, φ (mirror y) • g y := by
      rw [← hmp.integral_comp mirror_emb (fun y => φ (mirror y) • g y)]
      simp only [mirror_mirror]
    have e2 : (∫ y, fderiv ℝ (fun y => φ (mirror y)) y (unitVector j) • f y)
        = sgn j • ∫ y, fderiv ℝ φ y (unitVector j) • f (mirror y) := by
      simp only [deriv_comp hφ]
      rw [← integral_smul, ← hmp.integral_comp mirror_emb]
      simp only [mirror_mirror, smul_smul]
    have h := hw _ (test_comp hφ)
    rw [e2] at h
    rw [e1, h, neg_neg]
  have rhs : (∫ y, φ y • (c * sgn j) • mirror (g y)) = -((c * sgn j) • mirror (∫ y, fderiv ℝ φ y (unitVector j) • f y)) := by
    have : (fun y => φ y • (c * sgn j) • mirror (g y)) = fun y => (c * sgn j) • LinearSolveCore.mirrorIsometry.toLinearIsometry (φ y • g y) := by
      funext y; rw [map_smul, smul_comm]; rfl
    rw [this, integral_smul, LinearIsometry.integral_comp_comm, mirror_coe', hw φ hφ, mirror_neg, smul_neg, neg_neg]
  rw [lhs, rhs]
  have e3 : (∫ y, fderiv ℝ φ y (unitVector j) • f (mirror y)) = c • mirror (∫ y, fderiv ℝ φ y (unitVector j) • f y) := by
    rw [integral_congr_ae (hf.mono fun y hy => by rw [hy])]
    have : (fun y => fderiv ℝ φ y (unitVector j) • c • mirror (f y))
        = fun y => c • LinearSolveCore.mirrorIsometry.toLinearIsometry (fderiv ℝ φ y (unitVector j) • f y) := by
      funext y; rw [map_smul, smul_comm]; rfl
    rw [this, integral_smul, LinearIsometry.integral_comp_comm, mirror_coe']
  rw [e3, smul_smul, mul_comm (sgn j) c]


theorem vec_expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem lin_from_units {A B : Space →L[ℝ] Space}
    (h : ∀ j, A (unitVector j) = sgn j • mirror (B (unitVector j))) (u : Space) :
    A u = mirror (B (mirror u)) := by
  conv_lhs => rw [vec_expand u]
  conv_rhs => rw [vec_expand (mirror u)]
  simp only [map_sum, map_smul, h]
  simp only [Fin.sum_univ_three]
  ext a
  simp only [mirror_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem bilin_from_units {A B : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ j i, A (unitVector j) (unitVector i) = (sgn i * sgn j) • mirror (B (unitVector j) (unitVector i)))
    (u u' : Space) : A u u' = mirror (B (mirror u) (mirror u')) := by
  conv_lhs => rw [vec_expand u, vec_expand u']
  conv_rhs => rw [vec_expand (mirror u), vec_expand (mirror u')]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, h]
  simp only [Fin.sum_univ_three]
  ext a
  simp only [mirror_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem memLp_col {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (j : Fin 3) : MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    hm.apply_continuousLinearMap (unitVector j)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)


theorem memLp_col2 {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (j i : Fin 3) :
    MemLp (fun y => H y (unitVector j) (unitVector i)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
    (hm.apply_continuousLinearMap (unitVector j)).apply_continuousLinearMap (unitVector i)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  calc ‖H y (unitVector j) (unitVector i)‖ ^ 2 ≤ ∑ i' : Fin 3, ‖H y (unitVector j) (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ‖H y (unitVector j) (unitVector i')‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
    _ ≤ ∑ j' : Fin 3, ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

end Breakdown.FracInternal.CellDensityModesWeak

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert FracInternal.CellDensityModesMirror FracInternal.CellDensityModesWeak

theorem gradientMirror : GradientMirrorStatement := by
  intro m v G H hs
  have hv : ∀ᵐ y ∂volume, v (mirror y) = (1 : ℝ) • mirror (v y) :=
    hs.symmetric.2.mono fun y hy => by rw [hy, one_smul]
  have hG : ∀ j, ∀ᵐ y ∂volume, G (mirror y) (unitVector j) = (1 * sgn j) • mirror (G y (unitVector j)) :=
    fun j => weak_mirror (f := v) (g := fun y => G y (unitVector j)) j 1
      (fun φ hφ => hs.weak_gradient φ hφ j) (memLp_col hs.measurable_gradient hs.gradient_two j) hv
  have hH : ∀ i j, ∀ᵐ y ∂volume, H (mirror y) (unitVector j) (unitVector i)
      = (sgn i * sgn j) • mirror (H y (unitVector j) (unitVector i)) := fun i j =>
    weak_mirror (f := fun y => G y (unitVector i)) (g := fun y => H y (unitVector j) (unitVector i)) j (sgn i)
      (fun φ hφ => hs.weak_second φ hφ i j) (memLp_col2 hs.measurable_second hs.second_two j i)
      ((hG i).mono fun y hy => by rw [hy, one_mul])
  filter_upwards [ae_all_iff.2 hG, ae_all_iff.2 (fun i => ae_all_iff.2 (hH i))] with y hGy hHy
  exact ⟨lin_from_units (fun j => by rw [hGy j, one_mul]), bilin_from_units (fun j i => hHy i j)⟩

end Breakdown.CellCert.CellAnalysis

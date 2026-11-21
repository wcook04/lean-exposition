import Breakdown.FracCell.CellDensityModesWeak

open MeasureTheory Real

noncomputable section

namespace Breakdown.FracInternal.CellDensityModesTurn

open SteadyCert CellCert CellCert.CellAnalysis FracInternal.CellDensityModesWeak

theorem weak_dir {f : Space → Space} {g : Fin 3 → Space → Space} (hfl : LocallyIntegrable f volume)
    (hgl : ∀ j, LocallyIntegrable (g j) volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j, ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g j y)
    {φ : Space → ℝ} (hφ : IsTestScalar φ) (u : Space) :
    ∫ y, fderiv ℝ φ y u • f y = -∫ y, φ y • ∑ j : Fin 3, u j • g j y := by
  have e1 : ∀ y, fderiv ℝ φ y u • f y = ∑ j : Fin 3, u j • (fderiv ℝ φ y (unitVector j) • f y) := by
    intro y
    conv_lhs => rw [vec_expand u]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_smul, smul_smul]
  have e2 : ∀ y, φ y • ∑ j : Fin 3, u j • g j y = ∑ j : Fin 3, u j • (φ y • g j y) := by
    intro y; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  have i1 : ∀ j, Integrable (fun y => fderiv ℝ φ y (unitVector j) • f y) := fun j =>
    hfl.integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hφ.2.fderiv_apply ℝ (unitVector j))
  have i2 : ∀ j, Integrable (fun y => φ y • g j y) := fun j =>
    (hgl j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  simp only [e1, e2]
  rw [integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul, integral_smul, hw φ hφ j, smul_neg]
  · intro j _; exact (i2 j).smul (u j)
  · intro j _; exact (i1 j).smul (u j)


theorem test_equiv (L : Space ≃ₗᵢ[ℝ] Space) {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    IsTestScalar (fun w => φ (L.symm w)) := by
  refine ⟨?_, ?_⟩
  · have : (fun w => φ (L.symm w)) = φ ∘ (L.symm.toContinuousLinearEquiv : Space →L[ℝ] Space) := rfl
    rw [this]; exact hφ.1.comp (ContinuousLinearMap.contDiff _)
  · exact hφ.2.comp_homeomorph L.symm.toHomeomorph

theorem deriv_equiv (L : Space ≃ₗᵢ[ℝ] Space) {φ : Space → ℝ} (hφ : IsTestScalar φ) (w u : Space) :
    fderiv ℝ (fun w => φ (L.symm w)) w (L u) = fderiv ℝ φ (L.symm w) u := by
  have hL : (fun w => φ (L.symm w)) = φ ∘ (L.symm.toContinuousLinearEquiv : Space →L[ℝ] Space) := rfl
  rw [hL, fderiv_comp w ((hφ.1.differentiable (by simp)) _) (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  congr 1
  exact L.symm_apply_apply u

theorem weak_equiv (L : Space ≃ₗᵢ[ℝ] Space) {f f' : Space → Space} {g g' : Fin 3 → Space → Space}
    (hfl : LocallyIntegrable f' volume) (hg : ∀ j, MemLp (g j) 2 volume) (hg' : ∀ j, MemLp (g' j) 2 volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j, ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g j y)
    (hw' : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j, ∫ y, fderiv ℝ φ y (unitVector j) • f' y = -∫ y, φ y • g' j y)
    (hf : ∀ᵐ y ∂volume, f' (L y) = L (f y)) (j : Fin 3) :
    ∀ᵐ y ∂volume, ∑ k : Fin 3, (L (unitVector j)) k • g' k (L y) = L (g j y) := by
  have hmp : MeasurePreserving L volume volume := L.measurePreserving
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have h1 : LocallyIntegrable (fun y => ∑ k : Fin 3, (L (unitVector j)) k • g' k (L y)) volume := by
    refine locallyIntegrable_finsetSum _ fun k _ => ?_
    exact (((hg' k).comp_measurePreserving hmp).const_smul ((L (unitVector j)) k : ℝ)).locallyIntegrable (by norm_num)
  have h2 : LocallyIntegrable (fun y => L (g j y)) volume :=
    ((L.toContinuousLinearEquiv : Space →L[ℝ] Space).comp_memLp' (hg j)).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq h1 h2 fun φ hφd hφs => ?_
  have hφ : IsTestScalar φ := ⟨hφd, hφs⟩
  have e1 : (∫ y, φ y • ∑ k : Fin 3, (L (unitVector j)) k • g' k (L y))
      = ∫ w, φ (L.symm w) • ∑ k : Fin 3, (L (unitVector j)) k • g' k w := by
    rw [← hmp.integral_comp hemb (fun w => φ (L.symm w) • ∑ k : Fin 3, (L (unitVector j)) k • g' k w)]
    simp only [LinearIsometryEquiv.symm_apply_apply]
  have e2 := weak_dir hfl (fun k => (hg' k).locallyIntegrable (by norm_num)) hw' (test_equiv L hφ) (L (unitVector j))
  simp only [deriv_equiv L hφ] at e2
  have e3 : (∫ w, fderiv ℝ φ (L.symm w) (unitVector j) • f' w) = ∫ y, fderiv ℝ φ y (unitVector j) • f' (L y) := by
    rw [← hmp.integral_comp hemb (fun w => fderiv ℝ φ (L.symm w) (unitVector j) • f' w)]
    simp only [LinearIsometryEquiv.symm_apply_apply]
  have e4 : (∫ y, fderiv ℝ φ y (unitVector j) • f' (L y)) = L (∫ y, fderiv ℝ φ y (unitVector j) • f y) := by
    rw [integral_congr_ae (hf.mono fun y hy => by rw [hy])]
    simp only [← map_smul]
    exact L.toLinearIsometry.integral_comp_comm _
  have e5 : (∫ y, φ y • L (g j y)) = L (∫ y, φ y • g j y) := by
    simp only [← map_smul]
    exact L.toLinearIsometry.integral_comp_comm _
  rw [e1, e5, ← neg_neg (∫ w, φ (L.symm w) • _), ← e2, e3, e4, hw φ hφ j, map_neg, neg_neg]


theorem sum_units (A : Space →L[ℝ] Space) (w : Space) : ∑ k : Fin 3, w k • A (unitVector k) = A w := by
  conv_rhs => rw [vec_expand w]
  simp only [map_sum, map_smul]

theorem first_turn (L : Space ≃ₗᵢ[ℝ] Space) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    (hv : ∀ᵐ y ∂volume, v (L y) = L (v y)) :
    ∀ᵐ y ∂volume, ∀ u, G (L y) (L u) = L (G y u) := by
  have hb : ∀ j, ∀ᵐ y ∂volume, G (L y) (L (unitVector j)) = L (G y (unitVector j)) := by
    intro j
    have := weak_equiv L (f := v) (f' := v) (g := fun j y => G y (unitVector j)) (g' := fun j y => G y (unitVector j))
      (hs.velocity_six.locallyIntegrable (by norm_num)) (memLp_col hs.measurable_gradient hs.gradient_two)
      (memLp_col hs.measurable_gradient hs.gradient_two) (fun φ hφ j => hs.weak_gradient φ hφ j)
      (fun φ hφ j => hs.weak_gradient φ hφ j) hv j
    refine this.mono fun y hy => ?_
    rw [← hy, sum_units]
  filter_upwards [ae_all_iff.2 hb] with y hy u
  conv_lhs => rw [vec_expand u]
  conv_rhs => rw [vec_expand u]
  simp only [map_sum, map_smul, hy]


theorem sum_units2 (A : Space →L[ℝ] Space →L[ℝ] Space) (w u : Space) :
    ∑ k : Fin 3, w k • A (unitVector k) u = A w u := by
  conv_rhs => rw [vec_expand w]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]

theorem memLp_dir {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (w : Space) : MemLp (fun y => G y w) 2 volume := by
  have e : (fun y => G y w) = fun y => ∑ k : Fin 3, w k • G y (unitVector k) := funext fun y => (sum_units _ _).symm
  rw [e]
  exact memLp_finsetSum _ fun k _ => (memLp_col hm hi k).const_smul (w k)

theorem memLp_dir2 {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (k : Fin 3)
    (w : Space) : MemLp (fun y => H y (unitVector k) w) 2 volume := by
  have e : (fun y => H y (unitVector k) w) = fun y => ∑ l : Fin 3, w l • H y (unitVector k) (unitVector l) :=
    funext fun y => (sum_units _ _).symm
  rw [e]
  exact memLp_finsetSum _ fun l _ => (memLp_col2 hm hi k l).const_smul (w l)

theorem weak_comb {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (w : Space) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j, ∫ y, fderiv ℝ φ y (unitVector j) • G y w
      = -∫ y, φ y • H y (unitVector j) w := by
  intro φ hφ j
  have e1 : ∀ y, fderiv ℝ φ y (unitVector j) • G y w
      = ∑ l : Fin 3, w l • (fderiv ℝ φ y (unitVector j) • G y (unitVector l)) := by
    intro y; rw [← sum_units (G y) w, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  have e2 : ∀ y, φ y • H y (unitVector j) w = ∑ l : Fin 3, w l • (φ y • H y (unitVector j) (unitVector l)) := by
    intro y; rw [← sum_units (H y (unitVector j)) w, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  simp only [e1, e2]
  rw [integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_smul, integral_smul, hs.weak_second φ hφ l j, smul_neg]
  · intro l _
    exact (((memLp_col2 hs.measurable_second hs.second_two j l).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.1.continuous hφ.2).smul (w l)
  · intro l _
    exact (((memLp_col hs.measurable_gradient hs.gradient_two l).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hφ.2.fderiv_apply ℝ (unitVector j))).smul (w l)

theorem second_turn (L : Space ≃ₗᵢ[ℝ] Space) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    (hv : ∀ᵐ y ∂volume, v (L y) = L (v y)) :
    ∀ᵐ y ∂volume, ∀ u u', H (L y) (L u) (L u') = L (H y u u') := by
  have h1 := first_turn L hs hv
  have hb : ∀ i j, ∀ᵐ y ∂volume, H (L y) (L (unitVector j)) (L (unitVector i)) = L (H y (unitVector j) (unitVector i)) := by
    intro i j
    have := weak_equiv L (f := fun y => G y (unitVector i)) (f' := fun y => G y (L (unitVector i)))
      (g := fun j y => H y (unitVector j) (unitVector i)) (g' := fun k y => H y (unitVector k) (L (unitVector i)))
      ((memLp_dir hs.measurable_gradient hs.gradient_two _).locallyIntegrable (by norm_num))
      (fun j => memLp_col2 hs.measurable_second hs.second_two j i)
      (fun k => memLp_dir2 hs.measurable_second hs.second_two k _)
      (fun φ hφ j => hs.weak_second φ hφ i j) (weak_comb hs _) (h1.mono fun y hy => hy (unitVector i)) j
    refine this.mono fun y hy => ?_
    rw [← hy, sum_units2]
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (hb i)] with y hy u u'
  conv_lhs => rw [vec_expand u, vec_expand u']
  conv_rhs => rw [vec_expand u, vec_expand u']
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, hy]

end Breakdown.FracInternal.CellDensityModesTurn

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert FracInternal.CellDensityModesTurn

def GradientTurnStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
      ∀ᵐ y ∂volume, (∀ u, G (turnStep m y) (turnStep m u) = turnStep m (G y u)) ∧
        ∀ u u', H (turnStep m y) (turnStep m u) (turnStep m u') = turnStep m (H y u u')

theorem gradientTurn : GradientTurnStatement := by
  intro m v G H hs
  have hv : ∀ᵐ y ∂volume, v (LinearSolveCore.turnStepIsometry m y) = LinearSolveCore.turnStepIsometry m (v y) :=
    hs.symmetric.1
  filter_upwards [first_turn _ hs hv, second_turn _ hs hv] with y h1 h2
  exact ⟨h1, h2⟩

end Breakdown.CellCert.CellAnalysis

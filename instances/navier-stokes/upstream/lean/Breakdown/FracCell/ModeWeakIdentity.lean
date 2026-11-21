import Breakdown.FracCell.StCornerModesOpen
import Breakdown.FracCell.CylModeWeak

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

private def unitAt (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

private theorem unitAt_circle (θ : ℝ) : unitAt (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

private def angQ (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, unitAt q a k • EuclideanSpace.proj k

private def angL (a : Fin 3) (θ : ℝ) : Space →L[ℝ] ℝ := angQ a (Real.cos θ, Real.sin θ)

private theorem angL_apply (a : Fin 3) (θ : ℝ) (u : Space) : angL a θ u = inner ℝ u (frameUnit θ a) := by
  simp [angL, angQ, unitAt_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem unitAt_coord_smooth (a k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [unitAt, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

private theorem unitAt_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a) :=
  (contDiff_piLp 2).2 fun k => unitAt_coord_smooth a k

private theorem angQ_smooth (a : Fin 3) : ContDiff ℝ ∞ (angQ a) := by
  unfold angQ
  exact ContDiff.sum fun k _ => (unitAt_coord_smooth a k).smul contDiff_const

private def colQ (a : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (angQ a q).comp (ContinuousLinearMap.apply ℝ Space (unitAt q 0))

private def colL (a : Fin 3) (θ : ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ := colQ a (Real.cos θ, Real.sin θ)

private theorem colQ_smooth (a : Fin 3) : ContDiff ℝ ∞ (colQ a) :=
  (angQ_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (unitAt_smooth 0))

private theorem colL_apply (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    colL a θ M = inner ℝ (M (frameUnit θ 0)) (frameUnit θ a) := by
  simp only [colL, colQ, unitAt_circle, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact angL_apply a θ _

private theorem vec_expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem norm_le_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [vec_expand u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

private theorem loc_norm {E : Type} [NormedAddCommGroup E] {f : Space → E} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => ‖f y‖) volume :=
  hf.mono hf.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun y => by simp)

private theorem loc_of_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Space → (Space →L[ℝ] E)} (hm : AEStronglyMeasurable A volume)
    (hc : ∀ i, LocallyIntegrable (fun y => A y (unitVector i)) volume) : LocallyIntegrable A volume := by
  have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖A y (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((loc_norm (hc 0)).add (loc_norm (hc 1))).add (loc_norm (hc 2))
  refine hs.mono hm (Filter.Eventually.of_forall fun y => ?_)
  refine (norm_le_cols (A y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

private theorem memLp_col' {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (j : Fin 3) : MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    hm.apply_continuousLinearMap (unitVector j)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)

private theorem memLp_col2' {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
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

private def IsTest2 (ψ : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ∀ p ∈ tsupport ψ, 0 < p.1

private theorem test_facts {ψ : ℝ × ℝ → ℝ} (hψ : IsTest2 ψ) (u : ℝ × ℝ) :
    IsTest2 (fun p => fderiv ℝ ψ p u) :=
  ⟨(hψ.1.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const, hψ.2.1.fderiv_apply (𝕜 := ℝ) u,
    fun p hp => hψ.2.2 p (tsupport_fderiv_apply_subset ℝ u hp)⟩

private theorem mixed {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p u w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ ψ q u) p w = fderiv ℝ (fun q => fderiv ℝ ψ q w) p u := by
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp)
  have e : ∀ u', fderiv ℝ (fun q => fderiv ℝ ψ q u') p = (fderiv ℝ (fderiv ℝ ψ) p).flip u' := by
    intro u'
    rw [fderiv_clm_apply (hd p) (differentiableAt_const u')]
    simp
  rw [e, e]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) w u

private theorem third_of {V g0 g2 h : ℝ × ℝ → ℂ}
    (I1 : ∀ ψ, IsTest2 ψ → ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * V p = -∫ p, (ψ p : ℂ) * g0 p)
    (I2 : ∀ ψ, IsTest2 ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * V p = -∫ p, (ψ p : ℂ) * g2 p)
    (I4 : ∀ ψ, IsTest2 ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * g0 p = -∫ p, (ψ p : ℂ) * h p)
    (ψ : ℝ × ℝ → ℝ) (hψ : IsTest2 ψ) :
    ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * g2 p = -∫ p, (ψ p : ℂ) * h p := by
  have a := I2 _ (test_facts hψ (1, 0))
  have b := I1 _ (test_facts hψ (0, 1))
  have e : (fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (1, 0)) p (0, 1) : ℝ) : ℂ) * V p) =
      fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (0, 1)) p (1, 0) : ℝ) : ℂ) * V p :=
    funext fun p => by rw [mixed hψ.1]
  rw [e, b, I4 ψ hψ] at a
  rw [neg_neg] at a
  rw [a, neg_neg]

private theorem scale {A B c d : ℝ × ℝ → ℂ} (k : ℂ) (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p => c p * (k * A p)) = fun p => k * (c p * A p) := funext fun p => by ring
  have e2 : (fun p => d p * (k * B p)) = fun p => k * (d p * B p) := funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

private theorem frameVec_eq (θ : ℝ) (u : Space) (a : Fin 3) : frameVec θ u a = inner ℝ u (frameUnit θ a) := by
  fin_cases a <;> rfl

theorem modeWeakIdentity_of (h : CylModeWeakStatement) : ModeWeakIdentityStatement := by
  intro m v G H hs n a
  have hv : LocallyIntegrable v volume := hs.velocity_six.locallyIntegrable (by norm_num)
  have hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (memLp_col' hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)
  have hG : LocallyIntegrable G volume := loc_of_cols hs.measurable_gradient hGc
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    loc_of_cols (hs.measurable_second.apply_continuousLinearMap (unitVector j)) fun i =>
      (memLp_col2' hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)
  have hweakG : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
    intro φ hφ j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
      hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
      (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
        (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
      intro i
      rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
      simpa using hs.weak_second φ hφ i j
    refine ContinuousLinearMap.ext fun u => ?_
    rw [vec_expand u]
    simp only [map_sum, map_smul, key]
  have hmv : ∀ p : ℝ × ℝ, modeVec m n v p.1 p.2 a = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (angL a θ (v (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [modeVec, angL_apply, frameVec_eq]
  have hgm : ∀ (b : Fin 3) (p : ℝ × ℝ), gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (angL a θ (G (cylPoint p.1 θ p.2) (frameUnit θ b)) : ℂ) := by
    intro b p
    simp only [gradMode, modeMat, angL_apply]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a 0 2 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (colL a θ (H (cylPoint p.1 θ p.2) axialUnit) : ℂ) := by
    intro p
    simp only [modeThird, colL_apply]
    rfl
  have I1 : ∀ ψ, IsTest2 ψ → ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
      -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p := by
    intro ψ hψ
    simp only [hmv, hgm]
    exact scale _ (h Space v G hv hGc hs.weak_gradient (angQ a) (angQ_smooth a) m n ψ
      hψ.1 hψ.2.1 hψ.2.2).1
  have I2 : ∀ ψ, IsTest2 ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
      -∫ p, (ψ p : ℂ) * gradMode m n G a 2 p := by
    intro ψ hψ
    simp only [hmv, hgm]
    exact scale _ (h Space v G hv hGc hs.weak_gradient (angQ a) (angQ_smooth a) m n ψ
      hψ.1 hψ.2.1 hψ.2.2).2
  have I4 : ∀ ψ, IsTest2 ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a 0 p =
      -∫ p, (ψ p : ℂ) * modeThird m n H a 0 2 p := by
    intro ψ hψ
    simp only [hth, hgm]
    exact scale _ (h (Space →L[ℝ] Space) G H hG hHc hweakG (colQ a) (colQ_smooth a) m n ψ
      hψ.1 hψ.2.1 hψ.2.2).2
  intro ψ hψ hc hpos
  have ht : IsTest2 ψ := ⟨hψ, hc, hpos⟩
  exact ⟨I1 ψ ht, I2 ψ ht, third_of I1 I2 I4 ψ ht, I4 ψ ht⟩

theorem modeWeakIdentity : ModeWeakIdentityStatement :=
  modeWeakIdentity_of cylModeWeak

end Breakdown.CellCert.CellFormula

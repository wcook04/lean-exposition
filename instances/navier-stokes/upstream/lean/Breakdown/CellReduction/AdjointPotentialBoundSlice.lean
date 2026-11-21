import Breakdown.CellReduction.AdjointPotentialBoundPairing

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

namespace PotentialBound

structure SliceField (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) : Prop where
  mv : AEStronglyMeasurable v volume
  mG : AEStronglyMeasurable G volume
  weak : IsWeakGradient v G
  six : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 6) < ⊤
  grad : ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤

theorem integrable_of_decay {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) {B a : ℝ} (ha : 3 < a)
    (hb : ∀ᵐ y, |f y| ≤ B * (1 + ‖y‖) ^ (-a)) : Integrable f :=
  ((space_weight_integrable ha).const_mul B).mono' hf (hb.mono fun y hy => by rwa [Real.norm_eq_abs])

theorem sq_le_of_decay {t B a x : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (h : t ≤ B * (1 + x) ^ (-a)) :
    t ^ 2 ≤ B ^ 2 * (1 + x) ^ (-(2 * a)) := by
  have hp : 0 < 1 + x := by linarith
  have h1 : t ^ 2 ≤ (B * (1 + x) ^ (-a)) ^ 2 := pow_le_pow_left₀ ht h 2
  have e : (B * (1 + x) ^ (-a)) ^ 2 = B ^ 2 * (1 + x) ^ (-(2 * a)) := by
    rw [mul_pow, ← Real.rpow_natCast ((1 + x) ^ (-a)), ← Real.rpow_mul hp.le]
    congr 2
    push_cast
    ring
  linarith

theorem sq_integrable_of_decay {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) {B a : ℝ} (ha : 3 < 2 * a)
    (h0 : ∀ y, 0 ≤ f y) (hb : ∀ᵐ y, f y ≤ B * (1 + ‖y‖) ^ (-a)) : Integrable (fun y => f y ^ 2) := by
  refine integrable_of_decay (B := B ^ 2) (a := 2 * a) (hf.pow 2) ha (hb.mono fun y hy => ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact sq_le_of_decay (norm_nonneg y) (h0 y) hy

theorem column_norm_le (A : Space →L[ℝ] Space) (i : Fin 3) : ‖A (unitVector i)‖ ≤ ‖A‖ := by
  have := A.le_opNorm (unitVector i)
  rwa [FracInternal.ConvectionPairing.unit_norm, mul_one] at this

theorem weighted_integrable_of_decay {d : Space → Space} (hd : AEStronglyMeasurable d volume) {B a : ℝ}
    (ha : 3 < 2 * a) (hb : ∀ᵐ y, ‖y‖ * ‖d y‖ ≤ B * (1 + ‖y‖) ^ (-a)) :
    Integrable (fun y => ‖y‖ ^ 2 * ‖d y‖ ^ 2) := by
  have h := sq_integrable_of_decay (f := fun y => ‖y‖ * ‖d y‖)
    (continuous_norm.aestronglyMeasurable.mul hd.norm) ha (fun y => by positivity) hb
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [mul_pow]

theorem pair_flux {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hs : SliceField v G)
    {K : Space → (Space →L[ℝ] Space)} (hK : IsWeakMatrixDivergence K (matrixDivergence K)) {B a : ℝ}
    (ha : 3 < 2 * a) (hKb : ∀ y, ‖K y‖ ≤ B * (1 + ‖y‖) ^ (-a))
    (hdb : ∀ᵐ y, ‖y‖ * ‖matrixDivergence K y‖ ≤ B * (1 + ‖y‖) ^ (-a)) :
    Integrable (fun y => inner ℝ (v y) (matrixDivergence K y)) ∧
      ∫ y, inner ℝ (v y) (matrixDivergence K y) = -∫ y, matInner (G y) (K y) := by
  have hKm : AEStronglyMeasurable K volume := hK.1.aestronglyMeasurable
  have h := weak_pairing (m := fun i y => K y (unitVector i)) hs.mv hs.mG hs.weak hs.six hs.grad
    (fun i => column_locallyIntegrable hK.1 i) hK.2.1 hK.2.2
    (fun i => sq_integrable_of_decay (hKm.apply_continuousLinearMap _).norm ha (fun y => norm_nonneg _)
      (ae_of_all _ fun y => (column_norm_le _ i).trans (hKb y)))
    (weighted_integrable_of_decay hK.2.1.aestronglyMeasurable ha hdb)
  exact ⟨h.1, h.2⟩

theorem pair_pressure {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hs : SliceField v G)
    (hdiv : ∀ᵐ y, ∑ i : Fin 3, (G y (unitVector i)) i = 0)
    {p : Space → ℝ} (hp : IsWeakScalarGradient p (gradientAt p)) {B : ℝ}
    (hpb : ∀ y, |p y| ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (hgb : ∀ᵐ y, ‖y‖ * ‖gradientAt p y‖ ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ))) :
    Integrable (fun y => inner ℝ (v y) (gradientAt p y)) ∧ ∫ y, inner ℝ (v y) (gradientAt p y) = 0 := by
  have hpm : AEStronglyMeasurable p volume := hp.1.aestronglyMeasurable
  have hml : ∀ i : Fin 3, LocallyIntegrable (fun y => p y • unitVector i) volume := fun i x => by
    obtain ⟨s, hs', hi⟩ := hp.1 x
    exact ⟨s, hs', hi.smul_const _⟩
  have hrel : WeakColumnDivergence (fun i y => p y • unitVector i) (gradientAt p) := by
    intro φ hφ c
    rw [hp.2.2 φ hφ c]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [PiLp.smul_apply, smul_eq_mul, unitVector, EuclideanSpace.single_apply]
    simp
  have h := weak_pairing (m := fun i y => p y • unitVector i) hs.mv hs.mG hs.weak hs.six hs.grad hml hp.2.1 hrel
    (fun i => by
      refine sq_integrable_of_decay (B := B) (a := 2) (hpm.smul_const _).norm (by norm_num)
        (fun y => norm_nonneg _) (ae_of_all _ fun y => ?_)
      rw [norm_smul, FracInternal.ConvectionPairing.unit_norm, mul_one, Real.norm_eq_abs]
      exact hpb y)
    (weighted_integrable_of_decay hp.2.1.aestronglyMeasurable (by norm_num) hgb)
  refine ⟨h.1, ?_⟩
  rw [h.2, neg_eq_zero]
  refine integral_eq_zero_of_ae (hdiv.mono fun y hy => ?_)
  simp only [real_inner_smul_right, Pi.zero_apply]
  rw [← Finset.mul_sum]
  have e : ∀ i, inner ℝ (G y (unitVector i)) (unitVector i) = (G y (unitVector i)) i := fun i => by
    simp [unitVector, EuclideanSpace.inner_single_right]
  simp only [e, hy, mul_zero]

theorem column_sum_apply {F : Fin 3 → Space} (c : Fin 3) : (∑ i, F i) c = ∑ i, F i c := by
  simp

theorem integral_apply_comm {f : Space → Space} (hf : Integrable f) (c : Fin 3) :
    ∫ y, f y c = (∫ y, f y) c := by
  have h := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hf
  simpa using h

theorem pair_potential {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hs : SliceField v G)
    {θ : Space → Space} (hθ : ContDiff ℝ 1 θ)
    (hθw : ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ θ y (unitVector j))
      (fun y => (secondDeriv θ y).flip (unitVector j)))
    {B a : ℝ} (ha : 3 < 2 * a) (hb1 : ∀ y, ‖fderiv ℝ θ y‖ ≤ B * (1 + ‖y‖) ^ (-a))
    (hb2 : ∀ᵐ y, ‖y‖ * ‖secondDerivTrace (secondDeriv θ y)‖ ≤ B * (1 + ‖y‖) ^ (-a)) :
    Integrable (fun y => inner ℝ (v y) (secondDerivTrace (secondDeriv θ y))) ∧
      ∫ y, inner ℝ (v y) (secondDerivTrace (secondDeriv θ y)) = -∫ y, matInner (G y) (fderiv ℝ θ y) := by
  have hcol : ∀ j : Fin 3, LocallyIntegrable (fun y => secondDeriv θ y (unitVector j) (unitVector j)) volume := by
    intro j
    have h := column_locallyIntegrable (hθw j).2.1 j
    refine h.congr (ae_of_all _ fun y => ?_)
    simp [ContinuousLinearMap.flip_apply]
  have hdl : LocallyIntegrable (fun y => secondDerivTrace (secondDeriv θ y)) volume := by
    have h := locallyIntegrable_finset_sum (Finset.univ : Finset (Fin 3)) fun j _ => hcol j
    refine h.congr (ae_of_all _ fun y => ?_)
    simp [secondDerivTrace]
  have hDc : Continuous (fun y => fderiv ℝ θ y) := hθ.continuous_fderiv one_ne_zero
  have hml : ∀ i : Fin 3, LocallyIntegrable (fun y => fderiv ℝ θ y (unitVector i)) volume := fun i =>
    (hDc.clm_apply continuous_const).locallyIntegrable
  have hrel : WeakColumnDivergence (fun i y => fderiv ℝ θ y (unitVector i)) (fun y => secondDerivTrace (secondDeriv θ y)) := by
    intro φ hφ c
    have hφc : Continuous φ := hφ.1.continuous
    have hDφc : ∀ i : Fin 3, Continuous (fun y => fderiv ℝ φ y (unitVector i)) := fun i =>
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hDφs : ∀ i : Fin 3, HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) := fun i =>
      hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)
    have i1 : ∀ j : Fin 3, Integrable (fun y => φ y • secondDeriv θ y (unitVector j) (unitVector j)) := fun j =>
      (hcol j).integrable_smul_left_of_hasCompactSupport hφc hφ.2
    have i2 : ∀ j : Fin 3, Integrable (fun y => fderiv ℝ φ y (unitVector j) • fderiv ℝ θ y (unitVector j)) := fun j =>
      (hml j).integrable_smul_left_of_hasCompactSupport (hDφc j) (hDφs j)
    have i1' : ∀ j : Fin 3, Integrable (fun y => (φ y • secondDeriv θ y (unitVector j) (unitVector j)) c) :=
      fun j => (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp (i1 j)
    have i2' : ∀ j : Fin 3, Integrable (fun y => (fderiv ℝ φ y (unitVector j) • fderiv ℝ θ y (unitVector j)) c) :=
      fun j => (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp (i2 j)
    have hw : ∀ j : Fin 3, ∫ y, φ y • secondDeriv θ y (unitVector j) (unitVector j) =
        -∫ y, fderiv ℝ φ y (unitVector j) • fderiv ℝ θ y (unitVector j) := by
      intro j
      have h := (hθw j).2.2 φ hφ j
      refine Eq.trans ?_ h
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp [ContinuousLinearMap.flip_apply]
    calc ∫ y, φ y * secondDerivTrace (secondDeriv θ y) c
        = ∑ j, ∫ y, (φ y • secondDeriv θ y (unitVector j) (unitVector j)) c := by
          rw [← integral_finsetSum _ fun j _ => i1' j]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp [secondDerivTrace, Finset.mul_sum, smul_eq_mul]
      _ = ∑ j, (-∫ y, fderiv ℝ φ y (unitVector j) • fderiv ℝ θ y (unitVector j)) c := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_apply_comm (i1 j), hw j]
      _ = -∑ j, ∫ y, (fderiv ℝ φ y (unitVector j) • fderiv ℝ θ y (unitVector j)) c := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_apply_comm (i2 j)]
          simp
      _ = -∫ y, ∑ i, fderiv ℝ φ y (unitVector i) * fderiv ℝ θ y (unitVector i) c := by
          rw [← integral_finsetSum _ fun j _ => i2' j]
          congr 1
  have h := weak_pairing (m := fun i y => fderiv ℝ θ y (unitVector i)) hs.mv hs.mG hs.weak hs.six hs.grad hml hdl hrel
    (fun i => sq_integrable_of_decay ((hDc.clm_apply continuous_const).aestronglyMeasurable.norm) ha
      (fun y => norm_nonneg _) (ae_of_all _ fun y => (column_norm_le _ i).trans (hb1 y)))
    (weighted_integrable_of_decay hdl.aestronglyMeasurable ha hb2)
  exact ⟨h.1, h.2⟩

theorem integrable_weighted_cols {w : Space → Space} {m : Fin 3 → Space → Space}
    (hw : AEStronglyMeasurable w volume) (hm : ∀ i, AEStronglyMeasurable (m i) volume)
    (hH : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2) < ⊤) (hm2 : ∀ i, Integrable (fun y => ‖m i y‖ ^ 2)) :
    Integrable (fun y => ‖w y‖ / ‖y‖ * ∑ i, ‖m i y‖) := by
  have hH' : Integrable (fun y => ‖w y‖ ^ 2 / ‖y‖ ^ 2) :=
    integrable_of_lintegral_lt (((hw.norm.pow 2).aemeasurable.div
      (continuous_norm.measurable.pow_const 2).aemeasurable).aestronglyMeasurable) (fun y => by positivity) hH
  have hmsum : Integrable (fun y => ∑ i, ‖m i y‖ ^ 2) := integrable_finsetSum Finset.univ fun i _ => hm2 i
  refine ((hH'.const_mul 3).add hmsum).mono' ?_ ?_
  · exact (hw.norm.aemeasurable.div continuous_norm.measurable.aemeasurable).aestronglyMeasurable.mul
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hm i).norm)
  · refine ae_of_all _ fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hs : (∑ i, ‖m i y‖) ^ 2 ≤ 3 * ∑ i, ‖m i y‖ ^ 2 := by
      simp only [Fin.sum_univ_three]
      nlinarith [sq_nonneg (‖m 0 y‖ - ‖m 1 y‖), sq_nonneg (‖m 1 y‖ - ‖m 2 y‖),
        sq_nonneg (‖m 0 y‖ - ‖m 2 y‖)]
    have e : ‖w y‖ ^ 2 / ‖y‖ ^ 2 = (‖w y‖ / ‖y‖) ^ 2 := by rw [div_pow]
    simp only [Pi.add_apply]
    rw [e]
    nlinarith [sq_nonneg (3 * (‖w y‖ / ‖y‖) - ∑ i, ‖m i y‖),
      div_nonneg (norm_nonneg (w y)) (norm_nonneg y), Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (m i y)]

theorem pair_second {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hs : SliceField v G)
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hHw : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (hH2 : Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2))
    {θ : Space → Space} (hθ : ContDiff ℝ 1 θ) {B : ℝ}
    (hb0 : ∀ y, ‖θ y‖ ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ))) (hb1 : ∀ y, ‖fderiv ℝ θ y‖ ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ))) :
    Integrable (fun y => inner ℝ (secondDerivTrace (H y)) (θ y)) ∧
      ∫ y, inner ℝ (secondDerivTrace (H y)) (θ y) = -∫ y, matInner (G y) (fderiv ℝ θ y) := by
  have hcol : ∀ j : Fin 3, LocallyIntegrable (fun y => H y (unitVector j) (unitVector j)) volume := by
    intro j
    have h := column_locallyIntegrable (hHw j).2.1 j
    refine h.congr (ae_of_all _ fun y => ?_)
    simp [ContinuousLinearMap.flip_apply]
  have hdl : LocallyIntegrable (fun y => secondDerivTrace (H y)) volume := by
    have h := locallyIntegrable_finset_sum (Finset.univ : Finset (Fin 3)) fun j _ => hcol j
    refine h.congr (ae_of_all _ fun y => ?_)
    simp [secondDerivTrace]
  have hGl : ∀ j : Fin 3, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    column_locallyIntegrable hs.weak.2.1 j
  have hθc : Continuous θ := hθ.continuous
  have hDc : Continuous (fun y => fderiv ℝ θ y) := hθ.continuous_fderiv one_ne_zero
  have hrel : ∀ φ : Space → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ c : Fin 3,
      ∫ y, φ y * secondDerivTrace (H y) c = -∫ y, ∑ i, fderiv ℝ φ y (unitVector i) * G y (unitVector i) c := by
    intro φ hφ hφs c
    have hφc : Continuous φ := hφ.continuous
    have hDφc : ∀ i : Fin 3, Continuous (fun y => fderiv ℝ φ y (unitVector i)) := fun i =>
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hDφs : ∀ i : Fin 3, HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) := fun i =>
      hφs.fderiv_apply (𝕜 := ℝ) (unitVector i)
    have i1 : ∀ j : Fin 3, Integrable (fun y => φ y • H y (unitVector j) (unitVector j)) := fun j =>
      (hcol j).integrable_smul_left_of_hasCompactSupport hφc hφs
    have i2 : ∀ j : Fin 3, Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y (unitVector j)) := fun j =>
      (hGl j).integrable_smul_left_of_hasCompactSupport (hDφc j) (hDφs j)
    have i1' : ∀ j : Fin 3, Integrable (fun y => (φ y • H y (unitVector j) (unitVector j)) c) :=
      fun j => (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp (i1 j)
    have i2' : ∀ j : Fin 3, Integrable (fun y => (fderiv ℝ φ y (unitVector j) • G y (unitVector j)) c) :=
      fun j => (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp (i2 j)
    have hw : ∀ j : Fin 3, ∫ y, φ y • H y (unitVector j) (unitVector j) =
        -∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector j) := by
      intro j
      have h := FracInternal.ConvectionPairing.weak_of_C1 (hGl j) j
        (by
          have h' := column_locallyIntegrable (hHw j).2.1 j
          exact h')
        (weakOf_of (hHw j)) hφ hφs
      rw [h, neg_neg]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp [ContinuousLinearMap.flip_apply]
    calc ∫ y, φ y * secondDerivTrace (H y) c
        = ∑ j, ∫ y, (φ y • H y (unitVector j) (unitVector j)) c := by
          rw [← integral_finsetSum _ fun j _ => i1' j]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp [secondDerivTrace, Finset.mul_sum, smul_eq_mul]
      _ = ∑ j, (-∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector j)) c := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_apply_comm (i1 j), hw j]
      _ = -∑ j, ∫ y, (fderiv ℝ φ y (unitVector j) • G y (unitVector j)) c := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_apply_comm (i2 j)]
          simp
      _ = -∫ y, ∑ i, fderiv ℝ φ y (unitVector i) * G y (unitVector i) c := by
          rw [← integral_finsetSum _ fun j _ => i2' j]
          congr 1
  have hθ2 : Integrable (fun y => ‖θ y‖ ^ 2) :=
    sq_integrable_of_decay hθc.aestronglyMeasurable.norm (by norm_num : (3 : ℝ) < 2 * 2) (fun y => norm_nonneg _)
      (ae_of_all _ hb0)
  have hDθ2 : ∀ i : Fin 3, Integrable (fun y => ‖fderiv ℝ θ y (unitVector i)‖ ^ 2) := fun i =>
    sq_integrable_of_decay (hDc.clm_apply continuous_const).aestronglyMeasurable.norm
      (by norm_num : (3 : ℝ) < 2 * 2) (fun y => norm_nonneg _)
      (ae_of_all _ fun y => (column_norm_le _ i).trans (hb1 y))
  have hGm : ∀ i : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector i)) volume := fun i =>
    hs.mG.apply_continuousLinearMap _
  have hGi : Integrable (fun y => matSq (G y)) :=
    integrable_of_lintegral_lt (continuous_entrySq.comp_aestronglyMeasurable hs.mG) (fun y => entrySq_nonneg _) hs.grad
  have hG2 : ∀ j, Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) := fun j =>
    hGi.mono' ((hGm j).norm.pow 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have hdm : AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume := hdl.aestronglyMeasurable
  have h1 : Integrable (fun y => inner ℝ (θ y) (secondDerivTrace (H y))) := by
    refine ((hθ2.add hH2).div_const 2).mono' (hθc.aestronglyMeasurable.inner hdm) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖θ y‖ - ‖secondDerivTrace (H y)‖)]
  have hHθ : ∫⁻ y, ENNReal.ofReal (‖θ y‖ ^ 2 / ‖y‖ ^ 2) < ⊤ := by
    have h6 : ∫⁻ y, ENNReal.ofReal (‖θ y‖ ^ 6) < ⊤ := by
      refine Integrable.lintegral_lt_top (integrable_of_decay (B := B ^ 6) (a := 12)
        (hθc.aestronglyMeasurable.norm.pow 6) (by norm_num) (ae_of_all _ fun y => ?_))
      rw [abs_of_nonneg (by positivity)]
      have hp : 0 < 1 + ‖y‖ := by positivity
      have h1 : ‖θ y‖ ^ 6 ≤ (B * (1 + ‖y‖) ^ (-(2 : ℝ))) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) (hb0 y) 6
      refine h1.trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((1 + ‖y‖) ^ (-(2 : ℝ))), ← Real.rpow_mul hp.le]
      norm_num
    have hgr : ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ θ y)) < ⊤ := by
      refine Integrable.lintegral_lt_top ?_
      refine (integrable_finsetSum Finset.univ fun i _ => hDθ2 i).congr (ae_of_all _ fun y => ?_)
      simp [matSq]
    exact lt_of_le_of_lt (CertCell.Internal.slice_inverseSquare_lintegral θ (fun y => fderiv ℝ θ y)
      hθc.aestronglyMeasurable hDc.aestronglyMeasurable (weak_smooth hθ) h6) (ENNReal.mul_lt_top (by norm_num) hgr)
  have key := first_order_pairing (m := fun i y => G y (unitVector i)) hθ hGl hdl hrel h1
    (integrable_cols (fun i => (hDc.clm_apply continuous_const).aestronglyMeasurable) hGm hDθ2 hG2)
    (integrable_weighted_cols hθc.aestronglyMeasurable hGm hHθ hG2)
  refine ⟨h1.congr (ae_of_all _ fun y => real_inner_comm _ _), ?_⟩
  calc ∫ y, inner ℝ (secondDerivTrace (H y)) (θ y) = ∫ y, inner ℝ (θ y) (secondDerivTrace (H y)) :=
        integral_congr_ae (ae_of_all _ fun y => real_inner_comm _ _)
    _ = -∫ y, ∑ i, inner ℝ (fderiv ℝ θ y (unitVector i)) (G y (unitVector i)) := key
    _ = -∫ y, matInner (G y) (fderiv ℝ θ y) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [matInner]
        exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem div_pow_eq_rpow (C x : ℝ) (hx : 0 ≤ x) (k : ℕ) : C / (1 + x) ^ k = C * (1 + x) ^ (-(k : ℝ)) := by
  have hp : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, div_eq_mul_inv]

theorem div_rpow_eq (C x γ : ℝ) (hx : 0 ≤ x) : C / (1 + x) ^ γ = C * (1 + x) ^ (-γ) := by
  have hp : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hp.le, div_eq_mul_inv]

theorem decay_mono {x C e e' : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : e' ≤ e) :
    C * (1 + x) ^ (-e) ≤ C * (1 + x) ^ (-e') :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC

theorem mul_decay_le {x C e : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) :
    x * (C * (1 + x) ^ (-e)) ≤ C * (1 + x) ^ (-(e - 1)) := by
  have hp : 0 < 1 + x := by linarith
  have e1 : (1 + x) ^ (-(e - 1)) = (1 + x) * (1 + x) ^ (-e) := by
    rw [show -(e - 1) = 1 + -e by ring, Real.rpow_add hp, Real.rpow_one]
  rw [e1]
  have : 0 ≤ C * (1 + x) ^ (-e) := mul_nonneg hC (by positivity)
  nlinarith

theorem pressure_weight_le {x t C : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (h1 : x * t ≤ C) (h3 : x ^ 3 * t ≤ C) :
    x * t ≤ 4 * C * (1 + x) ^ (-(2 : ℝ)) := by
  have hp : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hp.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  rcases le_total x 1 with hx1 | hx1
  · have hC : 0 ≤ C := (mul_nonneg hx ht).trans h1
    have : (1 + x) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_nonneg hx ht]
  · have hxt : 0 ≤ x * t := mul_nonneg hx ht
    have e : (1 + x) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    have : x * t * (1 + x) ^ 2 ≤ x * t * (4 * x ^ 2) := mul_le_mul_of_nonneg_left e hxt
    nlinarith

theorem inverse_square_slice {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hs : SliceField v G) :
    ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2) < ⊤ :=
  lt_of_le_of_lt (CertCell.Internal.slice_inverseSquare_lintegral v G hs.mv hs.mG hs.weak hs.six)
    (ENNReal.mul_lt_top (by norm_num) hs.grad)

theorem slice_contDiff {f : ℝ → Space → Space} (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) :
    ContDiff ℝ 1 (f σ) :=
  hf.comp ((contDiff_const (c := σ)).prodMk contDiff_id)

theorem slice_identity (w₀ : ℝ) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : SliceField v G)
    (hdiv : ∀ᵐ y, ∑ i : Fin 3, (G y (unitVector i)) i = 0)
    (hHw : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (hH2 : Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2))
    {T : ℝ → Space → Space} {K : ℝ → Space → (Space →L[ℝ] Space)} {C γ : ℝ} (hR : IsResidualField T K C γ)
    {p : PotentialData} (hp : IsPotentialData p C) (σ : ℝ) (hTm : AEStronglyMeasurable (T σ) volume) :
    Integrable (fun y => inner ℝ (v y) (T σ y)) ∧
      Integrable (fun y => inner ℝ (secondDerivTrace (H y)) (p.theta σ y)) ∧
      (∫ y, inner ℝ (v y) (T σ y)) + (∫ y, matInner (G y) (K σ y)) =
        (∫ y, inner ℝ (v y) (remainderField w₀ T K p σ y)) - (∫ y, inner ℝ (secondDerivTrace (H y)) (p.theta σ y))
          + w₀ * (∫ y, matInner (G y) (fderiv ℝ (p.phi σ) y)) - ∫ y, matInner (G y) (p.flux σ y) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hp.value_decay σ 0).1
    simpa using h
  have hγ := hR.rate_gt
  have E1 := pair_flux hs (hR.flux_weak σ) (B := C) (a := γ - 1) (by linarith)
    (fun y => by
      have h := (hR.decay σ y).2
      rw [div_rpow_eq _ _ _ (norm_nonneg y)] at h
      exact h.trans (decay_mono (norm_nonneg y) hC (by linarith)))
    ((hR.flux_div_decay σ).mono fun y hy => by
      rw [div_rpow_eq _ _ _ (norm_nonneg y)] at hy
      exact (mul_le_mul_of_nonneg_left hy (norm_nonneg y)).trans (mul_decay_le (norm_nonneg y) hC))
  have E2 := pair_flux hs (hp.flux_weak σ) (B := C) (a := 2) (by norm_num)
    (fun y => by
      have h := (hp.value_decay σ y).2.2.2.2.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      exact_mod_cast h)
    ((hp.second_decay σ).mono fun y hy => by
      have h := hy.2.2.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      exact_mod_cast h)
  have E3 := pair_pressure hs hdiv (hp.pressure_weak σ) (B := 4 * C)
    (fun y => by
      have h := (hp.value_decay σ y).2.2.2.2.2
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      push_cast at h
      refine h.trans ?_
      have : 0 ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := mul_nonneg hC (by positivity)
      nlinarith)
    ((hp.second_decay σ).mono fun y hy =>
      pressure_weight_le (norm_nonneg y) (norm_nonneg _) hy.2.2.2.1 hy.2.2.2.2)
  have hθ1 := slice_contDiff hp.theta_smooth σ
  have hφ1 := slice_contDiff hp.phi_smooth σ
  have E4 := pair_potential hs hθ1 (hp.theta_weak σ) (B := C) (a := 3) (by norm_num)
    (fun y => by
      have h := (hp.value_decay σ y).2.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      exact_mod_cast h)
    ((hp.second_decay σ).mono fun y hy => by
      have h := hy.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      have h' := (mul_le_mul_of_nonneg_left h (norm_nonneg y)).trans (mul_decay_le (norm_nonneg y) hC)
      rwa [show (-(((4 : ℕ) : ℝ) - 1)) = -(3 : ℝ) by norm_num] at h')
  have E6 := pair_potential hs hφ1 (hp.phi_weak σ) (B := C) (a := 2) (by norm_num)
    (fun y => by
      have h := (hp.value_decay σ y).2.2.2.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      exact_mod_cast h)
    ((hp.second_decay σ).mono fun y hy => by
      have h := hy.2.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      have h' := (mul_le_mul_of_nonneg_left h (norm_nonneg y)).trans (mul_decay_le (norm_nonneg y) hC)
      rwa [show (-(((3 : ℕ) : ℝ) - 1)) = -(2 : ℝ) by norm_num] at h')
  have E5 := pair_second hs hHw hH2 hθ1 (B := C)
    (fun y => by
      have h := (hp.value_decay σ y).1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      exact_mod_cast h)
    (fun y => by
      have h := (hp.value_decay σ y).2.1
      rw [div_pow_eq_rpow _ _ (norm_nonneg y)] at h
      refine h.trans (decay_mono (norm_nonneg y) hC (by norm_num)))
  have IT : Integrable (fun y => inner ℝ (v y) (T σ y)) :=
    integrable_inner_weighted hs.mv hTm (inverse_square_slice hs)
      (weighted_integrable_of_decay hTm (B := C) (a := γ - 1) (by linarith) (ae_of_all _ fun y => by
        have h := (hR.decay σ y).1
        rw [div_rpow_eq _ _ _ (norm_nonneg y)] at h
        exact (mul_le_mul_of_nonneg_left h (norm_nonneg y)).trans (mul_decay_le (norm_nonneg y) hC)))
  refine ⟨IT, E5.1, ?_⟩
  have hpt : ∀ y, inner ℝ (v y) (remainderField w₀ T K p σ y) =
      inner ℝ (v y) (T σ y) - inner ℝ (v y) (matrixDivergence (K σ) y)
        + inner ℝ (v y) (gradientAt (p.pressure σ) y) + inner ℝ (v y) (secondDerivTrace (secondDeriv (p.theta σ) y))
        + w₀ * inner ℝ (v y) (secondDerivTrace (secondDeriv (p.phi σ) y))
        - inner ℝ (v y) (matrixDivergence (p.flux σ) y) := by
    intro y
    simp only [remainderField, inner_add_right, inner_sub_right, real_inner_smul_right]
  have hRint : ∫ y, inner ℝ (v y) (remainderField w₀ T K p σ y) =
      (∫ y, inner ℝ (v y) (T σ y)) - (∫ y, inner ℝ (v y) (matrixDivergence (K σ) y))
        + (∫ y, inner ℝ (v y) (gradientAt (p.pressure σ) y))
        + (∫ y, inner ℝ (v y) (secondDerivTrace (secondDeriv (p.theta σ) y)))
        + w₀ * (∫ y, inner ℝ (v y) (secondDerivTrace (secondDeriv (p.phi σ) y)))
        - ∫ y, inner ℝ (v y) (matrixDivergence (p.flux σ) y) := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub, integral_add, integral_add, integral_add, integral_sub,
      integral_const_mul]
    all_goals first
      | exact IT | exact E1.1 | exact E2.1 | exact E3.1 | exact E4.1 | exact E6.1.const_mul _
      | exact IT.sub E1.1 | exact (IT.sub E1.1).add E3.1 | exact ((IT.sub E1.1).add E3.1).add E4.1
      | exact (((IT.sub E1.1).add E3.1).add E4.1).add (E6.1.const_mul _)
  rw [hRint, E1.2, E2.2, E3.2, E4.2, E6.2, E5.2]
  ring

end PotentialBound

end Internal

end AdjointDefect

end Breakdown

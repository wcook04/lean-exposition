import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothIsPerturbation

def joint (u : ℝ → Space → Space) : ℝ × Space → Space := fun z => u z.1 z.2

theorem top_add_one_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact le_of_eq rfl

theorem slice_contDiff {u : ℝ → Space → Space} {n : WithTop ℕ∞} (hu : ContDiff ℝ n (joint u))
    (s : ℝ) : ContDiff ℝ n (u s) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

theorem line_contDiff {u : ℝ → Space → Space} {n : WithTop ℕ∞} (hu : ContDiff ℝ n (joint u))
    (y : Space) : ContDiff ℝ n (fun s => u s y) :=
  hu.comp (contDiff_id.prodMk contDiff_const)

theorem fderiv_slice {u : ℝ → Space → Space} (hu : ContDiff ℝ 1 (joint u)) (s : ℝ) (y w : Space) :
    fderiv ℝ (u s) y w = fderiv ℝ (joint u) (s, y) (0, w) := by
  have h1 : HasFDerivAt (joint u) (fderiv ℝ (joint u) (s, y)) (s, y) :=
    ((hu.differentiable one_ne_zero) _).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Space => ((s, x) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have h3 := h1.comp y h2
  have h4 : u s = joint u ∘ (fun x : Space => ((s, x) : ℝ × Space)) := rfl
  rw [h4, h3.fderiv]
  rfl

theorem deriv_line {u : ℝ → Space → Space} (hu : ContDiff ℝ 1 (joint u)) (s : ℝ) (y : Space) :
    deriv (fun t => u t y) s = fderiv ℝ (joint u) (s, y) (1, 0) := by
  have h1 : HasFDerivAt (joint u) (fderiv ℝ (joint u) (s, y)) (s, y) :=
    ((hu.differentiable one_ne_zero) _).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact (h1.comp_hasDerivAt s h2).deriv

theorem grad_contDiff {u : ℝ → Space → Space} (hu : ContDiff ℝ ∞ (joint u)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (u z.1) z.2) := by
  have h : ContDiff ℝ ∞ (Function.uncurry (fun (z : ℝ × Space) (y : Space) => u z.1 y)) :=
    hu.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h.fderiv contDiff_snd top_add_one_le

theorem secondDeriv_contDiff {u : ℝ → Space → Space} (hu : ContDiff ℝ ∞ (joint u)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (u z.1) x) z.2) := by
  have h : ContDiff ℝ ∞ (Function.uncurry
      (fun (z : ℝ × Space) (y : Space) => fderiv ℝ (u z.1) y)) :=
    (grad_contDiff hu).comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h.fderiv contDiff_snd top_add_one_le

theorem time_contDiff {u : ℝ → Space → Space} (hu : ContDiff ℝ ∞ (joint u)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => deriv (fun s => u s z.2) z.1) := by
  have h : ContDiff ℝ ∞ (Function.uncurry (fun (z : ℝ × Space) (s : ℝ) => u s z.2)) :=
    hu.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  have h2 := h.fderiv contDiff_fst top_add_one_le
  exact h2.clm_apply contDiff_const

theorem matSq_le (A : Space →L[ℝ] Space) : matSq A ≤ 3 * ‖A‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    intro i
    have h1 : ‖A (unitVector i)‖ ≤ ‖A‖ := by
      have := A.le_opNorm (unitVector i)
      have h2 : ‖unitVector i‖ = 1 := by simp [unitVector]
      rwa [h2, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖A‖ ^ 2 := by simp

theorem trace_sq_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace H‖ ^ 2 ≤ 9 * ‖H‖ ^ 2 := by
  have h2 : ∀ j : Fin 3, ‖unitVector j‖ = 1 := fun j => by simp [unitVector]
  have h : ∀ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ‖H‖ := by
    intro j
    calc ‖H (unitVector j) (unitVector j)‖ ≤ ‖H (unitVector j)‖ * ‖unitVector j‖ :=
          (H (unitVector j)).le_opNorm _
      _ ≤ ‖H‖ * ‖unitVector j‖ * ‖unitVector j‖ := by
          gcongr
          exact H.le_opNorm _
      _ = ‖H‖ := by rw [h2, mul_one, mul_one]
  have ht : ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
    unfold secondDerivTrace
    calc ‖∑ j : Fin 3, H (unitVector j) (unitVector j)‖
        ≤ ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖H‖ := Finset.sum_le_sum fun j _ => h j
      _ = 3 * ‖H‖ := by simp
  calc ‖secondDerivTrace H‖ ^ 2 ≤ (3 * ‖H‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ = 9 * ‖H‖ ^ 2 := by ring

theorem periodLIntegral_le_mul {f g : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ σ y, f σ y ≤ c * g σ y) :
    periodLIntegral f ≤ ENNReal.ofReal c * periodLIntegral g := by
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (h σ y)

theorem periodLIntegral_lt_top {f g : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ σ y, f σ y ≤ c * g σ y) (hg : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ :=
  lt_of_le_of_lt (periodLIntegral_le_mul hc h) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg)

theorem isWeakGradient_of_contDiff {f : Space → Space} (hf : ContDiff ℝ ∞ f) :
    IsWeakGradient f (fderiv ℝ f) := by
  refine ⟨hf.continuous.locallyIntegrable, (hf.continuous_fderiv (by simp)).locallyIntegrable, ?_⟩
  intro φ hφ i
  have hφc : Continuous φ := hφ.1.continuous
  have hφd : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have i1 : Integrable (fun x => ContinuousLinearMap.lsmul ℝ ℝ (fderiv ℝ φ x (unitVector i)) (f x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hφd.clm_apply continuous_const).smul hf.continuous)
    · exact (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right
  have i2 : Integrable (fun x => ContinuousLinearMap.lsmul ℝ ℝ (φ x) (fderiv ℝ f x (unitVector i))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφc.smul (hfd.clm_apply continuous_const)
    · exact hφ.2.smul_right
  have i3 : Integrable (fun x => ContinuousLinearMap.lsmul ℝ ℝ (φ x) (f x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφc.smul hf.continuous
    · exact hφ.2.smul_right
  have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (v := unitVector i) i1 i2 i3
    (fun x _ => (hφ.1.differentiable (by simp)) x) (fun x _ => (hf.differentiable (by simp)) x)
  simpa using this


theorem inner_integrable {f g : ℝ × Space → Space} (hf : Continuous f) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun z => inner ℝ (f z) (g z)) := by
  refine Continuous.integrable_of_hasCompactSupport (hf.inner hg) ?_
  refine hgc.mono ?_
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro h0
  apply hz
  rw [h0, inner_zero_right]

theorem ibp_zero {f : ℝ × Space → Space} {f' : ℝ × Space → (ℝ × Space →L[ℝ] Space)}
    {Φ : ℝ × Space → Space} {w : ℝ × Space}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hfc : Continuous f) (hf'c : Continuous (fun z => f' z w))
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (fun z => inner ℝ (f z) (fderiv ℝ Φ z w) + inner ℝ (f' z w) (Φ z)) ∧
      ∫ z, (inner ℝ (f z) (fderiv ℝ Φ z w) + inner ℝ (f' z w) (Φ z)) = 0 := by
  have hΦd : Continuous (fun z => fderiv ℝ Φ z w) :=
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : Integrable (fun z => inner ℝ (f' z w) (Φ z)) := inner_integrable hf'c hΦ.continuous hΦc
  have i2 : Integrable (fun z => inner ℝ (f z) (fderiv ℝ Φ z w)) :=
    inner_integrable hfc hΦd (hΦc.fderiv_apply (𝕜 := ℝ) w)
  have i3 : Integrable (fun z => inner ℝ (f z) (Φ z)) := inner_integrable hfc hΦ.continuous hΦc
  have : (volume : Measure (ℝ × Space)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h : ∫ z, inner ℝ (f z) (fderiv ℝ Φ z w) = -∫ z, inner ℝ (f' z w) (Φ z) :=
    integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
      (B := innerSL ℝ) (v := w) (f := f) (f' := f') (g := Φ) (g' := fderiv ℝ Φ) i1 i2 i3
      (fun z _ => hf z) (fun z _ => ((hΦ.differentiable one_ne_zero) z).hasFDerivAt)
  refine ⟨i2.add i1, ?_⟩
  rw [integral_add i2 i1, h]
  ring

theorem zero_prod_eq_sum (y : Space) :
    (((0 : ℝ), y) : ℝ × Space) = ∑ k : Fin 3, y k • (((0 : ℝ), unitVector k) : ℝ × Space) := by
  rw [Fin.sum_univ_three]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_add, Prod.smul_snd]
    ext j
    fin_cases j <;> simp [unitVector]

theorem fderiv_slice_self {u : ℝ → Space → Space} (hu : ContDiff ℝ 1 (joint u)) (z : ℝ × Space) :
    fderiv ℝ (u z.1) z.2 z.2 = ∑ k : Fin 3, z.2 k • fderiv ℝ (joint u) z ((0 : ℝ), unitVector k) := by
  rw [fderiv_slice hu z.1 z.2 z.2, zero_prod_eq_sum, map_sum]
  simp only [map_smul, Prod.mk.eta]

def coord (k : Fin 3) : ℝ × Space →L[ℝ] ℝ :=
  (EuclideanSpace.proj k).comp (ContinuousLinearMap.snd ℝ ℝ Space)

theorem coord_apply (k : Fin 3) (z : ℝ × Space) : coord k z = z.2 k := by
  simp [coord]

theorem transport_identity {P : ℝ} {v φ : ℝ → Space → Space}
    (hv : ContDiff ℝ ∞ (joint v)) (hφ : ContDiff ℝ ∞ (joint φ))
    (hφc : HasCompactSupport (joint φ)) :
    ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (-(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2
      - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2) =
      ∫ z : ℝ × Space, inner ℝ (transportPart P v z.1 z.2) (φ z.1 z.2) := by
  have hv1 : ContDiff ℝ 1 (joint v) := hv.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 (joint φ) := hφ.of_le (by simp)
  have hVc : Continuous (joint v) := hv.continuous
  have hDV : Continuous (fderiv ℝ (joint v)) := hv.continuous_fderiv (by simp)
  have hVd : ∀ z, HasFDerivAt (joint v) (fderiv ℝ (joint v) z) z :=
    fun z => ((hv1.differentiable one_ne_zero) z).hasFDerivAt
  have hR : Integrable (fun z : ℝ × Space => inner ℝ (transportPart P v z.1 z.2) (φ z.1 z.2)) := by
    refine inner_integrable ?_ hφ.continuous hφc
    have h1 := (time_contDiff hv).continuous
    have h2 := ((grad_contDiff hv).continuous).clm_apply continuous_snd
    unfold transportPart
    exact ((h1.const_smul (1 / P)).add (hv.continuous.const_smul (1 / 2 : ℝ))).add
      (h2.const_smul (1 / 2 : ℝ))
  have X0 := ibp_zero (w := ((1 : ℝ), (0 : Space))) hVd hVc (hDV.clm_apply continuous_const) hφ1 hφc
  have Xk : ∀ k : Fin 3, _ := fun k => ibp_zero (w := ((0 : ℝ), unitVector k))
    (f := fun z => coord k z • joint v z)
    (f' := fun z => coord k z • fderiv ℝ (joint v) z + (coord k).smulRight (joint v z))
    (fun z => (coord k).hasFDerivAt.smul (hVd z)) ((coord k).continuous.smul hVc)
    (by
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      exact ((coord k).continuous.smul (hDV.clm_apply continuous_const)).add
        (hVc.const_smul (coord k ((0 : ℝ), unitVector k))))
    hφ1 hφc
  have hI : Integrable (fun z : ℝ × Space =>
      -(1 / P) * (inner ℝ (joint v z) (fderiv ℝ (joint φ) z ((1 : ℝ), (0 : Space)))
        + inner ℝ (fderiv ℝ (joint v) z ((1 : ℝ), (0 : Space))) (joint φ z))
      - (1 / 2 : ℝ) * ∑ k : Fin 3,
        (inner ℝ (coord k z • joint v z) (fderiv ℝ (joint φ) z ((0 : ℝ), unitVector k))
          + inner ℝ ((coord k z • fderiv ℝ (joint v) z + (coord k).smulRight (joint v z))
            ((0 : ℝ), unitVector k)) (joint φ z))) :=
    (X0.1.const_mul _).sub ((integrable_finsetSum _ fun k _ => (Xk k).1).const_mul _)
  have hI0 : ∫ z : ℝ × Space,
      (-(1 / P) * (inner ℝ (joint v z) (fderiv ℝ (joint φ) z ((1 : ℝ), (0 : Space)))
        + inner ℝ (fderiv ℝ (joint v) z ((1 : ℝ), (0 : Space))) (joint φ z))
      - (1 / 2 : ℝ) * ∑ k : Fin 3,
        (inner ℝ (coord k z • joint v z) (fderiv ℝ (joint φ) z ((0 : ℝ), unitVector k))
          + inner ℝ ((coord k z • fderiv ℝ (joint v) z + (coord k).smulRight (joint v z))
            ((0 : ℝ), unitVector k)) (joint φ z))) = 0 := by
    rw [integral_sub (X0.1.const_mul _) ((integrable_finsetSum _ fun k _ => (Xk k).1).const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ fun k _ => (Xk k).1, X0.2,
      Finset.sum_eq_zero fun k _ => (Xk k).2]
    simp
  have hpt : ∀ z : ℝ × Space,
      inner ℝ (v z.1 z.2) (-(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2
        - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2) =
      inner ℝ (transportPart P v z.1 z.2) (φ z.1 z.2) +
      (-(1 / P) * (inner ℝ (joint v z) (fderiv ℝ (joint φ) z ((1 : ℝ), (0 : Space)))
        + inner ℝ (fderiv ℝ (joint v) z ((1 : ℝ), (0 : Space))) (joint φ z))
      - (1 / 2 : ℝ) * ∑ k : Fin 3,
        (inner ℝ (coord k z • joint v z) (fderiv ℝ (joint φ) z ((0 : ℝ), unitVector k))
          + inner ℝ ((coord k z • fderiv ℝ (joint v) z + (coord k).smulRight (joint v z))
            ((0 : ℝ), unitVector k)) (joint φ z))) := by
    intro z
    have e1 := deriv_line hφ1 z.1 z.2
    have e2 := fderiv_slice_self hφ1 z
    have e3 := deriv_line hv1 z.1 z.2
    have e4 := fderiv_slice_self hv1 z
    simp only [Prod.mk.eta] at e1 e3
    unfold transportPart
    rw [e1, e2, e3, e4]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, coord_apply, Fin.sum_univ_three]
    change inner ℝ (joint v z) _ = inner ℝ _ (joint φ z) + _
    simp only [inner_add_left, inner_add_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    have u0 : ∀ k : Fin 3, (unitVector k) k = 1 := fun k => by simp [unitVector]
    simp only [joint, u0]
    ring
  rw [show (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (-(1 / P) • deriv (fun s => φ s z.2) z.1
      - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2)) = _ from funext hpt,
    integral_add hR hI, hI0, add_zero]

theorem transport_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : ContDiff ℝ ∞ (joint v)) :
    Continuous (fun z : ℝ × Space => transportPart P v z.1 z.2) := by
  have h1 := (time_contDiff hv).continuous
  have h2 := ((grad_contDiff hv).continuous).clm_apply continuous_snd
  unfold transportPart
  exact ((h1.const_smul (1 / P)).add (hv.continuous.const_smul (1 / 2 : ℝ))).add
    (h2.const_smul (1 / 2 : ℝ))

theorem deriv_periodic {v : ℝ → Space → Space} (hv : IsTimePeriodic v) (σ : ℝ) (y : Space) :
    deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
  rw [← deriv_comp_add_const]
  congr 1
  funext s
  exact hv s y

theorem norm_secondDeriv_eq (f : Space → Space) (y : Space) :
    ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fun x => fderiv ℝ f x) y‖ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]

theorem secondDeriv_weak {v : ℝ → Space → Space} (hs : ∀ σ, ContDiff ℝ ∞ (v σ)) (σ : ℝ) (j : Fin 3) :
    IsWeakGradient (fun y => gradField v σ y (unitVector j))
      (fun y => (secondDerivField v σ y).flip (unitVector j)) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := (hs σ).fderiv_right top_add_one_le
  have hgj : ContDiff ℝ ∞ (fun y => fderiv ℝ (v σ) y (unitVector j)) := hd.clm_apply contDiff_const
  have h := isWeakGradient_of_contDiff hgj
  have heq : fderiv ℝ (fun y => fderiv ℝ (v σ) y (unitVector j)) =
      fun y => (secondDerivField v σ y).flip (unitVector j) := by
    funext y
    rw [fderiv_clm_apply ((hd.differentiable (by simp)) y) (differentiableAt_const _)]
    simp [secondDerivField]
  rw [heq] at h
  exact h

end Internal.SmoothIsPerturbation

open Internal.SmoothIsPerturbation in
theorem smoothPerturbationIsPerturbationHolds_proof : SmoothPerturbationIsPerturbationHolds := by
  intro P v hv
  have hs : ContDiff ℝ ∞ (joint v) := hv.smooth
  have hslice : ∀ σ, ContDiff ℝ ∞ (v σ) := fun σ => slice_contDiff hs σ
  have hper : ∀ σ, v (σ + 1) = v σ := fun σ => funext fun y => hv.periodic σ y
  have hgrad : periodLIntegral (fun σ y => matSq (gradField v σ y)) < ⊤ := by
    refine periodLIntegral_lt_top (c := 3) (by norm_num) (fun σ y => ?_) (hv.derivatives_finite 1 le_rfl)
    rw [norm_iteratedFDeriv_one]
    exact matSq_le _
  have hssp : periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) < ⊤ := by
    refine periodLIntegral_lt_top (c := 9) (by norm_num) (fun σ y => ?_)
      (hv.derivatives_finite 2 (by norm_num))
    rw [norm_secondDeriv_eq]
    exact trace_sq_le _
  have hder : periodLIntegral (fun σ y => ‖transportPart P v σ y‖ ^ 2) < ⊤ := by
    refine periodLIntegral_lt_top (c := 1) (by norm_num) (fun σ y => ?_) (hv.transport_finite 0)
    rw [norm_iteratedFDeriv_zero, one_mul]
  exact
    { measurable_velocity := hs.continuous.aestronglyMeasurable
      measurable_gradient := (grad_contDiff hs).continuous.aestronglyMeasurable
      measurable_secondDeriv := (secondDeriv_contDiff hs).continuous.aestronglyMeasurable
      measurable_derivative := (transport_continuous hs).aestronglyMeasurable
      periodic_velocity := hv.periodic
      periodic_gradient := fun σ y => by simp only [gradField, hper σ]
      periodic_secondDeriv := fun σ y => by simp only [secondDerivField, hper σ]
      periodic_derivative := fun σ y => by
        unfold transportPart
        rw [deriv_periodic hv.periodic σ y, hper σ]
      weak_gradient := ae_of_all _ fun σ => isWeakGradient_of_contDiff (hslice σ)
      weak_secondDeriv := ae_of_all _ fun σ j => secondDeriv_weak hslice σ j
      divergence_free := ae_of_all _ fun σ => ae_of_all _ fun y => hv.divergence_free σ y
      sixth_power := ae_of_all _ hv.sixth_power
      gradient_finite := hgrad
      sumSecondPartials_finite := hssp
      derivative_finite := hder
      transport := fun φ hφ => transport_identity hs hφ.1 hφ.2
      invariant := fun γ hγ => by simp at hγ }

end Coercive

end Breakdown

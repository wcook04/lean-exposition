import Breakdown.Torus.StatementsSmooth

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace MovingFrame.Internal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slice_contDiff {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.1 ((hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => mk_mem_prod ht (mem_univ _))) : ContDiffOn ℝ ∞ (fun x : Space => f t x) univ)

theorem time_contDiffOn {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) (y : Space) :
    ContDiffOn ℝ ∞ (fun τ => f τ y) (Ici 0) :=
  hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hτ => mk_mem_prod hτ (mem_univ _)

theorem joint_hasFDerivAt {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 < t)
    (y : Space) :
    HasFDerivAt (fun z : ℝ × Space => f z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y)) (t, y) :=
  ((hf.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) univ_mem)).differentiableAt
    (by simp)).hasFDerivAt

theorem time_hasDerivAt {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 < t)
    (y : Space) :
    HasDerivAt (fun τ => f τ y) (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y) (1, 0)) t :=
  (joint_hasFDerivAt hf ht y).comp_hasDerivAt_of_eq t
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t y)) rfl

theorem space_fderiv {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 < t)
    (y : Space) :
    fderiv ℝ (f t) y = (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) :=
  ((joint_hasFDerivAt hf ht y).comp y (hasFDerivAt_prodMk_right t y)).fderiv

theorem along_hasDerivAt {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 < t)
    (x : Space) {h : ℝ → Space} {v : Space} (hh : HasDerivAt h v t) :
    HasDerivAt (fun τ => f τ (x + h τ))
      (deriv (fun τ => f τ (x + h t)) t + fderiv ℝ (f t) (x + h t) v) t := by
  rw [(time_hasDerivAt hf ht _).deriv, space_fderiv hf ht, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  exact (joint_hasFDerivAt hf ht (x + h t)).comp_hasDerivAt_of_eq t
    ((hasDerivAt_id' t).prodMk (hh.const_add x)) rfl

theorem fderiv_shift (f : Space → E) (a : Space) (b : E) (x : Space) :
    fderiv ℝ (fun z => f (z + a) + b) x = fderiv ℝ f (x + a) := by
  rw [fderiv_add_const, fderiv_comp_add_right]

theorem iteratedFDeriv_shift {f : Space → E} (hf : ContDiff ℝ ∞ f) (a : Space) (b : E)
    (x : Space) :
    iteratedFDeriv ℝ 2 (fun z => f (z + a) + b) x = iteratedFDeriv ℝ 2 f (x + a) := by
  have h1 : ContDiff ℝ 2 (fun z => f (z + a)) :=
    (contDiff_infty.1 hf 2).comp (contDiff_id.add contDiff_const)
  have h2 : (fun z => f (z + a) + b) = (fun z => f (z + a)) + fun _ => b := rfl
  rw [h2, iteratedFDeriv_add_apply h1.contDiffAt contDiffAt_const, iteratedFDeriv_comp_add_right,
    iteratedFDeriv_const_of_ne (n := 2) (by norm_num), Pi.zero_apply, add_zero]

theorem eq_of_apply_unitVector {A B : Space →L[ℝ] ℝ} (h : ∀ i, A (unitVector i) = B (unitVector i)) :
    A = B := by
  have : (A : Space →ₗ[ℝ] ℝ) = (B : Space →ₗ[ℝ] ℝ) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => by simpa [unitVector] using h i
  exact ContinuousLinearMap.coe_injective this

theorem gradientAt_apply (q : Space → ℝ) (x : Space) (j : Fin 3) :
    gradientAt q x j = fderiv ℝ q x (unitVector j) := by
  simp [gradientAt, unitVector, Pi.single_apply]

theorem pressure_shift_pos {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hs : IsSmoothSolution 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t)) {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (x : Space) :
    p t (x + unitVector i) - p t x = p t (unitVector i) - p t 0 := by
  have hper : (fun z => u t (z + unitVector i)) = u t := funext (hu t ht.le i)
  have hgrad : ∀ w, gradientAt (p t) w = (1 : ℝ) • sumSecondPartialsAt (u t) w -
      (deriv (fun τ => u τ w) t + advectionAt (u t) w) := fun w => by
    rw [hs.momentum t ht w]; abel
  have hdt : ∀ w, deriv (fun τ => u τ (w + unitVector i)) t = deriv (fun τ => u τ w) t :=
    fun w => Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht) fun τ hτ => hu τ (le_of_lt hτ) i w)
  have hfd : ∀ w, fderiv ℝ (u t) (w + unitVector i) = fderiv ℝ (u t) w := fun w => by
    conv_rhs => rw [← hper]
    rw [fderiv_comp_add_right]
  have hssp : ∀ w, sumSecondPartialsAt (u t) (w + unitVector i) = sumSecondPartialsAt (u t) w := fun w => by
    conv_rhs => rw [← hper]
    simp only [sumSecondPartialsAt, iteratedFDeriv_comp_add_right]
  have hg : ∀ w, gradientAt (p t) (w + unitVector i) = gradientAt (p t) w := fun w => by
    rw [hgrad, hgrad (w := w), hssp, hdt]
    simp only [advectionAt, hfd, hu t ht.le i w]
  have hd : Differentiable ℝ (p t) := (slice_contDiff hs.smooth_pressure ht.le).differentiable (by simp)
  have hsh : Differentiable ℝ (fun z => p t (z + unitVector i)) :=
    hd.comp (differentiable_id.add_const _)
  have hφd : Differentiable ℝ (fun z => p t (z + unitVector i) - p t z) := hsh.sub hd
  have hφ : ∀ w, fderiv ℝ (fun z => p t (z + unitVector i) - p t z) w = 0 := fun w => by
    rw [fderiv_fun_sub (hsh w) (hd w), fderiv_comp_add_right, sub_eq_zero]
    exact eq_of_apply_unitVector fun j => by rw [← gradientAt_apply, ← gradientAt_apply, hg]
  have := is_const_of_fderiv_eq_zero hφd hφ x 0
  simp only [zero_add] at this
  exact this

theorem eq_zero_of_pos {ψ : ℝ → ℝ} (hc : ContinuousOn ψ (Ici 0)) (h : ∀ τ > 0, ψ τ = 0) :
    ψ 0 = 0 := by
  have hψ : ContinuousWithinAt ψ (Ioi 0) 0 := (hc 0 (le_refl (0 : ℝ))).mono Ioi_subset_Ici_self
  refine tendsto_nhds_unique hψ.tendsto (tendsto_const_nhds.congr' ?_)
  exact eventually_nhdsWithin_of_forall fun τ hτ => (h τ hτ).symm

theorem pressure_shift {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hs : IsSmoothSolution 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t)) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) (x : Space) :
    p t (x + unitVector i) = p t x + (p t (unitVector i) - p t 0) := by
  rcases ht.lt_or_eq with ht | rfl
  · linarith [pressure_shift_pos hs hu ht i x]
  · have hc := time_contDiffOn hs.smooth_pressure
    have := eq_zero_of_pos
      (ψ := fun τ => p τ (x + unitVector i) - p τ x - (p τ (unitVector i) - p τ 0))
      (((hc _).continuousOn.sub (hc _).continuousOn).sub
        ((hc _).continuousOn.sub (hc _).continuousOn))
      (fun τ hτ => by linarith [pressure_shift_pos hs hu hτ i x])
    linarith

theorem antideriv {a : ℝ → Space} (ha : ContDiffOn ℝ ∞ a (Ici 0)) :
    ∃ b : ℝ → Space, b 0 = 0 ∧ (∀ t, 0 < t → HasDerivAt b (a t) t) ∧
      ContDiffOn ℝ ∞ b (Ici 0) := by
  have hcont : Continuous (fun s => a (max s 0)) :=
    ha.continuousOn.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hd : ∀ t, HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, a (max s 0)) (a (max t 0)) t :=
    fun t => (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  refine ⟨fun t => ∫ s in (0 : ℝ)..t, a (max s 0), by simp,
    fun t ht => by simpa [max_eq_left ht.le] using hd t, ?_⟩
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t _ => (hd t).differentiableAt.differentiableWithinAt, ha.congr fun t ht => ?_⟩
  rw [(hd t).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht), max_eq_left ht]

def linearPart (p : ℝ → Space → ℝ) (t : ℝ) : Space :=
  ∑ j, (p t (unitVector j) - p t 0) • unitVector j

theorem inner_linearPart (p : ℝ → Space → ℝ) (t : ℝ) (i : Fin 3) :
    inner ℝ (linearPart p t) (unitVector i) = p t (unitVector i) - p t 0 := by
  simp [linearPart, unitVector, sum_inner, inner_smul_left, EuclideanSpace.inner_single_left]

theorem sum_inner_linearPart (p : ℝ → Space → ℝ) (t : ℝ) :
    ∑ i, inner ℝ (linearPart p t) (unitVector i) • unitVector i = linearPart p t := by
  simp only [inner_linearPart]
  rfl

theorem gradient_shift {q : Space → ℝ} (hq : Differentiable ℝ q) (a w x : Space) :
    gradientAt (fun z => q (z + a) - inner ℝ w (z + a)) x =
      gradientAt q (x + a) - ∑ i, inner ℝ w (unitVector i) • unitVector i := by
  have hd : HasFDerivAt (fun z => q (z + a) - inner ℝ w (z + a))
      (fderiv ℝ q (x + a) - innerSL ℝ w) x :=
    ((hasFDerivAt_comp_add_right a).2 (hq (x + a)).hasFDerivAt).sub
      ((hasFDerivAt_comp_add_right (f := ⇑(innerSL ℝ w)) a).2 (innerSL ℝ w).hasFDerivAt)
  simp only [gradientAt, hd.fderiv, sub_apply, innerSL_apply_apply, sub_smul,
    Finset.sum_sub_distrib]

theorem combine {W : Type*} [AddCommGroup W] (D Fv Fg c L G : W) (m : D + Fv = L - G) :
    D + -Fg + c + (Fv + Fg) = L - (G - c) := by
  rw [show D + -Fg + c + (Fv + Fg) = (D + Fv) + c by abel, m]
  abel

end MovingFrame.Internal

open MovingFrame.Internal

theorem movingFrameReduction : MovingFrameReduction := by
  intro u₀ u p hs hu
  have hcs : ContDiffOn ℝ ∞ (fun t => linearPart p t) (Ici 0) := by
    unfold linearPart
    exact ContDiffOn.sum fun j _ =>
      ((time_contDiffOn hs.smooth_pressure _).sub (time_contDiffOn hs.smooth_pressure _)).smul
        contDiffOn_const
  obtain ⟨g, hg0, hg', hgs⟩ := antideriv hcs
  obtain ⟨h, hh0, hh', hhs⟩ := antideriv (a := fun t => -g t) hgs.neg
  have hfst : MapsTo (Prod.fst : ℝ × Space → ℝ) (Ici 0 ×ˢ univ) (Ici 0) := fun z hz => hz.1
  have hΦ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => (z.1, z.2 + h z.1)) (Ici 0 ×ˢ univ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add (hhs.comp contDiffOn_fst hfst))
  have hmaps : MapsTo (fun z : ℝ × Space => (z.1, z.2 + h z.1)) (Ici 0 ×ˢ univ) (Ici 0 ×ˢ univ) :=
    fun z hz => mk_mem_prod hz.1 (mem_univ _)
  refine ⟨fun t x => u t (x + h t) + g t,
    fun t x => p t (x + h t) - inner ℝ (linearPart p t) (x + h t), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hs.smooth_velocity.comp hΦ hmaps).add (hgs.comp contDiffOn_fst hfst)
  · exact (hs.smooth_pressure.comp hΦ hmaps).sub ((hcs.comp contDiffOn_fst hfst).inner ℝ
      (contDiffOn_snd.add (hhs.comp contDiffOn_fst hfst)))
  · intro x
    simp only [hh0, hg0, add_zero, hs.initial]
  · intro t ht x
    beta_reduce
    have hD : deriv (fun τ => u τ (x + h τ) + g τ) t = deriv (fun τ => u τ (x + h t)) t +
        fderiv ℝ (u t) (x + h t) (-g t) + linearPart p t :=
      ((along_hasDerivAt hs.smooth_velocity ht x (hh' t ht)).add (hg' t ht)).deriv
    have hA : advectionAt (fun z => u t (z + h t) + g t) x =
        fderiv ℝ (u t) (x + h t) (u t (x + h t)) + fderiv ℝ (u t) (x + h t) (g t) := by
      rw [advectionAt, fderiv_shift, map_add]
    have hL : sumSecondPartialsAt (fun z => u t (z + h t) + g t) x = sumSecondPartialsAt (u t) (x + h t) := by
      simp only [sumSecondPartialsAt, iteratedFDeriv_shift (slice_contDiff hs.smooth_velocity ht.le)]
    have hG : gradientAt (fun z => p t (z + h t) - inner ℝ (linearPart p t) (z + h t)) x =
        gradientAt (p t) (x + h t) - linearPart p t := by
      rw [gradient_shift ((slice_contDiff hs.smooth_pressure ht.le).differentiable (by simp)),
        sum_inner_linearPart]
    rw [hD, hA, hL, hG, map_neg]
    exact combine _ _ _ _ _ _ (hs.momentum t ht (x + h t))
  · intro t ht x
    simp only [divergenceAt, fderiv_shift]
    exact hs.incompressible t ht (x + h t)
  · intro t ht i x
    simp only
    rw [add_right_comm x (unitVector i) (h t), hu t ht i]
  · intro t ht i x
    simp only
    rw [add_right_comm x (unitVector i) (h t), pressure_shift hs hu ht i (x + h t), inner_add_right,
      inner_linearPart]
    ring

end Breakdown.Periodic

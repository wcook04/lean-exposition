import Breakdown.Frac.StSpace

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal.SpacePressureTraceSecondDeriv

lemma fderiv_clm_comp_apply {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ℓ : E →L[ℝ] G) {g : H → E} {y : H} (hg : DifferentiableAt ℝ g y) (a : H) :
    fderiv ℝ (fun z => ℓ (g z)) y a = ℓ (fderiv ℝ g y a) := by
  have h : HasFDerivAt (fun z => ℓ (g z)) (ℓ.comp (fderiv ℝ g y)) y :=
    ℓ.hasFDerivAt.comp y hg.hasFDerivAt
  rw [h.fderiv]
  rfl

lemma fderiv_component_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → Space} {y : H} (hg : DifferentiableAt ℝ g y) (i : Fin 3) (a : H) :
    fderiv ℝ (fun z => g z i) y a = fderiv ℝ g y a i :=
  fderiv_clm_comp_apply (EuclideanSpace.proj i) hg a

lemma fderiv_slice_right_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} {t : ℝ} {x : Space} (hg : DifferentiableAt ℝ g (t, x)) (a : Space) :
    fderiv ℝ (fun y => g (t, y)) x a = fderiv ℝ g (t, x) (0, a) := by
  have h : HasFDerivAt (fun y => g (t, y))
      ((fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
    hg.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  rw [h.fderiv]
  rfl

lemma hasDerivAt_slice_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} {t : ℝ} {x : Space} (hg : DifferentiableAt ℝ g (t, x)) :
    HasDerivAt (fun τ => g (τ, x)) (fderiv ℝ g (t, x) (1, 0)) t := by
  have h : HasFDerivAt (fun τ : ℝ => g (τ, x))
      ((fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ Space)) t :=
    hg.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  simpa using h.hasDerivAt

def dirPartial (a : Space) (f : Space → ℝ) : Space → ℝ := fun z => fderiv ℝ f z a

lemma dirPartial_smooth {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a : Space) :
    ContDiff ℝ ∞ (dirPartial a f) :=
  (hf.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

lemma dirPartial_sum {f : Fin 3 → Space → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k)) (a : Space) :
    dirPartial a (fun z => ∑ k, f k z) = fun z => ∑ k, dirPartial a (f k) z := by
  funext z
  unfold dirPartial
  rw [fderiv_fun_sum (fun k _ => (hf k).differentiable (by simp) z)]
  simp

lemma dirPartial_mul {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a : Space) :
    dirPartial a (fun z => f z * g z) = fun z => f z * dirPartial a g z + g z * dirPartial a f z := by
  funext z
  unfold dirPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  simp

lemma dirPartial_dirPartial {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Space) (z : Space) :
    dirPartial a (dirPartial b f) z = fderiv ℝ (fderiv ℝ f) z a b := by
  unfold dirPartial
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) z
  exact fderiv_clm_comp_apply (ContinuousLinearMap.apply ℝ ℝ b) hd a

lemma secondPartial_eq_dirPartial {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) (x : Space) :
    FundSol.secondPartial θ i j x = dirPartial (unitVector i) (dirPartial (unitVector j) θ) x := by
  rw [dirPartial_dirPartial hθ]
  simp [FundSol.secondPartial, iteratedFDeriv_two_apply]

lemma component_smooth {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z => w z i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i)).comp hw

lemma dirPartial_component {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3)
    (a z : Space) : dirPartial a (fun z => w z i) z = fderiv ℝ w z a i :=
  fderiv_component_apply (hw.differentiable (by simp) z) i a

lemma divergence_eq_sum_dirPartial {w : Space → Space} (hw : ContDiff ℝ ∞ w) (y : Space) :
    divergenceAt w y = ∑ i, dirPartial (unitVector i) (fun z => w z i) y := by
  simp only [divergenceAt, dirPartial_component hw]

lemma space_eq_sum (u : Space) : u = ∑ j, u j • unitVector j := by
  ext k
  simp [unitVector, Pi.single_apply]

lemma advection_component {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3) (y : Space) :
    advectionAt w y i = ∑ j, w y j * dirPartial (unitVector j) (fun z => w z i) y := by
  simp only [dirPartial_component hw, advectionAt]
  conv_lhs => rw [space_eq_sum (w y)]
  simp

lemma advection_component_eq {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ y, divergenceAt w y = 0) (i : Fin 3) :
    (fun y => advectionAt w y i) =
      fun y => ∑ j, dirPartial (unitVector j) (fun z => w z i * w z j) y := by
  funext y
  rw [advection_component hw]
  have h0 := hdiv y
  rw [divergence_eq_sum_dirPartial hw] at h0
  simp only [dirPartial_mul (component_smooth hw i) (component_smooth hw _), Finset.sum_add_distrib,
    ← Finset.mul_sum, h0, mul_zero, zero_add]

lemma advection_term {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ y, divergenceAt w y = 0) (x : Space) :
    ∑ i, dirPartial (unitVector i) (fun y => advectionAt w y i) x =
      ∑ i, ∑ j, FundSol.secondPartial (fun y => w y i * w y j) i j x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [advection_component_eq hw hdiv,
    dirPartial_sum (fun j => dirPartial_smooth ((component_smooth hw i).mul (component_smooth hw j)) _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [secondPartial_eq_dirPartial ((component_smooth hw i).mul (component_smooth hw j))]

lemma gradient_term {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) (x : Space) :
    FundSol.scalarSumSecondPartials p x = ∑ i, dirPartial (unitVector i) (fun y => gradientAt p y i) x := by
  have hg : ∀ i, (fun y => gradientAt p y i) = dirPartial (unitVector i) p := by
    intro i
    funext y
    simp [gradientAt, dirPartial, unitVector, Pi.single_apply]
  simp only [FundSol.scalarSumSecondPartials, hg, secondPartial_eq_dirPartial hp]

lemma time_term {T : ℝ} {F : ℝ × Space → Space}
    (hF : ∀ τ ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ∞ F (τ, y))
    (hdiv : ∀ τ ∈ Ioo 0 T, ∀ y, divergenceAt (fun y => F (τ, y)) y = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    (∀ i, DifferentiableAt ℝ (fun y => deriv (fun τ => F (τ, y)) t i) x) ∧
    ∑ i, dirPartial (unitVector i) (fun y => deriv (fun τ => F (τ, y)) t i) x = 0 := by
  have hD : ∀ z, ContDiffAt ℝ ∞ F z → DifferentiableAt ℝ (fderiv ℝ F) z := fun z hz =>
    (hz.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiableAt (by simp)
  have hte : ∀ y, deriv (fun τ => F (τ, y)) t = fderiv ℝ F (t, y) (1, 0) := fun y =>
    (hasDerivAt_slice_left ((hF t ht y).differentiableAt (by simp))).deriv
  simp only [hte]
  let ℓ : Fin 3 → (ℝ × Space →L[ℝ] Space) →L[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).comp
      (ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space)))
  have hcomp : ∀ i, DifferentiableAt ℝ (fun z => ℓ i (fderiv ℝ F z)) (t, x) := fun i =>
    (ℓ i).differentiableAt.comp (t, x) (hD _ (hF t ht x))
  have hfun : ∀ i, (fun y => fderiv ℝ F (t, y) (1, 0) i) = fun y => ℓ i (fderiv ℝ F (t, y)) :=
    fun i => rfl
  have hsym := (hF t ht x).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  refine ⟨fun i => ?_, ?_⟩
  · rw [hfun i]
    exact (hcomp i).comp x (hasFDerivAt_prodMk_right t x).differentiableAt
  have hpart : ∀ i, dirPartial (unitVector i) (fun y => fderiv ℝ F (t, y) (1, 0) i) x =
      fderiv ℝ (fderiv ℝ F) (t, x) ((1 : ℝ), (0 : Space)) ((0 : ℝ), unitVector i) i := by
    intro i
    unfold dirPartial
    rw [hfun i, fderiv_slice_right_apply (g := fun z => ℓ i (fderiv ℝ F z)) (hcomp i),
      fderiv_clm_comp_apply (ℓ i) (hD _ (hF t ht x)), hsym]
    rfl
  simp only [hpart]
  let Λ : (ℝ × Space →L[ℝ] Space) →L[ℝ] ℝ := ∑ i, (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i))
  have hΛ : ∀ φ : ℝ × Space →L[ℝ] Space, Λ φ = ∑ i, φ ((0 : ℝ), unitVector i) i := by
    intro φ
    simp [Λ]
  have h1 : HasDerivAt (fun τ => fderiv ℝ F (τ, x)) (fderiv ℝ (fderiv ℝ F) (t, x) (1, 0)) t :=
    hasDerivAt_slice_left (hD _ (hF t ht x))
  have h2 := Λ.hasFDerivAt.comp_hasDerivAt t h1
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds t] (Λ ∘ fun τ => fderiv ℝ F (τ, x)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    have hd := hdiv τ hτ x
    simp only [divergenceAt] at hd
    simp only [Function.comp_apply, hΛ]
    refine Eq.symm (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hd)
    rw [fderiv_slice_right_apply ((hF τ hτ x).differentiableAt (by simp))]
  have h3 := (h2.congr_of_eventuallyEq hev).unique (hasDerivAt_const t (0 : ℝ))
  rw [hΛ] at h3
  exact h3

lemma dirPartial_neg_sub_sub {f g h : Space → ℝ} {x : Space} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (a : Space) :
    dirPartial a (fun y => -f y - g y - h y) x =
      -dirPartial a f x - dirPartial a g x - dirPartial a h x := by
  unfold dirPartial
  have hd : HasFDerivAt (fun y => -f y - g y - h y)
      (-fderiv ℝ f x - fderiv ℝ g x - fderiv ℝ h x) x :=
    (hf.hasFDerivAt.neg.sub hg.hasFDerivAt).sub hh.hasFDerivAt
  rw [hd.fderiv]
  rfl

end FracInternal.SpacePressureTraceSecondDeriv

open FracInternal.SpacePressureTraceSecondDeriv in
theorem forcedScalarTraceSecondDeriv : ForcedScalarTraceSecondDerivStatement := by
  intro T v q F hv t ht x
  have hopen : IsOpen (Ioo 0 T ×ˢ (univ : Set Space)) := isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo 0 T ×ˢ (univ : Set Space) ⊆ Icc 0 T ×ˢ univ :=
    prod_mono Ioo_subset_Icc_self subset_rfl
  have hFat : ∀ τ ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (τ, y) :=
    fun τ hτ y => (hv.smooth_velocity.mono hsub).contDiffAt (hopen.mem_nhds ⟨hτ, mem_univ y⟩)
  have hQat : ∀ τ ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) (τ, y) :=
    fun τ hτ y => (hv.smooth_pressure.mono hsub).contDiffAt (hopen.mem_nhds ⟨hτ, mem_univ y⟩)
  have hw : ContDiff ℝ ∞ (v t) := contDiff_iff_contDiffAt.2 fun y =>
    (hFat t ht y).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hp : ContDiff ℝ ∞ (q t) := contDiff_iff_contDiffAt.2 fun y =>
    (hQat t ht y).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hf : ContDiff ℝ ∞ (F t) := hv.force_smooth t ht
  have hdiv : ∀ y, divergenceAt (v t) y = 0 := hv.incompressible t (Ioo_subset_Icc_self ht)
  obtain ⟨hDd, hDz⟩ := time_term (F := fun z : ℝ × Space => v z.1 z.2) hFat
    (fun τ hτ y => hv.incompressible τ (Ioo_subset_Icc_self hτ) y) ht x
  have hmom : ∀ i, (fun y => gradientAt (q t) y i) =
      fun y => -F t y i - advectionAt (v t) y i - deriv (fun τ => v τ y) t i := by
    intro i
    funext y
    have h := hv.momentum t ht y
    have h' : gradientAt (q t) y =
        -F t y - advectionAt (v t) y - deriv (fun τ => v τ y) t := by
      have h2 := congrArg Neg.neg h
      rw [neg_neg] at h2
      rw [← h2]
      abel
    rw [h']
    rfl
  have hFd : ∀ i, DifferentiableAt ℝ (fun y => F t y i) x := fun i =>
    (component_smooth hf i).differentiable (by simp) x
  have hAd : ∀ i, DifferentiableAt ℝ (fun y => advectionAt (v t) y i) x := by
    intro i
    rw [advection_component_eq hw hdiv i]
    exact (ContDiff.sum fun j _ => dirPartial_smooth
      ((component_smooth hw i).mul (component_smooth hw j)) _).differentiable (by simp) x
  have hFz : ∑ i, dirPartial (unitVector i) (fun y => F t y i) x = 0 := by
    rw [← divergence_eq_sum_dirPartial hf]
    exact hv.force_div t ht x
  rw [gradient_term hp]
  simp only [hmom]
  rw [Finset.sum_congr rfl fun i _ => dirPartial_neg_sub_sub (hFd i) (hAd i) (hDd i) (unitVector i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hFz,
    advection_term hw hdiv, hDz]
  ring

end Breakdown

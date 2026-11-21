import Breakdown.Uniqueness.EnergyDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma fderiv_clm_comp_apply {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ℓ : E →L[ℝ] G) {g : H → E} {y : H} (hg : DifferentiableAt ℝ g y) (a : H) :
    fderiv ℝ (fun z => ℓ (g z)) y a = ℓ (fderiv ℝ g y a) := by
  have h : HasFDerivAt (fun z => ℓ (g z)) (ℓ.comp (fderiv ℝ g y)) y :=
    ℓ.hasFDerivAt.comp y hg.hasFDerivAt
  rw [h.fderiv]
  rfl

private lemma fderiv_component_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → Space} {y : H} (hg : DifferentiableAt ℝ g y) (i : Fin 3) (a : H) :
    fderiv ℝ (fun z => g z i) y a = fderiv ℝ g y a i :=
  fderiv_clm_comp_apply (EuclideanSpace.proj i) hg a

private lemma fderiv_slice_right_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} {t : ℝ} {x : Space} (hg : DifferentiableAt ℝ g (t, x)) (a : Space) :
    fderiv ℝ (fun y => g (t, y)) x a = fderiv ℝ g (t, x) (0, a) := by
  have h : HasFDerivAt (fun y => g (t, y))
      ((fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
    hg.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  rw [h.fderiv]
  rfl

private lemma hasDerivAt_slice_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × Space → E} {t : ℝ} {x : Space} (hg : DifferentiableAt ℝ g (t, x)) :
    HasDerivAt (fun τ => g (τ, x)) (fderiv ℝ g (t, x) (1, 0)) t := by
  have h : HasFDerivAt (fun τ : ℝ => g (τ, x))
      ((fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ Space)) t :=
    hg.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  simpa using h.hasDerivAt

private def partialAlong (a : Space) (f : Space → ℝ) : Space → ℝ := fun z => fderiv ℝ f z a

private lemma partialAlong_smooth {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a : Space) :
    ContDiff ℝ ∞ (partialAlong a f) :=
  (hf.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

private lemma partialAlong_sum {f : Fin 3 → Space → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k)) (a : Space) :
    partialAlong a (fun z => ∑ k, f k z) = fun z => ∑ k, partialAlong a (f k) z := by
  funext z
  unfold partialAlong
  rw [fderiv_fun_sum (fun k _ => (hf k).differentiable (by simp) z)]
  simp

private lemma partialAlong_mul {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a : Space) :
    partialAlong a (fun z => f z * g z) = fun z => f z * partialAlong a g z + g z * partialAlong a f z := by
  funext z
  unfold partialAlong
  rw [fderiv_fun_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  simp

private lemma partialAlong_const (c : ℝ) (a : Space) : partialAlong a (fun _ => c) = fun _ => 0 := by
  funext z
  simp [partialAlong]

private lemma partialAlong_partialAlong {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Space) (z : Space) :
    partialAlong a (partialAlong b f) z = fderiv ℝ (fderiv ℝ f) z a b := by
  unfold partialAlong
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) z
  exact fderiv_clm_comp_apply (ContinuousLinearMap.apply ℝ ℝ b) hd a

private lemma partialAlong_comm {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Space) :
    partialAlong a (partialAlong b f) = partialAlong b (partialAlong a f) := by
  funext z
  rw [partialAlong_partialAlong hf, partialAlong_partialAlong hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) a b

private lemma secondPartial_eq_partialAlong {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) (x : Space) :
    FundSol.secondPartial θ i j x = partialAlong (unitVector i) (partialAlong (unitVector j) θ) x := by
  rw [partialAlong_partialAlong hθ]
  simp [FundSol.secondPartial, iteratedFDeriv_two_apply]


private lemma component_smooth {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z => w z i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i)).comp hw

private lemma partialAlong_component {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3)
    (a z : Space) : partialAlong a (fun z => w z i) z = fderiv ℝ w z a i :=
  fderiv_component_apply (hw.differentiable (by simp) z) i a

private lemma partialAlong_partialAlong_component {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (i : Fin 3) (a b y : Space) :
    partialAlong a (partialAlong b (fun z => w z i)) y = fderiv ℝ (fderiv ℝ w) y a b i := by
  have hfun : partialAlong b (fun z => w z i) =
      fun z => ((EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ Space b)) (fderiv ℝ w z) := by
    funext z
    rw [partialAlong_component hw]
    rfl
  rw [hfun]
  have hd : DifferentiableAt ℝ (fderiv ℝ w) y :=
    (hw.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) y
  exact fderiv_clm_comp_apply _ hd a

private lemma divergence_eq_sum_partialAlong {w : Space → Space} (hw : ContDiff ℝ ∞ w) (y : Space) :
    divergenceAt w y = ∑ i, partialAlong (unitVector i) (fun z => w z i) y := by
  simp only [divergenceAt, partialAlong_component hw]

private lemma sumSecondPartials_component {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    (fun y => sumSecondPartialsAt w y i) =
      fun y => ∑ k, partialAlong (unitVector k) (partialAlong (unitVector k) (fun z => w z i)) y := by
  funext y
  simp only [partialAlong_partialAlong_component hw, sumSecondPartialsAt, iteratedFDeriv_two_apply]
  simp

private lemma space_eq_sum (u : Space) : u = ∑ j, u j • unitVector j := by
  ext k
  simp [unitVector, Pi.single_apply]

private lemma advection_component {w : Space → Space} (hw : ContDiff ℝ ∞ w) (i : Fin 3) (y : Space) :
    advectionAt w y i = ∑ j, w y j * partialAlong (unitVector j) (fun z => w z i) y := by
  simp only [partialAlong_component hw, advectionAt]
  conv_lhs => rw [space_eq_sum (w y)]
  simp

private lemma advection_component_eq {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ y, divergenceAt w y = 0) (i : Fin 3) :
    (fun y => advectionAt w y i) =
      fun y => ∑ j, partialAlong (unitVector j) (fun z => w z i * w z j) y := by
  funext y
  rw [advection_component hw]
  have h0 := hdiv y
  rw [divergence_eq_sum_partialAlong hw] at h0
  simp only [partialAlong_mul (component_smooth hw i) (component_smooth hw _), Finset.sum_add_distrib,
    ← Finset.mul_sum, h0, mul_zero, zero_add]

private lemma advection_term {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ y, divergenceAt w y = 0) (x : Space) :
    ∑ i, partialAlong (unitVector i) (fun y => advectionAt w y i) x =
      ∑ i, ∑ j, FundSol.secondPartial (fun y => w y i * w y j) i j x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [advection_component_eq hw hdiv,
    partialAlong_sum (fun j => partialAlong_smooth ((component_smooth hw i).mul (component_smooth hw j)) _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [secondPartial_eq_partialAlong ((component_smooth hw i).mul (component_smooth hw j))]

private lemma sumSecondPartials_term {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ y, divergenceAt w y = 0) (x : Space) :
    ∑ i, partialAlong (unitVector i) (fun y => sumSecondPartialsAt w y i) x = 0 := by
  have hdivf : (fun y => ∑ i, partialAlong (unitVector i) (fun z => w z i) y) = fun _ => 0 := by
    funext y
    rw [← divergence_eq_sum_partialAlong hw, hdiv]
  have hsm : ∀ i, ContDiff ℝ ∞ (partialAlong (unitVector i) (fun z => w z i)) :=
    fun i => partialAlong_smooth (component_smooth hw i) _
  have hk : ∀ k, partialAlong (unitVector k) (partialAlong (unitVector k)
      (fun y => ∑ i, partialAlong (unitVector i) (fun z => w z i) y)) x = 0 := by
    intro k
    rw [hdivf, partialAlong_const, partialAlong_const]
  have hk' : ∀ k, partialAlong (unitVector k) (partialAlong (unitVector k)
      (fun y => ∑ i, partialAlong (unitVector i) (fun z => w z i) y)) x =
      ∑ i, partialAlong (unitVector i) (partialAlong (unitVector k)
        (partialAlong (unitVector k) (fun z => w z i))) x := by
    intro k
    rw [partialAlong_sum hsm, partialAlong_sum (fun i => partialAlong_smooth (hsm i) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [partialAlong_comm (component_smooth hw i) (unitVector k) (unitVector i),
      partialAlong_comm (partialAlong_smooth (component_smooth hw i) _) (unitVector k) (unitVector i)]
  rw [Finset.sum_congr rfl fun i _ => by
    rw [sumSecondPartials_component hw i,
      partialAlong_sum (fun k => partialAlong_smooth (partialAlong_smooth (component_smooth hw i) _) _)]]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← hk' k, hk k]

private lemma gradient_term {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) (x : Space) :
    FundSol.scalarSumSecondPartials p x = ∑ i, partialAlong (unitVector i) (fun y => gradientAt p y i) x := by
  have hg : ∀ i, (fun y => gradientAt p y i) = partialAlong (unitVector i) p := by
    intro i
    funext y
    simp [gradientAt, partialAlong, unitVector, Pi.single_apply]
  simp only [FundSol.scalarSumSecondPartials, hg, secondPartial_eq_partialAlong hp]


private lemma time_term {T : ℝ} {F : ℝ × Space → Space}
    (hF : ∀ τ ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ∞ F (τ, y))
    (hdiv : ∀ τ ∈ Ioo 0 T, ∀ y, divergenceAt (fun y => F (τ, y)) y = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    (∀ i, DifferentiableAt ℝ (fun y => deriv (fun τ => F (τ, y)) t i) x) ∧
    ∑ i, partialAlong (unitVector i) (fun y => deriv (fun τ => F (τ, y)) t i) x = 0 := by
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
  have hpart : ∀ i, partialAlong (unitVector i) (fun y => fderiv ℝ F (t, y) (1, 0) i) x =
      fderiv ℝ (fderiv ℝ F) (t, x) ((1 : ℝ), (0 : Space)) ((0 : ℝ), unitVector i) i := by
    intro i
    unfold partialAlong
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

private lemma partialAlong_sub_sub {f g h : Space → ℝ} {x : Space} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (a : Space) :
    partialAlong a (fun y => f y - g y - h y) x =
      partialAlong a f x - partialAlong a g x - partialAlong a h x := by
  unfold partialAlong
  rw [fderiv_fun_sub (hf.fun_sub hg) hh, fderiv_fun_sub hf hg]
  rfl

theorem scalarSumSecondPartials_pressure {T : ℝ} {v : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (hv : IsSolutionOn T v q) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    FundSol.scalarSumSecondPartials (q t) x =
      -∑ i, ∑ j, FundSol.secondPartial (fun y => v t y i * v t y j) i j x := by
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
  have hdiv : ∀ y, divergenceAt (v t) y = 0 := hv.incompressible t (Ioo_subset_Icc_self ht)
  obtain ⟨hDd, hDz⟩ := time_term (F := fun z : ℝ × Space => v z.1 z.2) hFat
    (fun τ hτ y => hv.incompressible τ (Ioo_subset_Icc_self hτ) y) ht x
  have hmom : ∀ i, (fun y => gradientAt (q t) y i) =
      fun y => sumSecondPartialsAt (v t) y i - advectionAt (v t) y i - deriv (fun τ => v τ y) t i := by
    intro i
    funext y
    have h := hv.momentum t ht y
    have h' : gradientAt (q t) y =
        sumSecondPartialsAt (v t) y - advectionAt (v t) y - deriv (fun τ => v τ y) t := by
      rw [← sub_eq_zero, ← sub_eq_zero.2 h]
      abel
    rw [h']
    rfl
  have hLd : ∀ i, DifferentiableAt ℝ (fun y => sumSecondPartialsAt (v t) y i) x := by
    intro i
    rw [sumSecondPartials_component hw i]
    exact (ContDiff.sum fun k _ => partialAlong_smooth
      (partialAlong_smooth (component_smooth hw i) _) _).differentiable (by simp) x
  have hAd : ∀ i, DifferentiableAt ℝ (fun y => advectionAt (v t) y i) x := by
    intro i
    rw [advection_component_eq hw hdiv i]
    exact (ContDiff.sum fun j _ => partialAlong_smooth
      ((component_smooth hw i).mul (component_smooth hw j)) _).differentiable (by simp) x
  rw [gradient_term hp]
  simp only [hmom]
  rw [Finset.sum_congr rfl fun i _ => partialAlong_sub_sub (hLd i) (hAd i) (hDd i) (unitVector i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sumSecondPartials_term hw hdiv, advection_term hw hdiv,
    hDz]
  ring

end Breakdown

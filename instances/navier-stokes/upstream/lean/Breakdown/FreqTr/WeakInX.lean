import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.WeakInX

theorem fderiv_dir_eq {g : Space → Space} (hg : ContDiff ℝ ∞ g) (x u v : Space) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x u = fderiv ℝ (fderiv ℝ g) x u v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((contDiff_infty_iff_fderiv.1 hg).2.differentiable (by simp)) x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem smooth_partial {g : Space → Space} (hg : ContDiff ℝ ∞ g) (k : Fin 3) :
    ContDiff ℝ ∞ (partialField g k) :=
  (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const

theorem partial_comm {g : Space → Space} (hg : ContDiff ℝ ∞ g) (j k : Fin 3) :
    partialField (partialField g j) k = partialField (partialField g k) j := by
  funext x
  show fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x (unitVector k) =
    fderiv ℝ (fun y => fderiv ℝ g y (unitVector k)) x (unitVector j)
  rw [fderiv_dir_eq hg, fderiv_dir_eq hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)).eq _ _

theorem fderiv_sum_comp (h : Fin 3 → Space → Space) (hh : ∀ i, Differentiable ℝ (h i))
    (y v : Space) :
    fderiv ℝ (fun z => ∑ i : Fin 3, h i z i) y v = ∑ i : Fin 3, fderiv ℝ (h i) y v i := by
  have hd : HasFDerivAt (fun z => ∑ i : Fin 3, h i z i)
      (∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ (h i) y)) y := by
    exact HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y ((hh i) y).hasFDerivAt)
  rw [hd.fderiv]
  simp

theorem negSsp_eq {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) :
    negSsp φ = fun x => -∑ j : Fin 3, partialField (partialField φ j) j x := by
  funext x
  simp only [negSsp, sumSecondPartialsAt, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← fderiv_dir_eq hφ]
  rfl

theorem divergence_negSsp {φ : Space → Space} (hs : ContDiff ℝ ∞ φ)
    (hd : ∀ y, divergenceAt φ y = 0) (y : Space) : divergenceAt (negSsp φ) y = 0 := by
  have hP : ∀ i, ContDiff ℝ ∞ (partialField φ i) := smooth_partial hs
  have hPP : ∀ i j, ContDiff ℝ ∞ (partialField (partialField φ i) j) :=
    fun i j => smooth_partial (hP i) j
  have comm : ∀ i j, fderiv ℝ (partialField (partialField φ j) j) y (unitVector i) =
      partialField (partialField (partialField φ i) j) j y := by
    intro i j
    change partialField (partialField (partialField φ j) j) i y = _
    rw [partial_comm (hP j) j i, partial_comm hs j i]
  have key : ∀ j, ∑ i : Fin 3, partialField (partialField (partialField φ i) j) j y i = 0 := by
    intro j
    have h0 : (fun w => ∑ i : Fin 3, partialField φ i w i) = fun _ => 0 := by
      funext w; exact hd w
    have h1 : (fun z => ∑ i : Fin 3, partialField (partialField φ i) j z i) =
        fun z => fderiv ℝ (fun w => ∑ i : Fin 3, partialField φ i w i) z (unitVector j) := by
      funext z
      rw [fderiv_sum_comp _ (fun i => (hP i).differentiable (by simp))]
      rfl
    calc ∑ i : Fin 3, partialField (partialField (partialField φ i) j) j y i
        = fderiv ℝ (fun z => ∑ i : Fin 3, partialField (partialField φ i) j z i) y (unitVector j) :=
          (fderiv_sum_comp (fun i => partialField (partialField φ i) j)
            (fun i => (hPP i j).differentiable (by simp)) y (unitVector j)).symm
      _ = 0 := by rw [h1, h0]; simp
  have hder : HasFDerivAt (fun x => -∑ j : Fin 3, partialField (partialField φ j) j x)
      (-∑ j : Fin 3, fderiv ℝ (partialField (partialField φ j) j) y) y :=
    (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      ((hPP j j).differentiable (by simp) y).hasFDerivAt).neg
  unfold divergenceAt
  rw [negSsp_eq hs, hder.fderiv]
  have hi : ∀ i, ((-∑ j : Fin 3, fderiv ℝ (partialField (partialField φ j) j) y) (unitVector i)) i =
      -∑ j : Fin 3, partialField (partialField (partialField φ i) j) j y i := by
    intro i
    simp [comm]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_neg_distrib, Finset.sum_comm]
  simp [key]

end Internal.WeakInX

theorem isDecayField_of_isTestField {φ : Space → Space} (h : IsTestField φ) : IsDecayField φ := by
  obtain ⟨hs, hc, hd⟩ := h
  refine ⟨hs, hd, ?_⟩
  have c0 : Continuous φ := hs.continuous
  have c1 : Continuous (fderiv ℝ φ) := hs.continuous_fderiv (by simp)
  have g0 : Continuous fun y : Space => (1 + ‖y‖) * ‖φ y‖ :=
    (continuous_const.add continuous_norm).mul c0.norm
  have g1 : Continuous fun y : Space => (1 + ‖y‖) ^ 2 * ‖fderiv ℝ φ y‖ :=
    ((continuous_const.add continuous_norm).pow 2).mul c1.norm
  obtain ⟨A, hA⟩ := g0.bounded_above_of_compact_support hc.norm.mul_left
  obtain ⟨B, hB⟩ := g1.bounded_above_of_compact_support (hc.fderiv ℝ).norm.mul_left
  refine ⟨max A B, fun y => ⟨?_, ?_⟩⟩
  · have hp : 0 < 1 + ‖y‖ := by positivity
    rw [le_div_iff₀ hp]
    have := hA y
    rw [Real.norm_of_nonneg (by positivity)] at this
    nlinarith [le_max_left A B]
  · have hp : 0 < (1 + ‖y‖) ^ 2 := by positivity
    rw [le_div_iff₀ hp]
    have := hB y
    rw [Real.norm_of_nonneg (by positivity)] at this
    nlinarith [le_max_right A B]

theorem isTestField_negSsp {φ : Space → Space} (h : IsTestField φ) : IsTestField (negSsp φ) := by
  obtain ⟨hs, hc, hd⟩ := h
  refine ⟨?_, ?_, Internal.WeakInX.divergence_negSsp hs hd⟩
  · rw [Internal.WeakInX.negSsp_eq hs]
    exact (ContDiff.sum fun j _ =>
      Internal.WeakInX.smooth_partial (Internal.WeakInX.smooth_partial hs j) j).neg
  · refine hc.mono' fun x hx => ?_
    by_contra hn
    apply hx
    have h0 : iteratedFDeriv ℝ 2 φ x = 0 := by
      by_contra h0
      exact hn (support_iteratedFDeriv_subset 2 (Function.mem_support.2 h0))
    simp [negSsp, sumSecondPartialsAt, h0]

namespace Internal.WeakInX

theorem trilinear_sub_left (hT : TrilinearBound) (u u' v : X) (w : Space → Space)
    (h2 : MemLp w 2 volume) (h6 : MemLp w 6 volume) :
    trilinear (u - u') v w = trilinear u v w - trilinear u' v w := by
  obtain ⟨C, hC⟩ := hT
  unfold trilinear
  rw [← integral_sub (hC u v w h2 h6).1 (hC u' v w h2 h6).1]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (velocity u) (velocity u')] with x hx
  simp only [map_sub]
  rw [hx]
  simp [sub_mul, Finset.sum_sub_distrib]

theorem trilinear_sub_right (hT : TrilinearBound) (u v v' : X) (w : Space → Space)
    (h2 : MemLp w 2 volume) (h6 : MemLp w 6 volume) :
    trilinear u (v - v') w = trilinear u v w - trilinear u v' w := by
  obtain ⟨C, hC⟩ := hT
  unfold trilinear
  rw [← integral_sub (hC u v w h2 h6).1 (hC u v' w h2 h6).1]
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂volume, ∀ j : Fin 3,
      (partialX j v - partialX j v' : L2R) x = (partialX j v : Space → Space) x - (partialX j v' : Space → Space) x :=
    ae_all_iff.2 fun j => by
      filter_upwards [Lp.coeFn_sub (partialX j v) (partialX j v')] with x hx
      rw [hx]; rfl
  filter_upwards [hae] with x hx
  simp only [map_sub]
  simp only [hx, inner_sub_left, mul_sub, Finset.sum_sub_distrib]

theorem continuous_trilinear_diag (hT : TrilinearBound) (w : Space → Space)
    (h2 : MemLp w 2 volume) (h6 : MemLp w 6 volume) :
    Continuous (fun u : X => trilinear u u w) := by
  obtain ⟨C, hC⟩ := hT
  set K := Real.sqrt ((eLpNorm w 2 volume).toReal * (eLpNorm w 6 volume).toReal)
  rw [continuous_iff_continuousAt]
  intro u0
  have key : ∀ u, |trilinear u u w - trilinear u0 u0 w| ≤
      C * ‖u - u0‖ * ‖u‖ * K + C * ‖u0‖ * ‖u - u0‖ * K := by
    intro u
    have e : trilinear u u w - trilinear u0 u0 w =
        trilinear (u - u0) u w + trilinear u0 (u - u0) w := by
      rw [trilinear_sub_left ⟨C, hC⟩ _ _ _ w h2 h6, trilinear_sub_right ⟨C, hC⟩ _ _ _ w h2 h6]
      ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (hC _ _ w h2 h6).2 (hC _ _ w h2 h6).2)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero
    (g := fun u => C * ‖u - u0‖ * ‖u‖ * K + C * ‖u0‖ * ‖u - u0‖ * K)
    (fun _ => dist_nonneg) (fun u => ?_) ?_)
  · rw [Real.dist_eq]; exact key u
  · have hc : Continuous (fun u : X => C * ‖u - u0‖ * ‖u‖ * K + C * ‖u0‖ * ‖u - u0‖ * K) := by
      fun_prop
    simpa using hc.tendsto u0

end Internal.WeakInX

open Internal.WeakInX in
theorem weakInX (h1 : PairingEmbed) (h2 : PairingByParts) (h3 : AdvectionTrilinear)
    (h4 : TrilinearBound) (_h5 : EmbedLinear) : WeakInX := by
  intro v a b hab hw φ hφ t ht
  obtain ⟨hdec, hcont, -, -, hder, hpc⟩ := hw
  have hψ := isTestField_negSsp hφ
  have hφd := isDecayField_of_isTestField hφ
  have hψd := isDecayField_of_isTestField hψ
  have hψc : Continuous (negSsp φ) := hψ.1.continuous
  have hGc : ContinuousOn (fun s => inner ℝ (embedX (v s)) (embedX (negSsp φ)) +
      trilinear (embedX (v s)) (embedX (v s)) (negSsp φ)) (Icc a b) := by
    have hq := continuous_trilinear_diag h4 (negSsp φ) (hψc.memLp_of_hasCompactSupport hψ.2.1)
      (hψc.memLp_of_hasCompactSupport hψ.2.1)
    exact (hcont.inner continuousOn_const).add (hq.comp_continuousOn hcont)
  have hta : a ≤ t := ht.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hGi := (hGc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hta
  refine ⟨hGi, ?_⟩
  have hF : ∀ s ∈ Icc a b, fieldPairing (v s) (negSsp φ) = inner ℝ (embedX (v s)) (embedX φ) := by
    intro s hs
    rw [h1 _ _ (hdec s hs) hφd, h2 _ _ (hdec s hs) hφ]
  have hd' : ∀ s ∈ Ioo a t, HasDerivAt (fun τ => fieldPairing (v τ) (negSsp φ))
      (-(inner ℝ (embedX (v s)) (embedX (negSsp φ)) +
        trilinear (embedX (v s)) (embedX (v s)) (negSsp φ))) s := by
    intro s hs
    have hs' : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs'
    refine (hder _ hψ s hs').congr_deriv ?_
    rw [h1 _ _ (hdec s hsI) hψd, h3 _ _ (hdec s hsI) hψ]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hta ((hpc _ hψ).mono hsub)
    hd' hGi.neg
  rw [intervalIntegral.integral_neg, hF t ht, hF a ⟨le_rfl, hab.le⟩] at hftc
  linarith

end Breakdown.Freq

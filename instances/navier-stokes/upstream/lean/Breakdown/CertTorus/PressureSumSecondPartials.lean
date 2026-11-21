import Breakdown.CertTorus.DecayStatements

open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

namespace Internal.LerayDivergence

def traceMap : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector i))

lemma traceMap_apply (φ : Space →L[ℝ] Space) : traceMap φ = ∑ i : Fin 3, φ (unitVector i) i := by
  simp [traceMap]

lemma divergenceAt_eq_traceMap (V : Space → Space) (x : Space) :
    divergenceAt V x = traceMap (fderiv ℝ V x) := by
  rw [traceMap_apply]
  rfl

lemma smooth_two_le : minSmoothness ℝ 2 ≤ ∞ := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.2 le_top

lemma succ_le_smooth : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  exact_mod_cast le_rfl

lemma differentiable_fderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : E → G} (hV : ContDiff ℝ ∞ V) :
    Differentiable ℝ (fderiv ℝ V) :=
  (hV.fderiv_right (m := ∞) succ_le_smooth).differentiable (by simp)

lemma contDiff_partial {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Space → G} (hV : ContDiff ℝ ∞ V) (a : Space) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ V z a) :=
  (hV.fderiv_right (m := ∞) succ_le_smooth).clm_apply contDiff_const

lemma fderiv_partial_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Space → G} (hV : ContDiff ℝ ∞ V) (a b y : Space) :
    fderiv ℝ (fun z => fderiv ℝ V z a) y b = fderiv ℝ (fderiv ℝ V) y b a := by
  have h : HasFDerivAt (fun z => fderiv ℝ V z a)
      ((ContinuousLinearMap.apply ℝ G a).comp (fderiv ℝ (fderiv ℝ V) y)) y :=
    (ContinuousLinearMap.apply ℝ G a).hasFDerivAt.comp y (differentiable_fderiv hV y).hasFDerivAt
  rw [h.fderiv]
  rfl

lemma fderiv_component_apply {V : Space → Space} {x : Space} (hV : DifferentiableAt ℝ V x)
    (j : Fin 3) (v : Space) : fderiv ℝ (fun y => V y j) x v = fderiv ℝ V x v j := by
  have h : HasFDerivAt (fun y => V y j)
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).comp (fderiv ℝ V x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).hasFDerivAt.comp x hV.hasFDerivAt
  rw [h.fderiv]
  rfl

lemma fderiv_divergence_apply {V : Space → Space} (hV : ContDiff ℝ ∞ V) (x a : Space) :
    fderiv ℝ (divergenceAt V) x a = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ V) x a (unitVector i) i := by
  have hfun : divergenceAt V = fun z => traceMap (fderiv ℝ V z) :=
    funext fun z => divergenceAt_eq_traceMap V z
  have h : HasFDerivAt (fun z => traceMap (fderiv ℝ V z))
      (traceMap.comp (fderiv ℝ (fderiv ℝ V) x)) x :=
    traceMap.hasFDerivAt.comp x (differentiable_fderiv hV x).hasFDerivAt
  rw [hfun, h.fderiv, ContinuousLinearMap.comp_apply, traceMap_apply]

lemma divergence_fderiv_apply {V U : Space → Space} (hV : ContDiff ℝ ∞ V) {x : Space}
    (hU : DifferentiableAt ℝ U x) :
    divergenceAt (fun z => fderiv ℝ V z (U z)) x =
      fderiv ℝ (divergenceAt V) x (U x) +
        ∑ i : Fin 3, fderiv ℝ V x (fderiv ℝ U x (unitVector i)) i := by
  have hsym : IsSymmSndFDerivAt ℝ V x := (hV.contDiffAt).isSymmSndFDerivAt smooth_two_le
  have h := (differentiable_fderiv hV x).hasFDerivAt.clm_apply hU.hasFDerivAt
  rw [divergenceAt_eq_traceMap, h.fderiv, fderiv_divergence_apply hV, traceMap_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, PiLp.add_apply]
  rw [hsym (unitVector i) (U x)]
  ring

lemma divergence_partial_eq_zero {V : Space → Space} (hV : ContDiff ℝ ∞ V)
    (h0 : ∀ y, divergenceAt V y = 0) (a : Space) (y : Space) :
    divergenceAt (fun z => fderiv ℝ V z a) y = 0 := by
  have h := divergence_fderiv_apply (U := fun _ => a) hV (differentiableAt_const a) (x := y)
  have hc : divergenceAt V = fun _ => 0 := funext h0
  rw [h, hc]
  simp

lemma divergence_sum {f : Fin 3 → Space → Space} {x : Space}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    divergenceAt (fun y => ∑ i : Fin 3, f i y) x = ∑ i : Fin 3, divergenceAt (f i) x := by
  rw [divergenceAt_eq_traceMap, fderiv_fun_sum (fun i _ => hf i), map_sum]
  simp only [divergenceAt_eq_traceMap]

lemma laplacianAt_eq_sum {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    sumSecondPartialsAt w = fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ w z (unitVector i)) y (unitVector i) := by
  funext y
  simp only [sumSecondPartialsAt, fderiv_partial_apply hw, iteratedFDeriv_two_apply]
  simp

lemma divergence_laplacian_eq_zero {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (h0 : ∀ y, divergenceAt w y = 0) (x : Space) : divergenceAt (sumSecondPartialsAt w) x = 0 := by
  rw [laplacianAt_eq_sum hw, divergence_sum fun i =>
    (contDiff_partial (contDiff_partial hw _) _).differentiable (by simp) x]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact divergence_partial_eq_zero (contDiff_partial hw _)
    (divergence_partial_eq_zero hw h0 _) _ x

lemma space_eq_sum (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext k
  simp [unitVector, Pi.single_apply]

lemma trace_comp_self (L : Space →L[ℝ] Space) :
    ∑ i : Fin 3, L (L (unitVector i)) i =
      ∑ i : Fin 3, ∑ j : Fin 3, L (unitVector i) j * L (unitVector j) i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [space_eq_sum (L (unitVector i))]
  simp [map_sum, map_smul]

lemma laplacian_eq_divergence_gradient {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) (x : Space) :
    FundSol.scalarSumSecondPartials p x = divergenceAt (gradientAt p) x := by
  have hg : ContDiff ℝ ∞ (gradientAt p) := by
    show ContDiff ℝ ∞ (fun y => ∑ i : Fin 3, fderiv ℝ p y (unitVector i) • unitVector i)
    exact ContDiff.sum fun i _ => (contDiff_partial hp _).smul contDiff_const
  have hc : ∀ j, (fun y => gradientAt p y j) = fun y => fderiv ℝ p y (unitVector j) := by
    intro j
    funext y
    simp [gradientAt, unitVector, Pi.single_apply]
  simp only [FundSol.scalarSumSecondPartials, FundSol.secondPartial, divergenceAt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← fderiv_component_apply (hg.differentiable (by simp) x), hc j, fderiv_partial_apply hp,
    iteratedFDeriv_two_apply]
  simp

lemma divergence_time_deriv {F : ℝ × Space → Space} (hF : ContDiff ℝ ∞ F)
    (hdiv : ∀ σ y, divergenceAt (fun z => F (σ, z)) y = 0) (s : ℝ) (x : Space) :
    divergenceAt (fun y => fderiv ℝ F (s, y) ((1 : ℝ), (0 : Space))) x = 0 := by
  let Θ : (ℝ × Space →L[ℝ] Space) →L[ℝ] ℝ := ∑ i : Fin 3,
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i))
  have hΘ : ∀ φ : ℝ × Space →L[ℝ] Space, Θ φ = ∑ i : Fin 3, φ ((0 : ℝ), unitVector i) i := by
    intro φ
    simp [Θ]
  have hD2 := differentiable_fderiv hF
  have hsym : IsSymmSndFDerivAt ℝ F (s, x) := (hF.contDiffAt).isSymmSndFDerivAt smooth_two_le
  have hslice : ∀ σ y, fderiv ℝ (fun z => F (σ, z)) y =
      (fderiv ℝ F (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := fun σ y =>
    ((hF.differentiable (by simp) (σ, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)).fderiv
  have hg : ∀ σ, Θ (fderiv ℝ F (σ, x)) = 0 := by
    intro σ
    have h := hdiv σ x
    rw [divergenceAt, hslice] at h
    rw [hΘ]
    simpa using h
  have h1 : HasDerivAt (fun σ => Θ (fderiv ℝ F (σ, x)))
      (Θ (fderiv ℝ (fderiv ℝ F) (s, x) ((1 : ℝ), (0 : Space)))) s := by
    have h := Θ.hasFDerivAt.comp s ((hD2 (s, x)).hasFDerivAt.comp s (hasFDerivAt_prodMk_left s x))
    exact h.hasDerivAt
  have h0 : Θ (fderiv ℝ (fderiv ℝ F) (s, x) ((1 : ℝ), (0 : Space))) = 0 := by
    have hc : (fun σ => Θ (fderiv ℝ F (σ, x))) = fun _ => 0 := funext hg
    rw [hc] at h1
    exact h1.unique (hasDerivAt_const s 0)
  have hA : HasFDerivAt (fun y => fderiv ℝ F (s, y) ((1 : ℝ), (0 : Space)))
      ((ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space))).comp
        ((fderiv ℝ (fderiv ℝ F) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space))) x :=
    (ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space))).hasFDerivAt.comp x
      ((hD2 (s, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x))
  rw [hΘ] at h0
  rw [divergenceAt_eq_traceMap, hA.fderiv, traceMap_apply, ← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inr_apply]
  rw [hsym]

end Internal.LerayDivergence

open Internal.LerayDivergence in
theorem pressureLaplacian_holds : PressureSumSecondPartials := by
  intro W q P R hW s x
  have hF : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) := hW.smooth_field
  have hw : ContDiff ℝ ∞ (W s) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hp : ContDiff ℝ ∞ (q s) := hW.smooth_pressure.comp (contDiff_const.prodMk contDiff_id)
  have h0 : ∀ y, divergenceAt (W s) y = 0 := hW.divergence s
  have hdd : fderiv ℝ (divergenceAt (W s)) x = 0 := by
    have hc : divergenceAt (W s) = fun _ => 0 := funext h0
    rw [hc]
    simp
  have hA : (fun y => deriv (fun σ => W σ y) s) =
      fun y => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) ((1 : ℝ), (0 : Space)) := by
    funext y
    have h := ((hF.differentiable (by simp) (s, y)).hasFDerivAt.comp s
      (hasFDerivAt_prodMk_left s y)).hasDerivAt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at h
    exact h.deriv
  have hAs : ContDiff ℝ ∞ (fun y => deriv (fun σ => W σ y) s) := by
    rw [hA]
    exact ((hF.fderiv_right (m := ∞) succ_le_smooth).comp
      (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  have hAdiv : divergenceAt (fun y => deriv (fun σ => W σ y) s) x = 0 := by
    rw [hA]
    exact divergence_time_deriv hF (fun σ y => hW.divergence σ y) s x
  have hCs : ContDiff ℝ ∞ (fun y => fderiv ℝ (W s) y y) :=
    (hw.fderiv_right (m := ∞) succ_le_smooth).clm_apply contDiff_id
  have hCdiv : divergenceAt (fun y => fderiv ℝ (W s) y y) x = 0 := by
    have h := divergence_fderiv_apply (U := fun z => z) hw (x := x) differentiableAt_id
    rw [h, hdd]
    simp [← h0 x, divergenceAt]
  have hLs : ContDiff ℝ ∞ (sumSecondPartialsAt (W s)) := by
    rw [laplacianAt_eq_sum hw]
    exact ContDiff.sum fun i _ => contDiff_partial (contDiff_partial hw _) _
  have hDs : ContDiff ℝ ∞ (fun y => advectionAt (W s) y) :=
    (hw.fderiv_right (m := ∞) succ_le_smooth).clm_apply hw
  have hDdiv : divergenceAt (fun y => advectionAt (W s) y) x = pressureSource W s x := by
    show divergenceAt (fun z => fderiv ℝ (W s) z (W s z)) x = _
    rw [divergence_fderiv_apply hw (hw.differentiable (by simp) x), hdd, trace_comp_self]
    simp [pressureSource]
  have hres : gradientAt (q s) = fun y => -(deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y +
      (1 / 2 : ℝ) • fderiv ℝ (W s) y y - sumSecondPartialsAt (W s) y + advectionAt (W s) y) := by
    funext y
    have h := hW.residual s y
    unfold SimilarityResidual at h
    exact eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans h)
  have key : HasFDerivAt (fun y => -(deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y +
      (1 / 2 : ℝ) • fderiv ℝ (W s) y y - sumSecondPartialsAt (W s) y + advectionAt (W s) y))
      (-(fderiv ℝ (fun y => deriv (fun σ => W σ y) s) x + (1 / 2 : ℝ) • fderiv ℝ (W s) x +
        (1 / 2 : ℝ) • fderiv ℝ (fun y => fderiv ℝ (W s) y y) x - fderiv ℝ (sumSecondPartialsAt (W s)) x +
        fderiv ℝ (fun y => advectionAt (W s) y) x)) x :=
    (((((hAs.differentiable (by simp) x).hasFDerivAt.add
      ((hw.differentiable (by simp) x).hasFDerivAt.const_smul (1 / 2 : ℝ))).add
      ((hCs.differentiable (by simp) x).hasFDerivAt.const_smul (1 / 2 : ℝ))).sub
      (hLs.differentiable (by simp) x).hasFDerivAt).add
      (hDs.differentiable (by simp) x).hasFDerivAt).neg
  rw [laplacian_eq_divergence_gradient hp, hres, divergenceAt_eq_traceMap, key.fderiv]
  simp only [map_neg, map_add, map_sub, map_smul, ← divergenceAt_eq_traceMap]
  rw [hAdiv, h0 x, hCdiv, divergence_laplacian_eq_zero hw h0 x, hDdiv]
  simp

end Breakdown.FarField

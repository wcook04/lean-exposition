import Breakdown.CertTorus.DecayStatements

open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

namespace Internal.DivDivSource

lemma top_add_one_le_top : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  exact_mod_cast le_rfl

lemma differentiable_fderiv_of_smooth {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : Space → G} (hg : ContDiff ℝ ∞ g) : Differentiable ℝ (fderiv ℝ g) :=
  (hg.fderiv_right (m := ∞) top_add_one_le_top).differentiable (by simp)

lemma coord_hasFDerivAt {U : Space → Space} {x : Space} (hU : DifferentiableAt ℝ U x)
    (k : Fin 3) :
    HasFDerivAt (fun y => U y k)
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) k).comp (fderiv ℝ U x)) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) k).hasFDerivAt.comp x hU.hasFDerivAt

lemma slot_hasFDerivAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : Space → G} {x : Space} (hg : DifferentiableAt ℝ (fderiv ℝ g) x) (b : Space) :
    HasFDerivAt (fun y => fderiv ℝ g y b)
      ((ContinuousLinearMap.apply ℝ G b).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
  (ContinuousLinearMap.apply ℝ G b).hasFDerivAt.comp x hg.hasFDerivAt

lemma slot_coord_hasFDerivAt {V : Space → Space} (hV : ContDiff ℝ ∞ V) (b : Space) (k : Fin 3)
    (x : Space) :
    HasFDerivAt (fun y => fderiv ℝ V y b k)
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) k).comp
        ((ContinuousLinearMap.apply ℝ Space b).comp (fderiv ℝ (fderiv ℝ V) x))) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) k).hasFDerivAt.comp x
    (slot_hasFDerivAt (differentiable_fderiv_of_smooth hV x) b)

lemma product_fderiv_apply {V : Space → Space} (hV : Differentiable ℝ V) (i j : Fin 3)
    (x b : Space) :
    fderiv ℝ (fun y => V y i * V y j) x b =
      V x i * fderiv ℝ V x b j + fderiv ℝ V x b i * V x j := by
  have hP : HasFDerivAt (fun y => V y i * V y j) _ x :=
    (coord_hasFDerivAt (hV x) i).mul (coord_hasFDerivAt (hV x) j)
  rw [hP.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, PiLp.proj_apply]
  ring

lemma product_second_apply {V : Space → Space} (hV : ContDiff ℝ ∞ V) (i j : Fin 3)
    (z a b : Space) :
    iteratedFDeriv ℝ 2 (fun y => V y i * V y j) z ![a, b] =
      V z i * fderiv ℝ (fderiv ℝ V) z a b j + fderiv ℝ V z a i * fderiv ℝ V z b j +
        (fderiv ℝ V z b i * fderiv ℝ V z a j + V z j * fderiv ℝ (fderiv ℝ V) z a b i) := by
  have hV1 : Differentiable ℝ V := hV.differentiable (by simp)
  have hc : ∀ k : Fin 3, ContDiff ℝ ∞ (fun y => V y k) := fun k =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) k).contDiff.comp hV
  have hg : ContDiff ℝ ∞ (fun y => V y i * V y j) := (hc i).mul (hc j)
  have e1 : fderiv ℝ (fderiv ℝ (fun y => V y i * V y j)) z a b =
      fderiv ℝ (fun y => fderiv ℝ (fun x => V x i * V x j) y b) z a := by
    rw [(slot_hasFDerivAt (differentiable_fderiv_of_smooth hg z) b).fderiv]
    rfl
  have e2 : (fun y => fderiv ℝ (fun x => V x i * V x j) y b) =
      fun y => V y i * fderiv ℝ V y b j + fderiv ℝ V y b i * V y j :=
    funext fun y => product_fderiv_apply hV1 i j y b
  have hT : HasFDerivAt (fun y => V y i * fderiv ℝ V y b j + fderiv ℝ V y b i * V y j) _ z :=
    ((coord_hasFDerivAt (hV1 z) i).mul (slot_coord_hasFDerivAt hV b j z)).add
    ((slot_coord_hasFDerivAt hV b i z).mul (coord_hasFDerivAt (hV1 z) j))
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e1, e2, hT.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, PiLp.proj_apply,
    ContinuousLinearMap.apply_apply]
  ring

lemma sum_second_eq_zero {V : Space → Space} (hV : ContDiff ℝ ∞ V)
    (hdiv : ∀ y, divergenceAt V y = 0) (z a : Space) :
    ∑ k : Fin 3, fderiv ℝ (fderiv ℝ V) z a (unitVector k) k = 0 := by
  have hS : HasFDerivAt (fun y => ∑ k ∈ Finset.univ, fderiv ℝ V y (unitVector k) k) _ z :=
    HasFDerivAt.sum (u := Finset.univ)
    (fun k (_ : k ∈ Finset.univ) => slot_coord_hasFDerivAt hV (unitVector k) k z)
  have hc : (fun y => ∑ k ∈ Finset.univ, fderiv ℝ V y (unitVector k) k) = fun _ => (0 : ℝ) :=
    funext hdiv
  rw [hc] at hS
  have h0 := congrArg (fun L => L a) (hS.unique (hasFDerivAt_const (0 : ℝ) z))
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, ContinuousLinearMap.apply_apply,
    _root_.zero_apply] at h0
  exact h0

end Internal.DivDivSource

open Internal.DivDivSource in
theorem pressureSourceDivDiv_holds : PressureSourceDivDiv := by
  intro W q P R hW s z
  have hw : ContDiff ℝ ∞ (W s) := hW.smooth_field.comp (contDiff_const.prodMk contDiff_id)
  have hdiv : ∀ y, divergenceAt (W s) y = 0 := hW.divergence s
  have hsym : IsSymmSndFDerivAt ℝ (W s) z := hw.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top)
  have h1 : ∑ i : Fin 3, ∑ j : Fin 3,
      W s z i * fderiv ℝ (fderiv ℝ (W s)) z (unitVector i) (unitVector j) j = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, sum_second_eq_zero hw hdiv, mul_zero]
  have h2 : ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (W s) z (unitVector i) i * fderiv ℝ (W s) z (unitVector j) j = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum]
    have h := hdiv z
    simp only [divergenceAt] at h
    rw [h, mul_zero]
  have h3 : ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (W s) z (unitVector j) i * fderiv ℝ (W s) z (unitVector i) j =
        pressureSource W s z := by
    simp only [pressureSource]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h4 : ∑ i : Fin 3, ∑ j : Fin 3,
      W s z j * fderiv ℝ (fderiv ℝ (W s)) z (unitVector i) (unitVector j) i = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum]
    have h : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W s)) z (unitVector i) (unitVector j) i =
        ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W s)) z (unitVector j) (unitVector i) i :=
      Finset.sum_congr rfl fun i _ => by rw [hsym]
    rw [h, sum_second_eq_zero hw hdiv, mul_zero]
  simp only [divDivSource, pairTensor, tensorField, product_second_apply hw,
    Finset.sum_add_distrib]
  rw [h1, h2, h3, h4]
  ring

end Breakdown.FarField

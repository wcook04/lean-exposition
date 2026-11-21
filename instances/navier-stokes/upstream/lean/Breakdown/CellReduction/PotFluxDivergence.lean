import Breakdown.CellReduction.PotentialShape

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (radialVec polarVecQ)

def pointDivergence (V : Space → Fin 3 → ℂ) (y : Space) : ℂ :=
  ∑ i : Fin 3, fderiv ℝ (fun x => V x i) y (unitVector i)

def HasWeakPointDivergence (V : Space → Fin 3 → ℂ) : Prop :=
  (∀ i : Fin 3, LocallyIntegrable (fun y => V y i)) ∧
    (∀ᵐ y, ∀ i : Fin 3, DifferentiableAt ℝ (fun x => V x i) y) ∧
    LocallyIntegrable (pointDivergence V) ∧
    ∀ φ, IsTestFunction φ →
      ∫ y, (φ y : ℂ) * pointDivergence V y =
        -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * V y i

def RadialFluxPartWeak : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F →
    ∀ κ ∈ F.keys, ∀ (c : PotComponent) (σ : ℝ),
      HasWeakPointDivergence (fun y i => componentValue P κ (F.data κ).radialFlux c σ y * (radialVec y i : ℂ))

def PolarFluxPartWeak : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F →
    ∀ κ ∈ F.keys, ∀ (c : PotComponent) (σ : ℝ),
      HasWeakPointDivergence (fun y i => componentValue P κ (F.data κ).polarFlux c σ y * (polarVecQ y i : ℂ))

namespace Internal

theorem integrable_test_mul {f : Space → ℂ} (hf : LocallyIntegrable f) {φ : Space → ℝ}
    (hφ : IsTestFunction φ) : Integrable (fun y => (φ y : ℂ) * f y) := by
  have h := hf.integrable_smul_left_of_hasCompactSupport (g := fun y => (φ y : ℂ))
    (Complex.continuous_ofReal.comp hφ.1.continuous) (hφ.2.comp_left Complex.ofReal_zero)
  simpa only [smul_eq_mul] using h

theorem integrable_testDeriv_mul {f : Space → ℂ} (hf : LocallyIntegrable f) {φ : Space → ℝ}
    (hφ : IsTestFunction φ) (i : Fin 3) :
    Integrable (fun y => (fderiv ℝ φ y (unitVector i) : ℂ) * f y) := by
  have hc : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun y => ((fderiv ℝ φ y (unitVector i) : ℝ) : ℂ)) :=
    (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => ((L (unitVector i) : ℝ) : ℂ)) (by simp)
  have h := hf.integrable_smul_left_of_hasCompactSupport
    (g := fun y => ((fderiv ℝ φ y (unitVector i) : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hc) hs
  simpa only [smul_eq_mul] using h

theorem integrable_testDeriv_sum {V : Space → Fin 3 → ℂ} (hV : ∀ i, LocallyIntegrable (fun y => V y i))
    {φ : Space → ℝ} (hφ : IsTestFunction φ) :
    Integrable (fun y => ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * V y i) :=
  integrable_finsetSum _ fun i _ => integrable_testDeriv_mul (hV i) hφ i

theorem pointDivergence_linComb {ι : Type*} (s : Finset ι) (lam : ι → ℂ) (V : ι → Space → Fin 3 → ℂ)
    (y : Space) (h : ∀ j ∈ s, ∀ i, DifferentiableAt ℝ (fun x => V j x i) y) :
    pointDivergence (fun x i => ∑ j ∈ s, lam j * V j x i) y = ∑ j ∈ s, lam j * pointDivergence (V j) y := by
  unfold pointDivergence
  have hd : ∀ i : Fin 3, fderiv ℝ (fun x => ∑ j ∈ s, lam j * V j x i) y =
      ∑ j ∈ s, lam j • fderiv ℝ (fun x => V j x i) y := by
    intro i
    rw [fderiv_fun_sum (A := fun j x => lam j * V j x i) (fun j hj => (h j hj i).const_mul (lam j))]
    exact Finset.sum_congr rfl fun j hj => fderiv_const_mul (h j hj i) (lam j)
  simp only [hd, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem differentiableAt_linComb {ι : Type*} (s : Finset ι) (lam : ι → ℂ) (V : ι → Space → Fin 3 → ℂ)
    (y : Space) (h : ∀ j ∈ s, ∀ i, DifferentiableAt ℝ (fun x => V j x i) y) (i : Fin 3) :
    DifferentiableAt ℝ (fun x => ∑ j ∈ s, lam j * V j x i) y :=
  DifferentiableAt.fun_sum fun j hj => (h j hj i).const_mul (lam j)

theorem hasWeakPointDivergence_linComb {ι : Type*} (s : Finset ι) (lam : ι → ℂ) (V : ι → Space → Fin 3 → ℂ)
    (h : ∀ j ∈ s, HasWeakPointDivergence (V j)) :
    HasWeakPointDivergence (fun x i => ∑ j ∈ s, lam j * V j x i) := by
  have hdiff : ∀ᵐ y, ∀ j ∈ s, ∀ i, DifferentiableAt ℝ (fun x => V j x i) y :=
    (Filter.eventually_all_finset s).2 fun j hj => (h j hj).2.1
  have hpd : ∀ᵐ y, pointDivergence (fun x i => ∑ j ∈ s, lam j * V j x i) y =
      ∑ j ∈ s, lam j * pointDivergence (V j) y :=
    hdiff.mono fun y hy => pointDivergence_linComb s lam V y hy
  have hloc : LocallyIntegrable (fun y => ∑ j ∈ s, lam j * pointDivergence (V j) y) :=
    locallyIntegrable_finsetSum s fun j hj => (h j hj).2.2.1.continuous_mul continuous_const
  refine ⟨fun i => ?_, hdiff.mono fun y hy i => differentiableAt_linComb s lam V y hy i,
    hloc.congr (hpd.mono fun y hy => hy.symm), fun φ hφ => ?_⟩
  · exact locallyIntegrable_finsetSum s fun j hj => ((h j hj).1 i).continuous_mul continuous_const
  · have e1 : ∫ y, (φ y : ℂ) * pointDivergence (fun x i => ∑ j ∈ s, lam j * V j x i) y =
        ∫ y, ∑ j ∈ s, lam j * ((φ y : ℂ) * pointDivergence (V j) y) := by
      refine integral_congr_ae (hpd.mono fun y hy => ?_)
      simp only [hy, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (∑ j ∈ s, lam j * V j y i) =
        ∫ y, ∑ j ∈ s, lam j * ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * V j y i := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, integral_finsetSum s fun j hj => (integrable_test_mul (h j hj).2.2.1 hφ).const_mul (lam j),
      integral_finsetSum s fun j hj => (integrable_testDeriv_sum (h j hj).1 hφ).const_mul (lam j),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_const_mul, integral_const_mul, (h j hj).2.2.2 φ hφ]
    ring

end Internal

namespace Internal

def entryMap (a i : Fin 3) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (unitVector a)

theorem entryMap_apply (a i : Fin 3) (v : Space) (b : Fin 3) :
    entryMap a i v b = v i * (if b = a then 1 else 0) := by
  simp [entryMap, unitVector]

theorem eq_sum_entryMap (K : Space → (Space →L[ℝ] Space)) (k : Space → Fin 3 → Fin 3 → ℝ)
    (hK : ∀ y v a, K y v a = ∑ i : Fin 3, k y a i * v i) :
    K = fun y => ∑ a : Fin 3, ∑ i : Fin 3, k y a i • entryMap a i := by
  funext y
  ext v b
  rw [hK]
  have e : ((∑ a : Fin 3, ∑ i : Fin 3, k y a i • entryMap a i) v) b =
      ∑ a : Fin 3, ∑ i : Fin 3, k y a i * entryMap a i v b := by
    simp
  rw [e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [entryMap_apply, mul_comm]

theorem matrixDivergence_of_entries (K : Space → (Space →L[ℝ] Space)) (k : Space → Fin 3 → Fin 3 → ℝ)
    (hK : ∀ y v a, K y v a = ∑ i : Fin 3, k y a i * v i) (y : Space)
    (h : ∀ a i, DifferentiableAt ℝ (fun x => k x a i) y) (a : Fin 3) :
    matrixDivergence K y a = ∑ i : Fin 3, fderiv ℝ (fun x => k x a i) y (unitVector i) := by
  have hF : HasFDerivAt K (∑ a : Fin 3, ∑ i : Fin 3, (fderiv ℝ (fun x => k x a i) y).smulRight (entryMap a i)) y := by
    rw [eq_sum_entryMap K k hK]
    exact HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun i _ => (h a i).hasFDerivAt.smul_const _
  unfold matrixDivergence
  rw [hF.fderiv]
  simp [entryMap_apply, unitVector]

end Internal

namespace Internal

theorem locallyIntegrable_re {f : Space → ℂ} (hf : LocallyIntegrable f) :
    LocallyIntegrable (fun y => (f y).re) := by
  have h := Complex.reCLM.locallyIntegrableOn_comp (hf.locallyIntegrableOn Set.univ)
  rw [locallyIntegrableOn_univ] at h
  exact h

theorem hasFDerivAt_re {f : Space → ℂ} {y : Space} (h : DifferentiableAt ℝ f y) :
    HasFDerivAt (fun x => (f x).re) (Complex.reCLM.comp (fderiv ℝ f y)) y :=
  Complex.reCLM.hasFDerivAt.comp y h.hasFDerivAt

theorem matrixDivergence_of_rows (K : Space → (Space →L[ℝ] Space)) (W : Fin 3 → Space → Fin 3 → ℂ)
    (hK : ∀ y v a, K y v a = ∑ i : Fin 3, (W a y i).re * v i) (y : Space)
    (h : ∀ a i, DifferentiableAt ℝ (fun x => W a x i) y) (a : Fin 3) :
    matrixDivergence K y a = (pointDivergence (W a) y).re := by
  rw [matrixDivergence_of_entries K (fun y a i => (W a y i).re) hK y
    (fun a i => (hasFDerivAt_re (h a i)).differentiableAt) a]
  simp only [(hasFDerivAt_re (h _ _)).fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Complex.reCLM_apply, pointDivergence, Complex.re_sum]

theorem weakMatrixDivergence_of_rows (K : Space → (Space →L[ℝ] Space)) (W : Fin 3 → Space → Fin 3 → ℂ)
    (hK : ∀ y v a, K y v a = ∑ i : Fin 3, (W a y i).re * v i) (hW : ∀ a, HasWeakPointDivergence (W a)) :
    IsWeakMatrixDivergence K (matrixDivergence K) := by
  have hreLoc : ∀ a i, LocallyIntegrable (fun y => (W a y i).re) := fun a i => locallyIntegrable_re ((hW a).1 i)
  have hdiff : ∀ᵐ y, ∀ a i, DifferentiableAt ℝ (fun x => W a x i) y :=
    ae_all_iff.2 fun a => (hW a).2.1
  have hd : ∀ᵐ y, matrixDivergence K y = ∑ a : Fin 3, (pointDivergence (W a) y).re • unitVector a := by
    refine hdiff.mono fun y hy => ?_
    ext b
    rw [matrixDivergence_of_rows K W hK y hy b]
    simp [unitVector, Pi.single_apply]
  refine ⟨?_, ?_, fun φ hφ c => ?_⟩
  · rw [eq_sum_entryMap K (fun y a i => (W a y i).re) hK]
    exact locallyIntegrable_finsetSum _ fun a _ => locallyIntegrable_finsetSum _ fun i _ =>
      (hreLoc a i).smul_continuous continuous_const
  · refine LocallyIntegrable.congr ?_ (hd.mono fun y hy => hy.symm)
    exact locallyIntegrable_finsetSum _ fun a _ =>
      (locallyIntegrable_re (hW a).2.2.1).smul_continuous continuous_const
  · have e1 : ∫ y, φ y * matrixDivergence K y c = ∫ y, ((φ y : ℂ) * pointDivergence (W c) y).re := by
      refine integral_congr_ae (hdiff.mono fun y hy => ?_)
      simp only [matrixDivergence_of_rows K W hK y hy c, Complex.re_ofReal_mul]
    have e2 : ∫ y, ((φ y : ℂ) * pointDivergence (W c) y).re = (∫ y, (φ y : ℂ) * pointDivergence (W c) y).re :=
      integral_re (integrable_test_mul (hW c).2.2.1 hφ)
    have e3 : ∫ y, ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K y (unitVector i) c =
        ∫ y, (∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * W c y i).re := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [hK, unitVector, Complex.re_sum]
    have e4 : ∫ y, (∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * W c y i).re =
        (∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * W c y i).re :=
      integral_re (integrable_testDeriv_sum (hW c).1 hφ)
    rw [e1, e2, e3, e4, (hW c).2.2.2 φ hφ, Complex.neg_re]

theorem hasWeakPointDivergence_add {V W : Space → Fin 3 → ℂ} (hV : HasWeakPointDivergence V)
    (hW : HasWeakPointDivergence W) : HasWeakPointDivergence (fun x i => V x i + W x i) := by
  have h := hasWeakPointDivergence_linComb (Finset.univ : Finset Bool) (fun _ => 1)
    (fun b => if b then V else W) (fun b _ => by cases b <;> simpa)
  have e : (fun x i => ∑ j ∈ (Finset.univ : Finset Bool), (1 : ℂ) * (if j then V else W) x i) =
      fun x i => V x i + W x i := by
    funext x i
    simp
  rw [e] at h
  exact h

def allComponents : Finset PotComponent := {.plus, .minus, .axial}

def componentCoef (a : Fin 3) (c : PotComponent) : ℂ :=
  coordsOfComponents (if c = .plus then 1 else 0) (if c = .minus then 1 else 0) (if c = .axial then 1 else 0) a

theorem coords_eq_sum (g : PotComponent → ℂ) (a : Fin 3) :
    coordsOfComponents (g .plus) (g .minus) (g .axial) a = ∑ c ∈ allComponents, componentCoef a c * g c := by
  simp only [allComponents, componentCoef]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  fin_cases a <;> simp [coordsOfComponents] <;> first | ring1 | linear_combination (g .plus / 2) * Complex.inv_I

theorem sum_coords_eq (keys : Finset FieldKey) (g : FieldKey → PotComponent → ℂ) (a : Fin 3) :
    ∑ κ ∈ keys, coordsOfComponents (g κ .plus) (g κ .minus) (g κ .axial) a =
      ∑ j ∈ keys ×ˢ allComponents, componentCoef a j.2 * g j.1 j.2 := by
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun κ _ => coords_eq_sum (g κ) a

def keyFlux (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (j : FieldKey × PotComponent) :
    Space → Fin 3 → ℂ :=
  fluxVector P j.1 (F.data j.1) j.2 σ

def fluxRow (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (a : Fin 3) (y : Space) (i : Fin 3) : ℂ :=
  ∑ κ ∈ F.keys, coordsOfComponents (fluxVector P κ (F.data κ) .plus σ y i)
    (fluxVector P κ (F.data κ) .minus σ y i) (fluxVector P κ (F.data κ) .axial σ y i) a

theorem fluxRow_eq (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (a : Fin 3) :
    fluxRow P F σ a = fun y i => ∑ j ∈ F.keys ×ˢ allComponents,
      componentCoef a j.2 * keyFlux P F σ j y i := by
  funext y i
  exact sum_coords_eq F.keys (fun κ c => fluxVector P κ (F.data κ) c σ y i) a

theorem keyFlux_eq (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (j : FieldKey × PotComponent) :
    keyFlux P F σ j = fun y i => componentValue P j.1 (F.data j.1).radialFlux j.2 σ y * (radialVec y i : ℂ) +
      componentValue P j.1 (F.data j.1).polarFlux j.2 σ y * (polarVecQ y i : ℂ) := by
  funext y i
  rfl

theorem fluxMap_apply_eq (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (y v : Space) (a : Fin 3) :
    fluxMap P F σ y v a = ∑ i : Fin 3, (fluxRow P F σ a y i).re * v i := by
  simp [fluxMap, fluxRow, fluxEntry, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

end Internal

open Internal in
theorem matrixDivergence_fluxMap_apply (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (y : Space)
    (h : ∀ κ ∈ F.keys, ∀ c : PotComponent, ∀ i : Fin 3,
      DifferentiableAt ℝ (fun x => fluxVector P κ (F.data κ) c σ x i) y) (a : Fin 3) :
    matrixDivergence (fluxMap P F σ) y a =
      (∑ κ ∈ F.keys, coordsOfComponents
        (∑ i : Fin 3, fderiv ℝ (fun x => fluxVector P κ (F.data κ) .plus σ x i) y (unitVector i))
        (∑ i : Fin 3, fderiv ℝ (fun x => fluxVector P κ (F.data κ) .minus σ x i) y (unitVector i))
        (∑ i : Fin 3, fderiv ℝ (fun x => fluxVector P κ (F.data κ) .axial σ x i) y (unitVector i)) a).re := by
  have hj : ∀ j ∈ F.keys ×ˢ allComponents, ∀ i, DifferentiableAt ℝ (fun x => keyFlux P F σ j x i) y :=
    fun j hj i => h j.1 (Finset.mem_product.1 hj).1 j.2 i
  have hrow : ∀ b i, DifferentiableAt ℝ (fun x => fluxRow P F σ b x i) y := by
    intro b i
    rw [fluxRow_eq]
    exact differentiableAt_linComb (F.keys ×ˢ allComponents) (fun j => componentCoef b j.2) (keyFlux P F σ) y hj i
  rw [matrixDivergence_of_rows _ (fluxRow P F σ) (fluxMap_apply_eq P F σ) y hrow a, fluxRow_eq,
    pointDivergence_linComb (F.keys ×ˢ allComponents) (fun j => componentCoef a j.2) (keyFlux P F σ) y hj]
  exact congrArg Complex.re (sum_coords_eq F.keys (fun κ c => pointDivergence (keyFlux P F σ (κ, c)) y) a).symm

open Internal in
theorem fluxMap_weakMatrixDivergence_of (hrad : RadialFluxPartWeak) (hpol : PolarFluxPartWeak)
    (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P) (hF : IsPotentialSeries F) (σ : ℝ) :
    IsWeakMatrixDivergence (fluxMap P F σ) (matrixDivergence (fluxMap P F σ)) := by
  refine weakMatrixDivergence_of_rows _ (fluxRow P F σ) (fluxMap_apply_eq P F σ) fun a => ?_
  rw [fluxRow_eq]
  refine hasWeakPointDivergence_linComb (F.keys ×ˢ allComponents) (fun j => componentCoef a j.2) (keyFlux P F σ)
    fun j hj => ?_
  have hκ := (Finset.mem_product.1 hj).1
  rw [keyFlux_eq]
  exact hasWeakPointDivergence_add (hrad P F hP hF j.1 hκ j.2 σ) (hpol P F hP hF j.1 hκ j.2 σ)

end PotentialShape

end Breakdown

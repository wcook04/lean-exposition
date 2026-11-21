import Breakdown.Base.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

open scoped Classical

abbrev CSpace := EuclideanSpace ℂ (Fin 3)

abbrev L2C := Lp (α := Space) CSpace 2

abbrev L2R := Lp (α := Space) Space 2

instance factOneLeSix : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

abbrev L6R := Lp (α := Space) Space 6

def toLpOrZero {F : Type*} [NormedAddCommGroup F] (p : ℝ≥0∞) (f : Space → F) :
    Lp (α := Space) F p :=
  if h : MemLp f p volume then h.toLp f else 0

def complexifyVec : Space →L[ℝ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => ((z i : ℝ) : ℂ))
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }

def realVec : CSpace →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => (z i).re)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }

def conjVec : CSpace →L[ℝ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => star (z i))
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }

def cmul (c : ℂ) : CSpace →L[ℝ] CSpace :=
  (c • ContinuousLinearMap.id ℂ CSpace).restrictScalars ℝ

def complexify : L2R →L[ℝ] L2C := ContinuousLinearMap.compLpL 2 volume complexifyVec

def realPart : L2C →L[ℝ] L2R := ContinuousLinearMap.compLpL 2 volume realVec

def freqTrL2 : L2C ≃ₗᵢ[ℂ] L2C := Lp.fourierTransformₗᵢ Space CSpace

def freqTrR : L2C →L[ℝ] L2C :=
  (freqTrL2.toContinuousLinearEquiv : L2C →L[ℂ] L2C).restrictScalars ℝ

def freqTrInvR : L2C →L[ℝ] L2C :=
  (freqTrL2.symm.toContinuousLinearEquiv : L2C →L[ℂ] L2C).restrictScalars ℝ

def toPhys : L2C →L[ℝ] L2R := realPart ∘L freqTrInvR

def IsRealizedBy (T : L2C →L[ℝ] L2C) (A : Space → Space) (F : Space → CSpace →L[ℝ] CSpace) :
    Prop :=
  ∀ f : L2C, (T f : Space → CSpace) =ᵐ[volume] fun ξ => F ξ (f (A ξ))

def fieldOp (A : Space → Space) (F : Space → CSpace →L[ℝ] CSpace) : L2C →L[ℝ] L2C :=
  if h : ∃ T, IsRealizedBy T A F then h.choose else 0

def freqVec (ξ : Space) : CSpace := complexifyVec ξ

def longitudinal (ξ : Space) : CSpace →L[ℝ] CSpace :=
  ((‖ξ‖ ^ 2)⁻¹ : ℝ) •
    ((ContinuousLinearMap.smulRight (innerSL ℂ (freqVec ξ)) (freqVec ξ)).restrictScalars ℝ)

def reflConj : L2C →L[ℝ] L2C := fieldOp (fun ξ => -ξ) (fun _ => conjVec)

def Sig : Submodule ℝ L2C :=
  LinearMap.ker ((reflConj - ContinuousLinearMap.id ℝ L2C : L2C →L[ℝ] L2C) : L2C →ₗ[ℝ] L2C) ⊓
    LinearMap.ker ((fieldOp id longitudinal : L2C →L[ℝ] L2C) : L2C →ₗ[ℝ] L2C)

theorem isClosed_sig : IsClosed (Sig : Set L2C) :=
  (ContinuousLinearMap.isClosed_ker _).inter (ContinuousLinearMap.isClosed_ker _)

instance : CompleteSpace Sig := isClosed_sig.completeSpace_coe

abbrev X := Sig

def restrictX (T : L2C →L[ℝ] L2C) : X →L[ℝ] X :=
  if h : ∀ x ∈ Sig, T x ∈ Sig then (T ∘L Sig.subtypeL).codRestrict Sig (fun x => h x x.2) else 0

def heatFactor (t : ℝ) (ξ : Space) : ℝ := Real.exp (-(4 * π ^ 2 * max t 0 * ‖ξ‖ ^ 2))

def heatL2 (t : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace)

def heatX (t : ℝ) : X →L[ℝ] X := restrictX (heatL2 t)

def dilL2 (μ : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp (fun ξ => (Real.sqrt μ)⁻¹ • ξ) (fun _ => (Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace)

def dilX (μ : ℝ) : X →L[ℝ] X := if 0 < μ then restrictX (dilL2 μ) else 0

def rotC (R : Space ≃ₗᵢ[ℝ] Space) : CSpace →L[ℝ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) * z j)
      map_add' := fun a b => by ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by ext i; simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring) }

def rotL2 (R : Space ≃ₗᵢ[ℝ] Space) : L2C →L[ℝ] L2C := fieldOp (fun ξ => R.symm ξ) (fun _ => rotC R)

def rotX (R : Space ≃ₗᵢ[ℝ] Space) : X ≃ₗᵢ[ℝ] X :=
  if h : ∃ E : X ≃ₗᵢ[ℝ] X, ∀ x, (E x : L2C) = rotL2 R x then h.choose else LinearIsometryEquiv.refl ℝ X

def gradSymbol (k : Fin 3) (ξ : Space) : ℂ := -(Complex.I * ((ξ k : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ))

def derivSymbol (j : Fin 3) (ξ : Space) : ℂ := Complex.I * ((ξ j : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ)

def partialField (f : Space → Space) (k : Fin 3) : Space → Space := fun x => fderiv ℝ f x (unitVector k)

def ofGrad (f : Space → Space) : L2C :=
  ∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (freqTrR (complexify (toLpOrZero 2 (partialField f k))))

def embedX (f : Space → Space) : X := if h : ofGrad f ∈ Sig then ⟨ofGrad f, h⟩ else 0

def partialX (j : Fin 3) : X →L[ℝ] L2R :=
  toPhys ∘L fieldOp id (fun ξ => cmul (derivSymbol j ξ)) ∘L Sig.subtypeL

def VelocitySpec (V : X →L[ℝ] L6R) : Prop :=
  ∀ φ, IsTestField φ → V (embedX φ) = toLpOrZero 6 φ

def velocity : X →L[ℝ] L6R := if h : ∃ V, VelocitySpec V then h.choose else 0

def phiFactor (τ : ℝ) (ξ : Space) : ℝ := 2 * π * ‖ξ‖ * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))

def phiX (τ : ℝ) : X →L[ℝ] L2R :=
  toPhys ∘L fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) ∘L Sig.subtypeL

def trilinear (u v : X) (w : Space → Space) : ℝ :=
  ∫ x, ∑ j : Fin 3, (velocity u : Space → Space) x j * inner ℝ ((partialX j v : Space → Space) x) (w x)

def bilinForm (τ : ℝ) (u v ψ : X) : ℝ :=
  -(1 / 2 : ℝ) * (trilinear u v (phiX τ ψ) + trilinear v u (phiX τ ψ))

def BilinSpec (τ : ℝ) (B : X →L[ℝ] X →L[ℝ] X) : Prop :=
  ∀ u v ψ, inner ℝ (B u v) ψ = bilinForm τ u v ψ

def bilinX (τ : ℝ) : X →L[ℝ] X →L[ℝ] X := if h : 0 < τ ∧ ∃ B, BilinSpec τ B then h.2.choose else 0

def negSsp (φ : Space → Space) : Space → Space := fun x => -sumSecondPartialsAt φ x

def sspFactor (ξ : Space) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

def IsSspOf (χ ψ : X) : Prop := ∀ᵐ ξ ∂volume, (ψ : L2C) ξ = sspFactor ξ • (χ : L2C) ξ

def IsHalfSspOf (g h : X) : Prop := ∀ᵐ ξ ∂volume, (h : L2C) ξ = (2 * π * ‖ξ‖) • (g : L2C) ξ

def testSpan : Submodule ℝ X := Submodule.span ℝ {x | ∃ φ, IsTestField φ ∧ embedX φ = x}

end Breakdown.Freq

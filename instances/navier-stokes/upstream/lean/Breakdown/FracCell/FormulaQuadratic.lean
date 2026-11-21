import Breakdown.FracCell.StFormulaProof

open Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace FormulaQuadraticInternal

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

section Closure

variable {ι : Type} [Fintype ι]

theorem quad_add {f g : (ι → ℝ) → ℝ} (hf : IsRealQuadratic f) (hg : IsRealQuadratic g) :
    IsRealQuadratic (fun w => f w + g w) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨M', hM'⟩ := hg
  exact ⟨M + M', fun w => by beta_reduce; rw [hM, hM', Matrix.add_mulVec, dotProduct_add]⟩

theorem quad_mul (r : ℝ) {f : (ι → ℝ) → ℝ} (hf : IsRealQuadratic f) :
    IsRealQuadratic (fun w => r * f w) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨r • M, fun w => by beta_reduce; rw [hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]⟩

theorem quad_sub {f g : (ι → ℝ) → ℝ} (hf : IsRealQuadratic f) (hg : IsRealQuadratic g) :
    IsRealQuadratic (fun w => f w - g w) := by
  have h := quad_add hf (quad_mul (-1) hg)
  convert h using 2 with w
  ring

theorem quad_div {f : (ι → ℝ) → ℝ} (hf : IsRealQuadratic f) (r : ℝ) :
    IsRealQuadratic (fun w => f w / r) := by
  have h := quad_mul r⁻¹ hf
  convert h using 2 with w
  rw [div_eq_inv_mul]

theorem quad_sum {β : Type} (s : Finset β) (f : β → (ι → ℝ) → ℝ) (hf : ∀ b ∈ s, IsRealQuadratic (f b)) :
    IsRealQuadratic (fun w => ∑ b ∈ s, f b w) := by
  have h : IsRealQuadratic (∑ b ∈ s, f b) :=
    Finset.sum_induction f (fun g => IsRealQuadratic g) (fun a b ha hb => quad_add ha hb)
      ⟨0, fun w => by simp⟩ hf
  convert h using 1
  funext w
  rw [Finset.sum_apply]

theorem quad_of_bilin (B : LinearMap.BilinForm ℝ (ι → ℝ)) {f : (ι → ℝ) → ℝ} (h : ∀ w, f w = B w w) :
    IsRealQuadratic f := by
  classical
  exact ⟨LinearMap.BilinForm.toMatrix' B, fun w => by
    rw [h, ← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix']⟩

theorem quad_sq (g : (ι → ℝ) →ₗ[ℝ] ℝ) : IsRealQuadratic (fun w => g w ^ 2) :=
  quad_of_bilin ((LinearMap.mul ℝ ℝ).compl₁₂ g g) (fun w => by simp [sq])

theorem quad_form {D : Type} [Fintype D] (Φ : Matrix D D ℂ) (u : (ι → ℝ) →ₗ[ℝ] (D → ℂ)) :
    IsRealQuadratic (fun w => quadFormValue Φ (u w)) := by
  refine quad_of_bilin (LinearMap.mk₂ ℝ (fun v w => (star (u v) ⬝ᵥ (Φ *ᵥ u w)).re) ?_ ?_ ?_ ?_)
    (fun w => rfl)
  · intro a b x
    simp [map_add, star_add, add_dotProduct]
  · intro r a x
    simp [map_smul, star_smul, smul_dotProduct]
  · intro a b x
    simp [map_add, Matrix.mulVec_add, dotProduct_add]
  · intro r a x
    simp [map_smul, Matrix.mulVec_smul, dotProduct_smul]

end Closure

section Linear

variable {k N slots : ℕ} {S : CellScalars} (F : CellFormulaInputs k N S) (c : FracCellData k N) (K : CellBox)
  (B : CellBases) (R : CellRows N slots k)

def reLin {X : Type} [Fintype X] (t : X → ℂ) : (X → ℂ) →ₗ[ℝ] ℝ where
  toFun u := (∑ e, t e * u e).re
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply, smul_eq_mul]
    rw [show (∑ e, t e * (↑r * x e)) = ↑r * ∑ e, t e * x e by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring]
    exact Complex.re_ofReal_mul r _

def dotLin {X : Type} [Fintype X] (t : X → ℝ) : (X → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ e, u e * t e
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum, mul_assoc]

def dataMap (h : IsLinearMap ℝ F.coordToData) : (F.Coord → ℝ) →ₗ[ℝ] (F.D → ℂ) :=
  (IsLinearMap.mk' F.coordToData h).comp
    (LinearMap.funLeft ℝ ℝ (Sum.elim (fun s => Sum.inl s) (fun t => Sum.inr (Sum.inl t))))

def scaledMap (g : Fin k → F.Coord) : (F.Coord → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  c.splitVisc • LinearMap.funLeft ℝ ℝ g

def dataVecMap {V : Type} [AddCommGroup V] [Module ℝ V] (U : V →ₗ[ℝ] (F.D → ℂ))
    (κ ζ : V →ₗ[ℝ] (Fin k → ℝ)) : V →ₗ[ℝ] (F.D ⊕ (Fin k ⊕ Fin k) → ℂ) where
  toFun w := F.dataVec (U w) (κ w) (ζ w)
  map_add' x y := by
    funext d
    rcases d with d | i | i <;> simp [CellFormulaInputs.dataVec]
  map_smul' r x := by
    funext d
    rcases d with d | i | i <;> simp [CellFormulaInputs.dataVec, Complex.real_smul]

def augMap {V : Type} [AddCommGroup V] [Module ℝ V] (U : V →ₗ[ℝ] (F.D → ℂ))
    (κ ζ : V →ₗ[ℝ] (Fin k → ℝ)) : V →ₗ[ℝ] (Aug S k → ℂ) where
  toFun w := F.augOfData (U w) (κ w) (ζ w)
  map_add' x y := by
    funext d
    rcases d with d | i | i
    · cases h : F.lowEntry d <;> simp [CellFormulaInputs.augOfData, h]
    · simp [CellFormulaInputs.augOfData]
    · simp [CellFormulaInputs.augOfData]
  map_smul' r x := by
    funext d
    rcases d with d | i | i
    · cases h : F.lowEntry d <;> simp [CellFormulaInputs.augOfData, h]
    · simp [CellFormulaInputs.augOfData, Complex.real_smul]
    · simp [CellFormulaInputs.augOfData, Complex.real_smul]

end Linear

section Residual

variable {k N slots : ℕ} {S : CellScalars} (F : CellFormulaInputs k N S) (c : FracCellData k N) (K : CellBox)
  (B : CellBases) (R : CellRows N slots k)

def residualMap {V : Type} [AddCommGroup V] [Module ℝ V] (U : V →ₗ[ℝ] (F.D → ℂ))
    (κ ζ : V →ₗ[ℝ] (Fin k → ℝ)) (a : Fin N) : V →ₗ[ℝ] ℝ :=
  letI := F.dataFintype; letI := F.dataDecEq;
  (reLin (F.rowData a)).comp U + (dotLin (F.rowKappa a)).comp κ
    - (reLin (rowYVec c K S B R a)).comp (augMap F U κ ζ)

theorem residualMap_apply {V : Type} [AddCommGroup V] [Module ℝ V] (U : V →ₗ[ℝ] (F.D → ℂ))
    (κ ζ : V →ₗ[ℝ] (Fin k → ℝ)) (a : Fin N) (w : V) :
    residualMap F c K B R U κ ζ a w = F.residualValue c K B R a (U w) (κ w) (ζ w) := rfl

end Residual

end FormulaQuadraticInternal

open FormulaQuadraticInternal

theorem formulaQuadratic : FormulaQuadraticStatement := by
  intro k N slots S F c K B R hlin
  let _ := F.dataFintype
  let _ := F.dataDecEq
  let U := dataMap F hlin
  let κ := scaledMap F c (fun i : Fin k => (Sum.inr (Sum.inr (Sum.inl i)) : F.Coord))
  let ζ := scaledMap F c (fun i : Fin k => (Sum.inr (Sum.inr (Sum.inr i)) : F.Coord))
  have key : IsRealQuadratic (fun w : F.Coord → ℝ =>
      (quadFormValue F.localForm (dataVecMap F U κ ζ w)
        - quadFormValue (nearMatrix c K S B R) (augMap F U κ ζ w)
        - quadFormValue (farMatrix S R) (augMap F U κ ζ w) / R.farShare
        + ∑ b : Fin R.reducerCount,
            ((∑ a ∈ R.rowSet, R.reducer b a • residualMap F c K B R U κ ζ a) w) ^ 2) / c.splitVisc) :=
    quad_div (quad_add (quad_sub (quad_sub (quad_form _ _) (quad_form _ _)) (quad_div (quad_form _ _) _))
      (quad_sum _ _ fun b _ => quad_sq _)) _
  convert key using 2 with w
  simp only [CellFormulaInputs.formulaValue, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, residualMap_apply]
  rfl

end CellFormula

end CellCert

end Breakdown

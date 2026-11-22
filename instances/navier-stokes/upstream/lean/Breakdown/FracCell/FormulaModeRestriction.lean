import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.GivenModelModelModes

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

theorem rankOne_zero_vec {ι : Type} : rankOne (0 : ι → ℂ) = 0 := by
  funext e e'
  simp [rankOne]

theorem nearMatrix_yModes {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (R : CellRows N slots k) (Y : Finset ℤ) (hY : Y ⊆ R.yModes) (hcont : S.resolved ∪ S.band ⊆ Y)
    (hvan : ∀ n ∈ R.yModes \ Y, ∀ (j l : ℕ) (a b : Fin 3),
      symVec c K S B n j l a b = 0 ∧ antiVec c K S B n j l a b = 0) :
    nearMatrix c K S B R = nearMatrix c K S B ({ R with yModes := Y } : CellRows N slots k) := by
  unfold nearMatrix
  congr 1
  refine (Finset.sum_subset hY ?_).symm
  intro n hn hnY
  have hv := hvan n (Finset.mem_sdiff.mpr ⟨hn, hnY⟩)
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  split_ifs
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [(hv j l a b).1, (hv j l a b).2, rankOne_zero_vec, smul_zero, smul_zero, add_zero]
  · rfl

theorem exactFormula_systemRows {k N slots : ℕ} {S : CellScalars} (F : CellFormulaInputs k N S) (c : FracCellData k N)
    (K : CellBox) (B : CellBases) (R : CellRows N slots k) (Y : Finset ℤ) (S₀ : Finset LowIndex)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ)
    (hnear : nearMatrix c K S B R = nearMatrix c K S B ({ R with yModes := Y } : CellRows N slots k))
    (hfar : farMatrix S R = farMatrix S ({ R with farSupport := S₀, farKernel := Kr } : CellRows N slots k)) :
    F.exactFormula c K B R =
      F.exactFormula c K B ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k) := by
  have hn : nearMatrix c K S B ({ R with yModes := Y } : CellRows N slots k) =
      nearMatrix c K S B ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k) := rfl
  have hf : farMatrix S ({ R with farSupport := S₀, farKernel := Kr } : CellRows N slots k) =
      farMatrix S ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k) := rfl
  have hr : ∀ a, rowYVec c K S B R a =
      rowYVec c K S B ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k) a :=
    fun a => rfl
  have hv : F.formulaValue c K B R =
      F.formulaValue c K B ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k) := by
    funext w
    simp only [CellFormulaInputs.formulaValue, CellFormulaInputs.residualValue, hnear, hfar, hn, hf, hr]
  funext e e'
  simp only [CellFormulaInputs.exactFormula, hv]

theorem givenLeExact_of_systemRows (α : ℝ) {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k) (C : CellCoords k slots)
    (Y : Finset ℤ) (S₀ : Finset LowIndex) (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ)
    (hnear : nearMatrix c K S B R = nearMatrix c K S B ({ R with yModes := Y } : CellRows N slots k))
    (hfar : farMatrix S R = farMatrix S ({ R with farSupport := S₀, farKernel := Kr } : CellRows N slots k))
    (hsystem : ∀ (s : Fin (systemSkeletonCoords C.layout C.param).card → ℝ)
      (ξ : Fin (systemInteriorCoords C.layout C.param).card → ℝ) (κ' ζ' : Fin k → ℝ),
      quadValue C.given (Sum.elim s (Sum.elim κ' ζ')) ≤
        quadValue ((C.formula c K S B Cl ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k) α).exactFormula
            c K B ({ R with yModes := Y, farSupport := S₀, farKernel := Kr } : CellRows N slots k))
          (Sum.elim (fun i => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inl i))
            (Sum.elim (fun j => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inr j)) (Sum.elim κ' ζ')))) :
    ∀ (s : Fin (systemSkeletonCoords C.layout C.param).card → ℝ)
      (ξ : Fin (systemInteriorCoords C.layout C.param).card → ℝ) (κ' ζ' : Fin k → ℝ),
      quadValue C.given (Sum.elim s (Sum.elim κ' ζ')) ≤
        quadValue ((C.formula c K S B Cl R α).exactFormula c K B R)
          (Sum.elim (fun i => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inl i))
            (Sum.elim (fun j => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inr j)) (Sum.elim κ' ζ'))) := by
  intro s ξ κ' ζ'
  have h := hsystem s ξ κ' ζ'
  rw [exactFormula_systemRows (C.formula c K S B Cl R α) c K B R Y S₀ Kr hnear hfar]
  exact h

theorem turnAdjInv_zero_vec (k : ℝ) : turnAdjInv k 0 = 0 := by
  funext a
  fin_cases a <;> simp [turnAdjInv]

theorem yFoldedOf_eq_zero_of_off_band {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ) (κ ζ : Fin k → ℂ) (n : ℤ)
    (hn : n ∉ S.resolved ∪ S.band) (p : ℝ × ℝ)
    (hA : ∀ i, modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0)
    (hP : ∀ i, modeMat c.order n (c.modelPinField i) p.1 p.2 = 0) :
    yFoldedOf c K S sAt vAt κ ζ n p = 0 := by
  have hr : n ∉ S.resolved := fun h => hn (Finset.mem_union_left _ h)
  have hv : yVelocityOf c K S sAt vAt n p = 0 := by
    funext b
    simp [yVelocityOf, hn, hr]
  unfold yFoldedOf
  rw [if_neg hr, hv]
  funext a b
  simp [foldVelocity, yStrainOf, hn, hr, hA, hP, turnAdjInv_zero_vec]

theorem coef_eq_zero_off_axis (B : CellBases) (K : CellBox) (F : ℝ × ℝ → ℂ)
    (hF : ∀ p : ℝ × ℝ, p.1 ≠ 0 → F p = 0) (j l : ℕ) : B.coef K F j l = 0 := by
  have h0 : (volume : Measure (ℝ × ℝ)) {p | p.1 = 0} = 0 := by
    have hs : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp
    rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  simp only [CellBases.coef]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hae] with p hp
  simp [hF p hp]

theorem symVec_antiVec_eq_zero_of_off_band {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (B : CellBases) (n : ℤ) (hn : n ∉ S.resolved ∪ S.band)
    (hmodel : ∀ i (p : ℝ × ℝ), p.1 ≠ 0 →
      modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0)
    (j l : ℕ) (a b : Fin 3) :
    symVec c K S B n j l a b = 0 ∧ antiVec c K S B n j l a b = 0 := by
  have hy : ∀ a b : Fin 3, yVec c K S B n j l a b = 0 := by
    intro a b
    funext e
    simp only [yVec, yCoef, Pi.zero_apply]
    refine coef_eq_zero_off_axis B K _ (fun p hp => ?_) j l
    rw [yFoldedOf_eq_zero_of_off_band c K S _ _ _ _ n hn p (fun i => (hmodel i p hp).1) (fun i => (hmodel i p hp).2)]
    rfl
  constructor
  · funext e
    simp [symVec, hy]
  · funext e
    simp [antiVec, hy]

theorem modelModes_zero_of_piecewise {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (hm : 0 < c.order) {d J : ℕ}
    (QA QP : Fin k → Fin M.cellCount → Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d)
    (hA : ∀ i, c.modelActuatorGrad i = M.piecewise (fun K => tensorOf c.order (QA i K)))
    (hP : ∀ i, c.modelPinField i = M.piecewise (fun K => tensorOf c.order (QP i K)))
    (n : ℤ) (hβ : ∀ β : Fin (J + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n) :
    ∀ i (p : ℝ × ℝ), p.1 ≠ 0 →
      modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0 := by
  intro i p hp
  rw [hA i, hP i]
  exact ⟨Breakdown.FracInternal.GivenModelModelModes.modes_zero M c.order hm (QA i) p.1 p.2 hp n hβ,
    Breakdown.FracInternal.GivenModelModelModes.modes_zero M c.order hm (QP i) p.1 p.2 hp n hβ⟩

theorem nearMatrix_yModes_of_model {k N slots : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (B : CellBases) (R : CellRows N slots k) (Y : Finset ℤ) (hY : Y ⊆ R.yModes) (hcont : S.resolved ∪ S.band ⊆ Y)
    (hmodel : ∀ n ∈ R.yModes \ Y, ∀ i (p : ℝ × ℝ), p.1 ≠ 0 →
      modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0) :
    nearMatrix c K S B R = nearMatrix c K S B ({ R with yModes := Y } : CellRows N slots k) :=
  nearMatrix_yModes c K S B R Y hY hcont fun n hn j l a b =>
    symVec_antiVec_eq_zero_of_off_band c K S B n (fun h => (Finset.mem_sdiff.mp hn).2 (hcont h)) (hmodel n hn) j l a b

end CellSystem

end CellCert

end Breakdown

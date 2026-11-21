import TorusEuler.TerminalCoefficientTimeProduct
import TorusEuler.EndpointKinetic

/-! Mixed time and label derivative bounds for the actual algebraic mean coefficients. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "MatrixField" => (ℝ → Vec3 → Vec3 →L[ℝ] Vec3)

/-- The adjoint of a real deformation is a bounded linear change on its matrix jets. -/
def terminalRealAdjoint : (Vec3 →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).toContinuousLinearEquiv.toContinuousLinearMap

set_option maxHeartbeats 650000 in
/-- The three algebraic coefficients in the differentiated mean equation
inherit fixed spatial slope and order-independent polynomial amplitudes. -/
theorem exists_terminalMeanCoefficientCost (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (q : ℕ) :
    ∃ CK CΩ CD : ℕ → ℝ,
      (∀ n, 0 ≤ CK n) ∧ (∀ n, 0 ≤ CΩ n) ∧ (∀ n, 0 ≤ CD n) ∧
      ∀ {a b D A : ℝ} {p : ℕ} {F M : MatrixField}, a < b → 0 ≤ D → 0 ≤ A →
        ContDiffOn ℝ ∞ (Function.uncurry F) (Icc a b ×ˢ (univ : Set Vec3)) →
        ContDiffOn ℝ ∞ (Function.uncurry M) (Icc a b ×ˢ (univ : Set Vec3)) →
        TerminalMixedJetBound a b q p D A C F → TerminalMixedJetBound a b q p D A C M →
        TerminalMixedJetBound a b q p D (A * A) CK (fun t x => kineticForm (F t x)) ∧
        TerminalMixedJetBound a b q p D (A * (A * A)) CΩ (fun t x => vorticityForm (F t x) (M t x)) ∧
        TerminalMixedJetBound a b q p D (A * (A * A)) CD
          (fun t x => (2 : ℝ) • (F t x).adjoint.comp ((M t x).comp (F t x))) := by
  let Adj := terminalRealAdjoint
  let Skew := Adj - ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)
  let Scale := (2 : ℝ) • ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)
  let B := ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3
  let CA (n : ℕ) := ‖Adj‖ * C n
  let CS (n : ℕ) := ‖Skew‖ * C n
  let CK := terminalMixedProductCost q B CA C
  let CSm := terminalMixedProductCost q B CS C
  let CΩ := terminalMixedProductCost q B CA CSm
  let CMF := terminalMixedProductCost q B C C
  let CD₀ := terminalMixedProductCost q B CA CMF
  let CD (n : ℕ) := ‖Scale‖ * CD₀ n
  have hCA (n : ℕ) : 0 ≤ CA n := mul_nonneg (norm_nonneg Adj) (hC n)
  have hCS (n : ℕ) : 0 ≤ CS n := mul_nonneg (norm_nonneg Skew) (hC n)
  have hCK := terminalMixedProductCost_nonneg q B hCA hC
  have hCSm := terminalMixedProductCost_nonneg q B hCS hC
  have hCΩ := terminalMixedProductCost_nonneg q B hCA hCSm
  have hCMF := terminalMixedProductCost_nonneg q B hC hC
  have hCD₀ := terminalMixedProductCost_nonneg q B hCA hCMF
  refine ⟨CK, CΩ, CD, hCK, hCΩ, fun n => mul_nonneg (norm_nonneg Scale) (hCD₀ n), ?_⟩
  intro a b D A p F M hab hD hA hF hM hdF hdM
  have hA₂ : 0 ≤ A*A := mul_nonneg hA hA
  have hAdj := hdF.apply_clm hab hF Adj
  have hSkew := hdM.apply_clm hab hM Skew
  have hAdjreg : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => Adj (F t x)))
      (Icc a b ×ˢ (univ : Set Vec3)) := Adj.contDiff.comp_contDiffOn hF
  have hSkewreg : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => Skew (M t x)))
      (Icc a b ×ˢ (univ : Set Vec3)) := Skew.contDiff.comp_contDiffOn hM
  have hK := TerminalMixedJetBound.bilinear B hab hD hA hA hCA hC hAdj hdF hAdjreg hF
  have hSm := TerminalMixedJetBound.bilinear B hab hD hA hA hCS hC hSkew hdF hSkewreg hF
  have hSmreg : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => B (Skew (M t x)) (F t x)))
      (Icc a b ×ˢ (univ : Set Vec3)) := hSkewreg.clm_comp hF
  have hOmega := TerminalMixedJetBound.bilinear B hab hD hA hA₂ hCA hCSm hAdj hSm hAdjreg hSmreg
  have hMF := TerminalMixedJetBound.bilinear B hab hD hA hA hC hC hdM hdF hM hF
  have hMFreg : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => B (M t x) (F t x)))
      (Icc a b ×ˢ (univ : Set Vec3)) := hM.clm_comp hF
  have hD₀ := TerminalMixedJetBound.bilinear B hab hD hA hA₂ hCA hCMF hAdj hMF hAdjreg hMFreg
  have hD₀reg : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => B (Adj (F t x)) (B (M t x) (F t x))))
      (Icc a b ×ˢ (univ : Set Vec3)) := hAdjreg.clm_comp hMFreg
  have hDfinal := hD₀.apply_clm hab hD₀reg Scale
  exact ⟨hK, hOmega, hDfinal⟩

end

end TorusEuler

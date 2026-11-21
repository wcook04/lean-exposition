import Breakdown.CertCell.BridgeCreditStatements
import Breakdown.CertCell.PatchEntryLinks

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.CreditPatchBound

def toEntry (R : CreditPatch) : PatchEntry where
  label := R.label
  inner := R.inner
  outer := R.outer
  height := R.height
  charge := R.charge
  chargeLower := R.chargeLower
  chargeUpper := R.chargeUpper
  testCount := R.testCount
  test := R.test
  testSlope := R.testSlope
  testForm := R.testForm
  segmentCount := R.segmentCount
  segment := R.segment
  dataCount := R.dataCount
  dataOf := R.dataOf
  traceMap := R.traceMap
  factorRows := 0
  factor := 0
  factorSlack := 0
  credit := 0

theorem quadForm_zero {n : Type*} [Fintype n] (x : n → ℂ) :
    Coupling.quadForm (0 : Matrix n n ℂ) x = 0 := by
  simp [Coupling.quadForm]

theorem realQuadForm_zero {n : Type*} [Fintype n] (x : n → ℂ) :
    Coupling.realQuadForm (0 : Matrix n n ℝ) x = 0 := by
  simp [Coupling.realQuadForm]

theorem toEntry_valid (R : CreditPatch) (hR : IsCreditPatch R) : IsPatchEntry (toEntry R) where
  inner_pos := hR.inner_pos
  inner_lt_outer := hR.inner_lt_outer
  height_pos := hR.height_pos
  charge_measurable := hR.charge_measurable
  charge_lower_pos := hR.charge_lower_pos
  charge_between := hR.charge_between
  test_slope_bound := hR.test_slope_bound
  test_sides := hR.test_sides
  test_top := hR.test_top
  segments := hR.segments
  segments_cover := hR.segments_cover
  segments_disjoint := hR.segments_disjoint
  segments_inside := hR.segments_inside
  trace_expansion := hR.trace_expansion
  form_posDef := hR.form_posDef
  form_bound := hR.form_bound
  slack_nonneg := le_refl 0
  factor_bound := by
    have e : ((1 + (toEntry R).factorSlack) • (1 : Matrix (Fin (toEntry R).factorRows)
        (Fin (toEntry R).factorRows) ℝ) - (toEntry R).factor * (toEntry R).testForm
          * (toEntry R).factorᵀ) = 0 := by
      ext i
      exact i.elim0
    rw [e]
    exact PosSemidef.zero
  credit_le := fun g => by
    have e : ((toEntry R).factor * (toEntry R).traceMap)ᵀ * ((toEntry R).factor * (toEntry R).traceMap)
        = 0 := by
      show ((0 : Matrix (Fin 0) (Fin R.testCount) ℝ) * R.traceMap)ᵀ
        * ((0 : Matrix (Fin 0) (Fin R.testCount) ℝ) * R.traceMap) = 0
      simp
    rw [e, realQuadForm_zero, zero_div]
    exact (quadForm_zero g).le

end Internal.CreditPatchBound

open Internal.CreditPatchBound in
theorem creditPatchBound (hC : PatchCreditHolds) (hS : StripMomentTraceHolds) (hT : TraceHeightHolds)
    (hD : ModeHeightDerivHolds) : CreditPatchBoundHolds := by
  intro R hR Γ P v G H g hp hflip
  have key := Internal.PatchEntryLinks.trace_data hS hT hD (toEntry R) (toEntry_valid R hR) hp
  have htr : R.traceData (R.data v G) =
      fun i => patchTrace R.label v G R.inner R.outer R.height (fun p => (R.test i p : ℂ)) := by
    refine Eq.trans ?_ key
    funext i
    simp only [CreditPatch.traceData, Matrix.mulVec, dotProduct]
    rfl
  calc Coupling.quadForm R.credit (R.data v G)
      ≤ Coupling.realQuadForm R.testForm⁻¹ (R.traceData (R.data v G)) := hR.credit_le _
    _ = Coupling.realQuadForm R.testForm⁻¹
          (fun i => patchTrace R.label v G R.inner R.outer R.height (fun p => (R.test i p : ℂ))) := by
        rw [htr]
    _ ≤ ∫ p in patch R.inner R.outer R.height,
          R.charge p * cnormSq (modeVel (flipLabel R.label) v 0 (planePoint p)) * p.1 :=
        hC Γ P v G H g hp hflip R.label R.inner R.outer R.height R.charge R.test R.testSlope
          R.testForm hR.inner_pos hR.inner_lt_outer hR.height_pos hR.charge_measurable
          ⟨R.chargeLower, hR.charge_lower_pos, fun p => (hR.charge_between p).1⟩
          ⟨R.chargeUpper, fun p => (hR.charge_between p).2⟩ hR.test_slope_bound hR.test_sides
          hR.test_top hR.form_posDef hR.form_bound
    _ = ∫ p in R.region, R.charge p * cnormSq (modeVel (flipLabel R.label) v 0 (planePoint p)) * p.1 := rfl

end Breakdown.CertCell.Bridge

import Breakdown.FracCell.LayoutRowValuePressure
import Breakdown.FracCell.LayoutRowValueVolume
import Breakdown.FracCell.LayoutRowNormalFace
import Breakdown.FracCell.StrainFaceGuarded
import Breakdown.FracCell.AxisGradModeIntegrable
import Breakdown.FracCell.RowFacePolynomial

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars FracInternal.LayoutRowParts
  FracInternal.LayoutRowPressure FracInternal.LayoutRowNormalFace

private theorem inner_integrable_of_two {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

private theorem field_pairing_split {k N : ℕ} (c : FracCellData k N) (α : ℝ) (x : FieldTuple k) (a : Fin N)
    (hT : Integrable (fun y => inner ℝ (transportPart c α x y) (c.row a y)))
    (hS : Integrable (fun y => inner ℝ (secondTrace (x.2.2.1 y)) (c.row a y)))
    (hQ : Integrable (fun y => inner ℝ (x.2.2.2.2 y) (c.row a y)))
    (hA : ∀ i, Integrable (fun y => inner ℝ (c.modelActuator i y) (c.row a y))) :
    l2Pair (fun y => c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y) (c.row a) =
      l2Pair (transportPart c α x) (c.row a) - c.splitVisc * l2Pair (fun y => secondTrace (x.2.2.1 y)) (c.row a)
        + l2Pair x.2.2.2.2 (c.row a) + ∑ i, x.2.2.2.1 i * ∫ y, inner ℝ (c.modelActuator i y) (c.row a y) := by
  have hpt : ∀ y, inner ℝ (c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y) (c.row a y) =
      inner ℝ (transportPart c α x y) (c.row a y) - c.splitVisc * inner ℝ (secondTrace (x.2.2.1 y)) (c.row a y)
        + inner ℝ (x.2.2.2.2 y) (c.row a y) + ∑ i, x.2.2.2.1 i * inner ℝ (c.modelActuator i y) (c.row a y) := by
    intro y
    simp only [FracCellData.modelFieldOf, transportPart, inner_add_left, inner_sub_left, sum_inner,
      real_inner_smul_left]
    ring
  unfold l2Pair
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hA' : Integrable (fun y => ∑ i, x.2.2.2.1 i * inner ℝ (c.modelActuator i y) (c.row a y)) :=
    integrable_finsetSum _ (fun i _ => (hA i).const_mul _)
  have hTS : Integrable (fun y => inner ℝ (transportPart c α x y) (c.row a y)
      - c.splitVisc * inner ℝ (secondTrace (x.2.2.1 y)) (c.row a y)) := hT.sub (hS.const_mul _)
  have hTSQ : Integrable (fun y => inner ℝ (transportPart c α x y) (c.row a y)
      - c.splitVisc * inner ℝ (secondTrace (x.2.2.1 y)) (c.row a y) + inner ℝ (x.2.2.2.2 y) (c.row a y)) :=
    hTS.add hQ
  have hS' : Integrable (fun y => c.splitVisc * inner ℝ (secondTrace (x.2.2.1 y)) (c.row a y)) := hS.const_mul _
  rw [integral_add hTSQ hA', integral_add hTS hQ, integral_sub hT hS', integral_const_mul,
    integral_finsetSum _ (fun i _ => (hA i).const_mul _)]
  simp only [integral_const_mul]

private theorem data_sum_split {k N slots : ℕ} (c : FracCellData k N) (α : ℝ) (L : CellLayout)
    (R : CellRows N slots k) (a : Fin N) (x : FieldTuple k)
    (hN : gradSideNormalSum c L a x = ∑ d : L.Datum, normalFaceRowData c L a d * L.trueData x d) :
    ∑ d : L.Datum, layoutRowData c α L R a d * L.trueData x d =
      strainSum c α L R a x + velocitySum c α L R a x + gradSideSum c L a x + presSideSum c L a x := by
  rw [gradSide_split, hN]
  simp only [layoutRowData, add_mul, Finset.sum_add_distrib]
  generalize (∑ d : L.Datum, normalFaceRowData c L a d * L.trueData x d) = NF
  simp only [CellLayout.Datum, CellDatum, Fintype.sum_sum_type, CellLayout.trueData, Sum.elim_inl,
    Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, strainSum, velocitySum, gradSideTangentSum, presSideSum]
  ring

theorem layoutRowValue_of_strainFace (hSF : StrainFaceStatement) : LayoutRowValueStatement := by
  intro α hα1 hα2 k N slots c hc K S B Cl R hD hR L hL hseg hpres x hx a ha
  have hface := rowFacePoly_of_segments hL.layout hseg
  obtain ⟨hT, hS, hQ, hH⟩ := pairings_integrable hα1 hα2 hc hD hR hL hx ha
  have hA : ∀ i, Integrable (fun y => inner ℝ (c.modelActuator i y) (c.row a y)) := fun i =>
    inner_integrable_of_two (hD.actuator_memLp i) (hc.base.row_two a)
  have h1 := FracInternal.LayoutRowVolume.volume_identity_holds hα1 hα2 hc hD hR hL hx ha
  have h2 := FracInternal.LayoutRowVolume.viscous_identity_holds hα1 hα2 hc hD hR hL hx ha hseg
  have h3 := pressure_identity_of_modes hα1 hα2 hc hD hR hL hx ha hpres
  have hN := normal_face_sum hα1 hα2 hc hD hR hL hx ha hseg hface hSF
  unfold lowRowValue layoutRowValue layoutRowKappa
  rw [field_pairing_split c α x a hT hS hQ hA, data_sum_split c α L R a x hN, Complex.add_re, Complex.add_re,
    Complex.add_re]
  rw [Complex.add_re] at h1
  simp only [mul_div_assoc']
  rw [← Finset.sum_div]
  linear_combination h1 + h2 + h3

theorem layoutRowValue_holds : LayoutRowValueStatement :=
  layoutRowValue_of_strainFace (strainFace_of_axis axisGradModeIntegrable_holds)

end CellFormula

end CellCert

end Breakdown

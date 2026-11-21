import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxInverseSquareRing
import Breakdown.FracCell.GivenAuxInverseSquareModes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem trig_sub {S : Finset ℤ} {F G : Space → Space} (hF : IsRingTrigSum S F) (hG : IsRingTrigSum S G) :
    IsRingTrigSum S (fun y => F y - G y) := by
  have h := hF.add (hG.smul (-1))
  simp only [neg_one_smul, ← sub_eq_add_neg] at h
  exact h

private theorem trig_atomFamily (P : ChartParams) {k : ℕ} (F : AtomFamily k) (phase : (Fin k → ℝ) → ℝ)
    (p : Fin k → ℝ) : ∃ S : Finset ℤ, IsRingTrigSum S (F.eval P phase p) :=
  RingModesInternal.trig_fsum F.indices (fun γ => atomOf P (F.coef γ) (phase p)) (fun γ => multiPow γ p)
    (fun γ => ringTrig_atomOf P (F.coef γ) (phase p))

private theorem trig_turn {S : Finset ℤ} {F : Space → Space} (hF : IsRingTrigSum S F) :
    IsRingTrigSum S (fun y => axialTurn (F y)) := by
  intro ρ z
  obtain ⟨a, b, h⟩ := hF ρ z
  refine ⟨fun n => Complex.I * a n, fun _ => 0, fun θ => ⟨?_, ?_⟩⟩
  · have e1 := (h θ).1
    have hsum : (∑ n ∈ S, Complex.I * a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) =
        Complex.I * ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hsum, ← e1]
    simp only [Reduction.horizontalPart, axialTurn, PiLp.add_apply, PiLp.single_apply]
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [Reduction.verticalPart, axialTurn]

private theorem ringRep_of_trig {S : Finset ℤ} {F : Space → Space} (h : IsRingTrigSum S F) : HasRingRep F :=
  ⟨S, F, Filter.Eventually.of_forall (fun _ => rfl), h⟩

private theorem aesm_of_weighted {L : Space → Space} (hw : MemLp (fun y => ‖y‖ • L y) 2 volume) :
    AEStronglyMeasurable L volume := by
  have h1 : AEStronglyMeasurable (fun y : Space => ‖y‖⁻¹ • (‖y‖ • L y)) volume :=
    (measurable_norm.inv.aestronglyMeasurable).smul hw.aestronglyMeasurable
  refine h1.congr ?_
  have h0 : ∀ᵐ y : Space ∂volume, y ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with y hy
  rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

private theorem locInt_of_weighted {L : Space → Space} (hw : MemLp (fun y => ‖y‖ • L y) 2 volume) :
    LocallyIntegrable L volume :=
  weighted_locallyIntegrable (aesm_of_weighted hw) hw

theorem ringRep_drift (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) (α a : ℝ) :
    HasRingRep (fun y => Reduction.driftAdjointField α a (A.adjointField P j p)
      (fun z => fderiv ℝ (A.adjointField P j p) z) y) := by
  obtain ⟨S, hS⟩ := ringTrig_adjointField P A j p
  have h1 := ringRep_of_trig (hS.smul (1 - 4 * (1 / (2 * α))))
  have h2 := (ringRep_fderiv_self P hP A hA j p).smul (1 / (2 * α))
  have h3 := ((ringRep_fderiv_turn P hP A hA j p).sub (ringRep_of_trig (trig_turn hS))).smul a
  exact (h1.sub h2).sub h3

theorem ringRep_convection {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (A : AuxData k)
    (hA : IsAuxData D.chart A) (j : Fin k) (p : Fin k → ℝ) (W : Space → Space)
    (hW : W = D.profile p ∨ ∃ i, W = D.tangentField i) :
    HasRingRep (fun y => Reduction.convectionAdjointField W (fun z => fderiv ℝ W z) (A.adjointField D.chart j p)
      (fun z => fderiv ℝ (A.adjointField D.chart j p) z) y) :=
  ringRep_convectionField D hD A hA j p W hW

theorem ringRep_sharpTrace (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) (ν : ℝ) (L : Space → Space)
    (hL : Reduction.IsWeakNegTraceOf (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) L)
    (hLw : MemLp (fun y => ‖y‖ • L y) 2 volume) : HasRingRep L := by
  obtain ⟨S, hS⟩ := ringTrig_adjointField P A j p
  obtain ⟨T, hT⟩ := trig_atomFamily P (A.sharpSum j) A.phase p
  have hS' := hS.mono (Finset.subset_union_left (s₂ := T))
  have hT' := hT.mono (Finset.subset_union_right (s₁ := S))
  have hX : IsRingTrigSum (S ∪ T) (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) :=
    (hS'.smul ν).add (trig_sub (trig_sub (hS'.smul (A.sharpLead j)) hT') (hS'.smul ν))
  have hadj := locInt_adjointField P hP A hA j p
  have hsum := locInt_atomFamily P hP (A.sharpSum j) A.phase p
  have hXloc : LocallyIntegrable (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) volume :=
    (hadj.smul ν).add (((hadj.smul (A.sharpLead j)).sub hsum).sub (hadj.smul ν))
  exact ringRep_of_weakNegTrace hX hXloc (locInt_of_weighted hLw) hL

theorem ringRep_pinTrace (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (l : Fin k) (L : Space → Space) (hL : Reduction.IsWeakNegTraceOf (A.pinPotentialField P l) L)
    (hLm : AEStronglyMeasurable L volume) (hLb : ∃ C : ℝ, ∀ᵐ y ∂volume, ‖L y‖ ≤ C) : HasRingRep L := by
  obtain ⟨S, hS⟩ := ringTrig_fieldOf P (A.pinData l) A.phaseBase
  have hX := locInt_pinPotentialField P hP A hA l
  obtain ⟨C, hC⟩ := hLb
  exact ringRep_of_weakNegTrace hS hX ((memLp_top_of_bound hLm C hC).locallyIntegrable le_top) hL

theorem ringRep_pressureGrad (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) (Q : Space → Space)
    (hQ : Reduction.IsWeakScalarGradientOf (A.adjointPressureField P j p) Q)
    (hQw : MemLp (fun y => ‖y‖ • Q y) 2 volume) : HasRingRep Q := by
  obtain ⟨S, hS⟩ := ringTrig_adjointPressureField P A j p
  exact ringRep_of_weakScalarGradient hS (locInt_adjointPressureField P hP A j p) (locInt_of_weighted hQw) hQ

theorem ringRep_dualTrace (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) (L : Space → Space) (hL : Reduction.IsWeakNegTraceOf (A.dualFieldOf P j p) L)
    (hLw : MemLp (fun y => ‖y‖ • L y) 2 volume) : HasRingRep L := by
  obtain ⟨S, hS⟩ := trig_atomFamily P (A.dualFamily j) A.phase p
  exact ringRep_of_weakNegTrace hS (locInt_atomFamily P hP (A.dualFamily j) A.phase p)
    (locInt_of_weighted hLw) hL

theorem ringRep_potentialTrace (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k)
    (hA : IsAuxData P A) (j : Fin k) (p : Fin k → ℝ) (L : Space → Space)
    (hL : Reduction.IsWeakNegTraceOf (A.potentialFieldOf P j p) L)
    (hLw : MemLp (fun y => ‖y‖ • L y) 2 volume) : HasRingRep L := by
  obtain ⟨S, hS⟩ := trig_atomFamily P (A.potentialFamily j) A.phase p
  exact ringRep_of_weakNegTrace hS (locInt_atomFamily P hP (A.potentialFamily j) A.phase p)
    (locInt_of_weighted hLw) hL

theorem ringRep_fluxDiv (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) (L : Space → Space)
    (hL : Reduction.IsWeakMatrixDivergenceOf (A.fluxFieldOf P j p) L)
    (hLw : MemLp (fun y => ‖y‖ • L y) 2 volume) : HasRingRep L := by
  obtain ⟨S, hS⟩ := ringTrig_fluxFieldOf_columns P A j p
  exact ringRep_of_weakMatrixDivergence hS (locInt_fluxFieldOf P hP A j p) (locInt_of_weighted hLw) hL

end GivenFields

end CellCert

end Breakdown

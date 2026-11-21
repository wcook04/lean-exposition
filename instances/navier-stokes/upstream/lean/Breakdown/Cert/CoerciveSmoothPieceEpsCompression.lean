import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore Internal.PieceAbsorb

section Bound

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem edge_summable (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) (σ : ℝ)
    (y : Space) (hN : negSeries m h W v β σ y < ⊤) :
    Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp (secondDerivField v) κ σ y) ι) ∧
      Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp (gradField v) κ σ y) ι) ∧
      Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι) ∧
      Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι) := by
  have hwt0 : 0 ≤ (m.epsP β).wt y := hS.admissible.eps_wt_nonneg β y
  have hn : ∀ (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ), (∀ α, 0 ≤ X α) → (∀ κ, 0 ≤ g κ) →
      0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes X g ι := fun X g ι hX hg =>
    mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _)) (edge_nonneg _ _ _ _ _ hX hg)
  have n1 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp (secondDerivField v) κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have n2 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp (gradField v) κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have n3 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have n4 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have hE : ∀ ι, -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y
      = (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp (secondDerivField v) κ σ y) ι
        + (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp (gradField v) κ σ y) ι
        + (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι
        + (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := by
    intro ι
    unfold pieceEpsRestMode
    ring
  have hR0 : ∀ ι, 0 ≤ -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y := fun ι => by
    rw [hE]; linarith [n1 ι, n2 ι, n3 ι, n4 ι]
  have hAne : (∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.ne le_self_add
  have sR : Summable (fun ι => -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y) := by
    have := ENNReal.summable_toReal hAne
    simpa only [ENNReal.toReal_ofReal (hR0 _)] using this
  refine ⟨sR.of_nonneg_of_le n1 (fun ι => ?_), sR.of_nonneg_of_le n2 (fun ι => ?_),
    sR.of_nonneg_of_le n3 (fun ι => ?_), sR.of_nonneg_of_le n4 (fun ι => ?_)⟩ <;>
  · rw [hE ι]; linarith [n1 ι, n2 ι, n3 ι, n4 ι]

theorem transport_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) ι z.1 z.2) ∧
      -(∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [Internal.SmoothPieceEpsCompressionParts.transport_compression hPars hDer hRotM hSP hS β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable hS β z.1 z.2 hN
  have r := assemble (m.epsP β).modes (m.epsP β).wt v (transportRest (m.epsP β).frame W v) z.1 z.2 c _ _ (hS.admissible.eps_wt_nonneg β z.2)
    (fun ι => edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.1 hcs hcK
  exact ⟨r.1, r.2.1⟩

theorem stretch_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) ι z.1 z.2) ∧
      (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  filter_upwards [Internal.SmoothPieceEpsCompressionParts.stretch_compression hPars hDer hRotM hSP hS β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable hS β z.1 z.2 hN
  have r := assemble (m.epsP β).modes (m.epsP β).wt v (stretchRest W v) z.1 z.2 c _ _ (hS.admissible.eps_wt_nonneg β z.2)
    (fun ι => edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.2.1 hcs hcK
  exact ⟨r.1, r.2.2⟩

theorem vortTransport_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) ι z.1 z.2) ∧
      -(∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * vortGradSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [Internal.SmoothPieceEpsCompressionParts.vortTransport_compression hPars hDer hRotM hSP hS β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable hS β z.1 z.2 hN
  have r := assemble (m.epsP β).modes (m.epsP β).wt v (vortTransportRest W v) z.1 z.2 c _ _ (hS.admissible.eps_wt_nonneg β z.2)
    (fun ι => edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.2.2.1 hcs hcK
  exact ⟨r.1, r.2.1⟩

theorem vortStretch_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      Summable (fun ι => restPart (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) ι z.1 z.2) ∧
      (∑' ι, restPart (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [Internal.SmoothPieceEpsCompressionParts.vortStretch_compression hPars hDer hRotM hSP hS β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable hS β z.1 z.2 hN
  have r := assemble (m.epsP β).modes (m.epsP β).wt v (vortStretchRest W v) z.1 z.2 c _ _ (hS.admissible.eps_wt_nonneg β z.2)
    (fun ι => edge_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.2.2.2 hcs hcK
  exact ⟨r.1, r.2.2⟩

end Bound

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown

import Breakdown.FracCell.StMesh

noncomputable section

namespace Breakdown.CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

theorem meshCompatibility_of (h1 : MeshSkeletonSlotStatement) (h2 : MeshRootZeroStatement)
    (h3 : MeshEdgeJumpStatement) (h4 : MeshGaugeLinearStatement) (h5 : MeshMomentLinearStatement) :
    MeshCompatibilityStatement := by
  intro α hα₁ hα₂ k N c hc Sp M hM
  exact ⟨h1 α hα₁ hα₂ c hc Sp M hM, h2 α hα₁ hα₂ c hc Sp M hM, h3 α hα₁ hα₂ c hc Sp M hM,
    h4 α hα₁ hα₂ c hc Sp M hM, h5 α hα₁ hα₂ c hc Sp M hM⟩

theorem fluxStream_of (h1 : FluxRadialStatement) (h2 : FluxHeightStatement) (h3 : StreamPlaneStatement) :
    FluxStreamStatement := by
  intro k N c x hx L hL S hS o o'
  exact ⟨fun h1' h2' h3' h4' h5' => h1 c x hx L hL S hS o o' h1' h2' h3' h4' h5',
    fun h1' h2' h3' h4' => h2 c x hx L hL S hS o o' h1' h2' h3' h4',
    fun r o hr ho => h3 c x hx L hL r o hr ho⟩

end CellCoordinates

end Breakdown.CellCert

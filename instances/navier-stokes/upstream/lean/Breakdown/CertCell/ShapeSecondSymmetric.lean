import Breakdown.CertCell.ShapeJetEntry

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

def FieldSecondSymmetric : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData), IsShapeParams P → IsTimeFieldData D → ∀ σ y u w,
    shapeHess P D σ y u w = shapeHess P D σ y w u

theorem givenSecondSymmetric_of_entry (hs : FieldSecondSymmetric) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (hF : IsGivenShapeEntry D X F) : ∀ σ y u w, D.givenHess σ y u w = D.givenHess σ y w u := by
  rw [hF.givenHess_eq]
  exact hs F.params F.model hF.params_valid hF.model_valid

theorem givenSecondSymmetric_of_jets (hJ : JetParts) (hs : FieldSecondSymmetric) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k)
    (J : GivenJetData) (hJR : IsGivenJetEntry D X F J) : ∀ σ y u w, D.givenHess σ y u w = D.givenHess σ y w u :=
  givenSecondSymmetric_of_entry hs D X F (givenShapeEntry_of_jets hJ D X F J hJR)

end GivenShape

end CertCell

end Breakdown

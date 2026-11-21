import Breakdown.CertCell.AssemblyRowParts
import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.AssemblyExteriorValueSets
import Breakdown.CertCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

def CellResidualFromConditions : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (A : Assembly.AssemblyEntry D R) (P : Assembly.CouplingEntries D R) (T : TreeEntry D R)
    (W : Assembly.RowEntry D R T),
    FormNegFinite D D.coercivity → (∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity) →
    (∀ K, ∀ ι ∈ R.pairSlackLabels K, 0 < R.pairSlackWeight K ι) →
    Assembly.AssemblyConditions D R A P W → Assembly.CellStatesIn D R (Assembly.InRowRange W) →
    ∀ K, CellCalculus.IsResidualFormBound D R K (R.cellForm K - CellCalculus.energyLeafForm D R K)

def FieldGaugeParts : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R), T.gauge.Conditions → T.FieldGaugeHolds

def PressureFlipParts : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), Assembly.PressureFacts D →
    Assembly.ChosenPressureFlips D

structure CellLayerParts : Prop where
  initial_state : InitialStateHolds
  cell_form : CellCalculus.CellFormAssemblyStatement
  pair_shares : InstancePair.PairSharesFromSurrogateProfiles
  credit_leaves : CreditEval.CreditLeavesBoundHolds
  scaled_jets : GivenShape.ScaledJetParts
  actuator_pairing : ActuatorPairingHolds
  form_negative : FormNegFiniteHolds
  state_certificate : Certificate.StateEnclosureCertificateNonneg
  support_radius : GivenShape.CompactFieldSupportRadius
  row_shares : RowSharesOfInstanceHolds
  instance_parts : Instance.InstanceParts
  true_field : Assembly.TrueFieldRegularHolds
  off_modes : Assembly.OffModesVanishHolds
  exterior : Assembly.ExteriorNonnegHolds
  exterior_stretch : Assembly.ExteriorStretchChargedHolds
  exterior_values : Assembly.ExteriorValuesChargeHolds
  pressure : Assembly.PressureRecoveryHolds
  residual : CellResidualFromConditions
  tree_state : Assembly.TreeStateHolds
  rows_fields : Assembly.RowsMatchFieldsHolds
  rows_state : Assembly.RowsMatchStateOfFieldsHolds
  states_in : Assembly.CellStateInRowRangeHolds
  field_gauge : FieldGaugeParts
  pressure_flip : PressureFlipParts
  relations : CellCalculus.HarmonicRelationsStatement

section Closure

variable {k : ℕ} {C : Type} {nE nM : ℕ}

end Closure

end CertCell

end Breakdown

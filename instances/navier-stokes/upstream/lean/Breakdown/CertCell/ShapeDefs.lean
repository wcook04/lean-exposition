import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.StatementDefs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline TensorMesh cellCount atFirst atSecond tDeriv xDeriv weightPoly radialScale
  heightDeriv heightRatio radialVec polarVecQ azimVecQ)

namespace FieldKey

end FieldKey

def tDerivSpline (S : Spline) : Spline := ⟨S.mesh, fun i j => tDeriv 1 (S.piece i j)⟩

def xDerivSpline (S : Spline) : Spline := ⟨S.mesh, fun i j => xDeriv 1 (S.piece i j)⟩

namespace KeyAmp

end KeyAmp

namespace JetAxis

end JetAxis

namespace JetSpline

end JetSpline

def logRadialPhase (rate hbase s : ℝ) : ℝ := rate / 2 * Real.log (1 + s / hbase ^ 2)

def keysOfHarmonic (m : ℕ) (D : TimeFieldData) (ξ : ℤ × ℤ) : Finset FieldKey :=
  D.keys.filter fun κ => labelHarmonic m κ.label = ξ

def rotateVec (φ : ℝ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(Real.cos φ : ℂ) * w 0 - (Real.sin φ : ℂ) * w 1, (Real.sin φ : ℂ) * w 0 + (Real.cos φ : ℂ) * w 1, w 2]

def flipVec (w : Fin 3 → ℂ) : Fin 3 → ℂ := ![w 0, -w 1, -w 2]

structure IsGivenKeyData (S : Finset FieldKey) (given : FieldKey → KeyAmp) : Prop where
  one_per_orbit : ∀ κ ∈ S, ∀ κ' ∈ S, (κ' = κ.negKey ∨ κ' = κ.flipKey ∨ κ' = κ.flipKey.negKey) → κ' = κ
  radial_class : ∀ κ ∈ S, κ.label.1 ≠ 0 → IsJoinedSpline 2 1 (given κ).radial
  polar_class : ∀ κ ∈ S, κ.label.1 ≠ 0 → IsJoinedSpline 1 2 (given κ).polar
  lowOrder_ge : ∀ κ ∈ S, κ.label.1 ≠ 0 → 2 ≤ (given κ).lowOrder
  stream_class : ∀ κ ∈ S, κ.label.1 = 0 → IsJoinedSpline 2 2 (given κ).stream
  swirl_class : ∀ κ ∈ S, κ.label.1 = 0 → IsJoinedSpline 1 1 (given κ).swirl
  stream_origin : ∀ κ ∈ S, κ.label.1 = 0 → ∀ j < cellCount (given κ).stream.mesh.xBreaks,
    atFirst 0 ((given κ).stream.piece 0 j) = 0
  swirl_origin : ∀ κ ∈ S, κ.label.1 = 0 → ∀ j < cellCount (given κ).swirl.mesh.xBreaks,
    atFirst 0 ((given κ).swirl.piece 0 j) = 0
  highOrder_pos : ∀ κ ∈ S, 1 ≤ (given κ).highOrder
  stream_odd : ∀ κ ∈ S, κ.label.1 = 0 → SplineAgrees (given κ).stream (reflectSpline true (given κ).stream)
  swirl_odd : ∀ κ ∈ S, κ.label.1 = 0 → SplineAgrees (given κ).swirl (reflectSpline true (given κ).swirl)
  self_conj : ∀ κ ∈ S, κ.negKey = κ → SplineAgrees (given κ).stream (given κ).stream.conj ∧
    SplineAgrees (given κ).swirl (given κ).swirl.conj ∧ starRingEnd ℂ (given κ).axisCoef = (given κ).axisCoef
  self_conj_flip : ∀ κ ∈ S, κ.label.1 ≠ 0 → κ.flipKey.negKey = κ →
    SplineAgrees (given κ).radial (reflectSpline false (given κ).radial.conj) ∧
      SplineAgrees (given κ).polar (reflectSpline true (given κ).polar.conj)

end GivenShape

end CertCell

end Breakdown

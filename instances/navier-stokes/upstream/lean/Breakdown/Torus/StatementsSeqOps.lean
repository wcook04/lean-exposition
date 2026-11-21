import Breakdown.Transfer.StatementsDefs

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

def RightInversePerturb : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A A' : E →L[ℝ] F) (R : F →L[ℝ] E) (K : ℝ),
    A.comp R = ContinuousLinearMap.id ℝ F → ‖R‖ ≤ K → ‖A' - A‖ * K ≤ 1 / 2 →
      ∃ R' : F →L[ℝ] E, A'.comp R' = ContinuousLinearMap.id ℝ F ∧ ‖R'‖ ≤ 2 * K

def chainOp {E Y Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : Y →L[ℝ] Y) (G : E →L[ℝ] Y) (B : Z →L[ℝ] Y) (Rr : Y →L[ℝ] Z) : E × Y →L[ℝ] Y :=
  ContinuousLinearMap.snd ℝ E Y - S.comp (ContinuousLinearMap.snd ℝ E Y) -
    G.comp (ContinuousLinearMap.fst ℝ E Y) - (B.comp Rr).comp (ContinuousLinearMap.snd ℝ E Y)

def ShellInverseTransfer : Prop :=
  ∀ (E Y Yt Z : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Yt] [NormedSpace ℝ Yt] [CompleteSpace Yt]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (S : Y →L[ℝ] Y) (G : E →L[ℝ] Y) (B : Z →L[ℝ] Y) (Rr : Y →L[ℝ] Z)
    (St : Yt →L[ℝ] Yt) (Gt : E →L[ℝ] Yt) (Bt : Z →L[ℝ] Yt) (Rt : Yt →L[ℝ] Z)
    (Rf : Y →L[ℝ] E × Y) (q Kf δ : ℝ),
    0 ≤ q → q < 1 → ‖S‖ ≤ q → ‖St‖ ≤ q →
    (chainOp S G B Rr).comp Rf = ContinuousLinearMap.id ℝ Y → ‖Rf‖ ≤ Kf →
    ‖Rt.comp ((Ring.inverse (1 - St)).comp Bt) - Rr.comp ((Ring.inverse (1 - S)).comp B)‖ ≤ δ →
    ‖Rt.comp ((Ring.inverse (1 - St)).comp Gt) - Rr.comp ((Ring.inverse (1 - S)).comp G)‖ ≤ δ →
    4 * δ * (1 + Kf * ‖B‖ * (1 + ‖Rr‖)) ≤ 1 →
    ∃ R' : Yt →L[ℝ] E × Yt, (chainOp St Gt Bt Rt).comp R' = ContinuousLinearMap.id ℝ Yt ∧
      ‖R'‖ ≤ (1 - q)⁻¹ * (1 + (‖Bt‖ + ‖Gt‖ + 1) * 2 * (1 + Kf * ‖B‖ * (1 + ‖Rr‖)) * ‖Rt‖ * (1 - q)⁻¹)

end Breakdown.Periodic

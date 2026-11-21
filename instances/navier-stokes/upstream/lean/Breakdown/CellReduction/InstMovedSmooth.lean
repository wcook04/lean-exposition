import Breakdown.CellReduction.InstMovedSmoothFactor
import Breakdown.CertCell.CellLayerClosed
import Breakdown.CertCell.ShapeFieldSmooth

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

theorem keyVector_jointSmooth {P : ShapeParams} {D : TimeFieldData} (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) {κ : FieldKey} (hκ : κ ∈ D.keys) :
    ContDiff ℝ 1 (fun z : ℝ × Space => keyVector P κ (D.amp κ) z.1 z.2) := by
  have h0 : ContDiff ℝ 1 (keyVector P κ (D.amp κ) 0) := by
    by_cases h : κ.label.1 = 0
    · exact (typeTwoKeySmooth_closed P D κ 0 hP hD hκ h).smooth
    · exact (typeOneKeySmooth_closed P D κ 0 hP hD hκ h).smooth
  have he : (fun z : ℝ × Space => keyVector P κ (D.amp κ) z.1 z.2) =
      fun z => CertCell.GivenShape.Internal.keyTimeFactor κ z.1 • keyVector P κ (D.amp κ) 0 z.2 := by
    funext z
    rw [CertCell.GivenShape.Internal.keyVector_eq_timeFactor]
    rfl
  rw [he]
  exact ((CertCell.GivenShape.Internal.contDiff_keyTimeFactor κ).comp contDiff_fst).smul
    (h0.comp contDiff_snd)

theorem movedField_jointSmooth {P : ShapeParams} {moving : ℝ → ℝ} {D : TimeFieldData}
    (hP : IsShapeParams P) (hm : IsRadialPhase moving) (hD : IsTimeFieldData D) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ × Space => shapeInfoField (movedParams P moving z.1) D z.2.1 z.2.2) := by
  have hP1 : IsShapeParams (movedParams P moving 1) := movedParamsValid_holds P moving 1 hP hm
  have he : (fun z : ℝ × ℝ × Space => shapeInfoField (movedParams P moving z.1) D z.2.1 z.2.2) =
      fun z => realPartVec (∑ κ ∈ D.keys,
        ((((1 - z.1 : ℝ) : ℂ) * movePhase κ.phaseIndex moving z.1 z.2.2) • keyVector P κ (D.amp κ) z.2.1 z.2.2 +
          (((z.1 : ℝ) : ℂ) * movePhase κ.phaseIndex moving (z.1 - 1) z.2.2) •
            keyVector (movedParams P moving 1) κ (D.amp κ) z.2.1 z.2.2)) := by
    funext z
    simp only [shapeInfoField, complexField]
    congr 1
    exact Finset.sum_congr rfl fun κ _ => keyVector_moved P moving hP.phase hm κ (D.amp κ) z.1 z.2.1 z.2.2
  rw [he]
  refine realPartVec.contDiff.comp (ContDiff.sum fun κ hκ => ?_)
  have hA : ContDiff ℝ 1 (fun z : ℝ × ℝ × Space => (z.1, z.2.2)) :=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hB : ContDiff ℝ 1 (fun z : ℝ × ℝ × Space => (z.1 - 1, z.2.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.comp contDiff_snd)
  have hC : ContDiff ℝ 1 (fun z : ℝ × ℝ × Space => z.2) := contDiff_snd
  have c1 : ContDiff ℝ 1 (fun z : ℝ × ℝ × Space => (((1 - z.1 : ℝ) : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_fst)
  have c2 : ContDiff ℝ 1 (fun z : ℝ × ℝ × Space => (((z.1 : ℝ) : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  exact ((c1.mul ((contDiff_movePhase _ hm).comp hA)).smul ((keyVector_jointSmooth hP hD hκ).comp hC)).add
    ((c2.mul ((contDiff_movePhase _ hm).comp hB)).smul ((keyVector_jointSmooth hP1 hD hκ).comp hC))

end Internal

open Breakdown.CellReduction.Instantiation.Internal in
theorem movedFieldJointSmooth_holds : MovedFieldJointSmoothHolds := by
  intro k P moving rate g centre gt tangent hP hm hg hgt hc ht
  have hPg : ∀ g' : OriginProfile, IsOriginProfile g' → IsShapeParams (withOrigin P g') :=
    fun g' hg' => ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hg'⟩
  have hrate : ContDiff ℝ 1 (fun q : Fin k → ℝ => phaseRate rate q) := by
    unfold phaseRate
    exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)
  have hmap : ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space => (phaseRate rate z.1, z.2)) :=
    (hrate.comp contDiff_fst).prodMk contDiff_snd
  have hpiece : ∀ (g' : OriginProfile) (D : TimeFieldData), IsOriginProfile g' → IsTimeFieldData D →
      ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space =>
        shapeInfoField (withOrigin (movedParams P moving (phaseRate rate z.1)) g') D z.2.1 z.2.2) :=
    fun g' D hg' hD => by
      have hw : ∀ a : ℝ, withOrigin (movedParams P moving a) g' = movedParams (withOrigin P g') moving a :=
        fun _ => rfl
      have h1 := movedField_jointSmooth (hPg g' hg') hm hD
      have h2 := ContDiff.comp h1 hmap
      simp only [hw]
      exact h2
  unfold affineField
  refine ContDiff.add (hpiece g centre hg hc) (ContDiff.sum fun i _ => ?_)
  have h3 := ContDiff.smul ((contDiff_apply ℝ ℝ i).comp (contDiff_fst (𝕜 := ℝ) (E := Fin k → ℝ) (F := ℝ × Space)))
    (hpiece (gt i) (tangent i) (hgt i) (ht i))
  exact h3

end Instantiation

end CellReduction

end Breakdown

import PCP.Complexity.DerivedGridSite

/-! # Identifying the structural certificate-seed codec at each derived-grid site -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

theorem coordinateCodec_valid (n : ℕ) : CorrectionContext.coordinateCodec .valid n =
    (Codec.fin n).sum (Codec.fin n) := by
  unfold CorrectionContext.coordinateCodec Codec.sum Codec.fin
  congr 1
  ext i
  cases i <;> rfl

theorem coordinateCodec_proper (n : ℕ) : CorrectionContext.coordinateCodec .proper n =
    (Codec.fin (n+n)).sum (Codec.fin (n+n)) := by
  unfold CorrectionContext.coordinateCodec Codec.sum Codec.fin
  congr 1
  ext i
  cases i <;> rfl

theorem firstSeed_code (k : Certificate) (s : DerivedGrid.Sample k t n m) :
    ((callCodec (BinaryMaterializedField.coordinates t)
      ((Codec.fin (baseDimension k n)).sum (Codec.fin (baseDimension k n))) m 4).equiv
        (padDerived s).2.1.2.1).val =
    ((callCodec (BinaryMaterializedField.coordinates t)
      (CorrectionContext.coordinateCodec k n) m 4).equiv (padCall (firstSeed k s))).val := by
  cases k with
  | valid =>
      change ((callCodec (BinaryMaterializedField.coordinates t)
        ((Codec.fin n).sum (Codec.fin n)) m 4).equiv (padCall s.2.1.2.1)).val =
        ((callCodec (BinaryMaterializedField.coordinates t)
          (CorrectionContext.coordinateCodec .valid n) m 4).equiv
            (padCall s.2.1.2.1)).val
      rw [coordinateCodec_valid]
      rfl
  | proper =>
      change ((callCodec (BinaryMaterializedField.coordinates t)
        ((Codec.fin (n+n)).sum (Codec.fin (n+n))) m 4).equiv (padCall s.2.1.2.1)).val =
        ((callCodec (BinaryMaterializedField.coordinates t)
          (CorrectionContext.coordinateCodec .proper n) m 4).equiv
            (padCall s.2.1.2.1)).val
      rw [coordinateCodec_proper]
      rfl

theorem secondSeed_code (k : Certificate) (s : DerivedGrid.Sample k t n m) :
    ((callCodec (BinaryMaterializedField.coordinates t)
      ((Codec.fin (baseDimension k n)).sum (Codec.fin (baseDimension k n))) m 4).equiv
        (padDerived s).2.1.2.2).val =
    ((callCodec (BinaryMaterializedField.coordinates t)
      (CorrectionContext.coordinateCodec k n) m 4).equiv (padCall (secondSeed k s))).val := by
  cases k with
  | valid =>
      change ((callCodec (BinaryMaterializedField.coordinates t)
        ((Codec.fin n).sum (Codec.fin n)) m 4).equiv (padCall s.2.1.2.2)).val =
        ((callCodec (BinaryMaterializedField.coordinates t)
          (CorrectionContext.coordinateCodec .valid n) m 4).equiv
            (padCall s.2.1.2.2)).val
      rw [coordinateCodec_valid]
      rfl
  | proper =>
      change ((callCodec (BinaryMaterializedField.coordinates t)
        ((Codec.fin (n+n)).sum (Codec.fin (n+n))) m 4).equiv (padCall s.2.1.2.2)).val =
        ((callCodec (BinaryMaterializedField.coordinates t)
          (CorrectionContext.coordinateCodec .proper n) m 4).equiv
            (padCall s.2.1.2.2)).val
      rw [coordinateCodec_proper]
      rfl

end PCP.Lang.DerivedSeed

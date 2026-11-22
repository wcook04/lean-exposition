import PCP.Complexity.OuterBranchState
import PCP.Complexity.ThreeColorNestedSeedSemantics
import PCP.Complexity.LangSeedMaterialization

/-!
# Structural outer-seed codecs and the physical coordinate order
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def Kind.codec (n : ℕ) (k : Kind) : Codec (k.Coordinates n) :=
  match k with
  | .color => Codec.fin n
  | .valid | .difference => (Codec.fin n).sum (Codec.fin n)
  | .proper => (Codec.fin (n+n)).sum (Codec.fin (n+n))

def Kind.cubic : Kind → Bool
  | .color | .difference => true
  | .valid | .proper => false

theorem Kind.codec_size (k : Kind) (n : ℕ) : (k.codec n).size = k.dimension n := by
  cases k <;> rfl

theorem Kind.degree_cubic (k : Kind) : k.degree = if k.cubic then 3 else 1 := by
  cases k <;> rfl

def seedCodec (k : Kind) (t n m : ℕ) [NeZero t] : Codec (Sample k t n m) :=
  outerCodec (BinaryMaterializedField.coordinates t) (k.codec n) m 4 k.degree

theorem Kind.codec_point (k : Kind) (x : Point k t n) :
    (((k.codec n).function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv x).val =
      k.pointCode (fieldEquiv t) x := by
  unfold Codec.function
  simp only [Equiv.trans_apply, UniformDecode.fieldCodec_materialized]
  cases k <;> apply congrArg Fin.val <;> apply congrArg finFunctionFinEquiv <;> funext i
  all_goals simp [Kind.codec, Codec.sum, Codec.fin, Kind.vector,
    Kind.coordinateEquiv, Equiv.arrowCongr, Equiv.sumCongr]
  all_goals rfl


theorem innerPointCodec_materialized (x : BinaryLocalCorrection.InnerPoint (Field t) m 4) :
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv x).val =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 x).val := by
  unfold innerPointCodec Codec.function
  simp only [Equiv.trans_apply, UniformDecode.fieldCodec_materialized]
  rfl

def decodeOuter (k : Kind) : Stmt 16 4 := NestedSeed.outer k.cubic

attribute [local irreducible] NestedSeed.outer

/-- The exact seven stored codes are computed from the one numeric outer sampler seed. -/
theorem decodeOuter_run (k : Kind) (s : Sample k t n m) (st : State 16 4)
    (hc : ComputedSeed.Context (k.dimension n) m 4 t ((seedCodec k t n m).equiv s).val st) :
    ((decodeOuter k).run st).1.lists 1 =
      [((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv (innerSeed s)).val,
       ((hadamardCodec t k.degree).equiv (primarySeed s)).val,
       ((bitsCodec t).equiv s.2.2.1.2).val,
       (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 s.2.2.1.1).val,
       (fieldEquiv t s.2.1).val,
       k.pointCode (fieldEquiv t) s.1.2,
       k.pointCode (fieldEquiv t) s.1.1] := by
  have hr : ((decodeOuter k).run st).1.lists 1 =
      [((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv (innerSeed s)).val,
       ((hadamardCodec t k.degree).equiv (primarySeed s)).val,
       ((bitsCodec t).equiv s.2.2.1.2).val,
       ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.1.1).val,
       ((fieldCodec (BinaryMaterializedField.coordinates t)).equiv s.2.1).val,
       (((k.codec n).function
         (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1.2).val,
       (((k.codec n).function
         (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1.1).val] := by
    cases k with
    | color =>
        exact NestedSeed.outer_run (BinaryMaterializedField.coordinates t)
          (Codec.fin n) n m 4 true rfl s st hc
    | valid =>
        exact NestedSeed.outer_run (BinaryMaterializedField.coordinates t)
          ((Codec.fin n).sum (Codec.fin n)) (n+n) m 4 false rfl s st hc
    | difference =>
        exact NestedSeed.outer_run (BinaryMaterializedField.coordinates t)
          ((Codec.fin n).sum (Codec.fin n)) (n+n) m 4 true rfl s st hc
    | proper =>
        exact NestedSeed.outer_run (BinaryMaterializedField.coordinates t)
          ((Codec.fin (n+n)).sum (Codec.fin (n+n))) ((n+n)+(n+n)) m 4 false rfl s st hc
  rw [hr]
  simp only [UniformDecode.fieldCodec_materialized, Kind.codec_point,
    innerPointCodec_materialized]
  rfl

end PCP.Lang.OuterBranch

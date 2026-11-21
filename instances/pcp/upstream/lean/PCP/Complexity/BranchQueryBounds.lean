import PCP.Complexity.QueryAddressBounds
import PCP.Complexity.OuterBranchCost
import PCP.Complexity.LocalCorrectionCost

/-! Discharging branch address and payload bounds uniformly over every sample. -/

namespace PCP.Lang.BranchQueryBounds

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace BooleanCoefficientIndex
  InterpolationBranch

variable {t n m W : ℕ} [NeZero t]

omit [NeZero t] in
theorem payload {r : ℕ} (loc : HadamardRow.Location (Field t) n m 4 r)
    (hW : QueryAddress.width t n m 4 ≤ W) (i : Fin 10) :
    Nat.size (loc.payload (t := t) (fieldEquiv t) i) ≤ W :=
  QueryAddress.inputs_size_le (fieldEquiv t) (loc.query 0) hW i.castSucc

omit [NeZero t] in
theorem read (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (p : Coefficients t 1) (hW : QueryAddress.width t n m 4 ≤ W) :
    ReadBound site x p W :=
  ⟨QueryAddress.inputs_size_le (fieldEquiv t) (site.query x p) hW,
    (QueryAddress.address_size (fieldEquiv t) (site.query x p)).trans hW⟩

theorem interpolation (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (hW : QueryAddress.width t n m 4 ≤ W) : QueryBound a z u v w site W :=
  ⟨read _ _ _ hW, fun _ => read _ _ _ hW⟩

theorem standard (site : StandardCorrection.Site (Field t) n) (ζ : Field t)
    (u v : Point t m) (w : Fin t → ZMod 2) (hW : QueryAddress.width t n m 4 ≤ W) :
    StandardCorrection.QueryBound site ζ u v w W := by
  intro j _
  exact ⟨QueryAddress.inputs_size_le (fieldEquiv t) _ hW,
    (QueryAddress.address_size (fieldEquiv t) _).trans hW⟩

theorem inner (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (hW : QueryAddress.width t n m 4 ≤ W) :
    InnerBranch.Bounds a site s W := by
  constructor
  · exact payload _ hW
  · intro p _
    exact (QueryAddress.address_size (fieldEquiv t) (site.query s.2.1.1 p)).trans hW
  · exact interpolation _ _ _ _ _ _ hW

omit [NeZero t] in
theorem primary (k : OuterBranch.Kind) (x : OuterBranch.Point k t n)
    (p : Coefficients t k.degree) (hW : QueryAddress.width t n m 4 ≤ W) :
    OuterBranch.PrimaryBound (m := m) k x p W :=
  ⟨QueryAddress.inputs_size_le (fieldEquiv t) ((k.primary (m := m) x).query p) hW,
    (QueryAddress.address_size (fieldEquiv t) ((k.primary (m := m) x).query p)).trans hW⟩

variable [NeZero m]

omit [NeZero m] in
theorem outer (k : OuterBranch.Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : OuterBranch.Sample k t n m) (hW : QueryAddress.width t n m 4 ≤ W) :
    OuterBranch.Bounds k a ζ s W := by
  constructor
  · exact payload _ hW
  · intro q hq
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hq
    exact (QueryAddress.address_size (fieldEquiv t) ((k.primary (m := m) s.1.1).query p)).trans hW
  · exact inner _ _ _ hW
  · exact standard _ _ _ _ _ hW
  · exact primary _ _ _ hW

omit [NeZero m] in
theorem correction (k : OuterBranch.Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : OuterBranch.Sample k t n m) (hW : QueryAddress.width t n m 4 ≤ W) :
    LocalCorrection.Bounds k a ζ s W :=
  ⟨inner _ _ _ hW, standard _ _ _ _ _ hW, standard _ _ _ _ _ hW, primary _ _ _ hW⟩

end PCP.Lang.BranchQueryBounds

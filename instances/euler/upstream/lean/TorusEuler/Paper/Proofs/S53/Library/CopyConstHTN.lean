import TorusEuler.HierarchyTransverseNorms
import TorusEuler.Paper.Proofs.S53.Library.Leaves

/-!
# S53 library: Lemma 5.3 chain: transverse constants

Generated copy (script `s53tools/mkcopy.py`) of the declarations transverseVelocityWordConstant, transverseSolveNormConstant of
`TorusEuler/HierarchyTransverseNorms.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

open TorusEuler.HierarchyTwistedProfile
section WordNorm

variable {T : ℝ} {k : Vec3} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end WordNorm

section SelectedSolve

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- The per-word velocity constant from the fixed-plane solve and the two coframes. -/
def transverseVelocityWordConstant (n : ℕ) (duration K Ccomm CJ CR : ℝ) : ℝ :=
  (2 : ℝ) ^ n * CJ * (linearODEWordFactor Ccomm n * (K * (duration * ((2 : ℝ) ^ n * CR))))

/-- The selected oscillatory inverse constant in the sum of velocity and
carrier-weighted pressure seminorms. -/
def transverseSolveNormConstant (n : ℕ) (duration K Ccomm CJ CR CA CB : ℝ) : ℝ :=
  let V := transverseVelocityWordConstant n duration K Ccomm CJ CR
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  count * (V + 2 * (count * ((2 : ℝ) ^ n * CA * V + (2 : ℝ) ^ n * CB)))

end SelectedSolve

section PhysicalCoframe

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Plane" => transversePlane k

end PhysicalCoframe

end TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile


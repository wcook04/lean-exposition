import Breakdown.FracCell.StMesh

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshEdgeJumpInternal

theorem dep_congr {n : ℕ} {β : Fin n → Type} (f : (K : Fin n) → β K → ℝ) {K K' : Fin n} {d : β K} {d' : β K'}
    (h : K = K') (hd : HEq d d') : f K d = f K' d' := by
  subst h
  rw [eq_of_heq hd]

theorem rootValue_congr {k N : ℕ} {Sp : CellSplit k N} (M : MeshData k N Sp) (x : FieldTuple k)
    {a b : Fin M.classCount} (h1 : M.classRoot a = M.classRoot b) (h2 : M.classRootSide a = M.classRootSide b)
    (h3 : HEq (M.classRootDatum a) (M.classRootDatum b)) : M.rootValue x a = M.rootValue x b := by
  unfold MeshData.rootValue
  rw [h2]
  exact dep_congr (β := fun K => Fin (M.coords K).layout.presCount × Fin (M.coords K).layout.degSide)
    (fun K d => -((M.coords K).layout.pressureDatumValue x d) /
      (if M.classRootSide b then (M.coords K).layout.shiftCoefRight d else (M.coords K).layout.shiftCoefLeft d))
    h1 h3

end MeshEdgeJumpInternal

open MeshEdgeJumpInternal

theorem meshEdgeJump : MeshEdgeJumpStatement := by
  intro α _ _ k N c _ Sp M hM K e he x _
  obtain ⟨⟨h1, h2, h3⟩, hp⟩ := hM.path_edges K e he
  have hr := rootValue_congr M x h1 h2 h3
  unfold MeshData.canonicalRight MeshData.canonicalLeft MeshData.classValue
  rcases hp with hp | hp
  · rw [hp, hr, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, if_true, List.sum_cons, List.sum_nil]
    ring
  · rw [hp, hr, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, Bool.false_eq_true, if_false, List.sum_cons, List.sum_nil]
    ring

end CellCoordinates

end CellCert

end Breakdown

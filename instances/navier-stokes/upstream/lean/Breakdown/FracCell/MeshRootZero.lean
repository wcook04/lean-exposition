import Breakdown.FracCell.StMesh

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

theorem meshRootZero : MeshRootZeroStatement := by
  intro α _ _ k N c _ Sp M hM K r hr x _
  obtain ⟨cl, hK, hr', hpath⟩ := hM.roots_exact K r hr
  subst hK
  have hrr := eq_of_heq hr'
  subst hrr
  have hnode := (hM.root_cells cl).1.1 hpath
  obtain ⟨_, _, hR, hL⟩ := hM.root_cells cl
  unfold CellLayout.rootShifted MeshData.canonicalLeft MeshData.canonicalRight
  cases hs : M.classRootSide cl with
  | false =>
    rw [hs] at hnode
    obtain ⟨h1, h2⟩ := hL hs
    rw [hnode, h2]
    simp only [MeshData.classValue, MeshData.rootValue, hpath, hs, List.map_nil, List.sum_nil, add_zero,
      Bool.false_eq_true, if_false, zero_mul]
    field_simp
    ring
  | true =>
    rw [hs] at hnode
    obtain ⟨h1, h2⟩ := hR hs
    rw [hnode, h2]
    simp only [MeshData.classValue, MeshData.rootValue, hpath, hs, List.map_nil, List.sum_nil, add_zero,
      if_true, zero_mul]
    field_simp
    ring

end CellCoordinates

end CellCert

end Breakdown

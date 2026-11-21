import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount)

namespace Internal

private theorem getD_succ_ge (l : List ℝ) (hs : l.Pairwise (· < ·)) (hl : l.getLast? = some 1) (i : ℕ) :
    l.getD i 1 ≤ l.getD (i + 1) 1 := by
  rcases lt_or_ge (i + 1) l.length with h | h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by omega)]
    exact (List.pairwise_iff_getElem.mp hs i (i + 1) (by omega) h (by omega)).le
  · rw [List.getD_eq_default _ _ h]
    rcases lt_or_ge i l.length with h' | h'
    · have hi : i = l.length - 1 := by omega
      rw [List.getD_eq_getElem _ _ h']
      rw [List.getLast?_eq_getElem?] at hl
      subst hi
      rw [List.getElem?_eq_getElem h'] at hl
      exact (Option.some.inj hl).le
    · rw [List.getD_eq_default _ _ h']

private theorem dof_term_zero (H : JetSpline) (tb : ℝ) (hA : IsJetAxis H.tAxis 0 1)
    (hnode : ∀ k p e, tb ≤ H.tAxis.breaks.getD k 1 → H.coef (JetDof.node k p) e = 0)
    (hbub : ∀ i s e, tb ≤ H.tAxis.breaks.getD i 1 → H.coef (JetDof.bubble i s) e = 0)
    (i : ℕ) (hi : tb ≤ H.tAxis.breaks.getD i 1) (d e : JetDof) :
    MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly i d) = 0 := by
  cases d with
  | node k p =>
    simp only [JetAxis.dofPoly]
    split_ifs with hp hk hk1
    · subst hk
      rw [hnode k p e hi]
      simp
    · subst hk1
      rw [hnode (i + 1) p e (hi.trans (getD_succ_ge _ hA.sorted hA.last i))]
      simp
    · simp [embedFirst]
    · simp [embedFirst]
  | bubble i' s =>
    simp only [JetAxis.dofPoly]
    split_ifs with h
    · rw [h.1, hbub i s e hi]
      simp
    · simp [embedFirst]

end Internal

theorem jetSplineVanishesFrom : JetSplineVanishesFrom := by
  intro H tb hA _ hnode hbub i j hi
  change (∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs,
    MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly i d) * embedSecond (H.xAxis.dofPoly j e)) = 0
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e _ => ?_
  rw [Internal.dof_term_zero H tb hA hnode hbub i hi d e, zero_mul]

end GivenShape

end CertCell

end Breakdown

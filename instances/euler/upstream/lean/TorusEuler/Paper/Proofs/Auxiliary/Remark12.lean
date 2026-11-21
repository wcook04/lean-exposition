import TorusEuler.Paper.Auxiliary.Statements
import TorusEuler.Paper.S678.StepData

/-! # Proof of Remark 1.2 -/

open Filter Set

namespace TorusEuler.Paper

/-- (Conditional and unused since decision D28: the spine proves Remark 1.2 from the library,
`Paper.Proof.remark_1_2` in `Proofs/Rem12`; this version assumes the unproved
`Aux.Statement.theorem_1_1`.) **Proof of Remark 1.2** (sections/01_problem.tex:80-84). "The solution in Theorem 1.1 may be
chosen so that it extends smoothly in space and time through `T_*` away from the origin. A proof
is given in the auxiliary note." The remark is Theorem 1.1 of the note (`hAux_1_1`) applied to a
cutoff symbol, the floor `a₀ = 0`, the threshold that the first conjunct of the note's theorem
provides, and a large `N`; the solution, its maximality and the extension are read off. -/
theorem Proof.remark_1_2_of (hAux_1_1 : Aux.Statement.theorem_1_1) : Statement.remark_1_2 := by
  obtain ⟨ψ, hψ⟩ := exists_appendixB_cutoffSymbol
  obtain ⟨b, a, F, G, -, -, ⟨B, hF, hG⟩, hAll⟩ := hAux_1_1 ψ hψ 0
  obtain ⟨N₁, hN⟩ := hAll B hF hG
  obtain ⟨P, c, T, u, p, -, -, -, -, -, -, -, hW, hU, hE⟩ := hN N₁ le_rfl
  exact ⟨u 0, T, u, p, hW, hU, hE⟩

end TorusEuler.Paper

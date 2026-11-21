import TorusEuler.Paper.Spine

/-! # The main theorem

`TorusEuler.theorem11` is the projection of the spine theorem `TorusEuler.Paper.theorem_1_1`
(Theorem 1.1 of the latest manuscript) onto the existence part: the uniqueness clause of the
latest statement is dropped. -/

namespace TorusEuler

/-- **Theorem 1.1** (main theorem): the existence of an odd smooth initial datum whose Euler
solution develops the singularity, obtained from `Paper.theorem_1_1`. -/
theorem theorem11 : Theorem11 := by
  obtain ⟨u₀, T, u, p, hw, _⟩ := Paper.theorem_1_1
  exact ⟨u₀, T, u, p, hw⟩

end TorusEuler

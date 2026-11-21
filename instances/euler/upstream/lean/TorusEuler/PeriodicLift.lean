import TorusEuler.Statement

open Set

namespace TorusEuler

theorem isCompact_centeredCell : IsCompact centeredCell := by
  let box : Set (Fin 3 → ℝ) := pi univ fun _ => Icc (-(1 / 2 : ℝ)) (1 / 2)
  have hbox : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have himage : WithLp.toLp 2 '' box = centeredCell := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i (mem_univ i)
    · intro hx
      exact ⟨WithLp.ofLp x, fun i _ => hx i, rfl⟩
  rw [← himage]
  exact hbox.image (PiLp.continuous_toLp 2 fun _ => ℝ)

/-- Every point of the lift has a representative in the centered cell. -/
theorem exists_sub_latticeVector_mem_centeredCell (x : Vec3) :
    ∃ n : Fin 3 → ℤ, x - latticeVector n ∈ centeredCell := by
  refine ⟨fun i => ⌊x i + 1 / 2⌋, fun i => ?_⟩
  change -(1 / 2 : ℝ) ≤ x i - (⌊x i + 1 / 2⌋ : ℤ) ∧
    x i - (⌊x i + 1 / 2⌋ : ℤ) ≤ 1 / 2
  exact ⟨by linarith [Int.floor_le (x i + 1 / 2)],
    by linarith [Int.lt_floor_add_one (x i + 1 / 2)]⟩

theorem isClosed_range_latticeVector : IsClosed (range latticeVector) := by
  have hrange : range latticeVector =
      ⋂ i : Fin 3, (fun x : Vec3 => x i) ⁻¹' range (Int.cast : ℤ → ℝ) := by
    ext x
    rw [mem_iInter]
    constructor
    · rintro ⟨n, rfl⟩ i
      exact ⟨n i, rfl⟩
    · intro hx
      choose n hn using hx
      refine ⟨n, ?_⟩
      exact PiLp.ext fun i => hn i
  rw [hrange]
  exact isClosed_iInter fun i =>
    Real.isClosed_range_intCast.preimage (PiLp.continuous_apply 2 (fun _ => ℝ) i)

theorem isOpen_offOrigin : IsOpen offOrigin :=
  isClosed_range_latticeVector.isOpen_compl

end TorusEuler

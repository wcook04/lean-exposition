import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5Bridge.Construction

/-!
# S5a library: a launch for every parent

The statements of Proposition 5.2 and of the displays (5.13), (5.14) concern the parent alone, while
the coefficient bounds of Proposition 5.1 are stated with a launch `(k_*, t₀)`; the coefficients
`D_aX`, `(D_aX)^{-1}`, `M` do not depend on it. Any parent admits a launch: take `t₀ = 0` and a
rescaled coordinate vector `k_*` with `|κ(0,0)| = λ`.
-/

open Set

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

/-- Every parent with `λ ≥ 1` admits a launch (`t₀ = 0`, `k_* ≠ 0` with `|κ(0,0)| = λ`). -/
theorem exists_launch {T D lam : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure}
    (hT : 0 < T) (hP : S5.Parent T U X pU D lam) : ∃ (k : Vec3) (t₀ : ℝ), S5.Launch T X k lam t₀ := by
  let k₀ : Vec3 := EuclideanSpace.single 0 1
  have hk₀ : k₀ ≠ 0 := by
    intro h
    have := congrArg (fun v : Vec3 => v 0) h
    simp [k₀] at this
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hne := Bridge.Parent.waveVector_ne_zero hT hP hk₀ h₀ 0
  have hpos : 0 < ‖S5.waveVector X k₀ 0 0‖ := norm_pos_iff.mpr hne
  have hlam : 0 < lam := zero_lt_one.trans_le hP.frequency_ge_one
  have hlin : S5.waveVector X ((lam / ‖S5.waveVector X k₀ 0 0‖) • k₀) 0 0 =
      (lam / ‖S5.waveVector X k₀ 0 0‖) • S5.waveVector X k₀ 0 0 := by
    unfold S5.waveVector labelWaveVector
    exact map_smul _ _ _
  refine ⟨(lam / ‖S5.waveVector X k₀ 0 0‖) • k₀, 0, le_rfl, hT, ?_, ?_⟩
  · exact smul_ne_zero (div_pos hlam hpos).ne' hk₀
  · rw [hlin, norm_smul, Real.norm_of_nonneg (div_pos hlam hpos).le]
    field_simp

end

end TorusEuler.Paper.Lib.S5a

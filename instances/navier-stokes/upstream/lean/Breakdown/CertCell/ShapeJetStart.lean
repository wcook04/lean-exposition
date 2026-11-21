import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount atFirst)

namespace Internal

private theorem jetUnit_eval_zero_of_ne (n p : ℕ) (hp : p ≠ 0) : (jetUnit n p).eval 0 = 0 := by
  simp [jetUnit, zero_pow hp]

private theorem jetUnit_eval_one (n p : ℕ) (hn : n ≠ 0) : (jetUnit n p).eval 1 = 0 := by
  simp [jetUnit, zero_pow hn]

private theorem nodalLeft_eval_left (n p : ℕ) (a b : ℝ) (hp : p ≠ 0) :
    (nodalLeft n p a b).eval (a : ℂ) = 0 := by
  simp only [nodalLeft, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, sub_self, mul_zero, jetUnit_eval_zero_of_ne n p hp]

private theorem nodalRight_eval_left (n p : ℕ) (a b : ℝ) (hn : n ≠ 0) (hab : a ≠ b) :
    (nodalRight n p a b).eval (a : ℂ) = 0 := by
  have hba : (b : ℂ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.symm)
  have hone : (((b - a)⁻¹ : ℝ) : ℂ) * ((b : ℂ) - a) = 1 := by
    push_cast
    exact inv_mul_cancel₀ hba
  simp only [nodalRight, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, hone, jetUnit_eval_one n p hn, mul_zero]

private theorem bubblePoly_eval_left (n s : ℕ) (a b : ℝ) (hn : n ≠ 0) :
    (bubblePoly n s a b).eval (a : ℂ) = 0 := by
  simp [bubblePoly, zero_pow hn]

private theorem breaks_start (A : JetAxis) (hA : IsJetAxis A 0 1) :
    A.breaks.getD 0 0 = 0 ∧ 0 < A.breaks.getD 1 0 := by
  have hf := hA.first
  have hl := hA.last
  have hs := hA.sorted
  match hb : A.breaks with
  | [] => simp [hb] at hf
  | [x] =>
    rw [hb] at hf hl
    simp at hf hl
    rw [hf] at hl
    norm_num at hl
  | x :: y :: l =>
    rw [hb] at hf hs
    simp at hf
    subst hf
    refine ⟨rfl, ?_⟩
    exact List.rel_of_pairwise_cons hs (by simp)

private theorem dofPoly_start_eval (A : JetAxis) (hA : IsJetAxis A 0 1) (d : JetDof)
    (hd : d ≠ JetDof.node 0 0) : (A.dofPoly 0 d).eval 0 = 0 := by
  have hn : A.depth ≠ 0 := by have := hA.depth_pos; omega
  obtain ⟨h0, h1⟩ := breaks_start A hA
  have he : Polynomial.eval (0 : ℂ) = Polynomial.eval ((A.breaks.getD 0 0 : ℝ) : ℂ) := by
    rw [h0]
    simp
  rw [he]
  cases d with
  | node k p =>
    simp only [JetAxis.dofPoly]
    split_ifs with hp hk hk1
    · subst hk
      have hp0 : p ≠ 0 := by
        rintro rfl
        exact hd rfl
      exact nodalLeft_eval_left A.depth p (A.breaks.getD 0 0) (A.breaks.getD (0 + 1) 0) hp0
    · exact nodalRight_eval_left A.depth p (A.breaks.getD 0 0) (A.breaks.getD (0 + 1) 0) hn
        (by rw [h0]; exact h1.ne)
    · simp
    · simp
  | bubble i s =>
    simp only [JetAxis.dofPoly]
    split_ifs with hi
    · exact bubblePoly_eval_left A.depth s (A.breaks.getD 0 0) (A.breaks.getD (0 + 1) 0) hn
    · simp

private theorem atFirst_embedFirst (c : ℂ) (P : Polynomial ℂ) :
    atFirst c (embedFirst P) = MvPolynomial.C (P.eval c) := by
  rw [atFirst, embedFirst, ← Polynomial.aeval_algHom_apply, MvPolynomial.bind₁_X_right, if_pos rfl,
    ← MvPolynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

end Internal

theorem jetStartVanish : JetStartVanish := by
  intro H ht _ hv j _
  have hterm : ∀ d e, atFirst 0 (MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly 0 d) *
      embedSecond (H.xAxis.dofPoly j e)) = 0 := by
    intro d e
    by_cases hd : d = JetDof.node 0 0
    · subst hd
      rw [hv e]
      simp [atFirst]
    · have hmul : atFirst 0 (MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly 0 d) *
          embedSecond (H.xAxis.dofPoly j e)) =
          atFirst 0 (MvPolynomial.C (H.coef d e)) * atFirst 0 (embedFirst (H.tAxis.dofPoly 0 d)) *
            atFirst 0 (embedSecond (H.xAxis.dofPoly j e)) := by
        simp only [atFirst, map_mul]
      rw [hmul, Internal.atFirst_embedFirst, Internal.dofPoly_start_eval H.tAxis ht d hd]
      simp
  show atFirst 0 (∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs, _) = 0
  simp only [atFirst, map_sum]
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e _ => ?_
  exact hterm d e

end GivenShape

end CertCell

end Breakdown

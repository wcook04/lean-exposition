import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount atFirst atSecond tDeriv xDeriv)

namespace Internal

theorem tDeriv_map_conj (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    tDeriv o (MvPolynomial.map (starRingEnd ℂ) P) = MvPolynomial.map (starRingEnd ℂ) (tDeriv o P) := by
  unfold tDeriv
  induction o with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, MvPolynomial.pderiv_map]

theorem xDeriv_map_conj (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.map (starRingEnd ℂ) P) = MvPolynomial.map (starRingEnd ℂ) (xDeriv o P) := by
  unfold xDeriv
  induction o with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, MvPolynomial.pderiv_map]

theorem atFirst_map_conj (r : ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    atFirst (r : ℂ) (MvPolynomial.map (starRingEnd ℂ) P) =
      MvPolynomial.map (starRingEnd ℂ) (atFirst (r : ℂ) P) := by
  unfold atFirst
  rw [MvPolynomial.map_bind₁]
  congr 1
  congr 1
  funext k
  split_ifs <;> simp

theorem atSecond_map_conj (r : ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    atSecond (r : ℂ) (MvPolynomial.map (starRingEnd ℂ) P) =
      MvPolynomial.map (starRingEnd ℂ) (atSecond (r : ℂ) P) := by
  unfold atSecond
  rw [MvPolynomial.map_bind₁]
  congr 1
  congr 1
  funext k
  split_ifs <;> simp

theorem eval_real_map_conj (t x : ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.map (starRingEnd ℂ) P) =
      starRingEnd ℂ (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] P) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  congr 1
  funext k
  fin_cases k <;> simp

end Internal

theorem splineConjugation : SplineConjugation := by
  intro a b S hS
  refine ⟨⟨hS.mesh, ?_, ?_⟩, ?_⟩
  · intro i hi hic j hj o ho
    change atFirst _ (tDeriv o (MvPolynomial.map (starRingEnd ℂ) (S.piece (i - 1) j))) =
      atFirst _ (tDeriv o (MvPolynomial.map (starRingEnd ℂ) (S.piece i j)))
    rw [Internal.tDeriv_map_conj, Internal.tDeriv_map_conj, Internal.atFirst_map_conj,
      Internal.atFirst_map_conj]
    exact congrArg _ (hS.t_joins i hi hic j hj o ho)
  · intro j hj hjc i hi o ho
    change atSecond _ (xDeriv o (MvPolynomial.map (starRingEnd ℂ) (S.piece i (j - 1)))) =
      atSecond _ (xDeriv o (MvPolynomial.map (starRingEnd ℂ) (S.piece i j)))
    rw [Internal.xDeriv_map_conj, Internal.xDeriv_map_conj, Internal.atSecond_map_conj,
      Internal.atSecond_map_conj]
    exact congrArg _ (hS.x_joins j hj hjc i hi o ho)
  · intro t x
    exact Internal.eval_real_map_conj t x _

end GivenShape

end CertCell

end Breakdown

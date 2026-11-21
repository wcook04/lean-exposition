import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount)

namespace Internal

private theorem jetUnit_map_conj (n p : ℕ) : (jetUnit n p).map (starRingEnd ℂ) = jetUnit n p := by
  simp [jetUnit, Polynomial.map_sum, map_inv₀, map_natCast]

private theorem nodalLeft_map_conj (n p : ℕ) (a b : ℝ) : (nodalLeft n p a b).map (starRingEnd ℂ) = nodalLeft n p a b := by
  rw [nodalLeft, Polynomial.map_mul, Polynomial.map_comp, jetUnit_map_conj]
  simp

private theorem nodalRight_map_conj (n p : ℕ) (a b : ℝ) :
    (nodalRight n p a b).map (starRingEnd ℂ) = nodalRight n p a b := by
  rw [nodalRight, Polynomial.map_mul, Polynomial.map_comp, jetUnit_map_conj]
  simp

private theorem bubblePoly_map_conj (n s : ℕ) (a b : ℝ) :
    (bubblePoly n s a b).map (starRingEnd ℂ) = bubblePoly n s a b := by
  simp only [bubblePoly, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Complex.conj_ofReal]

private theorem dofPoly_map_conj (A : JetAxis) (i : ℕ) (d : JetDof) :
    (A.dofPoly i d).map (starRingEnd ℂ) = A.dofPoly i d := by
  cases d with
  | node k p =>
    simp only [JetAxis.dofPoly]
    split_ifs <;> simp [nodalLeft_map_conj, nodalRight_map_conj]
  | bubble i' s =>
    simp only [JetAxis.dofPoly]
    split_ifs <;> simp [bubblePoly_map_conj]

private theorem embedFirst_map_conj (P : Polynomial ℂ) (hP : P.map (starRingEnd ℂ) = P) :
    MvPolynomial.map (starRingEnd ℂ) (embedFirst P) = embedFirst P := by
  unfold embedFirst
  conv_rhs => rw [← hP]
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
    MvPolynomial.map_X]
  congr 1
  ext c
  simp [MvPolynomial.algebraMap_eq]

private theorem embedSecond_map_conj (P : Polynomial ℂ) (hP : P.map (starRingEnd ℂ) = P) :
    MvPolynomial.map (starRingEnd ℂ) (embedSecond P) = embedSecond P := by
  unfold embedSecond
  conv_rhs => rw [← hP]
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
    MvPolynomial.map_X]
  congr 1
  ext c
  simp [MvPolynomial.algebraMap_eq]

private def withCoef (H : JetSpline) (c : JetDof → JetDof → ℂ) : JetSpline := ⟨H.tAxis, H.xAxis, c⟩

private theorem toSpline_conj_piece (H : JetSpline) (i j : ℕ) :
    H.toSpline.conj.piece i j = (withCoef H (fun d e => starRingEnd ℂ (H.coef d e))).toSpline.piece i j := by
  simp only [Spline.conj, JetSpline.toSpline, withCoef, map_sum, map_mul, MvPolynomial.map_C,
    embedFirst_map_conj _ (dofPoly_map_conj _ _ _), embedSecond_map_conj _ (dofPoly_map_conj _ _ _)]

private theorem withCoef_add_piece (H : JetSpline) (c c' : JetDof → JetDof → ℂ) (i j : ℕ) :
    (withCoef H (fun d e => c d e + c' d e)).toSpline.piece i j =
      (withCoef H c).toSpline.piece i j + (withCoef H c').toSpline.piece i j := by
  simp only [JetSpline.toSpline, withCoef, map_add, add_mul, Finset.sum_add_distrib]

private theorem withCoef_sub_piece (H : JetSpline) (c c' : JetDof → JetDof → ℂ) (i j : ℕ) :
    (withCoef H (fun d e => c d e - c' d e)).toSpline.piece i j =
      (withCoef H c).toSpline.piece i j - (withCoef H c').toSpline.piece i j := by
  simp only [JetSpline.toSpline, withCoef, map_sub, sub_mul, Finset.sum_sub_distrib]

private theorem withCoef_self (H : JetSpline) : withCoef H H.coef = H := rfl

private theorem reflectPoly_add (P Q : MvPolynomial (Fin 2) ℂ) : reflectPoly (P + Q) = reflectPoly P + reflectPoly Q := by
  simp [reflectPoly]

private theorem reflectPoly_sub (P Q : MvPolynomial (Fin 2) ℂ) : reflectPoly (P - Q) = reflectPoly P - reflectPoly Q := by
  simp [reflectPoly]

private theorem dofSign_conj (e : JetDof) : starRingEnd ℂ (JetAxis.dofSign e) = JetAxis.dofSign e := by
  cases e <;> simp [JetAxis.dofSign]

private theorem sign_conj (odd : Bool) : starRingEnd ℂ (if odd then -1 else 1 : ℂ) = (if odd then -1 else 1 : ℂ) := by
  cases odd <;> simp

private theorem sign_not (odd : Bool) : (if !odd then -1 else 1 : ℂ) = -(if odd then -1 else 1 : ℂ) := by
  cases odd <;> simp

end Internal

open Internal in
theorem jetConjReflection_of_jetReflection (hR : JetReflection) : JetConjReflection := by
  intro odd H ht hx hsym hfix
  set σ : ℂ := (if odd then -1 else 1 : ℂ) with hσ
  set c' : JetDof → JetDof → ℂ := fun d e => starRingEnd ℂ (H.coef d e) with hc'
  have hfix' : ∀ d, ∀ e ∈ H.xAxis.dofs, c' d (H.xAxis.reflectDof e) = σ * JetAxis.dofSign e * H.coef d e := by
    intro d e he
    simp only [hc', hfix d e he, map_mul, sign_conj, dofSign_conj, Complex.conj_conj, hσ]
  set K := withCoef H (fun d e => H.coef d e + c' d e) with hK
  set L := withCoef H (fun d e => H.coef d e - c' d e) with hL
  have hKfix : K.IsReflectFixed odd := by
    intro d e he
    change H.coef d (H.xAxis.reflectDof e) + c' d (H.xAxis.reflectDof e) =
      σ * JetAxis.dofSign e * (H.coef d e + c' d e)
    rw [hfix d e he, hfix' d e he]
    ring
  have hLfix : L.IsReflectFixed (!odd) := by
    intro d e he
    change H.coef d (H.xAxis.reflectDof e) - c' d (H.xAxis.reflectDof e) =
      (if !odd then -1 else 1 : ℂ) * JetAxis.dofSign e * (H.coef d e - c' d e)
    rw [hfix d e he, hfix' d e he, sign_not]
    ring
  have hKa := hR odd K ht hx hsym hKfix
  have hLa := hR (!odd) L ht hx hsym hLfix
  refine ⟨hKa.mesh_eq, ?_⟩
  intro i hi j hj
  have e1 := hKa.piece_eq i hi j hj
  have e2 := hLa.piece_eq i hi j hj
  set n := cellCount H.xAxis.breaks - 1 - j with hn
  change K.toSpline.piece i j = MvPolynomial.C σ * reflectPoly (K.toSpline.piece i n) at e1
  change L.toSpline.piece i j = MvPolynomial.C (if !odd then -1 else 1 : ℂ) * reflectPoly (L.toSpline.piece i n) at e2
  change H.toSpline.piece i j = MvPolynomial.C σ * reflectPoly (H.toSpline.conj.piece i n)
  rw [toSpline_conj_piece]
  rw [hK, withCoef_add_piece, withCoef_add_piece, withCoef_self, reflectPoly_add] at e1
  rw [hL, withCoef_sub_piece, withCoef_sub_piece, withCoef_self, reflectPoly_sub, sign_not, map_neg, ← hσ] at e2
  have h2 : (2 : MvPolynomial (Fin 2) ℂ) * H.toSpline.piece i j =
      2 * (MvPolynomial.C σ * reflectPoly ((withCoef H c').toSpline.piece i n)) := by
    linear_combination e1 + e2
  exact mul_left_cancel₀ two_ne_zero h2

end GivenShape

end CertCell

end Breakdown

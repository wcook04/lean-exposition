import Breakdown.CertCell.ShapeStatements
import Breakdown.CertCell.ShapeJetUnit

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline TensorMesh cellCount atFirst atSecond tDeriv xDeriv)
open Polynomial

namespace Internal

theorem pderiv_zero_embedFirst (P : ℂ[X]) :
    MvPolynomial.pderiv 0 (embedFirst P) = embedFirst (derivative P) := by
  unfold embedFirst
  rw [Derivation.map_aeval, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]

theorem pderiv_zero_embedSecond (Q : ℂ[X]) : MvPolynomial.pderiv 0 (embedSecond Q) = 0 := by
  unfold embedSecond
  rw [Derivation.map_aeval, MvPolynomial.pderiv_X_of_ne (by decide), smul_zero]

theorem pderiv_one_embedSecond (Q : ℂ[X]) :
    MvPolynomial.pderiv 1 (embedSecond Q) = embedSecond (derivative Q) := by
  unfold embedSecond
  rw [Derivation.map_aeval, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]

theorem pderiv_one_embedFirst (P : ℂ[X]) : MvPolynomial.pderiv 1 (embedFirst P) = 0 := by
  unfold embedFirst
  rw [Derivation.map_aeval, MvPolynomial.pderiv_X_of_ne (by decide), smul_zero]

theorem iterate_pderiv_sum (k : Fin 2) (o : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin 2) ℂ) :
    (MvPolynomial.pderiv k)^[o] (∑ x ∈ s, f x) = ∑ x ∈ s, (MvPolynomial.pderiv k)^[o] (f x) := by
  induction o with
  | zero => rfl
  | succ o ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    simp only [Function.iterate_succ_apply']

theorem tDeriv_sum (o : ℕ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    tDeriv o (∑ x ∈ s, f x) = ∑ x ∈ s, tDeriv o (f x) :=
  iterate_pderiv_sum 0 o s f

theorem xDeriv_sum (o : ℕ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    xDeriv o (∑ x ∈ s, f x) = ∑ x ∈ s, xDeriv o (f x) :=
  iterate_pderiv_sum 1 o s f

theorem tDeriv_term (o : ℕ) (c : ℂ) (P Q : ℂ[X]) :
    tDeriv o (MvPolynomial.C c * embedFirst P * embedSecond Q) =
      MvPolynomial.C c * embedFirst (derivative^[o] P) * embedSecond Q := by
  induction o with
  | zero => rfl
  | succ o ih =>
    unfold tDeriv at ih ⊢
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Derivation.leibniz,
      Derivation.leibniz, MvPolynomial.pderiv_C, pderiv_zero_embedFirst, pderiv_zero_embedSecond]
    simp only [smul_eq_mul, mul_zero, zero_add, add_zero]
    ring

theorem xDeriv_term (o : ℕ) (c : ℂ) (P Q : ℂ[X]) :
    xDeriv o (MvPolynomial.C c * embedFirst P * embedSecond Q) =
      MvPolynomial.C c * embedFirst P * embedSecond (derivative^[o] Q) := by
  induction o with
  | zero => rfl
  | succ o ih =>
    unfold xDeriv at ih ⊢
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Derivation.leibniz,
      Derivation.leibniz, MvPolynomial.pderiv_C, pderiv_one_embedFirst, pderiv_one_embedSecond]
    simp only [smul_eq_mul, mul_zero, add_zero]

theorem atFirst_term (z c : ℂ) (P Q : ℂ[X]) :
    atFirst z (MvPolynomial.C c * embedFirst P * embedSecond Q) =
      MvPolynomial.C c * MvPolynomial.C (P.eval z) * embedSecond Q := by
  unfold atFirst embedFirst embedSecond
  rw [map_mul, map_mul, MvPolynomial.bind₁_C_right, ← Polynomial.aeval_algHom_apply,
    ← Polynomial.aeval_algHom_apply, MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right]
  simp only [if_true, show ((1 : Fin 2) = 0) = False by decide, if_false]
  rw [← MvPolynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

theorem atSecond_term (z c : ℂ) (P Q : ℂ[X]) :
    atSecond z (MvPolynomial.C c * embedFirst P * embedSecond Q) =
      MvPolynomial.C c * embedFirst P * MvPolynomial.C (Q.eval z) := by
  unfold atSecond embedFirst embedSecond
  rw [map_mul, map_mul, MvPolynomial.bind₁_C_right, ← Polynomial.aeval_algHom_apply,
    ← Polynomial.aeval_algHom_apply, MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right]
  simp only [if_true, show ((0 : Fin 2) = 1) = False by decide, if_false]
  rw [← MvPolynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

theorem getD_lt_getD_of_sorted {l : List ℝ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (hij.trans hj), List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hl i j (hij.trans hj) hj hij

theorem dofPoly_jets_agree (hLl : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n →
      (derivative^[o] (nodalLeft n p a b)).eval (a : ℂ) = if o = p then 1 else 0)
    (hLr : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n → (derivative^[o] (nodalLeft n p a b)).eval (b : ℂ) = 0)
    (hRr : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n →
      (derivative^[o] (nodalRight n p a b)).eval (b : ℂ) = if o = p then 1 else 0)
    (hRl : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n → (derivative^[o] (nodalRight n p a b)).eval (a : ℂ) = 0)
    (hBl : ∀ (n s o : ℕ) (a b : ℝ), o < n → (derivative^[o] (bubblePoly n s a b)).eval (a : ℂ) = 0)
    (hBr : ∀ (n s o : ℕ) (a b : ℝ), o < n → (derivative^[o] (bubblePoly n s a b)).eval (b : ℂ) = 0)
    (A : JetAxis) (hA : A.breaks.Pairwise (· < ·)) (i : ℕ) (hi1 : 1 ≤ i) (hi : i < cellCount A.breaks)
    (o : ℕ) (ho : o < A.depth) (d : JetDof) :
    (derivative^[o] (A.dofPoly (i - 1) d)).eval ((A.breaks.getD i 0 : ℝ) : ℂ) =
      (derivative^[o] (A.dofPoly i d)).eval ((A.breaks.getD i 0 : ℝ) : ℂ) := by
  have hlen : i + 1 < A.breaks.length := by unfold cellCount at hi; omega
  have hab : A.breaks.getD (i - 1) 0 ≠ A.breaks.getD i 0 :=
    (getD_lt_getD_of_sorted hA (by omega) (by omega)).ne
  have hbc : A.breaks.getD i 0 ≠ A.breaks.getD (i + 1) 0 :=
    (getD_lt_getD_of_sorted hA (by omega) hlen).ne
  have hsub : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  cases d with
  | node k p =>
    simp only [JetAxis.dofPoly, hsub]
    by_cases hp : p < A.depth
    · simp only [hp, if_true]
      by_cases h1 : k = i - 1
      · have h2 : k ≠ i := by omega
        have h3 : k ≠ i + 1 := by omega
        simp only [h1, if_true, show i - 1 ≠ i by omega, show i - 1 ≠ i + 1 by omega, if_false,
          iterate_derivative_zero, eval_zero]
        rw [← hsub, hLr _ _ _ (hsub ▸ hab) ho]
      · by_cases h2 : k = i
        · subst h2
          simp only [h1, if_false, if_true]
          rw [hRr _ _ _ hab ho, hLl _ _ _ hbc ho]
        · by_cases h3 : k = i + 1
          · subst h3
            simp only [h1, h2, if_false, if_true, iterate_derivative_zero, eval_zero]
            rw [hRl _ _ _ hbc ho]
          · simp only [h1, h2, h3, if_false, iterate_derivative_zero, eval_zero]
    · simp only [hp, if_false]
  | bubble i' s =>
    simp only [JetAxis.dofPoly, hsub]
    split_ifs
    · rw [hBr _ _ _ _ _ ho, hBl _ _ _ _ _ ho]
    · rw [hBr _ _ _ _ _ ho, iterate_derivative_zero, eval_zero]
    · rw [hBl _ _ _ _ _ ho, iterate_derivative_zero, eval_zero]
    · rfl

theorem atFirst_sum (z : ℂ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    atFirst z (∑ x ∈ s, f x) = ∑ x ∈ s, atFirst z (f x) := by
  unfold atFirst
  exact map_sum _ _ _

theorem atSecond_sum (z : ℂ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    atSecond z (∑ x ∈ s, f x) = ∑ x ∈ s, atSecond z (f x) := by
  unfold atSecond
  exact map_sum _ _ _

theorem toSpline_piece (H : JetSpline) (i j : ℕ) :
    H.toSpline.piece i j = ∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs,
      MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly i d) * embedSecond (H.xAxis.dofPoly j e) :=
  rfl

theorem toSpline_tBreaks (H : JetSpline) : H.toSpline.mesh.tBreaks = H.tAxis.breaks := rfl

theorem toSpline_xBreaks (H : JetSpline) : H.toSpline.mesh.xBreaks = H.xAxis.breaks := rfl

theorem jetSpline_isJoined_of_endJets (hLl : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n →
      (derivative^[o] (nodalLeft n p a b)).eval (a : ℂ) = if o = p then 1 else 0)
    (hLr : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n → (derivative^[o] (nodalLeft n p a b)).eval (b : ℂ) = 0)
    (hRr : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n →
      (derivative^[o] (nodalRight n p a b)).eval (b : ℂ) = if o = p then 1 else 0)
    (hRl : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n → (derivative^[o] (nodalRight n p a b)).eval (a : ℂ) = 0)
    (hBl : ∀ (n s o : ℕ) (a b : ℝ), o < n → (derivative^[o] (bubblePoly n s a b)).eval (a : ℂ) = 0)
    (hBr : ∀ (n s o : ℕ) (a b : ℝ), o < n → (derivative^[o] (bubblePoly n s a b)).eval (b : ℂ) = 0)
    (H : JetSpline) (ht : IsJetAxis H.tAxis 0 1) (hx : IsJetAxis H.xAxis (-1) 1) :
    IsJoinedSpline (H.tAxis.depth - 1) (H.xAxis.depth - 1) H.toSpline := by
  refine ⟨⟨ht.sorted, hx.sorted, ht.first, ht.last, hx.first, hx.last⟩, ?_, ?_⟩
  · intro i hi1 hi j hj o ho
    rw [toSpline_tBreaks] at hi ⊢
    have ho' : o < H.tAxis.depth := by have := ht.depth_pos; omega
    rw [toSpline_piece, toSpline_piece, tDeriv_sum, tDeriv_sum, atFirst_sum, atFirst_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [tDeriv_sum, tDeriv_sum, atFirst_sum, atFirst_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [tDeriv_term, tDeriv_term, atFirst_term, atFirst_term,
      dofPoly_jets_agree hLl hLr hRr hRl hBl hBr H.tAxis ht.sorted i hi1 hi o ho' d]
  · intro j hj1 hj i hi o ho
    rw [toSpline_xBreaks] at hj ⊢
    have ho' : o < H.xAxis.depth := by have := hx.depth_pos; omega
    rw [toSpline_piece, toSpline_piece, xDeriv_sum, xDeriv_sum, atSecond_sum, atSecond_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [xDeriv_sum, xDeriv_sum, atSecond_sum, atSecond_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [xDeriv_term, xDeriv_term, atSecond_term, atSecond_term,
      dofPoly_jets_agree hLl hLr hRr hRl hBl hBr H.xAxis hx.sorted j hj1 hj o ho' e]

end Internal

theorem jetSplineJoined_of_endJets (hLl : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n →
      (derivative^[o] (nodalLeft n p a b)).eval (a : ℂ) = if o = p then 1 else 0)
    (hLr : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n → (derivative^[o] (nodalLeft n p a b)).eval (b : ℂ) = 0)
    (hRr : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n →
      (derivative^[o] (nodalRight n p a b)).eval (b : ℂ) = if o = p then 1 else 0)
    (hRl : ∀ (n p o : ℕ) {a b : ℝ}, a ≠ b → o < n → (derivative^[o] (nodalRight n p a b)).eval (a : ℂ) = 0)
    (hBl : ∀ (n s o : ℕ) (a b : ℝ), o < n → (derivative^[o] (bubblePoly n s a b)).eval (a : ℂ) = 0)
    (hBr : ∀ (n s o : ℕ) (a b : ℝ), o < n → (derivative^[o] (bubblePoly n s a b)).eval (b : ℂ) = 0) : JetSplineJoined :=
  fun H ht hx => Internal.jetSpline_isJoined_of_endJets hLl hLr hRr hRl hBl hBr H ht hx

theorem jetSplineJoined : JetSplineJoined :=
  jetSplineJoined_of_endJets (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_left n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_left n p o hab ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_left n s o a b ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_right n s o a b ho)

end GivenShape

end CertCell

end Breakdown

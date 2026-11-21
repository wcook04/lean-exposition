import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount cellIndex atFirst atSecond tDeriv xDeriv)

namespace Internal

theorem eval_bind_two (v : Fin 2 → ℂ) (g : Fin 2 → MvPolynomial (Fin 2) ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g P) = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem reflectPoly_C_mul (s : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    reflectPoly (MvPolynomial.C s * P) = MvPolynomial.C s * reflectPoly P := by
  simp [reflectPoly]

theorem pderiv_zero_reflectPoly (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 0 (reflectPoly P) = reflectPoly (MvPolynomial.pderiv 0 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [reflectPoly]
  | add p q hp hq =>
    simp only [reflectPoly] at hp hq ⊢
    rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    simp only [reflectPoly] at hp ⊢
    simp only [map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_mul, map_add, hp]
    fin_cases i <;> simp [MvPolynomial.pderiv_X]

theorem pderiv_one_reflectPoly (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 1 (reflectPoly P) = -reflectPoly (MvPolynomial.pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [reflectPoly]
  | add p q hp hq =>
    simp only [reflectPoly] at hp hq ⊢
    rw [map_add, map_add, hp, hq, map_add, map_add, neg_add]
  | mul_X p i hp =>
    simp only [reflectPoly] at hp ⊢
    simp only [map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_mul, map_add, hp]
    fin_cases i
    · simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X]
      ring

theorem tDeriv_reflect (o : ℕ) (s : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    tDeriv o (MvPolynomial.C s * reflectPoly P) = MvPolynomial.C s * reflectPoly (tDeriv o P) := by
  induction o with
  | zero => simp [tDeriv]
  | succ n ih =>
    simp only [tDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, MvPolynomial.pderiv_C_mul, pderiv_zero_reflectPoly]

theorem xDeriv_reflect (o : ℕ) (s : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.C s * reflectPoly P) = MvPolynomial.C (s * (-1) ^ o) * reflectPoly (xDeriv o P) := by
  induction o with
  | zero => simp [xDeriv]
  | succ n ih =>
    simp only [xDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, MvPolynomial.pderiv_C_mul, pderiv_one_reflectPoly]
    simp only [pow_succ, map_mul, map_neg, map_one]
    ring

theorem atFirst_reflect (c s : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    atFirst c (MvPolynomial.C s * reflectPoly P) = MvPolynomial.C s * reflectPoly (atFirst c P) := by
  simp only [atFirst, reflectPoly, map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_bind₁]
  refine congrArg (fun g => MvPolynomial.C s * MvPolynomial.bind₁ g P) (funext fun k => ?_)
  fin_cases k <;> simp

theorem atSecond_reflect (c s : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    atSecond (-c) (MvPolynomial.C s * reflectPoly P) = MvPolynomial.C s * reflectPoly (atSecond c P) := by
  simp only [atSecond, reflectPoly, map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_bind₁]
  refine congrArg (fun g => MvPolynomial.C s * MvPolynomial.bind₁ g P) (funext fun k => ?_)
  fin_cases k <;> simp

theorem eval_reflect (t x : ℝ) (s : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.C s * reflectPoly P) =
      s * MvPolynomial.eval ![(t : ℂ), ((-x : ℝ) : ℂ)] P := by
  rw [map_mul, MvPolynomial.eval_C, reflectPoly, eval_bind_two]
  refine congrArg (fun v => s * MvPolynomial.eval v P) (funext fun k => ?_)
  fin_cases k <;> simp

theorem eval_atSecond_self (t y : ℝ) (Q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![(t : ℂ), (y : ℂ)] (atSecond (y : ℂ) Q) = MvPolynomial.eval ![(t : ℂ), (y : ℂ)] Q := by
  rw [atSecond, eval_bind_two]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun k => ?_)
  fin_cases k <;> simp

theorem cellCount_reflect (l : List ℝ) : cellCount (l.map Neg.neg).reverse = cellCount l := by
  simp [cellCount]

theorem interior_reflect (l : List ℝ) :
    (((l.map Neg.neg).reverse).drop 1).dropLast = (((l.drop 1).dropLast).map Neg.neg).reverse := by
  simp [List.drop_one, List.tail_reverse, List.dropLast_reverse, List.map_dropLast, List.map_tail,
    List.tail_dropLast]

theorem cellIndex_reflect (l : List ℝ) (x : ℝ) :
    cellIndex (l.map Neg.neg).reverse x = (((l.drop 1).dropLast).filter (fun b => decide (-x ≤ b))).length := by
  unfold cellIndex
  rw [interior_reflect, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter, List.countP_reverse,
    List.countP_map]
  congr 1
  funext b
  simp [neg_le]

theorem getD_reflect (l : List ℝ) (j : ℕ) (hj : j < l.length) :
    ((l.map Neg.neg).reverse).getD j 0 = -(l.getD (l.length - 1 - j) 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by omega)]
  simp [List.getElem_reverse]

theorem count_split (I : List ℝ) (hI : I.Nodup) (u : ℝ) :
    (I.filter (fun b => decide (u ≤ b))).length + (I.filter (fun b => decide (b ≤ u))).length =
      I.length + (if u ∈ I then 1 else 0) := by
  induction I with
  | nil => simp
  | cons a I ih =>
    rw [List.nodup_cons] at hI
    have h := ih hI.2
    rcases lt_trichotomy a u with h1 | h1 | h1
    · have hne : u ≠ a := ne_of_gt h1
      have e1 : (a :: I).filter (fun b => decide (u ≤ b)) = I.filter (fun b => decide (u ≤ b)) := by
        simp [not_le.2 h1]
      have e2 : (a :: I).filter (fun b => decide (b ≤ u)) = a :: I.filter (fun b => decide (b ≤ u)) := by
        simp [h1.le]
      have e3 : (u ∈ a :: I) ↔ u ∈ I := by simp [hne]
      simp only [e1, e2, e3, List.length_cons]
      omega
    · subst h1
      have e1 : (a :: I).filter (fun b => decide (a ≤ b)) = a :: I.filter (fun b => decide (a ≤ b)) := by
        simp
      have e2 : (a :: I).filter (fun b => decide (b ≤ a)) = a :: I.filter (fun b => decide (b ≤ a)) := by
        simp
      rw [if_neg hI.1] at h
      simp only [e1, e2, List.length_cons, List.mem_cons_self, if_true]
      omega
    · have hne : u ≠ a := ne_of_lt h1
      have e1 : (a :: I).filter (fun b => decide (u ≤ b)) = a :: I.filter (fun b => decide (u ≤ b)) := by
        simp [h1.le]
      have e2 : (a :: I).filter (fun b => decide (b ≤ u)) = I.filter (fun b => decide (b ≤ u)) := by
        simp [not_le.2 h1]
      have e3 : (u ∈ a :: I) ↔ u ∈ I := by simp [hne]
      simp only [e1, e2, e3, List.length_cons]
      omega

theorem sorted_filter_le (I : List ℝ) (hs : I.Pairwise (· < ·)) (p : ℕ) (hp : p < I.length) :
    (I.filter (fun b => decide (b ≤ I[p]))).length = p + 1 := by
  induction I generalizing p with
  | nil => simp at hp
  | cons a I ih =>
    rw [List.pairwise_cons] at hs
    rcases p with _ | p
    · have h0 : I.filter (fun b => decide (b ≤ a)) = [] :=
        List.filter_eq_nil_iff.2 fun y hy => by simp [not_le.2 (hs.1 y hy)]
      simp [h0]
    · have hp' : p < I.length := by simpa using hp
      have hlt : a < I[p] := hs.1 _ (List.getElem_mem hp')
      simp only [List.getElem_cons_succ, List.filter_cons, hlt.le, decide_true, if_true, List.length_cons,
        ih hs.2 p hp']

theorem breaks_two_le_length (l : List ℝ) {u v : ℝ} (huv : u ≠ v) (h1 : l.head? = some u) (h2 : l.getLast? = some v) :
    2 ≤ l.length := by
  match l, h1, h2 with
  | [], h1, _ => simp at h1
  | [c], h1, h2 => simp at h1 h2; exact absurd (h1.symm.trans h2) huv
  | _ :: _ :: _, _, _ => simp

theorem cellIndex_lt (l : List ℝ) (hl : 2 ≤ l.length) (u : ℝ) : cellIndex l u < cellCount l := by
  unfold cellIndex cellCount
  have := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).dropLast)
  simp only [List.length_dropLast, List.length_drop] at this
  omega

theorem getD_interior (l : List ℝ) (p : ℕ) (hp : p < ((l.drop 1).dropLast).length) :
    l.getD (p + 1) 0 = ((l.drop 1).dropLast)[p] := by
  cases l with
  | nil => simp at hp
  | cons c rest =>
    have hp' : p < rest.length := by simp at hp; omega
    simp [List.getElem?_eq_getElem hp']

theorem evalHalf_reflect (a b : ℕ) (odd : Bool) (S : Spline) (hS : IsJoinedSpline a b S) (t x : ℝ) :
    (reflectSpline odd S).evalHalf t x = (if odd then -1 else 1) * S.evalHalf t (-x) := by
  have hm := hS.mesh
  set l := S.mesh.xBreaks with hl
  set I := (l.drop 1).dropLast with hI
  have hlen : 2 ≤ l.length := breaks_two_le_length l (by norm_num) hm.x_first hm.x_last
  have htlen : 2 ≤ S.mesh.tBreaks.length := breaks_two_le_length _ (by norm_num) hm.t_first hm.t_last
  have hIlen : I.length = cellCount l - 1 := by
    simp only [hI, List.length_dropLast, List.length_drop, cellCount]
  have hIs : I.Pairwise (· < ·) := (hm.x_sorted.sublist (List.drop_sublist 1 l)).sublist (List.dropLast_sublist _)
  have hsplit := count_split I hIs.nodup (-x)
  have hti := cellIndex_lt _ htlen t
  simp only [Spline.evalHalf, reflectSpline]
  rw [eval_reflect]
  congr 1
  rw [cellIndex_reflect]
  change MvPolynomial.eval _ (S.piece _ (cellCount l - 1 - (I.filter (fun b => decide (-x ≤ b))).length)) =
    MvPolynomial.eval _ (S.piece _ ((I.filter (fun b => decide (b ≤ -x))).length))
  by_cases hx : -x ∈ I
  · rw [if_pos hx] at hsplit
    obtain ⟨p, hp, hpx⟩ := List.getElem_of_mem hx
    have hcount := sorted_filter_le I hIs p hp
    rw [hpx] at hcount
    rw [hcount]
    have e1 : cellCount l - 1 - (I.filter (fun b => decide (-x ≤ b))).length = p := by omega
    rw [e1]
    have hgd : l.getD (p + 1) 0 = -x := by
      rw [getD_interior l p hp]
      exact hpx
    have hj := hS.x_joins (p + 1) (by omega) (by rw [← hl]; omega) _ hti 0 (Nat.zero_le _)
    simp only [xDeriv, Function.iterate_zero, id, Nat.add_sub_cancel] at hj
    rw [← hl, hgd] at hj
    have := congrArg (MvPolynomial.eval ![(t : ℂ), (((-x : ℝ)) : ℂ)]) hj
    rwa [eval_atSecond_self, eval_atSecond_self] at this
  · rw [if_neg hx] at hsplit
    have e1 : cellCount l - 1 - (I.filter (fun b => decide (-x ≤ b))).length =
        (I.filter (fun b => decide (b ≤ -x))).length := by omega
    rw [e1]

theorem joined_reflect (a b : ℕ) (odd : Bool) (S : Spline) (hS : IsJoinedSpline a b S) :
    IsJoinedSpline a b (reflectSpline odd S) := by
  have hm := hS.mesh
  refine ⟨⟨hm.t_sorted, ?_, hm.t_first, hm.t_last, ?_, ?_⟩, ?_, ?_⟩
  · show ((S.mesh.xBreaks.map Neg.neg).reverse).Pairwise (· < ·)
    rw [List.pairwise_reverse, List.pairwise_map]
    exact hm.x_sorted.imp fun h => neg_lt_neg h
  · show ((S.mesh.xBreaks.map Neg.neg).reverse).head? = some (-1)
    rw [List.head?_reverse, List.getLast?_map, hm.x_last]
    rfl
  · show ((S.mesh.xBreaks.map Neg.neg).reverse).getLast? = some 1
    rw [List.getLast?_reverse, List.head?_map, hm.x_first]
    simp
  · intro i hi1 hi2 j hj o ho
    simp only [reflectSpline, cellCount_reflect] at hi2 hj ⊢
    rw [tDeriv_reflect, tDeriv_reflect, atFirst_reflect, atFirst_reflect,
      hS.t_joins i hi1 hi2 _ (by omega) o ho]
  · intro j hj1 hj2 i hi o ho
    simp only [reflectSpline, cellCount_reflect] at hj2 hi ⊢
    have hlen : j < S.mesh.xBreaks.length := by unfold cellCount at hj2; omega
    rw [getD_reflect _ _ hlen, Complex.ofReal_neg, xDeriv_reflect, xDeriv_reflect, atSecond_reflect,
      atSecond_reflect]
    have hj := hS.x_joins (cellCount S.mesh.xBreaks - j) (by omega) (by omega) i hi o ho
    have e0 : S.mesh.xBreaks.length - 1 - j = cellCount S.mesh.xBreaks - j := by unfold cellCount; omega
    have e1 : cellCount S.mesh.xBreaks - 1 - (j - 1) = cellCount S.mesh.xBreaks - j := by omega
    have e2 : cellCount S.mesh.xBreaks - 1 - j = cellCount S.mesh.xBreaks - j - 1 := by omega
    rw [e0, e1, e2, hj]

end Internal

theorem splineReflection : SplineReflection := fun a b odd S hS =>
  ⟨Internal.joined_reflect a b odd S hS, Internal.evalHalf_reflect a b odd S hS⟩

end GivenShape

end CertCell

end Breakdown

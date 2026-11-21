import Breakdown.CertCell.ShapeJetScaled

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount)
open Polynomial

namespace Internal

theorem sortedGetD_lt {l : List ℝ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (hij.trans hj), List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hl i j (hij.trans hj) hj hij

theorem symmetricJacobi_natDegree_le (α j : ℕ) : (symmetricJacobi α j).natDegree ≤ j := by
  unfold symmetricJacobi
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : ((X : ℝ[X]) - 1).natDegree ≤ 1 := by
    rw [← C_1]; exact natDegree_X_sub_C_le _
  have h2 : ((X : ℝ[X]) + 1).natDegree ≤ 1 := by
    rw [← C_1]; exact natDegree_add_le_of_degree_le (by simp) (by simp)
  refine natDegree_mul_le.trans ?_
  refine (Nat.add_le_add ((natDegree_C_mul_le _ _).trans natDegree_pow_le) natDegree_pow_le).trans ?_
  have h3 : (j - i) * ((X : ℝ[X]) - 1).natDegree ≤ j - i := by
    simpa using Nat.mul_le_mul_left (j - i) h1
  have h4 : i * ((X : ℝ[X]) + 1).natDegree ≤ i := by
    simpa using Nat.mul_le_mul_left i h2
  omega

theorem jacobiBubble_real_expand (n j bc : ℕ) (c a b : ℝ) (hh : b - a ≠ 0) (hj : j < bc) :
    ∑ s ∈ Finset.range bc, C (c * (4 / (b - a) ^ 2) ^ n * (2 / (b - a)) ^ s * (symmetricJacobi (2 * n) j).coeff s) *
      (((X - C a) * (C b - X)) ^ n * (X - C ((a + b) / 2)) ^ s) =
      C c * (1 - cellVariable a b ^ 2) ^ n * (symmetricJacobi (2 * n) j).comp (cellVariable a b) := by
  have hdeg : (symmetricJacobi (2 * n) j).natDegree < bc :=
    lt_of_le_of_lt (symmetricJacobi_natDegree_le _ _) hj
  apply Polynomial.funext
  intro x
  have hv : (cellVariable a b).eval x = 2 / (b - a) * (x - (a + b) / 2) := by
    simp only [cellVariable, eval_sub, eval_mul, eval_C, eval_X]
    field_simp
  have h1 : 1 - (2 / (b - a) * (x - (a + b) / 2)) ^ 2 = 4 / (b - a) ^ 2 * ((x - a) * (b - x)) := by
    field_simp
    ring
  rw [eval_mul, eval_comp, eval_eq_sum_range' hdeg, eval_mul, eval_pow, eval_sub, eval_one, eval_pow, hv, h1,
    eval_C, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  simp only [mul_pow]
  ring

theorem bubblePoly_eq_map (n s : ℕ) (a b : ℝ) :
    bubblePoly n s a b = ((((X - C a) * (C b - X)) ^ n * (X - C ((a + b) / 2)) ^ s : ℝ[X])).map (algebraMap ℝ ℂ) := by
  simp [bubblePoly, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub]

theorem jacobiBubble_expand (n j bc : ℕ) (c a b : ℝ) (hh : b - a ≠ 0) (hj : j < bc) :
    ∑ s ∈ Finset.range bc, C (((c * (4 / (b - a) ^ 2) ^ n * (2 / (b - a)) ^ s *
      (symmetricJacobi (2 * n) j).coeff s : ℝ) : ℂ)) * bubblePoly n s a b = jacobiBubble n j c a b := by
  unfold jacobiBubble
  rw [← jacobiBubble_real_expand n j bc c a b hh hj, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, bubblePoly_eq_map]
  rfl

theorem scaledAxis_dofPoly_sum (A : ScaledJetAxis) (hA : A.breaks.Pairwise (· < ·)) (i : ℕ)
    (hi : i < cellCount A.breaks) (d' : JetDof) (hd' : d' ∈ A.base.dofs) :
    ∑ d ∈ A.base.dofs, C (A.convert d d') * A.base.dofPoly i d = A.dofPoly i d' := by
  cases d' with
  | node k' p' =>
    rw [Finset.sum_eq_single_of_mem (JetDof.node k' p') hd']
    · simp [ScaledJetAxis.convert, ScaledJetAxis.dofPoly]
    · intro d _ hne
      cases d with
      | node k p =>
        have : ¬ (k = k' ∧ p = p') := by
          rintro ⟨rfl, rfl⟩; exact hne rfl
        simp [ScaledJetAxis.convert, this]
      | bubble i s => simp [ScaledJetAxis.convert]
  | bubble i' j =>
    have hmem := hd'
    simp only [JetAxis.dofs, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      reduceCtorEq, and_false, exists_false, false_or, JetDof.bubble.injEq] at hmem
    obtain ⟨⟨i'', s''⟩, ⟨hi'', hs''⟩, rfl, rfl⟩ := hmem
    have hdisj : Disjoint
        (((Finset.range (cellCount A.base.breaks + 1)) ×ˢ (Finset.range A.base.depth)).image
          (fun kp => JetDof.node kp.1 kp.2))
        (((Finset.range (cellCount A.base.breaks)) ×ˢ (Finset.range A.base.bubbleCount)).image
          (fun is => JetDof.bubble is.1 is.2)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      simp only [Finset.mem_image] at hd1 hd2
      obtain ⟨_, _, rfl⟩ := hd1
      obtain ⟨_, _, h⟩ := hd2
      exact JetDof.noConfusion h
    rw [JetAxis.dofs, Finset.sum_union hdisj, Finset.sum_eq_zero (fun d hd => by
      simp only [Finset.mem_image] at hd
      obtain ⟨_, _, rfl⟩ := hd
      simp [ScaledJetAxis.convert]), zero_add,
      Finset.sum_image (fun x _ y _ h => by
        simp only [JetDof.bubble.injEq] at h
        exact Prod.ext h.1 h.2),
      Finset.sum_product, Finset.sum_eq_single_of_mem i'' (Finset.mem_range.mpr hi'')]
    · simp only [ScaledJetAxis.convert, if_true]
      by_cases hii : i'' = i
      · subst hii
        have hsub : A.breaks.getD (i'' + 1) 0 - A.breaks.getD i'' 0 ≠ 0 := by
          have hlen : i'' + 1 < A.breaks.length := by unfold cellCount at hi; omega
          exact sub_ne_zero.mpr (sortedGetD_lt hA (Nat.lt_succ_self _) hlen).ne'
        have hs : s'' < A.bubbleCount := hs''
        simp only [ScaledJetAxis.dofPoly, JetAxis.dofPoly, ScaledJetAxis.base, true_and, hs, and_self,
          if_true]
        rw [← jacobiBubble_expand A.depth s'' A.bubbleCount _ _ _ hsub hs]
        refine Finset.sum_congr rfl fun s hs' => ?_
        have : s < A.bubbleCount := Finset.mem_range.mp hs'
        simp [this]
      · simp [ScaledJetAxis.dofPoly, JetAxis.dofPoly, hii]
    · intro b _ hb
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [ScaledJetAxis.convert, hb]

theorem embedFirst_sum_C_mul (s : Finset JetDof) (c : JetDof → ℂ) (P : JetDof → ℂ[X]) :
    embedFirst (∑ d ∈ s, C (c d) * P d) = ∑ d ∈ s, MvPolynomial.C (c d) * embedFirst (P d) := by
  unfold embedFirst
  simp [map_sum, map_mul, MvPolynomial.algebraMap_eq]

theorem embedSecond_sum_C_mul (s : Finset JetDof) (c : JetDof → ℂ) (P : JetDof → ℂ[X]) :
    embedSecond (∑ d ∈ s, C (c d) * P d) = ∑ d ∈ s, MvPolynomial.C (c d) * embedSecond (P d) := by
  unfold embedSecond
  simp [map_sum, map_mul, MvPolynomial.algebraMap_eq]

theorem sum_four_comm {α β γ δ M : Type} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (v : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d
      = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

end Internal

open Internal in
theorem scaledSplineAgreementHolds : ScaledSplineAgreementHolds := by
  intro H hT hX
  refine ⟨rfl, ?_⟩
  intro i hi j hj
  have hi' : i < cellCount H.tAxis.breaks := hi
  have hj' : j < cellCount H.xAxis.breaks := hj
  show ∑ d ∈ H.tAxis.base.dofs, ∑ e ∈ H.xAxis.base.dofs,
      MvPolynomial.C (∑ d' ∈ H.tAxis.base.dofs, ∑ e' ∈ H.xAxis.base.dofs,
        H.tAxis.convert d d' * H.xAxis.convert e e' * H.coef d' e') *
        embedFirst (H.tAxis.base.dofPoly i d) * embedSecond (H.xAxis.base.dofPoly j e) =
    ∑ d' ∈ H.tAxis.base.dofs, ∑ e' ∈ H.xAxis.base.dofs,
      MvPolynomial.C (H.coef d' e') * embedFirst (H.tAxis.dofPoly i d') * embedSecond (H.xAxis.dofPoly j e')
  have hR : ∀ d' ∈ H.tAxis.base.dofs, ∀ e' ∈ H.xAxis.base.dofs,
      MvPolynomial.C (H.coef d' e') * embedFirst (H.tAxis.dofPoly i d') * embedSecond (H.xAxis.dofPoly j e') =
        ∑ d ∈ H.tAxis.base.dofs, ∑ e ∈ H.xAxis.base.dofs,
          MvPolynomial.C (H.tAxis.convert d d' * H.xAxis.convert e e' * H.coef d' e') *
            embedFirst (H.tAxis.base.dofPoly i d) * embedSecond (H.xAxis.base.dofPoly j e) := by
    intro d' hd' e' he'
    rw [← scaledAxis_dofPoly_sum H.tAxis hT.sorted i hi' d' hd',
      ← scaledAxis_dofPoly_sum H.xAxis hX.sorted j hj' e' he',
      embedFirst_sum_C_mul, embedSecond_sum_C_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [map_mul]
    ring
  rw [Finset.sum_congr rfl fun d' hd' => Finset.sum_congr rfl fun e' he' => hR d' hd' e' he']
  rw [← sum_four_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [map_sum, Finset.sum_mul]

end GivenShape

end CertCell

end Breakdown

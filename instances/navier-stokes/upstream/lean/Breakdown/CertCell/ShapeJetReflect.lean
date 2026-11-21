import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount)

namespace Internal

theorem reflectPoly_embedFirst (P : Polynomial ℂ) : reflectPoly (embedFirst P) = embedFirst P := by
  unfold reflectPoly embedFirst
  rw [← Polynomial.aeval_algHom_apply]
  simp

theorem reflectPoly_embedSecond (Q : Polynomial ℂ) :
    reflectPoly (embedSecond Q) = embedSecond (Q.comp (-Polynomial.X)) := by
  unfold reflectPoly embedSecond
  rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_comp]
  simp

theorem reflectPoly_C (c : ℂ) : reflectPoly (MvPolynomial.C c) = MvPolynomial.C c := by
  unfold reflectPoly
  simp

theorem embedSecond_C_mul (c : ℂ) (Q : Polynomial ℂ) :
    embedSecond (Polynomial.C c * Q) = MvPolynomial.C c * embedSecond Q := by
  unfold embedSecond
  simp [map_mul, Polynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem nodalLeft_comp_neg (n p : ℕ) (a b : ℝ) :
    (nodalLeft n p (-b) (-a)).comp (-Polynomial.X) = Polynomial.C ((-1 : ℂ) ^ p) * nodalRight n p a b := by
  unfold nodalLeft nodalRight
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
  have h1 : (Polynomial.C (((-a - -b)⁻¹ : ℝ) : ℂ) * (Polynomial.X - Polynomial.C ((-b : ℝ) : ℂ))).comp
      (-Polynomial.X) = Polynomial.C (((b - a)⁻¹ : ℝ) : ℂ) * (Polynomial.C (b : ℂ) - Polynomial.X) := by
    have : (-a - -b) = b - a := by ring
    rw [this]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp, Polynomial.X_comp]
    push_cast
    simp only [map_neg]
    ring
  rw [h1, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  have : (-a - -b) = (-1) * (a - b) := by ring
  rw [this]
  push_cast
  rw [mul_pow]

theorem nodalRight_comp_neg (n p : ℕ) (a b : ℝ) :
    (nodalRight n p (-b) (-a)).comp (-Polynomial.X) = Polynomial.C ((-1 : ℂ) ^ p) * nodalLeft n p a b := by
  unfold nodalLeft nodalRight
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
  have h1 : (Polynomial.C (((-a - -b)⁻¹ : ℝ) : ℂ) * (Polynomial.C ((-a : ℝ) : ℂ) - Polynomial.X)).comp
      (-Polynomial.X) = Polynomial.C (((b - a)⁻¹ : ℝ) : ℂ) * (Polynomial.X - Polynomial.C (a : ℂ)) := by
    have : (-a - -b) = b - a := by ring
    rw [this]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp, Polynomial.X_comp]
    push_cast
    simp only [map_neg]
    ring
  rw [h1, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  have : (-b - -a) = (-1) * (b - a) := by ring
  rw [this]
  push_cast
  rw [mul_pow]

theorem bubblePoly_comp_neg (n s : ℕ) (a b : ℝ) :
    (bubblePoly n s (-b) (-a)).comp (-Polynomial.X) = Polynomial.C ((-1 : ℂ) ^ s) * bubblePoly n s a b := by
  unfold bubblePoly
  have hm : ((-b + -a) / 2 : ℝ) = -((a + b) / 2) := by ring
  rw [hm]
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.neg_comp, Polynomial.C_comp, Complex.ofReal_neg, map_neg, map_pow, map_one]
  have hq : ∀ q : Polynomial ℂ, (-Polynomial.X - -q) ^ s = (-1) ^ s * (Polynomial.X - q) ^ s := fun q => by
    rw [← mul_pow]
    ring
  rw [hq]
  ring

theorem reflectPoly_mul (x y : MvPolynomial (Fin 2) ℂ) : reflectPoly (x * y) = reflectPoly x * reflectPoly y := by
  unfold reflectPoly
  exact map_mul _ x y

theorem reflectPoly_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    reflectPoly (∑ x ∈ s, f x) = ∑ x ∈ s, reflectPoly (f x) := by
  unfold reflectPoly
  exact map_sum _ f s

theorem reflectPoly_term (c : ℂ) (P Q : Polynomial ℂ) :
    reflectPoly (MvPolynomial.C c * embedFirst P * embedSecond Q) =
      MvPolynomial.C c * embedFirst P * embedSecond (Q.comp (-Polynomial.X)) := by
  rw [reflectPoly_mul, reflectPoly_mul, reflectPoly_C, reflectPoly_embedFirst, reflectPoly_embedSecond]

theorem getD_of_symmetric (l : List ℝ) (hS : (l.map Neg.neg).reverse = l) (m : ℕ) (hm : m < l.length) :
    l.getD (l.length - 1 - m) 0 = -l.getD m 0 := by
  have h1 : l.length - 1 - m < ((l.map Neg.neg).reverse).length := by simp; omega
  calc l.getD (l.length - 1 - m) 0 = ((l.map Neg.neg).reverse).getD (l.length - 1 - m) 0 := by rw [hS]
    _ = -l.getD m 0 := by
      rw [List.getD_eq_getElem _ _ h1, List.getElem_reverse, List.getElem_map, List.getD_eq_getElem _ _ hm]
      congr 2
      simp
      omega

theorem mem_dofs (A : JetAxis) (e : JetDof) : e ∈ A.dofs ↔
    (∃ k p, k ≤ cellCount A.breaks ∧ p < A.depth ∧ e = JetDof.node k p) ∨
      (∃ i s, i < cellCount A.breaks ∧ s < A.bubbleCount ∧ e = JetDof.bubble i s) := by
  simp only [JetAxis.dofs, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro (⟨k, p, ⟨hk, hp⟩, rfl⟩ | ⟨i, s, ⟨hi, hs⟩, rfl⟩)
    · exact Or.inl ⟨k, p, by omega, hp, rfl⟩
    · exact Or.inr ⟨i, s, hi, hs, rfl⟩
  · rintro (⟨k, p, hk, hp, rfl⟩ | ⟨i, s, hi, hs, rfl⟩)
    · exact Or.inl ⟨k, p, ⟨by omega, hp⟩, rfl⟩
    · exact Or.inr ⟨i, s, ⟨hi, hs⟩, rfl⟩

theorem reflectDof_mem (A : JetAxis) (e : JetDof) (he : e ∈ A.dofs) : A.reflectDof e ∈ A.dofs := by
  rw [mem_dofs] at he ⊢
  rcases he with ⟨k, p, hk, hp, rfl⟩ | ⟨i, s, hi, hs, rfl⟩
  · exact Or.inl ⟨cellCount A.breaks - k, p, by omega, hp, rfl⟩
  · exact Or.inr ⟨cellCount A.breaks - 1 - i, s, by omega, hs, rfl⟩

theorem reflectDof_reflectDof (A : JetAxis) (e : JetDof) (he : e ∈ A.dofs) :
    A.reflectDof (A.reflectDof e) = e := by
  rw [mem_dofs] at he
  rcases he with ⟨k, p, hk, hp, rfl⟩ | ⟨i, s, hi, hs, rfl⟩
  · simp only [JetAxis.reflectDof, JetDof.node.injEq, and_true]
    omega
  · simp only [JetAxis.reflectDof, JetDof.bubble.injEq, and_true]
    omega

theorem dofPoly_reflect (A : JetAxis) (hS : IsSymmetricAxis A) (j : ℕ) (hj : j < cellCount A.breaks)
    (e : JetDof) (he : e ∈ A.dofs) :
    (A.dofPoly (cellCount A.breaks - 1 - j) e).comp (-Polynomial.X) =
      Polynomial.C (JetAxis.dofSign e) * A.dofPoly j (A.reflectDof e) := by
  have hlen : j + 1 < A.breaks.length := by unfold cellCount at hj; omega
  have h0 : A.breaks.getD (cellCount A.breaks - 1 - j) 0 = -A.breaks.getD (j + 1) 0 := by
    rw [← getD_of_symmetric A.breaks hS (j + 1) hlen]
    congr 1
    unfold cellCount
    omega
  have h1 : A.breaks.getD (cellCount A.breaks - 1 - j + 1) 0 = -A.breaks.getD j 0 := by
    rw [← getD_of_symmetric A.breaks hS j (by omega)]
    congr 1
    unfold cellCount
    omega
  rw [mem_dofs] at he
  rcases he with ⟨k, p, hk, hp, rfl⟩ | ⟨i, s, hi, hs, rfl⟩
  · simp only [JetAxis.dofPoly, JetAxis.reflectDof, JetAxis.dofSign, if_pos hp]
    rw [h0, h1]
    by_cases hk1 : k = cellCount A.breaks - 1 - j
    · rw [if_pos hk1, if_neg (by omega), if_pos (by omega), nodalLeft_comp_neg]
    · rw [if_neg hk1]
      by_cases hk2 : k = cellCount A.breaks - 1 - j + 1
      · rw [if_pos hk2, if_pos (by omega), nodalRight_comp_neg]
      · rw [if_neg hk2, if_neg (by omega), if_neg (by omega)]
        simp
  · simp only [JetAxis.dofPoly, JetAxis.reflectDof, JetAxis.dofSign]
    rw [h0, h1]
    by_cases hi1 : i = cellCount A.breaks - 1 - j
    · rw [if_pos ⟨hi1, hs⟩, if_pos ⟨by omega, hs⟩, bubblePoly_comp_neg]
    · rw [if_neg (fun h => hi1 h.1), if_neg (fun h => hi1 (by omega))]
      simp

end Internal

open Internal in
theorem jetReflection : JetReflection := by
  intro odd H _ _ hS hfix
  unfold IsSymmetricAxis at hS
  refine ⟨?_, ?_⟩
  · simp only [JetSpline.toSpline, reflectSpline]
    rw [hS]
  · intro i _ j hj
    change j < cellCount H.xAxis.breaks at hj
    simp only [JetSpline.toSpline, reflectSpline]
    rw [reflectPoly_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [reflectPoly_sum, Finset.mul_sum]
    symm
    refine Finset.sum_nbij' H.xAxis.reflectDof H.xAxis.reflectDof (fun e he => reflectDof_mem _ _ he)
      (fun e he => reflectDof_mem _ _ he) (fun e he => reflectDof_reflectDof _ _ he)
      (fun e he => reflectDof_reflectDof _ _ he) (fun e he => ?_)
    rw [reflectPoly_term, dofPoly_reflect H.xAxis hS j hj e he, embedSecond_C_mul, hfix d e he]
    simp only [map_mul]
    ring

end GivenShape

end CertCell

end Breakdown

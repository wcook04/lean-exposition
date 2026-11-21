import TorusEuler.Paper.SBD.Vocabulary

/-! # Glue for the proof of display (D.2): sorted words and the half-Hölder term bound

Public copies (namespace `TorusEuler.Paper.Lib.SBD`) of private lemmas of
TorusEuler/HierarchySourceBounds.lean, verbatim except for names and
visibility:

* `appendSorted`, `appendSorted_perm`, `appendSorted_mem`,
  `appendSorted_injective` (HierarchySourceBounds.lean:61-85) →
  `appendSorted'`, `appendSorted'_perm`, `appendSorted'_mem`,
  `appendSorted'_injective` (glue on nondecreasing words);
* `norm_labelLinearMap_le_sum` (:375) → `norm_labelLinearMap_le_sum'` (glue);
* `norm_sub_sqrt_of_derivative` (:397) → `norm_sub_sqrt_of_derivative'` (the
  interpolation `[v]_{C^{0,1/2}} ≤ (2‖v‖_∞ ‖∇v‖_∞)^{1/2}` of
  sections/appD_finite_norms.tex:31-33, which belongs to display (D.2));
* `holderWord_le` is the per-word bound `hTerm` (:437-477) inside the proof of
  `hierarchyFiniteWordNorm_holder_le` (:417-494), extracted as a lemma whose
  boundedness hypotheses are stated per word (display (D.2), own content of
  the row `Text eq_D_2`). -/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.SBD

section Words

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Append a letter to a word and sort. Copy of the private `appendSorted`
(HierarchySourceBounds.lean:61). -/
def appendSorted' (i : ι) (w : List ι) : List ι := (w ++ [i]).mergeSort

omit [Fintype ι] in
/-- Copy of the private `appendSorted_perm` (HierarchySourceBounds.lean:64). -/
theorem appendSorted'_perm (i : ι) (w : List ι) :
    (appendSorted' i w).Perm (w ++ [i]) := List.mergeSort_perm _ _

/-- Copy of the private `appendSorted_mem` (HierarchySourceBounds.lean:67). -/
theorem appendSorted'_mem (i : ι) {n : ℕ} {w : List ι}
    (hw : w ∈ hierarchyAdmissibleWords ι n) :
    appendSorted' i w ∈ hierarchyAdmissibleWords ι (n + 1) := by
  have hlen := (appendSorted'_perm i w).length_eq
  have hwlen := (mem_hierarchyAdmissibleWords.mp hw).1
  have hsort : (appendSorted' i w).Pairwise (· ≤ ·) := List.pairwise_mergeSort' _ _
  apply mem_hierarchyAdmissibleWords.mpr
  simpa only [hlen, List.length_append, List.length_singleton] using
    ⟨Nat.succ_le_succ hwlen, hsort⟩

/-- Copy of the private `appendSorted_injective` (HierarchySourceBounds.lean:76). -/
theorem appendSorted'_injective (i : ι) {n : ℕ} :
    Set.InjOn (appendSorted' i) (hierarchyAdmissibleWords ι n : Set (List ι)) := by
  intro v hv w hw h
  have h₁' : (v ++ [i]).Perm (w ++ [i]) :=
    (appendSorted'_perm i v).symm.trans (h ▸ appendSorted'_perm i w)
  have hv' : (v ++ [i]).Perm (i :: v) := List.perm_append_comm
  have hw' : (w ++ [i]).Perm (i :: w) := List.perm_append_comm
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ a b => le_antisymm a b)
    (mem_hierarchyAdmissibleWords.mp hv).2 (mem_hierarchyAdmissibleWords.mp hw).2
    ((hv'.symm.trans (h₁'.trans hw')).cons_inv)

end Words

section Holder

variable {T G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The operator norm of a linear map on `ℝ³` is at most the sum of its values
on the coordinate directions. Copy of the private `norm_labelLinearMap_le_sum`
(HierarchySourceBounds.lean:375). -/
theorem norm_labelLinearMap_le_sum' (A : Vec3 →L[ℝ] G) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (coordinateDirection i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : ∑ i : Fin 3, (x i) • coordinateDirection i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateDirection]
      using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  calc
    ‖A x‖ = ‖∑ i : Fin 3, (x i) • A (coordinateDirection i)‖ := by
      have h := congrArg A hx
      rw [map_sum] at h
      simp only [map_smul] at h
      exact congrArg norm h.symm
    _ ≤ ∑ i : Fin 3, ‖(x i) • A (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖A (coordinateDirection i)‖ * ‖x‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]

/-- The geometric-mean estimate of (D.2): bounding `|v(x) - v(y)|` by both
`2‖v‖_∞` and `‖∇v‖_∞ |x - y|` gives `|v(x) - v(y)| ≤ (2AB)^{1/2} |x - y|^{1/2}`.
Copy of the private `norm_sub_sqrt_of_derivative` (HierarchySourceBounds.lean:397). -/
theorem norm_sub_sqrt_of_derivative' {f : Vec3 → G} (hf : Differentiable ℝ f)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ x, ‖f x‖ ≤ A) (hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ B) (x y : Vec3) :
    ‖f x - f y‖ ≤ Real.sqrt (2 * A * B) * Real.sqrt (dist x y) := by
  have hdiff : ‖f x - f y‖ ≤ B * dist x y := by
    simpa only [dist_eq_norm] using
      (convex_univ : Convex ℝ (Set.univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hf z) (fun z _ => hderiv z) (Set.mem_univ y) (Set.mem_univ x)
  have hsum : ‖f x - f y‖ ≤ 2 * A := by
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hval x) (hval y))
  have hsq : ‖f x - f y‖ ^ 2 ≤ (2 * A * B) * dist x y := by
    rw [sq, mul_assoc]
    exact mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The per-word half-Hölder bound of (D.2): for `0 < ℓ ≤ 1`, every quantity
of the half-Hölder word `w` (in the directions `ℓ e_i`) is at most
`(A_w + ∑_i A_{w i}) / √ℓ`, where `A_v` is the supremum of the word `v` and
`w i` is `w` with the letter `i` appended and sorted. This is the bound `hTerm`
in the proof of `hierarchyFiniteWordNorm_holder_le`
(HierarchySourceBounds.lean:437-477), with per-word boundedness hypotheses. -/
theorem holderWord_le (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1)
    {f : T → Vec3 → G} (hf : ∀ t, ContDiff ℝ ∞ (f t)) (w : List (Fin 3))
    (hbw : BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) w f))
    (hbi : ∀ i, BddAbove
      (hierarchyJetValues False (hierarchyLabelDirection ℓ) (appendSorted' i w) f)) :
    ∀ r ∈ hierarchyJetValues True (hierarchyLabelDirection ℓ) w f,
      r ≤ (sSup (hierarchyJetValues False (hierarchyLabelDirection ℓ) w f) +
        ∑ i : Fin 3,
          sSup (hierarchyJetValues False (hierarchyLabelDirection ℓ) (appendSorted' i w) f)) /
          Real.sqrt ℓ := by
  let D := hierarchyLabelDirection ℓ
  let d (i : Fin 3) := D i 0
  let A := sSup (hierarchyJetValues False D w f)
  let B (i : Fin 3) := sSup (hierarchyJetValues False D (appendSorted' i w) f)
  let b := ∑ i : Fin 3, B i
  let g (t : T) := phaseOperatorWord D w (f t)
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have hsℓ₁ : Real.sqrt ℓ ≤ 1 := by simpa using Real.sqrt_le_sqrt hℓ₁
  have ha : 0 ≤ A := le_csSup hbw (Or.inl rfl)
  have hbi0 (i : Fin 3) : 0 ≤ B i := le_csSup (hbi i) (Or.inl rfl)
  have hbb : 0 ≤ b := Finset.sum_nonneg fun i _ => hbi0 i
  have hval (t : T) (x : Vec3) : ‖g t x‖ ≤ A :=
    le_csSup hbw (Or.inr (Or.inl ⟨t, x, rfl⟩))
  have hderiv (t : T) (x : Vec3) : ‖fderiv ℝ (g t) x‖ ≤ b / ℓ := by
    refine (norm_labelLinearMap_le_sum' _).trans ?_
    rw [show b / ℓ = ∑ i : Fin 3, B i / ℓ from Finset.sum_div _ _ _]
    refine Finset.sum_le_sum fun i _ => ?_
    have hperm : (i :: w).Perm (appendSorted' i w) :=
      (show ([i] ++ w).Perm (w ++ [i]) from List.perm_append_comm).trans
        (appendSorted'_perm i w).symm
    have heq := congrFun (phaseOperatorWord_constantDirections_perm d (hf t) hperm) x
    have hp : ‖phaseOperatorWord D (appendSorted' i w) (f t) x‖ ≤ B i :=
      le_csSup (hbi i) (Or.inr (Or.inl ⟨t, x, rfl⟩))
    change fderiv ℝ (g t) x (ℓ • coordinateDirection i) =
      phaseOperatorWord D (appendSorted' i w) (f t) x at heq
    rw [← heq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at hp
    exact (le_div_iff₀ hℓ).2 (by simpa only [mul_comm] using hp)
  have h0 : 0 ≤ (A + b) / Real.sqrt ℓ := by positivity
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩)
  · exact h0
  · apply (le_div_iff₀ hsℓ).2
    exact (mul_le_mul (hval t x) hsℓ₁ (Real.sqrt_nonneg _) ha).trans (by linarith)
  · by_cases hxy : x = y
    · subst y
      simpa only [sub_self, norm_zero, zero_div] using h0
    · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).2
      have hd : Differentiable ℝ (g t) :=
        (contDiff_phaseOperatorWord (fun _ => contDiff_const) (hf t) w).differentiable (by simp)
      refine (norm_sub_sqrt_of_derivative' hd ha (div_nonneg hbb hℓ.le)
        (hval t) (hderiv t) x y).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      rw [show 2 * A * (b / ℓ) = (2 * A * b) / ℓ by ring,
        Real.sqrt_div (by positivity)]
      apply div_le_div_of_nonneg_right _ hsℓ.le
      exact Real.sqrt_le_iff.mpr ⟨add_nonneg ha hbb, by nlinarith [sq_nonneg A, sq_nonneg b]⟩

end Holder

end TorusEuler.Paper.Lib.SBD

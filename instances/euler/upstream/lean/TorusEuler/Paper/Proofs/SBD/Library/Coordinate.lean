import TorusEuler.Paper.SBD.Vocabulary

/-! # Glue for the proof of Lemma D.2: coordinate words and operator norms

Public copies (namespace `TorusEuler.Paper.Lib.SBD`) of two private glue
lemmas of TorusEuler/PaperAppendixDCoordinate.lean, generalized from a normed
algebra `A` to an arbitrary real normed space `X` (Lemma D.2 is stated for
bilinear products of normed-space-valued coefficients):

* `appendixSumCoordinateDirection` (PaperAppendixDCoordinate.lean:28) →
  `sumCoordinateDirection'` (verbatim);
* `appendixOpNorm_le_coordinateSum` (PaperAppendixDCoordinate.lean:37) →
  `opNorm_le_coordinateSum'` (target type `A` replaced by `X`; proof verbatim).

Then the glue between (D.6) (`AppendixD.CoefficientPower`, stated with one
nondecreasing unit coordinate word per multi-index) and pointwise bounds on
the operator norms of the iterated derivatives, in both directions. -/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.SBD

open AppendixD

section
variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A vector of `ℝ³` is the sum of its coordinates times the coordinate
directions. Copy of the private `appendixSumCoordinateDirection`
(PaperAppendixDCoordinate.lean:28). -/
theorem sumCoordinateDirection' (v : Vec3) : (∑ i, v i • coordinateDirection i) = v := by
  apply PiLp.ext
  intro j
  let ev := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change ev (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [ev, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

/-- The operator norm of a multilinear map on `ℝ³` is at most the sum of its
values on the ordered coordinate words. Copy of the private
`appendixOpNorm_le_coordinateSum` (PaperAppendixDCoordinate.lean:37), with the
target normed algebra replaced by a real normed space. -/
theorem opNorm_le_coordinateSum' {m : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) X) :
    ‖D‖ ≤ ∑ β : Fin m → Fin 3, ‖D (fun i => coordinateDirection (β i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro p
  have h := D.toMultilinearMap.map_sum (fun j i => p j i • coordinateDirection i)
  have hsum : (fun j => ∑ i, p j i • coordinateDirection i) = p :=
    funext fun j => sumCoordinateDirection' (p j)
  rw [hsum] at h
  change D p = ∑ β : Fin m → Fin 3, D (fun j => p j (β j) • coordinateDirection (β j)) at h
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [show D (fun j => p j (β j) • coordinateDirection (β j)) =
    (∏ j, p j (β j)) • D (fun j => coordinateDirection (β j)) from
      D.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun j _ => PiLp.norm_apply_le (p j) (β j))) (norm_nonneg _)

/-- The unweighted label directions are the constant coordinate directions. -/
theorem hierarchyLabelDirection_one :
    hierarchyLabelDirection 1 = fun j (_ : Vec3) => coordinateDirection j := by
  funext j x
  exact one_smul ℝ (coordinateDirection j)

/-- A unit coordinate word, applied to a smooth field, is the iterated
derivative evaluated at the coordinate directions of the word. -/
theorem phaseOperatorWord_labelOne_ofFn (m : ℕ) (β : Fin m → Fin 3) {f : Vec3 → X}
    (hf : ContDiff ℝ ∞ f) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) (List.ofFn β) f x =
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by
  rw [hierarchyLabelDirection_one, phaseOperatorWord_constant_eq_iteratedFDeriv _ hf]
  simp only [List.get_ofFn]
  have h (k : ℕ) (hk : k = m) :
      iteratedFDeriv ℝ k f x (fun j => coordinateDirection (β (Fin.cast hk j))) =
        iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by subst k; rfl
  exact h _ List.length_ofFn

/-- (D.6) gives pointwise operator-norm bounds: `‖D^m c(t,x)‖ ≤ 3^m C_m 𝖣^{a(m+1)}`.
Every ordered coordinate word is a permutation of a nondecreasing one, whose
supremum is bounded by `|c|_m`. -/
theorem coefficientPower_pointwise {C : ℕ → ℝ} {D : ℝ} {a : ℕ} {c : I → Vec3 → X}
    (hc : CoefficientPower C D a c) (m : ℕ) (t : I) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (c t) x‖ ≤ 3 ^ m * (C m * D ^ (a * (m + 1))) := by
  refine (opNorm_le_coordinateSum' _).trans ?_
  have hterm (β : Fin m → Fin 3) :
      ‖iteratedFDeriv ℝ m (c t) x (fun i => coordinateDirection (β i))‖ ≤
        C m * D ^ (a * (m + 1)) := by
    let w := (List.ofFn β).mergeSort (· ≤ ·)
    have hperm : w.Perm (List.ofFn β) := List.mergeSort_perm _ _
    have hlen : w.length = m := hperm.length_eq.trans List.length_ofFn
    have hw : w ∈ appendixCoefficientOrderWords m :=
      Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr
        ⟨hlen.le, List.pairwise_mergeSort' (· ≤ ·) _⟩, hlen⟩
    have hword := congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection
      (hc.1 t) hperm) x
    rw [← phaseOperatorWord_labelOne_ofFn m β (hc.1 t), hierarchyLabelDirection_one, ← hword,
      ← hierarchyLabelDirection_one]
    exact (le_csSup (hc.2.1 m w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans
      ((Finset.single_le_sum (fun v hv => le_csSup (hc.2.1 m v hv) (Or.inl rfl)) hw).trans
        (hc.2.2 m))
  calc
    _ ≤ ∑ _β : Fin m → Fin 3, C m * D ^ (a * (m + 1)) := Finset.sum_le_sum fun β _ => hterm β
    _ = _ := by simp

/-- Conversely, pointwise operator-norm bounds `‖D^m f(t,x)‖ ≤ K_m 𝖣^{a(m+1)}`
give (D.6) with the constants `#W_m · K_m`, where `W_m` are the nondecreasing
words of length `m`. -/
theorem coefficientPower_of_pointwise {K : ℕ → ℝ} {D : ℝ} {a : ℕ} {f : I → Vec3 → X}
    (hs : ∀ t, ContDiff ℝ ∞ (f t)) (hK : ∀ m, 0 ≤ K m) (hD : 0 ≤ D)
    (h : ∀ m t x, ‖iteratedFDeriv ℝ m (f t) x‖ ≤ K m * D ^ (a * (m + 1))) :
    CoefficientPower (fun m => (appendixCoefficientOrderWords m).card * K m) D a f := by
  have hb (m : ℕ) (w : List (Fin 3)) (hw : w ∈ appendixCoefficientOrderWords m) :
      K m * D ^ (a * (m + 1)) ∈
        upperBounds (hierarchyJetValues False (hierarchyLabelDirection 1) w f) := by
    have hlen := (Finset.mem_filter.mp hw).2
    rintro y (rfl | ⟨t, x, rfl⟩ | ⟨hf, _⟩)
    · exact mul_nonneg (hK m) (by positivity)
    · rw [hierarchyLabelDirection_one, phaseOperatorWord_constant_eq_iteratedFDeriv _ (hs t)]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      calc
        _ ≤ K w.length * D ^ (a * (w.length + 1)) := by
          simpa [coordinateDirection] using h w.length t x
        _ = _ := by rw [hlen]
    · exact hf.elim
  refine ⟨hs, fun m w hw => ⟨_, hb m w hw⟩, fun m => ?_⟩
  unfold coefficientOrderNorm
  calc
    _ ≤ ∑ _w ∈ appendixCoefficientOrderWords m, K m * D ^ (a * (m + 1)) :=
      Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hb m w hw)
    _ = _ := by simp [mul_assoc]

end

end TorusEuler.Paper.Lib.SBD

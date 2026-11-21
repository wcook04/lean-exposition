import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.SBD.Statements

/-! # Coordinate jets (copy for package S678a)

Copy of the coordinate-derivative glue (`Lib.S5a`, `Proofs/S5a/Library/Jets.lean`, lines 23-143), unchanged
except for the namespace `Lib.S678a`; used for the Bernstein bounds derived from (B.1). -/

open Set UnitAddTorus MeasureTheory
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S678a

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

section Coordinates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A vector of `ℝ³` is the sum of its coordinates times the coordinate directions. -/
theorem sum_coordinateDirection (v : Vec3) : (∑ i, v i • coordinateDirection i) = v := by
  apply PiLp.ext
  intro j
  let ev := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change ev (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [ev, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

/-- The operator norm of a multilinear map on `ℝ³` is at most the sum of its values on
coordinate directions. Copy of the private `appendixOpNorm_le_coordinateSum`
(`TorusEuler/PaperAppendixDCoordinate.lean:37`), stated for any normed target space
instead of a normed algebra; same proof. -/
theorem opNorm_le_coordinateSum {m : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) X) :
    ‖D‖ ≤ ∑ β : Fin m → Fin 3, ‖D (fun i => coordinateDirection (β i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro p
  have h := D.toMultilinearMap.map_sum (fun j i => p j i • coordinateDirection i)
  have hsum : (fun j => ∑ i, p j i • coordinateDirection i) = p :=
    funext fun j => sum_coordinateDirection (p j)
  rw [hsum] at h
  change D p = ∑ β : Fin m → Fin 3, D (fun j => p j (β j) • coordinateDirection (β j)) at h
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [show D (fun j => p j (β j) • coordinateDirection (β j)) =
    (∏ j, p j (β j)) • D (fun j => coordinateDirection (β j)) from
      D.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun j _ => PiLp.norm_apply_le (p j) (β j))) (norm_nonneg _)

/-- A linear map on `ℝ³` whose values on the coordinate directions are at most `M` has
operator norm at most `3M`. Copy of the private `norm_linearMap_le_of_coordinateBounds`
(`TorusEuler/ParentVelocityEstimates.lean:165`), for any target space; same proof. -/
theorem norm_linearMap_le_of_coordinateBounds {A : Vec3 →L[ℝ] X} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i, ‖A (coordinateDirection i)‖ ≤ M) : ‖A‖ ≤ 3 * M := by
  refine ContinuousLinearMap.opNorm_le_bound A (mul_nonneg (by norm_num) hM) fun x => ?_
  calc
    ‖A x‖ = ‖∑ i : Fin 3, x i • A (coordinateDirection i)‖ := by
      have heq := congrArg A (sum_coordinateDirection x)
      simp only [map_sum, map_smul] at heq
      exact congrArg norm heq.symm
    _ ≤ ∑ i : Fin 3, ‖x i • A (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, M * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (hA i) (PiLp.norm_apply_le x i) (norm_nonneg _) hM
    _ = _ := by simp; ring

/-- The unit label directions of Appendix D are the coordinate directions. -/
theorem labelDirection_one :
    hierarchyLabelDirection 1 = fun j (_ : Vec3) => coordinateDirection j := by
  funext j x
  exact one_smul ℝ (coordinateDirection j)

/-- The value of a coordinate word is the iterated derivative on the coordinate
directions of its letters. -/
theorem labelWord_eq_iteratedFDeriv {f : Vec3 → X} (hf : ContDiff ℝ ∞ f)
    (w : List (Fin 3)) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => coordinateDirection (w.get i)) := by
  rw [labelDirection_one, phaseOperatorWord_constant_eq_iteratedFDeriv _ hf]

/-- The word of the letters `β 0, …, β (m-1)` is the iterated derivative on
`e_{β 0}, …, e_{β (m-1)}`. -/
theorem ofFnWord_eq_iteratedFDeriv {f : Vec3 → X} (hf : ContDiff ℝ ∞ f) {m : ℕ}
    (β : Fin m → Fin 3) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) (List.ofFn β) f x =
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by
  rw [labelWord_eq_iteratedFDeriv hf]
  simp only [List.get_ofFn]
  have h (k : ℕ) (hk : k = m) :
      iteratedFDeriv ℝ k f x (fun j => coordinateDirection (β (Fin.cast hk j))) =
        iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by subst k; rfl
  exact h _ List.length_ofFn

/-- Symmetry of the derivatives of a smooth function: every coordinate component
`D^m f(x)(e_{β 0}, …, e_{β (m-1)})` is the value of one nondecreasing coordinate word
of length `m` (the sorted word of the letters of `β`). -/
theorem exists_sortedWord {f : Vec3 → X} (hf : ContDiff ℝ ∞ f) {m : ℕ} (β : Fin m → Fin 3) :
    ∃ w ∈ appendixCoefficientOrderWords m, ∀ x,
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) =
        phaseOperatorWord (hierarchyLabelDirection 1) w f x := by
  let w := (List.ofFn β).mergeSort (· ≤ ·)
  have hperm : w.Perm (List.ofFn β) := List.mergeSort_perm _ _
  have hlen : w.length = m := hperm.length_eq.trans List.length_ofFn
  refine ⟨w, Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr
    ⟨hlen.le, List.pairwise_mergeSort' (· ≤ ·) _⟩, hlen⟩, fun x => ?_⟩
  have hword := congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection hf hperm) x
  rw [← ofFnWord_eq_iteratedFDeriv hf β x, labelDirection_one, ← hword]

/-- A nondecreasing coordinate word of length `m` is the word of a monotone map
`Fin m → Fin 3`. -/
theorem exists_monotone_of_orderWord {m : ℕ} {w : List (Fin 3)}
    (hw : w ∈ appendixCoefficientOrderWords m) :
    ∃ β : Fin m → Fin 3, Monotone β ∧ List.ofFn β = w := by
  obtain ⟨hadm, hlen⟩ := Finset.mem_filter.mp hw
  have hsorted := (mem_hierarchyAdmissibleWords.mp hadm).2
  refine ⟨fun i => w.get (Fin.cast hlen.symm i), fun i j hij => ?_, ?_⟩
  · exact List.Pairwise.rel_get_of_le hsorted (a := Fin.cast hlen.symm i) (b := Fin.cast hlen.symm j) hij
  · apply List.ext_get
    · simp [hlen]
    · intro n h₁ h₂
      simp

end Coordinates

end

end TorusEuler.Paper.Lib.S678a

module

public import QuarticQuery.Paper.AppendixAHuang
public import Complexity.Foundations.BooleanAnalysis.FourierRestriction
public import Complexity.Foundations.Data.Finset.Expect

/-!
# Appendix A: coefficient preservation under restriction

Compiled as part of the `QuarticQuery` library target.

The restriction is first represented on the original ambient cube by a function
ignoring all coordinates outside `S`. The normalized Fourier coefficient is
unchanged for every fixed outside assignment. The subsequent face-restriction
and coordinate-reindexing lemmas identify the same coefficient on the genuine
`Fin #S` cube, and the final theorem gives its explicit large parity fiber.
-/

public section

namespace QuarticQuery.Paper

open Finset Function Cslib
open Cslib.BitString Cslib.QueryComplexity

variable {n : ℕ}

/-- Ledger: claim-restrict-parity. Fill the coordinates outside `S` from `z`. -/
def appendixAFaceFill (S : Finset (Fin n)) (z : BitInput (Fin n))
    (y : S → Bool) : BitInput (Fin n) :=
  fun i => if hi : i ∈ S then y ⟨i, hi⟩ else z i

/-- Ledger: claim-restrict-parity. Filling the restriction of an ambient input
is the usual piecewise restriction. -/
theorem appendixAFaceFill_restrict (S : Finset (Fin n)) (z x : BitInput (Fin n)) :
    appendixAFaceFill S z (fun i : S => x i) = S.piecewise x z := by
  funext i
  by_cases hi : i ∈ S <;> simp [appendixAFaceFill, hi]

/-- Ledger: claim-restrict-parity. Restricting a filled face recovers its input. -/
theorem appendixAFaceFill_apply (S : Finset (Fin n)) (z : BitInput (Fin n))
    (y : S → Bool) (i : S) : appendixAFaceFill S z y i = y i := by
  simp [appendixAFaceFill, i.property]

/-- Ledger: claim-restrict-parity. Parity on the face is parity on its support. -/
theorem appendixA_chi_restrict (S : Finset (Fin n)) (x : BitInput (Fin n)) :
    chi ℝ (univ : Finset S) (fun i : S => x i) = chi ℝ S x := by
  simp only [chi]
  exact Finset.prod_coe_sort S (fun i : Fin n => (-1 : ℝ) ^ (x i).toNat)

/-- Ledger: claim-restrict-parity. Renaming all parity coordinates preserves
their product. -/
theorem appendixA_chi_univ_equiv {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (x : α → Bool) :
    chi ℝ (univ : Finset β) (fun j => x (e.symm j)) = chi ℝ univ x := by
  simp only [chi]
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

/-- Ledger: claim-restrict-parity. A genuine `#S`-dimensional restricted
function, with the support enumerated by `S.equivFin`. -/
noncomputable def appendixAFaceEmbedding (S : Finset (Fin n)) (z : BitInput (Fin n))
    (y : BitInput (Fin #S)) : BitInput (Fin n) :=
  appendixAFaceFill S z (fun i : S => y (S.equivFin i))

/-- Ledger: claim-restrict-parity. Evaluation at the enumerated free coordinate. -/
theorem appendixAFaceEmbedding_apply (S : Finset (Fin n)) (z : BitInput (Fin n))
    (y : BitInput (Fin #S)) (i : Fin #S) :
    appendixAFaceEmbedding S z y (S.equivFin.symm i) = y i := by
  simp [appendixAFaceEmbedding, appendixAFaceFill, (S.equivFin.symm i).property]

/-- Ledger: claim-restrict-parity. Distinct face inputs remain distinct after filling. -/
theorem appendixAFaceEmbedding_injective (S : Finset (Fin n)) (z : BitInput (Fin n)) :
    Function.Injective (appendixAFaceEmbedding S z) := by
  intro x y h
  funext i
  have hi := congrFun h (S.equivFin.symm i)
  simpa only [appendixAFaceEmbedding_apply] using hi

/-- Ledger: claim-restrict-parity. A free-coordinate bit flip becomes exactly
one original-coordinate bit flip after filling. -/
theorem appendixAFaceEmbedding_update (S : Finset (Fin n)) (z : BitInput (Fin n))
    (x : BitInput (Fin #S)) (i : Fin #S) :
    appendixAFaceEmbedding S z (update x i (!x i)) =
      update (appendixAFaceEmbedding S z x) (S.equivFin.symm i).val
        (!(appendixAFaceEmbedding S z x (S.equivFin.symm i))) := by
  funext j
  by_cases hji : j = (S.equivFin.symm i).val
  · subst j
    simp only [appendixAFaceEmbedding_apply, update_self]
  · rw [update_of_ne hji]
    by_cases hj : j ∈ S
    · have hindex : S.equivFin ⟨j, hj⟩ ≠ i := by
        intro h
        have heq : (⟨j, hj⟩ : S) = S.equivFin.symm i :=
          S.equivFin.injective (by simpa using h)
        exact hji (congrArg Subtype.val heq)
      simp [appendixAFaceEmbedding, appendixAFaceFill, hj, hindex]
    · simp [appendixAFaceEmbedding, appendixAFaceFill, hj]

/-- Ledger: claim-restrict-parity. The restricted Boolean function on `Fin #S`. -/
noncomputable def appendixAFaceFin (f : TotalBool (Fin n)) (S : Finset (Fin n))
    (z : BitInput (Fin n)) : TotalBool (Fin #S) :=
  fun y => f (appendixAFaceEmbedding S z y)

/-- Ledger: lem-A.4. Sensitive face coordinates remain sensitive in the
original cube, with the exact filled input and coordinate. -/
theorem appendixAFaceEmbedding_sensitive (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (z : BitInput (Fin n)) (x : BitInput (Fin #S))
    (i : Fin #S) (hi : IsSensitiveCoord (appendixAFaceFin f S z) x i) :
    IsSensitiveCoord f (appendixAFaceEmbedding S z x) (S.equivFin.symm i).val := by
  change f (update (appendixAFaceEmbedding S z x) (S.equivFin.symm i).val
    (!(appendixAFaceEmbedding S z x (S.equivFin.symm i)))) ≠ _
  rw [← appendixAFaceEmbedding_update]
  exact hi

/-- Ledger: claim-restrict-parity. The face's normalized parity correlation
equals the ambient restriction's coefficient, with no cardinality factor. -/
theorem appendixA_faceSubtype_fourier (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (z : BitInput (Fin n)) :
    fourierCoeff (fun y : S → Bool => signVal (f (appendixAFaceFill S z y))) univ =
      fourierCoeff (fun x => signVal (f (S.piecewise x z))) S := by
  unfold Cslib.BitString.fourierCoeff
  dsimp only
  have hrestrict := Fintype.expect_restrict_coordinates
    (p := fun i : Fin n => i ∈ S)
    (fun y : S → Bool => signVal (f (appendixAFaceFill S z y)) * chi ℝ univ y)
  have hinst : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) =
      Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hinst] at hrestrict
  refine hrestrict.symm.trans ?_
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [appendixAFaceFill_restrict, appendixA_chi_restrict]

/-- Ledger: claim-restrict-parity. Enumerating the face by `Fin #S` preserves
its normalized parity correlation. -/
theorem appendixA_faceFin_fourier (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (z : BitInput (Fin n)) :
    fourierCoeff (fun y => signVal (appendixAFaceFin f S z y)) univ =
      fourierCoeff (fun x => signVal (f (S.piecewise x z))) S := by
  rw [← appendixA_faceSubtype_fourier f S z]
  unfold Cslib.BitString.fourierCoeff
  rw [← Fintype.expect_comp_arrowCongr S.equivFin
    (fun y : BitInput (Fin #S) =>
      signVal (appendixAFaceFin f S z y) * chi ℝ univ y)]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [appendixA_chi_univ_equiv S.equivFin]
  congr 1
  simp [appendixAFaceFin, appendixAFaceEmbedding]

/-- Ledger: claim-restrict-parity. Fixing coordinates outside an inclusion-
maximal Fourier support preserves its coefficient for every assignment. -/
theorem appendixA_maximal_fourierCoeff_piecewise
    (p : BitInput (Fin n) → ℝ) (S : Finset (Fin n))
    (hmax : ∀ T, S ⊂ T → fourierCoeff p T = 0) (z : BitInput (Fin n)) :
    fourierCoeff (fun x => p (S.piecewise x z)) S = fourierCoeff p S := by
  rw [fourierCoeff_piecewise,
    sum_eq_single_of_mem S (by simp) fun T hT hTS => ?_]
  · simp
  · have hST : S ⊆ T := by
      rw [← (mem_filter.1 hT).2]
      exact inter_subset_left
    have hstrict : S ⊂ T := Finset.ssubset_iff_subset_ne.2 ⟨hST, Ne.symm hTS⟩
    rw [hmax T hstrict, zero_mul]

/-- Ledger: claim-restrict-parity. Maximum degree makes every strict superset
of the selected sign Fourier support vanish. -/
theorem appendixA_topFourier_strictSupersets_zero (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (hS : #S = degree f) :
    ∀ T, S ⊂ T → fourierCoeff (fun x => signVal (f x)) T = 0 := by
  intro T hST
  refine fourierCoeff_eq_zero_of_mem_lowDegree
    (mem_lowDegree_totalDegree (fun x => signVal (f x))) ?_
  rw [← degree_eq_totalDegree_signVal f, ← hS]
  exact card_lt_card hST

/-- Ledger: claim-restrict-parity. The coefficient of a maximum-degree
monomial survives every outside assignment, with its exact normalization. -/
theorem appendixA_topFourier_survives (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (hS : #S = degree f) (z : BitInput (Fin n)) :
    fourierCoeff (fun x => signVal (f (S.piecewise x z))) S =
      fourierCoeff (fun x => signVal (f x)) S :=
  appendixA_maximal_fourierCoeff_piecewise (fun x => signVal (f x)) S
    (appendixA_topFourier_strictSupersets_zero f S hS) z

/-- Ledger: claim-restrict-parity. The restriction has nonzero parity
correlation for every assignment outside the selected maximum support. -/
theorem appendixA_topFourier_survives_ne_zero (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (hS : #S = degree f)
    (hcoeff : fourierCoeff (fun x => signVal (f x)) S ≠ 0)
    (z : BitInput (Fin n)) :
    fourierCoeff (fun x => signVal (f (S.piecewise x z))) S ≠ 0 := by
  rw [appendixA_topFourier_survives f S hS z]
  exact hcoeff

/-- Ledger: claim-restrict-parity. Every restriction admits a large parity
fiber, in the ambient representation that repeats unused coordinates.
Its internal `S`-edges are sensitive for the restricted function. -/
theorem appendixA_every_restriction_large_fiber (f : TotalBool (Fin n))
    (S : Finset (Fin n)) (hS : #S = degree f)
    (hcoeff : fourierCoeff (fun x => signVal (f x)) S ≠ 0)
    (z : BitInput (Fin n)) :
    ∃ V : Finset (BitInput (Fin n)), 2 ^ n < 2 * #V ∧
      ∀ x ∈ V, ∀ i ∈ S, update x i (!x i) ∈ V →
        IsSensitiveCoord (fun y => f (S.piecewise y z)) x i :=
  appendixA_parityFiber_of_fourier
    (appendixA_topFourier_survives_ne_zero f S hS hcoeff z)

/-- Ledger: claim-restrict-parity. Select the support once; the survival and
large-fiber conclusions hold uniformly for every outside assignment. -/
theorem appendixA_restriction_parity (f : TotalBool (Fin n)) (hf : degree f ≠ 0) :
    ∃ S : Finset (Fin n), #S = degree f ∧
      ∀ z : BitInput (Fin n),
        fourierCoeff (fun x => signVal (f (S.piecewise x z))) S ≠ 0 ∧
        ∃ V : Finset (BitInput (Fin n)), 2 ^ n < 2 * #V ∧
          ∀ x ∈ V, ∀ i ∈ S, update x i (!x i) ∈ V →
            IsSensitiveCoord (fun y => f (S.piecewise y z)) x i := by
  obtain ⟨S, hS, hcoeff⟩ := appendixA_topFourierSupport f hf
  refine ⟨S, hS, fun z => ?_⟩
  exact ⟨appendixA_topFourier_survives_ne_zero f S hS hcoeff z,
    appendixA_every_restriction_large_fiber f S hS hcoeff z⟩

/-- Ledger: claim-restrict-parity. The literal face statement: its dimension
is `degree f`, its parity correlation is nonzero, and an explicit parity fiber
contains more than half its inputs, with every internal cube edge sensitive.
The support is chosen before the arbitrary outside assignment. -/
theorem appendixA_restriction_parity_face (f : TotalBool (Fin n)) (hf : degree f ≠ 0) :
    ∃ S : Finset (Fin n), #S = degree f ∧ ∀ z : BitInput (Fin n),
      fourierCoeff (fun y => signVal (appendixAFaceFin f S z y)) univ ≠ 0 ∧
      ∃ c : Bool,
        2 ^ #S < 2 * #{y : BitInput (Fin #S) |
          (appendixAFaceFin f S z y ^^ parityOn univ y) = c} ∧
        ∀ y, (appendixAFaceFin f S z y ^^ parityOn univ y) = c →
          ∀ i : Fin #S,
            (appendixAFaceFin f S z (update y i (!y i)) ^^
              parityOn univ (update y i (!y i))) = c →
                IsSensitiveCoord (appendixAFaceFin f S z) y i := by
  obtain ⟨S, hS, hcoeff⟩ := appendixA_topFourierSupport f hf
  refine ⟨S, hS, fun z => ?_⟩
  have hne : fourierCoeff (fun y => signVal (appendixAFaceFin f S z y)) univ ≠ 0 := by
    rw [appendixA_faceFin_fourier f S z]
    exact appendixA_topFourier_survives_ne_zero f S hS hcoeff z
  refine ⟨hne, ?_⟩
  obtain ⟨c, hc, he⟩ := appendixA_parityFiber_explicit hne
  exact ⟨c, hc, fun y hy i => he y hy i (mem_univ i)⟩

end QuarticQuery.Paper

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic

/-!
Independent finite-product success mass identity. The result is scalar and
does not claim that the proposed `GateState` source has elaborated. It is the
probability calculation needed after the flag-marking and routing gates.
-/

public section

namespace QuarticQuery.Upper

theorem success_mass_product
    {ι ζ : Type} [Fintype ι] [DecidableEq ι] [Fintype ζ]
    (a : ι → ζ → ℝ) (S : ζ → Bool) :
    (∑ y : ι → ζ,
      if ∃ i, S (y i) = true then ∏ i, a i (y i) else 0) =
      (∏ i, ∑ z, a i z) -
        (∏ i, ∑ z, if S z = false then a i z else 0) := by
  classical
  have htotal :
      (∑ y : ι → ζ, ∏ i, a i (y i)) = ∏ i, ∑ z, a i z := by
    simpa only [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (Finset.univ : Finset ζ) a)
  have hbad :
      (∑ y : ι → ζ,
        if ∀ i, S (y i) = false then ∏ i, a i (y i) else 0) =
        ∏ i, ∑ z, if S z = false then a i z else 0 := by
    let f : ι → ζ → ℝ := fun i z => if S z = false then a i z else 0
    have h := Finset.sum_prod_piFinset (Finset.univ : Finset ζ) f
    simp only [Fintype.piFinset_univ] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hb : ∀ i, S (y i) = false
    · simp [f, hb]
    · obtain ⟨j, hj⟩ := not_forall.mp hb
      have htrue : S (y j) = true := by cases h : S (y j) <;> simp_all
      simp only [if_neg hb, f]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [htrue]
  rw [← htotal, ← hbad, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hs : ∃ i, S (y i) = true
  · have hb : ¬ ∀ i, S (y i) = false := by
      obtain ⟨i, hi⟩ := hs
      intro hall
      have hf := hall i
      rw [hi] at hf
      cases hf
    simp [hs, hb]
  · have hb : ∀ i, S (y i) = false := by
      intro i
      cases h : S (y i) <;> simp_all
    simp [hs, hb]

end QuarticQuery.Upper
end


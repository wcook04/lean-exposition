module

public import QuarticQuery.ForrelationLower.RealLeaves

/-!
# Independent expected values for the real-leaf semantics

These checks use the actual new implementation but fix their expected
answers as rational constants.  They distinguish three-valued leaf
semantics from the earlier two-output interface and detect missing
nonnegativity or reversed input/algorithm quantifiers.
-/

@[expose] public section
set_option autoImplicit false

namespace QuarticQuery.Independent.RealLeaves

open QuarticQuery.ForrelationLower

noncomputable def threeValue : RealQueryTree (Fin 2) :=
  .query 0 (.leaf (-1 / 3)) (.query 1 (.leaf (1 / 5)) (.leaf (4 / 5)))

def x00 : BitInput (Fin 2) := fun _ => false
def x10 : BitInput (Fin 2) := fun i => decide (i = 0)
def x11 : BitInput (Fin 2) := fun _ => true

theorem threeValue_bounded : threeValue.Bounded := by
  norm_num [threeValue, RealQueryTree.Bounded]

theorem threeValue_depth : threeValue.depth = 2 := by decide +kernel

theorem threeValue_answers :
    threeValue.eval x00 = (-1 / 3 : ℝ) ∧
    threeValue.eval x10 = (1 / 5 : ℝ) ∧
    threeValue.eval x11 = (4 / 5 : ℝ) := by
  norm_num [threeValue, RealQueryTree.eval, x00, x10, x11]

/-- A `Bool`-valued function followed by one fixed map cannot produce
these three distinct reachable values, regardless of its query budget. -/
theorem threeValue_not_two_outputs :
    ¬ ∃ (B : BitInput (Fin 2) → Bool) (v : Bool → ℝ),
      ∀ x, v (B x) = threeValue.eval x := by
  rintro ⟨B, v, h⟩
  have h0 := h x00
  have h1 := h x10
  have h2 := h x11
  rw [threeValue_answers.1] at h0
  rw [threeValue_answers.2.1] at h1
  rw [threeValue_answers.2.2] at h2
  cases hb0 : B x00 <;> cases hb1 : B x10 <;> cases hb2 : B x11 <;>
    simp only [hb0, hb1, hb2] at h0 h1 h2 <;> linarith

/-- The missing boundedness guard would permit a normalized *signed*
representation; it is not a probability mixture. -/
theorem unbounded_leaf_has_negative_weight :
    (RealQueryTree.leaf (ι := Fin 1) 2).weight true = (-1 / 2 : ℝ) ∧
    ¬ (RealQueryTree.leaf (ι := Fin 1) 2).Bounded := by
  norm_num [RealQueryTree.weight, RealQueryTree.answerSign, RealQueryTree.Bounded]

/-- A pointwise choice of cap-zero constant tree can follow the input bit. -/
theorem wrong_order_pointwise_constants :
    ∀ x : BitInput (Fin 1), ∃ S : QueryTree (Fin 1),
      S.depth = 0 ∧ S.eval x = x 0 := by
  intro x
  exact ⟨.leaf (x 0), rfl, rfl⟩

/-- A single cap-zero Boolean tree cannot follow both inputs. -/
theorem no_global_zero_tree_for_identity :
    ¬ ∃ S : QueryTree (Fin 1), S.depth = 0 ∧ ∀ x, S.eval x = x 0 := by
  rintro ⟨S, hdepth, h⟩
  cases S with
  | leaf b =>
      have h0 := h (fun _ => false)
      have h1 := h (fun _ => true)
      cases b <;> simp [QueryTree.eval] at h0 h1
  | query i l r =>
      simp only [QueryTree.depth] at hdepth
      omega

end QuarticQuery.Independent.RealLeaves
